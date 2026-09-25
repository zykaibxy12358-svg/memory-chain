/**
 * 记忆链 MemoryChain —— SillyTavern 扩展
 * 实体索引 + 章节链 + 激活衰减 + 分级注入（full / digest / hidden）
 *
 * 性能设计要点：
 *  1. Aho–Corasick 自动机做实体扫描：O(文本长度)，与实体表规模无关
 *  2. 全内存索引：每轮 0 次 I/O；IndexedDB 只在写入章节卡时使用
 *  3. 惰性激活：只对"本轮命中"的实体计算分数，不遍历全库
 *  4. 每轮结果缓存：同一消息（重新生成/多候选）直接复用
 *  5. 预算硬顶 + 早停：注入字数不可能超限
 *  6. 摘要走异步队列（requestIdleCallback + generateQuietPrompt, skipWIAN）
 */

(function () {
    'use strict';

    const MODULE = 'memoryChain';
    const AC_KEY = 'memoryChain';
    const DB_NAME = 'memoryChain';
    const DB_VER = 1;
    const STORE_KV = 'kv';
    const STORE_CARDS = 'cards';
    const NS_TAURI = 'memory-chain';   // TauriTavern extension.store 命名空间（只允许 [A-Za-z0-9_.-]）

    const DEFAULT_SETTINGS = {
        enabled: true,
        budgetChars: 1200,      // 每轮注入硬上限
        hotTurns: 4,            // 热区轮数（只看最近 N 条）
        maxCandidates: 24,      // 参与打分的候选上限
        maxPerEntity: 3,        // 每个实体最多带出几张卡
        lambda: 0.85,           // 时间衰减系数（每章剩 85%）
        fullAge: 6,             // 距今 ≤ N 章 → 完整注入
        digestAge: 30,          // 距今 ≤ N 章 → 一行摘要；再老则隐藏
        minScore: 0.10,         // 低于此分不注入
        autoChapterTurns: 8,    // 每 N 轮自动成章（0 = 关）
        autoSummarize: true,    // 用模型生成章节卡（关则用粗记）
        position: 'IN_CHAT',    // IN_CHAT | IN_PROMPT | BEFORE_PROMPT
        depth: 2,
        genericKeyLimit: 3,     // 某关键词出现在 > N 个条目里 → 视为通用词，丢弃
        minAliasLen: 2,
        debug: false,
    };

    // 兜底停用词（自动通用词过滤之外再挡一层）
    const STOPWORDS = new Set([
        '军团', '战团', '智库', '军团长', '战团长', '动力甲', '终结者', '流星枪', '风暴', '风暴剑',
        '灵气', '虚能', '虚界', '境界', '人口', '声音', '气味', '氛围', '天气', '季节', '建筑', '服饰',
        '饮食', '交通', '能源', '材料', '礼仪', '甲型', '型谱', '力场', '军团编制', '战团编制',
    ]);

    // ---------------------------------------------------------------- 上下文
    // 注意：TauriTavern 以 <script type="module"> 加载扩展，求值时机可能早于宿主就绪，
    //       因此上下文一律用 bindContext() 惰性获取，而不是在模块顶层一次性绑定。
    let ctx = {};
    let eventSource = null;
    let event_types = {};
    let extTypes = { IN_PROMPT: 0, IN_CHAT: 1, BEFORE_PROMPT: 2 };
    let extRoles = { SYSTEM: 0, USER: 1, ASSISTANT: 2 };

    function bindContext() {
        if (typeof SillyTavern === 'undefined' || typeof SillyTavern.getContext !== 'function') return false;
        let c = null;
        try { c = SillyTavern.getContext(); } catch (e) { return false; }
        if (!c) return false;
        ctx = c;
        if (c.eventSource) eventSource = c.eventSource;
        if (c.event_types) event_types = c.event_types;
        if (c.extension_prompt_types) extTypes = c.extension_prompt_types;
        if (c.extension_prompt_roles) extRoles = c.extension_prompt_roles;
        return true;
    }

    const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

    async function waitForContext(timeoutMs) {
        const limit = Date.now() + (timeoutMs || 10000);
        while (Date.now() < limit) {
            if (bindContext()) return true;
            await sleep(200);
        }
        return bindContext();
    }

    // ---------------------------------------------------------------- 状态
    const S = {
        settings: { ...DEFAULT_SETTINGS },
        ns: 'default',
        chapters: [],               // 按 ch 升序
        cardByCh: new Map(),
        entities: new Map(),        // name -> { name, aliases:[], cards:[], lastCh, hits, world }
        aliasMap: new Map(),        // alias -> name
        ac: null,                   // Aho–Corasick 节点
        manualAliases: [],          // [{alias, name}]
        lexicon: null,              // 持久化的世界书词表 { names:[], aliases:[[alias,name]] }
        worldDropped: 0,
        maxHits: 1,
        turnsSinceChapter: 0,
        cache: { key: '', block: '' },
        stats: {
            lastMs: 0, matched: 0, candidates: 0, injected: 0,
            chapters: 0, entities: 0, aliases: 0, lastAt: '',
        },
        db: null,
        storeNote: '',
        pendingSummaries: 0,
    };

    // ---------------------------------------------------------------- 工具
    const log = (...a) => { if (S.settings.debug) console.log('[记忆链]', ...a); };
    const warn = (...a) => console.warn('[记忆链]', ...a);
    const nowMs = () => (typeof performance !== 'undefined' && performance.now ? performance.now() : Date.now());
    const clamp = (v, a, b) => Math.max(a, Math.min(b, v));

    function nsKey() {
        const ch = (ctx.characters && ctx.characters[ctx.characterId]) || null;
        const name = ch ? ch.name : (ctx.name2 || ctx.groupId || 'unknown');
        const meta = ctx.chatMetadata || {};
        // 必须是"稳定"的 id：绝不使用聊天长度（否则每章都会换命名空间）
        const id = ctx.chatId || meta.chat_id || meta.file_name || 'default';
        return String(name) + '::' + String(id);
    }

    // ---------------------------------------------------------------- Aho–Corasick
    function buildAutomaton(pairs) {
        const nodes = [{ next: new Map(), fail: 0, out: [] }];
        for (let i = 0; i < pairs.length; i++) {
            const p = pairs[i].p;
            const e = pairs[i].e;
            let cur = 0;
            for (let j = 0; j < p.length; j++) {
                const c = p[j];
                let nx = nodes[cur].next.get(c);
                if (nx === undefined) {
                    nx = nodes.length;
                    nodes[cur].next.set(c, nx);
                    nodes.push({ next: new Map(), fail: 0, out: [] });
                }
                cur = nx;
            }
            nodes[cur].out.push(e);
        }
        const queue = [];
        nodes[0].next.forEach((n) => { nodes[n].fail = 0; queue.push(n); });
        for (let head = 0; head < queue.length; head++) {
            const r = queue[head];
            nodes[r].next.forEach((n, c) => {
                let f = nodes[r].fail;
                while (f !== 0 && !nodes[f].next.has(c)) f = nodes[f].fail;
                const cand = nodes[f].next.get(c);
                nodes[n].fail = (cand !== undefined && cand !== n) ? cand : 0;
                if (nodes[nodes[n].fail].out.length) {
                    nodes[n].out = nodes[n].out.concat(nodes[nodes[n].fail].out);
                }
                queue.push(n);
            });
        }
        return nodes;
    }

    function acScan(nodes, text) {
        const res = new Map();
        if (!nodes) return res;
        let cur = 0;
        for (let i = 0; i < text.length; i++) {
            const c = text.charCodeAt(i) < 128 ? text[i].toLowerCase() : text[i];
            while (cur !== 0 && !nodes[cur].next.has(c)) cur = nodes[cur].fail;
            const nx = nodes[cur].next.get(c);
            cur = nx !== undefined ? nx : 0;
            const out = nodes[cur].out;
            if (out.length) {
                for (let k = 0; k < out.length; k++) res.set(out[k], (res.get(out[k]) || 0) + 1);
            }
        }
        return res;
    }

    // ---------------------------------------------------------------- 词表 / 实体
    function normalizeAlias(a) {
        return String(a == null ? '' : a).trim();
    }

    function ensureEntity(name) {
        let e = S.entities.get(name);
        if (!e) {
            e = { name: name, aliases: [], cards: [], lastCh: 0, hits: 0, world: false };
            S.entities.set(name, e);
        }
        return e;
    }

    function addAlias(alias, name, force) {
        const a = normalizeAlias(alias);
        if (!a) return false;
        if (a.length < S.settings.minAliasLen && !/^[A-Za-z0-9]{2,}$/.test(a)) return false;
        if (!force && STOPWORDS.has(a)) return false;
        const prev = S.aliasMap.get(a);
        if (prev && prev !== name) return false;      // 别名冲突：先到先得，避免误召回
        const ent = ensureEntity(name);
        if (!S.aliasMap.has(a)) { S.aliasMap.set(a, name); ent.aliases.push(a); }
        return true;
    }

    /** 从世界书 JSON（{entries:{...}}）建实体表：comment = 实体名，key[] = 别名 */
    function buildFromWorldBook(json) {
        const entries = json && json.entries ? json.entries : null;
        if (!entries) throw new Error('不是世界书 JSON（缺少 entries）');
        const list = Array.isArray(entries) ? entries : Object.values(entries);
        const keyFreq = new Map();
        for (const en of list) {
            const keys = Array.isArray(en.key) ? en.key : [];
            for (const k of keys) {
                const kk = normalizeAlias(k);
                if (!kk) continue;
                keyFreq.set(kk, (keyFreq.get(kk) || 0) + 1);
            }
        }
        let dropped = 0, stopped = 0, added = 0;
        for (const en of list) {
            const name = normalizeAlias(en.comment);
            if (!name) continue;
            const ent = ensureEntity(name);
            ent.world = true;
            if (addAlias(name, name, true)) added++;          // 实体名一律保留（即使是"虚能"这类词）
            const keys = Array.isArray(en.key) ? en.key : [];
            for (const k of keys) {
                const kk = normalizeAlias(k);
                if (!kk) continue;
                if ((keyFreq.get(kk) || 0) > S.settings.genericKeyLimit) { dropped++; continue; }
                if (STOPWORDS.has(kk) || kk.length < S.settings.minAliasLen) { stopped++; continue; }
                if (addAlias(kk, name)) added++;
            }
        }
        S.worldDropped = dropped + stopped;
        S.manualAliases.forEach((m) => addAlias(m.alias, m.name, true));
        rebuildAutomaton();
        saveLexicon();
        log('词表构建完成：实体', S.entities.size, '别名', S.aliasMap.size, '丢弃通用词', dropped, '停用词/过短', stopped);
        return { entities: S.entities.size, aliases: S.aliasMap.size, dropped: dropped, stopped: stopped };
    }

    /** 手写别名：每行「别名 => 实体名」 */
    function parseAliasText(text) {
        const out = [];
        String(text || '').split(/\r?\n/).forEach((line) => {
            const m = line.split(/=>|＝>|→|=|＝/);
            if (m.length >= 2) {
                const a = normalizeAlias(m[0]), n = normalizeAlias(m.slice(1).join('='));
                if (a && n) out.push({ alias: a, name: n });
            }
        });
        return out;
    }

    function rebuildAutomaton() {
        const pairs = [];
        S.aliasMap.forEach((name, alias) => pairs.push({ p: alias, e: name }));
        S.ac = buildAutomaton(pairs);
        S.entities.forEach((e) => { e.aliases = e.aliases.filter((a) => S.aliasMap.get(a) === e.name); });
    }

    /** 词表（世界书实体 + 手写别名）持久化：否则每次启动都要重新导入世界书 */
    function saveLexicon() {
        const names = [];
        S.entities.forEach((e) => { if (e.world || e.aliases.length) names.push(e.name); });
        const aliases = [];
        S.aliasMap.forEach((name, alias) => aliases.push([alias, name]));
        persistKV('lexicon', { v: 1, names: names, aliases: aliases, dropped: S.worldDropped });
    }

    function restoreLexicon(lex) {
        if (!lex || !Array.isArray(lex.aliases)) return 0;
        (lex.names || []).forEach((n) => { ensureEntity(n).world = true; });
        let n = 0;
        lex.aliases.forEach((pair) => { if (Array.isArray(pair) && addAlias(pair[0], pair[1], true)) n++; });
        if (typeof lex.dropped === 'number') S.worldDropped = lex.dropped;
        log('词表已从存储恢复：别名', n, '条');
        return n;
    }

    // ---------------------------------------------------------------- 章节卡
    function makeCard(raw) {
        const card = {
            ch: raw.ch,
            span: raw.span || '',
            to: Number.isFinite(Number(raw.to)) ? Number(raw.to) : null,
            when: raw.when || '',
            where: raw.where || '',
            who: Array.isArray(raw.who) ? raw.who : [],
            what: raw.what || '',
            evidence: Array.isArray(raw.evidence) ? raw.evidence : [],
            open: raw.open || '',
            salience: typeof raw.salience === 'number' ? clamp(raw.salience, 0, 1) : 0.5,
            hits: 0,
            len: 0,
        };
        card.len = renderCard(card, 'full').length;
        return card;
    }

    function indexCard(card) {
        const text = [card.who.join(' '), card.what, card.evidence.join(' '), card.open, card.where, card.when].join('\n');
        const hits = acScan(S.ac, text);
        card.ents = Array.from(hits.keys());
        for (const name of card.ents) {
            const ent = ensureEntity(name);
            if (ent.cards.indexOf(card.ch) < 0) ent.cards.push(card.ch);
            ent.lastCh = Math.max(ent.lastCh, card.ch);
        }
    }

    function addChapter(raw) {
        const ch = S.chapters.length ? S.chapters[S.chapters.length - 1].ch + 1 : 1;
        const card = makeCard(Object.assign({}, raw, { ch }));
        S.chapters.push(card);
        S.cardByCh.set(card.ch, card);
        indexCard(card);
        S.turnsSinceChapter = 0;
        S.cache = { key: '', block: '' };
        syncStats();
        persistCard(card);
        return card;
    }

    function syncStats() {
        S.stats.chapters = S.chapters.length;
        S.stats.entities = S.entities.size;
        S.stats.aliases = S.aliasMap.size;
    }

    // ---------------------------------------------------------------- 渲染
    function renderCard(card, state) {
        if (state === 'digest') {
            const who = card.who.length ? card.who.slice(0, 3).join('、') : '';
            const head = '第' + card.ch + '章' + (card.where ? '·' + card.where : '');
            const body = card.what ? '：' + String(card.what).slice(0, 40) : '';
            const open = card.open ? '；悬念：' + card.open : '';
            return '· ' + head + '（' + who + '）' + body + open;
        }
        const lines = [];
        lines.push('【第' + card.ch + '章】' + (card.when || '') + (card.where ? '｜' + card.where : ''));
        if (card.who.length) lines.push('人物：' + card.who.join('、'));
        if (card.what) lines.push('经过：' + card.what);
        if (card.evidence.length) lines.push('物证：' + card.evidence.join(' / '));
        if (card.open) lines.push('悬念：' + card.open);
        return lines.join('\n');
    }

    // ---------------------------------------------------------------- 召回
    function collectHotText(userText) {
        const chat = ctx.chat || [];
        const n = clamp(Number(S.settings.hotTurns) || 4, 1, 20);
        const parts = [];
        for (let i = Math.max(0, chat.length - n); i < chat.length; i++) {
            const m = chat[i];
            if (!m || m.is_system) continue;
            let t = String(m.mes || '');
            if (t.length > 800) t = t.slice(-800);
            parts.push(t);
        }
        if (userText) parts.push(String(userText));
        return parts.join('\n');
    }

    function recall(userText) {
        const t0 = nowMs();
        const empty = { block: '', stats: { ms: nowMs() - t0, matched: 0, candidates: 0, chars: 0 } };
        if (!S.ac || S.chapters.length === 0) return empty;

        const hot = collectHotText(userText);
        const matched = acScan(S.ac, hot);
        if (matched.size === 0) return empty;

        const chNow = S.chapters[S.chapters.length - 1].ch;
        const nMatched = matched.size;
        const candMap = new Map();     // ch -> { card, rel, cnt }

        matched.forEach((cnt, name) => {
            const ent = S.entities.get(name);
            if (!ent || !ent.cards.length) return;
            const list = ent.cards.slice(-clamp(Number(S.settings.maxPerEntity) || 3, 1, 10));
            const newest = ent.cards[ent.cards.length - 1];
            for (const ch of list) {
                const card = S.cardByCh.get(ch);
                if (!card) continue;
                let c = candMap.get(ch);
                if (!c) { c = { card, rel: 0, cnt: 0, latest: false }; candMap.set(ch, c); }
                c.rel += 1;
                c.cnt += cnt;
                if (ch === newest) c.latest = true;
                card.hits++;
                S.maxHits = Math.max(S.maxHits, card.hits);
            }
        });
        if (candMap.size === 0) return empty;

        const budget = clamp(Number(S.settings.budgetChars) || 1200, 200, 8000);
        const lambda = clamp(Number(S.settings.lambda) || 0.85, 0.3, 0.995);
        const maxCand = clamp(Number(S.settings.maxCandidates) || 24, 1, 200);
        const logMax = Math.log(1 + S.maxHits) || 1;

        const cands = [];
        candMap.forEach((c) => {
            const age = Math.max(0, chNow - c.card.ch);
            const rel = c.rel / nMatched;
            const rec = Math.pow(lambda, age);
            const freq = Math.log(1 + c.card.hits) / logMax;
            const type = (c.card.evidence.length ? 1.0 : 0.8) + (c.card.open ? 0.05 : 0) + c.card.salience * 0.15;
            const cost = c.card.len / budget;
            const score = 0.45 * rel + 0.30 * rec + 0.15 * freq + 0.20 * type - 0.10 * cost;
            let state;
            if (age <= Number(S.settings.fullAge) || c.card.salience >= 0.85) state = 'full';
            else if (c.latest && c.cnt > 0) state = 'digest';                       // 复活：被点名就出来
            else if (age <= Number(S.settings.digestAge)) state = 'digest';
            else state = 'hidden';
            cands.push({ card: c.card, score: score, age: age, state: state });
        });

        // 归一化（min-max）
        let lo = Infinity, hi = -Infinity;
        for (const c of cands) { if (c.score < lo) lo = c.score; if (c.score > hi) hi = c.score; }
        const span = (hi - lo) || 1;
        for (const c of cands) c.norm = (c.score - lo) / span;

        cands.sort((a, b) => (b.norm - a.norm) || (a.age - b.age));
        const picked = [];
        let used = 0;
        for (let i = 0; i < cands.length && picked.length < maxCand; i++) {
            const c = cands[i];
            if (c.state === 'hidden') continue;
            if (c.norm < Number(S.settings.minScore) && picked.length > 0) continue;
            let text = renderCard(c.card, c.state);
            if (used + text.length + 1 > budget) {
                if (c.state === 'full') {
                    text = renderCard(c.card, 'digest');
                    if (used + text.length + 1 > budget) break;
                } else break;
            }
            used += text.length + 1;
            picked.push({ ch: c.card.ch, state: c.state, norm: Math.round(c.norm * 100) / 100, text: text });
        }

        if (!picked.length) return empty;
        const block = '【记忆链·相关往事】\n' + picked.map((p) => p.text).join('\n') +
            '\n（以上为既往章节摘要，只能引用其中出现过的人、物与悬念，不得编造新的章节。）';

        const ms = nowMs() - t0;
        S.stats.lastMs = Math.round(ms * 100) / 100;
        S.stats.matched = nMatched;
        S.stats.candidates = cands.length;
        S.stats.injected = block.length;
        S.stats.lastAt = new Date().toLocaleTimeString();
        renderStats();
        log('召回', S.stats, picked.map((p) => p.ch + ':' + p.state).join(','));
        return { block: block, stats: { ms: ms, matched: nMatched, candidates: cands.length, chars: block.length, picked: picked } };
    }

    // ---------------------------------------------------------------- 注入
    function positionValue() {
        const p = S.settings.position;
        if (p === 'IN_PROMPT') return extTypes.IN_PROMPT;
        if (p === 'BEFORE_PROMPT') return extTypes.BEFORE_PROMPT;
        return extTypes.IN_CHAT;
    }

    function inject(text) {
        const fn = (ctx && typeof ctx.setExtensionPrompt === 'function') ? ctx.setExtensionPrompt
            : (typeof setExtensionPrompt === 'function' ? setExtensionPrompt : null);
        if (!fn) return;
        fn(AC_KEY, text || '', positionValue(), clamp(Number(S.settings.depth) || 2, 0, 100), false, extRoles.SYSTEM);
    }

    function onGenerate(userText) {
        if (!S.settings.enabled) { inject(''); return; }
        const key = (ctx.chat ? ctx.chat.length : 0) + '|' + String(userText || '').slice(0, 120);
        if (S.cache.key === key) { inject(S.cache.block); return; }
        const r = recall(userText);
        S.cache = { key: key, block: r.block };
        inject(r.block);
    }

    // ---------------------------------------------------------------- 存储
    // 三级后端：TauriTavern 原生 store（首选）→ IndexedDB → 内存
    const CHUNK = 100;                 // 每 100 章一个分块文件

    function slugify(ns) {
        let h = 5381;
        for (let i = 0; i < ns.length; i++) h = ((h * 33) ^ ns.charCodeAt(i)) >>> 0;
        const ascii = ns.replace(/[^A-Za-z0-9]+/g, '-').replace(/^-+|-+$/g, '').slice(0, 24);
        return (ascii || 'chat') + '-' + h.toString(36);
    }

    const Store = {
        kind: 'memory',
        tauri: null,
        db: null,
        mem: { cards: new Map(), kv: new Map() },
        note: '',

        // ---- TauriTavern：window.__TAURITAVERN__.api.extension.store ----
        async detectTauri(timeoutMs) {
            const w = typeof window !== 'undefined' ? window : {};
            const direct = w.__TAURITAVERN__ && w.__TAURITAVERN__.api && w.__TAURITAVERN__.api.extension && w.__TAURITAVERN__.api.extension.store;
            if (direct) return direct;
            const p = (w.__TAURITAVERN__ && w.__TAURITAVERN__.ready) || w.__TAURITAVERN_MAIN_READY__;
            if (!p || typeof p.then !== 'function') return null;
            try {
                await Promise.race([
                    Promise.resolve(p).catch(() => null),
                    new Promise((r) => setTimeout(r, timeoutMs || 2500)),
                ]);
            } catch (e) { return null; }
            const w2 = typeof window !== 'undefined' ? window : {};
            return (w2.__TAURITAVERN__ && w2.__TAURITAVERN__.api && w2.__TAURITAVERN__.api.extension && w2.__TAURITAVERN__.api.extension.store) || null;
        },

        async init() {
            // 1) TauriTavern
            try {
                const t = await this.detectTauri(2500);
                if (t && typeof t.setJson === 'function') {
                    // 契约自检：写读一次，确认可用
                    const probe = 'probe.' + Date.now();
                    await t.setJson({ namespace: NS_TAURI, key: probe, value: 1 });
                    const back = await t.getJson({ namespace: NS_TAURI, key: probe });
                    await t.deleteJson({ namespace: NS_TAURI, key: probe }).catch(() => {});
                    if (back === 1) {
                        this.tauri = t; this.kind = 'tauri';
                        this.note = 'TauriTavern 原生存储';
                        return;
                    }
                }
            } catch (e) { warn('TauriTavern store 不可用', e); }

            // 2) IndexedDB
            const db = await this.openIDB();
            if (db) { this.db = db; this.kind = 'idb'; this.note = 'IndexedDB'; return; }

            // 3) 内存
            this.kind = 'memory';
            this.note = this.note || '仅内存（本次会话有效）';
        },

        openIDB() {
            return new Promise((resolve) => {
                if (typeof indexedDB === 'undefined' || !indexedDB) { this.note = '环境无 IndexedDB，仅内存模式'; resolve(null); return; }
                let req;
                try { req = indexedDB.open(DB_NAME, DB_VER); } catch (e) { this.note = String(e && e.message); resolve(null); return; }
                req.onupgradeneeded = () => {
                    const db = req.result;
                    if (!db.objectStoreNames.contains(STORE_KV)) db.createObjectStore(STORE_KV);
                    if (!db.objectStoreNames.contains(STORE_CARDS)) {
                        const st = db.createObjectStore(STORE_CARDS);
                        st.createIndex('ns', 'ns', { unique: false });
                    }
                };
                req.onsuccess = () => resolve(req.result);
                req.onerror = () => { this.note = 'IndexedDB 打开失败'; resolve(null); };
            });
        },

        idb(store, mode, fn) {
            if (!this.db) return null;
            try {
                const st = this.db.transaction(store, mode).objectStore(store);
                return fn(st);
            } catch (e) { warn('存储操作失败', e); return null; }
        },

        // ---- 写：卡片 ----
        async saveCard(card) {
            const slug = slugify(S.ns);
            try {
                if (this.kind === 'tauri') {
                    const table = 'cards.' + slug;
                    const idx = Math.floor((card.ch - 1) / CHUNK) + 1;
                    const from = (idx - 1) * CHUNK;
                    const chunk = S.chapters.slice(from, from + CHUNK).map(plainCard);
                    await this.tauri.setJson({ namespace: NS_TAURI, table: table, key: 'chunk' + String(idx).padStart(4, '0'), value: chunk });
                    await this.tauri.setJson({ namespace: NS_TAURI, table: 'main', key: slug + '.meta', value: { ns: S.ns, count: S.chapters.length, chunks: Math.ceil(S.chapters.length / CHUNK), maxHits: S.maxHits, updated: Date.now() } });
                    return;
                }
                if (this.kind === 'idb') {
                    this.idb(STORE_CARDS, 'readwrite', (st) => st.put(Object.assign({}, plainCard(card), { ns: S.ns }), S.ns + '|' + card.ch));
                    return;
                }
                this.mem.cards.set(S.ns + '|' + card.ch, plainCard(card));
            } catch (e) { warn('保存章节失败', e); }
        },

        async saveKV(key, value) {
            const slug = slugify(S.ns);
            try {
                if (this.kind === 'tauri') {
                    await this.tauri.setJson({ namespace: NS_TAURI, table: 'main', key: slug + '.' + key, value: value });
                    return;
                }
                if (this.kind === 'idb') { this.idb(STORE_KV, 'readwrite', (st) => st.put(value, S.ns + '|' + key)); return; }
                this.mem.kv.set(S.ns + '|' + key, value);
            } catch (e) { warn('保存设置失败', e); }
        },

        async clearCards() {
            const slug = slugify(S.ns);
            try {
                if (this.kind === 'tauri') { await this.tauri.deleteTable({ namespace: NS_TAURI, table: 'cards.' + slug }); return; }
                if (this.kind === 'idb') {
                    await new Promise((resolve) => {
                        const req = this.idb(STORE_CARDS, 'readwrite', (st) => st.index('ns').openCursor(S.ns));
                        if (!req) { resolve(); return; }
                        req.onsuccess = () => { const c = req.result; if (c) { c.delete(); c.continue(); } else resolve(); };
                        req.onerror = () => resolve();
                    });
                    return;
                }
                this.mem.cards.clear();
            } catch (e) { warn('清空失败', e); }
        },

        // ---- 读：整条记忆链 ----
        async loadAll() {
            const slug = slugify(S.ns);
            let cards = [], aliases = null, settings = null, lexicon = null;
            try {
                if (this.kind === 'tauri') {
                    const meta = await this.tauri.tryGetJson({ namespace: NS_TAURI, table: 'main', key: slug + '.meta' });
                    const nChunks = (meta && meta.found && meta.value && Number(meta.value.chunks)) || 0;
                    const table = 'cards.' + slug;
                    for (let i = 1; i <= nChunks; i++) {
                        const part = await this.tauri.tryGetJson({ namespace: NS_TAURI, table: table, key: 'chunk' + String(i).padStart(4, '0') });
                        if (part && part.found && Array.isArray(part.value)) cards = cards.concat(part.value);
                    }
                    const a = await this.tauri.tryGetJson({ namespace: NS_TAURI, table: 'main', key: slug + '.manualAliases' });
                    if (a && a.found) aliases = a.value;
                    const st = await this.tauri.tryGetJson({ namespace: NS_TAURI, table: 'main', key: slug + '.settings' });
                    if (st && st.found) settings = st.value;
                    const lx = await this.tauri.tryGetJson({ namespace: NS_TAURI, table: 'main', key: slug + '.lexicon' });
                    if (lx && lx.found) lexicon = lx.value;
                } else if (this.kind === 'idb') {
                    const got = await new Promise((resolve) => {
                        const t = this.db.transaction([STORE_CARDS, STORE_KV], 'readonly');
                        const out = { cards: [], aliases: null, settings: null, lexicon: null };
                        const reqC = t.objectStore(STORE_CARDS).index('ns').getAll(S.ns);
                        const reqA = t.objectStore(STORE_KV).get(S.ns + '|manualAliases');
                        const reqS = t.objectStore(STORE_KV).get(S.ns + '|settings');
                        const reqL = t.objectStore(STORE_KV).get(S.ns + '|lexicon');
                        reqC.onsuccess = () => { out.cards = reqC.result || []; };
                        reqA.onsuccess = () => { out.aliases = reqA.result || null; };
                        reqS.onsuccess = () => { out.settings = reqS.result || null; };
                        reqL.onsuccess = () => { out.lexicon = reqL.result || null; };
                        t.oncomplete = () => resolve(out);
                        t.onerror = () => resolve(out);
                        t.onabort = () => resolve(out);
                    });
                    cards = got.cards; aliases = got.aliases; settings = got.settings; lexicon = got.lexicon;
                } else {
                    this.mem.cards.forEach((v, k) => { if (k.indexOf(S.ns + '|') === 0) cards.push(v); });
                    aliases = this.mem.kv.get(S.ns + '|manualAliases') || null;
                    settings = this.mem.kv.get(S.ns + '|settings') || null;
                    lexicon = this.mem.kv.get(S.ns + '|lexicon') || null;
                }
            } catch (e) { warn('读取记忆失败，按空记忆启动', e); }

            cards.sort((a, b) => a.ch - b.ch);
            S.chapters = cards.map((c) => {
                const card = makeCard(c);
                card.hits = c.hits || 0;
                S.maxHits = Math.max(S.maxHits, card.hits);
                return card;
            });
            S.chapters.forEach((c) => S.cardByCh.set(c.ch, c));
            if (Array.isArray(aliases)) S.manualAliases = aliases;
            if (settings && typeof settings === 'object') Object.assign(S.settings, settings);
            if (lexicon) S.lexicon = lexicon;
            S.storeNote = this.kind === 'tauri' ? 'TauriTavern 原生存储' : this.note;
        },
    };

    function plainCard(card) {
        return {
            ch: card.ch, span: card.span || '', to: card.to == null ? null : card.to,
            when: card.when || '', where: card.where || '',
            who: card.who || [], what: card.what || '',
            evidence: card.evidence || [], open: card.open || '',
            salience: card.salience, hits: card.hits || 0,
        };
    }

    const persistCard = (card) => { Store.saveCard(card); };
    const persistKV = (key, value) => { Store.saveKV(key, value); };
    const loadAll = () => Store.loadAll();

    // ---------------------------------------------------------------- 摘要（异步、低优先）
    function buildSummaryPrompt(fromIdx) {
        const chat = ctx.chat || [];
        const lines = [];
        const names = [];
        for (let i = fromIdx; i < chat.length; i++) {
            const m = chat[i];
            if (!m || m.is_system) continue;
            const who = m.is_user ? (ctx.name1 || '我') : (m.name || ctx.name2 || '对方');
            if (names.indexOf(who) < 0) names.push(who);
            let t = String(m.mes || '').replace(/\s+/g, ' ');
            if (t.length > 700) t = t.slice(0, 700) + '…';
            lines.push(who + '：' + t);
        }
        const body = lines.join('\n');
        const prompt = [
            '你是记忆整理器。把下面这段对话压成一张「章节卡」，只输出 JSON，不要任何解释。',
            '字段：when(时间/时令), where(地点), who(人名数组), what(一句话经过，60字内),',
            'evidence(物证数组：物品/伤口/承诺/数字/文书，必须原样保留), open(未解决的悬念，一句话), salience(0-1 重要度)',
            '要求：只写对话里真实出现过的内容；人名用原样称呼；evidence 没有就给空数组；open 没有就给空字符串。',
            '',
            '已知在场人物参考：' + names.join('、'),
            '---对话---',
            body,
            '---结束---',
            'JSON：',
        ].join('\n');
        return prompt;
    }

    function extractJSON(text) {
        if (!text) return null;
        let t = String(text).trim();
        const fence = t.match(/```(?:json)?\s*([\s\S]*?)```/i);
        if (fence) t = fence[1].trim();
        const s = t.indexOf('{'), e = t.lastIndexOf('}');
        if (s < 0 || e <= s) return null;
        try { return JSON.parse(t.slice(s, e + 1)); } catch (err) { return null; }
    }

    function coarseCard(fromIdx) {
        const chat = ctx.chat || [];
        const who = [];
        const bits = [];
        for (let i = fromIdx; i < chat.length; i++) {
            const m = chat[i];
            if (!m || m.is_system) continue;
            const nm = m.is_user ? (ctx.name1 || '我') : (m.name || ctx.name2 || '对方');
            if (who.indexOf(nm) < 0) who.push(nm);
            const t = String(m.mes || '').replace(/\s+/g, ' ').trim();
            if (t) bits.push(t.slice(0, 60));
        }
        return {
            when: '', where: '', who: who,
            what: bits.join('；').slice(0, 120) || '（未整理）',
            evidence: [], open: '', salience: 0.4,
        };
    }

    /** 下一章的起点：上一章覆盖到的消息下标 + 1（对未成章的尾部不重复摘要） */
    function nextFrom() {
        const last = S.chapters[S.chapters.length - 1];
        const covered = last && Number.isFinite(Number(last.to)) ? Number(last.to) : -1;
        return Math.max(covered + 1, 0);
    }

    async function summarizeNow(fromIdx, quiet) {
        const chat = ctx.chat || [];
        if (!Number.isFinite(fromIdx) || fromIdx >= chat.length) return null;
        let card = null;
        if (S.settings.autoSummarize && !quiet && typeof ctx.generateQuietPrompt === 'function') {
            S.pendingSummaries++;
            try {
                const prompt = buildSummaryPrompt(fromIdx);
                const res = await ctx.generateQuietPrompt(prompt, false, true);   // skipWIAN：避免世界书额外开销
                const obj = extractJSON(res);
                if (obj) card = addChapter(obj);
                else warn('摘要解析失败，退回粗记', res);
            } catch (e) {
                warn('摘要生成失败，退回粗记', e);
            } finally { S.pendingSummaries--; }
        }
        if (!card) card = addChapter(coarseCard(fromIdx));
        card.to = chat.length - 1;
        card.span = '第' + fromIdx + '–' + card.to + '楼';
        persistCard(card);
        return card;
    }

    function scheduleIdle(fn) {
        if (typeof requestIdleCallback === 'function') requestIdleCallback(() => fn(), { timeout: 4000 });
        else setTimeout(fn, 1200);
    }

    function maybeAutoChapter(force) {
        if (!S.settings.enabled && !force) return;
        const auto = Number(S.settings.autoChapterTurns) || 0;
        if (!force && (!auto || S.turnsSinceChapter < auto)) return;
        const chat = ctx.chat || [];
        if (!chat.length) return;
        const from = nextFrom();
        if (from >= chat.length) return;
        scheduleIdle(async () => {
            const card = await summarizeNow(from, false);
            if (card) renderStats();
        });
    }

    // ---------------------------------------------------------------- UI
    let $panel = null;

    function buildUI() {
        if (typeof $ !== 'function') return;
        const html = `
<div class="memory-chain-settings">
  <div class="inline-drawer">
    <div class="inline-drawer-toggle inline-drawer-header">
      <b>记忆链 MemoryChain</b>
      <div class="inline-drawer-icon fa-solid fa-circle-chevron-down down"></div>
    </div>
    <div class="inline-drawer-content">
      <label class="checkbox_label"><input id="mc-enabled" type="checkbox"><span>启用（每轮按实体注入相关往事）</span></label>
      <div class="mc-row"><span>注入预算（字）</span><input id="mc-budget" type="number" min="200" max="8000" step="100"></div>
      <div class="mc-row"><span>热区轮数</span><input id="mc-hot" type="number" min="1" max="20"></div>
      <div class="mc-row"><span>时间衰减 λ（每章保留）</span><input id="mc-lambda" type="number" min="0.3" max="0.995" step="0.01"></div>
      <div class="mc-row"><span>完整注入（章内）</span><input id="mc-full" type="number" min="1" max="200"></div>
      <div class="mc-row"><span>摘要注入（章内）</span><input id="mc-digest" type="number" min="1" max="500"></div>
      <div class="mc-row"><span>每实体最多卡片</span><input id="mc-perent" type="number" min="1" max="10"></div>
      <div class="mc-row"><span>自动成章（轮，0=关）</span><input id="mc-auto" type="number" min="0" max="50"></div>
      <label class="checkbox_label"><input id="mc-summarize" type="checkbox"><span>用模型生成章节卡（关则用粗记）</span></label>
      <div class="mc-row"><span>注入位置</span>
        <select id="mc-position"><option value="IN_CHAT">对话内（按深度）</option><option value="IN_PROMPT">提示词内</option><option value="BEFORE_PROMPT">提示词之前</option></select>
      </div>
      <div class="mc-row"><span>注入深度</span><input id="mc-depth" type="number" min="0" max="50"></div>

      <hr>
      <div class="mc-row"><span>世界书 JSON</span><input id="mc-file" type="file" accept=".json"></div>
      <div class="mc-hint">导入 <code>今山 6.json</code> 可自动生成实体表（comment=实体，key=别名，通用词自动丢弃）。</div>
      <div class="mc-row"><span>手动别名</span></div>
      <textarea id="mc-aliases" rows="4" placeholder="苓公子 => 茯苓&#10;宵塔主 => 茯宵"></textarea>
      <div class="mc-buttons">
        <button id="mc-save-aliases" class="menu_button">保存别名</button>
        <button id="mc-chapter" class="menu_button">记录本章</button>
        <button id="mc-export" class="menu_button">导出记忆</button>
        <button id="mc-import" class="menu_button">导入记忆</button>
        <button id="mc-clear" class="menu_button">清空本章记忆</button>
      </div>
      <input id="mc-import-file" type="file" accept=".json" style="display:none">
      <label class="checkbox_label"><input id="mc-debug" type="checkbox"><span>调试日志</span></label>
      <div id="mc-stats" class="mc-stats"></div>
      <div id="mc-warn" class="mc-warn"></div>
    </div>
  </div>
</div>`;
        $('#extensions_settings').append(html);
        $panel = $('.memory-chain-settings');

        const bind = (sel, key, type, after) => {
            const el = $panel.find(sel);
            if (type === 'bool') el.prop('checked', !!S.settings[key]);
            else el.val(S.settings[key]);
            el.on('input change', function () {
                S.settings[key] = type === 'bool' ? $(this).prop('checked')
                    : (type === 'num' ? Number($(this).val()) : $(this).val());
                saveSettings();
                if (after) after();
            });
        };
        bind('#mc-enabled', 'enabled', 'bool');
        bind('#mc-budget', 'budgetChars', 'num');
        bind('#mc-hot', 'hotTurns', 'num');
        bind('#mc-lambda', 'lambda', 'num');
        bind('#mc-full', 'fullAge', 'num');
        bind('#mc-digest', 'digestAge', 'num');
        bind('#mc-perent', 'maxPerEntity', 'num');
        bind('#mc-auto', 'autoChapterTurns', 'num');
        bind('#mc-summarize', 'autoSummarize', 'bool');
        bind('#mc-position', 'position', 'str');
        bind('#mc-depth', 'depth', 'num');
        bind('#mc-debug', 'debug', 'bool');

        $panel.find('#mc-aliases').val(S.manualAliases.map((m) => m.alias + ' => ' + m.name).join('\n'));
        $panel.find('#mc-save-aliases').on('click', () => {
            S.manualAliases = parseAliasText($panel.find('#mc-aliases').val());
            persistKV('manualAliases', S.manualAliases);
            rebuildAutomaton();
            renderStats();
            toast('别名已保存');
        });

        $panel.find('#mc-file').on('change', function () {
            const f = this.files && this.files[0];
            if (!f) return;
            const rd = new FileReader();
            rd.onload = () => {
                try {
                    const r = buildFromWorldBook(JSON.parse(String(rd.result)));
                    renderStats();
                    toast(`实体 ${r.entities} 个 / 别名 ${r.aliases} 条（丢弃通用词 ${r.dropped}）`);
                } catch (e) { toast('导入失败：' + e.message, true); }
            };
            rd.readAsText(f, 'utf-8');
        });

        $panel.find('#mc-chapter').on('click', () => {
            summarizeNow(nextFrom(), false).then((c) => {
                if (c) toast('已记录第 ' + c.ch + ' 章');
                renderStats();
            });
        });

        $panel.find('#mc-export').on('click', () => {
            const data = { v: 1, ns: S.ns, chapters: S.chapters, manualAliases: S.manualAliases, settings: S.settings };
            const blob = new Blob([JSON.stringify(data)], { type: 'application/json' });
            const a = document.createElement('a');
            a.href = URL.createObjectURL(blob);
            a.download = 'memory-chain-' + Date.now() + '.json';
            a.click();
            URL.revokeObjectURL(a.href);
        });

        $panel.find('#mc-import').on('click', () => $panel.find('#mc-import-file').trigger('click'));
        $panel.find('#mc-import-file').on('change', function () {
            const f = this.files && this.files[0];
            if (!f) return;
            const rd = new FileReader();
            rd.onload = () => {
                try {
                    const d = JSON.parse(String(rd.result));
                    const arr = Array.isArray(d.chapters) ? d.chapters : [];
                    let n = 0;
                    for (const raw of arr) {
                        if (!raw) continue;
                        const card = makeCard(Object.assign({}, raw, { ch: S.chapters.length + 1 }));
                        S.chapters.push(card); S.cardByCh.set(card.ch, card); indexCard(card); persistCard(card); n++;
                    }
                    if (Array.isArray(d.manualAliases) && d.manualAliases.length) {
                        S.manualAliases = d.manualAliases;
                        persistKV('manualAliases', S.manualAliases);
                        rebuildAutomaton();
                    }
                    syncStats(); renderStats();
                    toast('导入 ' + n + ' 章');
                } catch (e) { toast('导入失败：' + e.message, true); }
            };
            rd.readAsText(f, 'utf-8');
        });

        $panel.find('#mc-clear').on('click', () => {
            S.chapters = []; S.cardByCh.clear();
            S.entities.forEach((e) => { e.cards = []; e.lastCh = 0; e.hits = 0; });
            S.cache = { key: '', block: '' };
            Store.clearCards();
            syncStats(); renderStats();
            toast('本章记忆已清空');
        });
        renderStats();
    }

    function renderStats() {
        if (!$panel || !$panel.length) return;
        const s = S.stats;
        const storeLabel = { tauri: 'TauriTavern store', idb: 'IndexedDB', memory: '内存（不持久）' }[Store.kind] || Store.kind;
        $panel.find('#mc-stats').text(
            `存储：${storeLabel} · 命名空间 ${slugify(S.ns)}` +
            `\n章节 ${s.chapters} · 实体 ${s.entities} · 别名 ${s.aliases} · 过滤词 ${S.worldDropped}` +
            `\n上轮：命中 ${s.matched} 实体 / 候选 ${s.candidates} / 注入 ${s.injected} 字 / 耗时 ${s.lastMs} ms ${s.lastAt}`
        );
        $panel.find('#mc-warn').text(Store.kind === 'memory' ? '⚠ ' + (S.storeNote || '当前环境无法持久化，记忆仅本次会话有效') : '');
    }

    function toast(msg, isErr) {
        try {
            if (typeof toastr !== 'undefined') toastr[isErr ? 'error' : 'info'](msg, '记忆链');
            else console.log('[记忆链]', msg);
        } catch (e) { console.log('[记忆链]', msg); }
    }

    function saveSettings() {
        try {
            if (ctx.extensionSettings) ctx.extensionSettings[MODULE] = S.settings;
            if (typeof ctx.saveSettingsDebounced === 'function') ctx.saveSettingsDebounced();
            persistKV('settings', S.settings);
        } catch (e) { warn('设置保存失败', e); }
    }

    // ---------------------------------------------------------------- 事件绑定
    function bindEvents() {
        if (!eventSource) return;
        const onSent = () => { S.turnsSinceChapter++; };
        if (event_types.GENERATION_AFTER_COMMANDS) {
            eventSource.on(event_types.GENERATION_AFTER_COMMANDS, () => {
                const chat = ctx.chat || [];
                const lastUser = [...chat].reverse().find((m) => m && m.is_user);
                onGenerate(lastUser ? lastUser.mes : '');
            });
        }
        if (event_types.MESSAGE_SENT) eventSource.on(event_types.MESSAGE_SENT, onSent);
        else if (event_types.USER_MESSAGE_RENDERED) eventSource.on(event_types.USER_MESSAGE_RENDERED, onSent);

        if (event_types.GENERATION_ENDED) {
            eventSource.on(event_types.GENERATION_ENDED, () => { maybeAutoChapter(false); });
        }
        if (event_types.CHAT_CHANGED) {
            eventSource.on(event_types.CHAT_CHANGED, async () => {
                S.ns = nsKey();
                S.chapters = []; S.cardByCh.clear(); S.cache = { key: '', block: '' };
                await loadAll();
                syncStats();
                S.entities.forEach((e) => { e.cards = []; e.lastCh = 0; e.hits = 0; });
                S.chapters.forEach((c) => indexCard(c));
                inject('');
                renderStats();
            });
        }
        if (event_types.MESSAGE_DELETED) {
            eventSource.on(event_types.MESSAGE_DELETED, () => { S.cache = { key: '', block: '' }; });
        }
    }

    // ---------------------------------------------------------------- 初始化
    async function init() {
        if (!bindContext()) await waitForContext(10000);
        try {
            if (ctx.extensionSettings && ctx.extensionSettings[MODULE]) {
                Object.assign(S.settings, ctx.extensionSettings[MODULE]);
            }
        } catch (e) { /* ignore */ }
        S.ns = nsKey();
        buildUI();
        await Store.init();
        await loadAll();
        if (S.lexicon) restoreLexicon(S.lexicon);
        S.manualAliases.forEach((m) => addAlias(m.alias, m.name, true));
        rebuildAutomaton();
        syncStats();
        S.chapters.forEach((c) => indexCard(c));
        bindEvents();
        renderStats();
        console.log('[记忆链] 就绪：存储', Store.kind, '・章节', S.chapters.length, '实体', S.entities.size, '别名', S.aliasMap.size);
    }

    // 调试出口（也可在控制台手动调用）
    window.__memoryChain = {
        state: S, Store, recall, addChapter, buildFromWorldBook, parseAliasText, rebuildAutomaton,
        get settings() { return S.settings; }, init,
    };

    if (typeof jQuery !== 'undefined') jQuery(() => init());
    else if (typeof document !== 'undefined' && document.readyState !== 'loading') init();
    else if (typeof document !== 'undefined') document.addEventListener('DOMContentLoaded', () => init());
})();
