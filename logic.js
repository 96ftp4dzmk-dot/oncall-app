/* 值班 PWA - pure logic (no DOM): priority items, check-state helpers, banner priority.
 * Thresholds follow docs/ui-redesign/spec.md 5.1. Exposes window.LG (and the same names as globals, classic script).
 * Data facts (verified against booklet_app / booklet): p.labs[].v are strings - WBC/ANC per uL, PLT like "18k",
 * others raw and possibly prefixed "<" / ">"; p.ser rows are [t, TP, HR, RR, SBP, DBP, SpO2], oldest first, any field null. */
(function (G) {
  'use strict';

  const GROUPS = [{g: 1, name: 'VITAL SIGNS'}, {g: 2, name: 'NEUTROPENIA'}, {g: 3, name: 'BACTEREMIA'},
                  {g: 4, name: 'AKI'}, {g: 5, name: 'ELECTROLYTES'}, {g: 6, name: 'OTHERS'}];

  /* number from a lab string: drop a leading "<" / ">" and a trailing "k"; null when it is not a finite number */
  function parseNum(s) {
    if (s == null) return null;
    const t = String(s).trim().replace(/^[<>]\s*/, '').replace(/k$/i, '');
    if (t === '') return null;
    const n = Number(t);
    return Number.isFinite(n) ? n : null;
  }
  const finite = v => { if (v == null || v === '') return null; const n = Number(v); return Number.isFinite(n) ? n : null; };

  /* latest non-null value of series column col (1 = TP ... 6 = SpO2) */
  function lastOf(ser, col) {
    if (!Array.isArray(ser)) return null;
    for (let i = ser.length - 1; i >= 0; i--) {
      const row = ser[i];
      const n = Array.isArray(row) ? finite(row[col]) : null;
      if (n != null) return n;
    }
    return null;
  }
  function labNum(p, label) {
    if (!Array.isArray(p.labs)) return null;
    const l = p.labs.find(x => x && typeof x === 'object' && x.l === label);
    return l ? parseNum(l.v) : null;
  }
  function firstPos(p) {
    if (!p.micro || typeof p.micro !== 'object') return null;
    for (const rows of Object.values(p.micro)) {
      if (!Array.isArray(rows)) continue;
      const r = rows.find(x => x && x.pos === true);
      if (r) return r;
    }
    return null;
  }

  /* rule table, in display order within a patient: {key, g, help (one line for the 「優先門檻」 sheet), f(patient) -> text | null} */
  const RULES = [
    {key: 'T', g: 1, help: 'T ≥ 38.0', f: p => { const n = lastOf(p.ser, 1); return n != null && n >= 38.0 ? `T ${n.toFixed(1)}` : null; }},
    {key: 'SBP', g: 1, help: 'SBP < 90', f: p => { const n = lastOf(p.ser, 4); return n != null && n < 90 ? `SBP ${n}` : null; }},
    {key: 'HR', g: 1, help: 'HR > 130', f: p => { const n = lastOf(p.ser, 2); return n != null && n > 130 ? `HR ${n}` : null; }},
    {key: 'RR', g: 1, help: 'RR > 30', f: p => { const n = lastOf(p.ser, 3); return n != null && n > 30 ? `RR ${n}` : null; }},
    {key: 'SpO2', g: 1, help: 'SpO₂ < 90', f: p => { const n = lastOf(p.ser, 6); return n != null && n < 90 ? `SpO₂ ${n}%` : null; }},
    {key: 'ANC', g: 2, help: 'ANC < 500', f: p => { const n = labNum(p, 'ANC'); return n != null && n < 500 ? `ANC ${n}` : null; }},
    {key: 'CX', g: 3, help: '培養：7 天內有陽性', f: p => { const r = firstPos(p); return r ? ('Cx+ ' + String(r.t == null ? '' : r.t).slice(0, 20)).trimEnd() : null; }},
    {key: 'Cre', g: 4, help: 'Cre > 3', f: p => { const n = labNum(p, 'Cre'); return n != null && n > 3 ? `Cre ${n}` : null; }},
    {key: 'K', g: 5, help: 'K < 3.0 或 > 6.0', f: p => { const n = labNum(p, 'K'); return n != null && (n < 3.0 || n > 6.0) ? `K ${n}` : null; }},
    {key: 'Na', g: 5, help: 'Na < 125 或 > 155', f: p => { const n = labNum(p, 'Na'); return n != null && (n < 125 || n > 155) ? `Na ${n}` : null; }},
    {key: 'Ca', g: 5, help: 'Ca > 12', f: p => { const n = labNum(p, 'Ca'); return n != null && n > 12 ? `Ca ${n}` : null; }},
    {key: 'PLT', g: 6, help: 'PLT < 20k', f: p => { const n = labNum(p, 'PLT'); return n != null && n < 20 ? `PLT ${Math.round(n)}k` : null; }},
    {key: 'Hb', g: 6, help: 'Hb < 7', f: p => { const n = labNum(p, 'Hb'); return n != null && n < 7 ? `Hb ${n}` : null; }},
    {key: 'WBC', g: 6, help: 'WBC > 50k', f: p => { const n = labNum(p, 'WBC'); return n != null && n > 50000 ? `WBC ${(n / 1000).toFixed(1)}k` : null; }},
    {key: 'INR', g: 6, help: 'INR > 3', f: p => { const n = labNum(p, 'INR'); return n != null && n > 3 ? `INR ${n}` : null; }},
    {key: 'CRIT', g: 6, help: '病危（CRIT）', f: p => p.crit ? 'CRIT' : null},
    {key: 'NEW', g: 6, help: '新病人（NEW）', f: p => p.new ? 'NEW' : null},
  ];
  /* the thresholds as text for the 「優先門檻」 sheet: [{g, name, lines}], generated from the rule table above */
  const priorityHelp = () => GROUPS.map(g => ({g: g.g, name: g.name, lines: RULES.filter(r => r.g === g.g).map(r => r.help)}));

  /* every critical item of every patient, one per row: sorted by group, then bed (string), then patient, then rule order */
  function priorityItems(P) {
    const out = [];
    (Array.isArray(P) ? P : []).forEach((p, pi) => {
      if (!p || typeof p !== 'object') return;
      RULES.forEach((r, ri) => {
        const txt = r.f(p);
        if (txt != null) out.push({g: r.g, key: r.key, id: `${p.chart}|${r.key}|${txt}`, pi: pi, txt: txt, _ri: ri});
      });
    });
    out.sort((a, b) => a.g - b.g || cmpWard(P[a.pi], P[b.pi]) || a.pi - b.pi || a._ri - b._ri);
    const seen = new Set();                                  // two patients sharing (or lacking) a chart number must not share tick ids
    out.forEach(it => { delete it._ri; if (seen.has(it.id)) it.id += '#' + it.pi; seen.add(it.id); });
    return out;
  }
  /* series rows that can be drawn: arrays whose time is a finite number inside [t0, t1] */
  const cleanSer = (ser, t0, t1) => (Array.isArray(ser) ? ser : []).filter(r => Array.isArray(r) && finite(r[0]) != null && r[0] >= t0 && r[0] <= t1);
  /* "2026-11-22 13:00" -> "11/22 13:00"; anything else is returned as is ('' for null) */
  const shortStamp = s => { const m = /^\d{4}-(\d{2}-\d{2}) (\d{2}:\d{2})$/.exec(String(s == null ? '' : s)); return m ? m[1].replace('-', '/') + ' ' + m[2] : String(s == null ? '' : s); };

  /* check state = ids in the order they were ticked */
  const toggleId = (list, id) => list.includes(id) ? list.filter(x => x !== id) : list.concat([id]);
  function pruneChecks(list, items) {
    const live = new Set(items.map(i => i.id));
    return list.filter((id, i) => live.has(id) && list.indexOf(id) === i);
  }
  function splitItems(items, list) {
    const byId = new Map(items.map(i => [i.id, i]));
    const done = list.filter((id, i) => byId.has(id) && list.indexOf(id) === i).map(id => byId.get(id));
    const ticked = new Set(done.map(i => i.id));
    return {open: items.filter(i => !ticked.has(i.id)), done: done};
  }
  /* patient indexes in order of first appearance = prev/next order of the priority tab */
  const patientsInOrder = items => Array.from(new Set(items.map(i => i.pi)));
  /* ward order by building (VGHTC floor map): 0 = 第二醫療大樓 (內圍), 1 = 急診大樓, 2 = 第一醫療大樓.
     ward number comes from bed "W106-05"; within a building the higher ward number comes first, then bed */
  const wardNo = p => { const m = /^\s*W?(\d+)/i.exec(String(p && p.bed != null ? p.bed : '')); return m ? +m[1] : 0; };
  const SECOND_BLD = [66, 76, 86, 96, 106, 116, 131];
  const bldRank = p => { const w = wardNo(p); if (w >= 30 && w <= 39) return 1; if (SECOND_BLD.includes(w) || (p && p.zone === '內圍')) return 0; return 2; };
  const cmpWard = (a, b) => bldRank(a) - bldRank(b) || wardNo(b) - wardNo(a) || String(a.bed == null ? '' : a.bed).localeCompare(String(b.bed == null ? '' : b.bed));

  /* normal ranges [lo, hi] for the mild-abnormal grey text of the 「全部」 list (display only, never a priority) */
  const NORMAL = {WBC: [4000, 11000], ANC: [1500, Infinity], Hb: [12, Infinity], PLT: [150, 450], Cre: [0, 1.3], BUN: [0, 20],
                  ALT: [0, 40], 'T-bil': [0, 1.2], INR: [0, 1.2], Na: [135, 145], K: [3.5, 5.1], Ca: [8.5, 10.5]};
  function labArrow(label, v) {
    const r = Object.prototype.hasOwnProperty.call(NORMAL, label) ? NORMAL[label] : null, n = parseNum(v);
    if (!r || n == null) return '';
    return n < r[0] ? '↓' : n > r[1] ? '↑' : '';
  }

  /* the five vital-sign strips of the patient page (spec 6.4): value range lo..hi, normal band, series column
   * (p.ser rows are [t, TP, HR, RR, SBP, DBP, SpO2]; BP draws SBP (col) to DBP (col + 1) as a vertical bar) */
  const stripSpec = [
    {key: 'T', label: 'T', col: 1, lo: 35, hi: 41, bandLo: 36, bandHi: 37.7},
    {key: 'HR', label: 'HR', col: 2, lo: 40, hi: 160, bandLo: 60, bandHi: 100},
    {key: 'BP', label: 'BP', col: 4, lo: 40, hi: 180, bandLo: 90, bandHi: 120},
    {key: 'SpO2', label: 'SpO₂', col: 6, lo: 80, hi: 100, bandLo: 94, bandHi: 100},
    {key: 'RR', label: 'RR', col: 3, lo: 8, hi: 36, bandLo: 12, bandHi: 20},
  ];
  /* y offset in a strip of height h: spec.hi at 0 (top), spec.lo at h; values outside are clamped, non-numbers sit at the bottom */
  function stripY(spec, v, h) {
    const n = finite(v);
    if (n == null) return h;
    return h - (Math.min(Math.max(n, spec.lo), spec.hi) - spec.lo) / (spec.hi - spec.lo) * h;
  }

  /* hours since stamp "YYYY-MM-DD HH:MM" (local time), or null */
  function stampAgeH(stamp, nowMs) {
    const m = typeof stamp === 'string' && /^(\d{4})-(\d{2})-(\d{2}) (\d{2}):(\d{2})$/.exec(stamp);
    if (!m) return null;
    return (nowMs - new Date(+m[1], +m[2] - 1, +m[3], +m[4], +m[5]).getTime()) / 3600e3;
  }

  /* one banner at most, highest priority first */
  function pickBanner(c) {
    if (c.statusAgeH != null && c.statusAgeH >= 3) return {id: 'silent', text: `電腦已 ${Math.floor(c.statusAgeH)} 小時未回報`};
    if (c.stampAgeH != null && c.stampAgeH > 12) return {id: 'stale', text: '資料已超過 12 小時'};
    if (c.badStampIgnored) return {id: 'badstamp', text: '收到異常資料已忽略，請聯絡管理者'};
    if (c.newKeyUnopenable) return {id: 'reopen', text: '有新版資料，重新開啟以查看', action: 'reopen'};
    if (c.pending) return {id: 'pending', text: '已下載新資料，返回清單即更新'};
    return null;
  }

  const api = {GROUPS, priorityHelp, cleanSer, shortStamp, priorityItems, toggleId, pruneChecks, splitItems, patientsInOrder, cmpWard, bldRank, labArrow, stripSpec, stripY, stampAgeH, pickBanner};
  Object.assign(G, api);
  G.LG = api;
})(self);
