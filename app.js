/* 值班手冊 PWA - list / detail / chart rendering ported from booklet_app.TEMPLATE, plus the PWA flow:
 * first-run setup (Face ID enrolment or backup password) -> local encrypted blob (IndexedDB) -> Face ID / password
 * login -> decrypt in memory; background download of a newer blob; computer status + 「請更新」 request; monthly
 * key rotation; idle lock that wipes plaintext and keys without reloading the page. */
'use strict';
if (top !== self) { try { top.location = self.location.href; } catch (e) { /* ignore */ } throw new Error('framed'); }

const IS_LOCALHOST = location.hostname === 'localhost' || location.hostname === '127.0.0.1';
const LOCAL = IS_LOCALHOST && new URLSearchParams(location.search).has('local');   // dev only: ./data.json, ./status.json, ./grant.json
const RP_ID = '96ftp4dzmk-dot.github.io';
const PERIOD_RE = /^\d{4}-\d{2}$/;
const IDLE_MS = 10 * 60 * 1000;                                             // lock after 10 min idle / hidden
const STALE_H = 3;                                                          // status older than this: PC may be off
const POLL_MS = 90 * 1000, POLL_MAX_MS = 20 * 60 * 1000;                    // after 「請更新」: poll status for new data
const GRANT_POLL_MS = 60 * 1000;                                            // waiting for approval: check ?a=grant
const ROT_RETRY_MS = 6 * 3600e3;                                            // resend an unanswered rotation after this

/* local dev only: a simulated passkey. PRF(salt) = SHA-256("oncall-fake-passkey-v1\0" || salt), the same derivation
 * pwa_make_fake_data.py uses for the fake x25519 user. Never defined on a real host. */
if (LOCAL) {
  window.__TEST_PRF__ = salt => {
    const pre = new TextEncoder().encode('oncall-fake-passkey-v1\x00'), m = new Uint8Array(pre.length + salt.length);
    m.set(pre); m.set(salt, pre.length);
    return sha256(m);
  };
}

const dataUrl = () => LOCAL ? './data.json' : EXEC_URL + '?a=data&k=' + encodeURIComponent(REG.access);
const statusUrl = () => LOCAL ? './status.json' : EXEC_URL + '?a=status&k=' + encodeURIComponent(REG.access);
const grantUrl = acct => LOCAL ? './grant.json' : EXEC_URL + '?a=grant&acct=' + encodeURIComponent(acct);

let REG = null;       // registration (IndexedDB "reg"): {state:'pending'|'ok', mode:'x'|'pw', acct, access, grant, grantP, ...}
let BLOB = null;      // encrypted payload as stored (has plaintext stamp/count only)
let STATUS = null;    // last status.json
let D = null, P = null;   // decrypted app data (memory only, wiped by lock())
let KEYS = null;      // Face ID: {period: X25519 private key} from this login's PRF outputs (memory only)
let KEK = null, USER = null, LOGIN_KEY = null;   // password login: kek64, account, "salt|iterations" at login (memory only)
let AUTH = null;      // auth key signing refresh / rotate requests (memory only)
let AUTH_BAD = false; // the server answered err:"auth" (access key revoked)
let PENDING = null;   // newer decrypted data waiting until the detail pane is closed (memory only)
let POLL = null;      // interval id of the post-request status poll
let GPOLL = null;     // interval id of the grant poll
let NOTE = '';        // small notice (offline / cloud unavailable)
let REQ_MSG = '';     // result of the last 「請更新」
let REQ_SENDING = false;   // a 「請更新」 POST is in flight
let SESSION = 0;      // bumped by lock(): async work that started in an earlier session must not touch the screen or memory
let ITEMS = [];       // priority items for the current data (logic.js priorityItems), memory only
let CHECKS = [];      // ticked item ids in tick order, memory only; stored encrypted (see loadChecks / saveChecks)
let BANNER_CTX = {badStampIgnored: false, newKeyUnopenable: false, pending: false};   // inputs of logic.js pickBanner
const APP_V = 'v17';   // keep equal to SHELL_V in sw.js
const NOTE_INFO = 'oncall-notes-v1';   // subkey label for the to-do notes and the audio (crypto.js sealBytes)
let NOTES = {};       // {chart: {todo: bool, items: [{id, t, done}], audio: [{id, ts, s, mime}]}}; memory only, stored sealed
let UNDO = null;      // last 「待辦」 change {chart, before} for the 復原 button
let REC = null, RECCHUNKS = [], RECT0 = 0;   // MediaRecorder in progress (memory only, dropped on lock)
let AUDIO = null;     // element that is playing a recording (stopped on lock)

const $ = s => document.querySelector(s);
const esc = s => String(s == null ? '' : s).replace(/[‪-‮⁦-⁩]/g, '')
  .replace(/[&<>"']/g, c => ({'&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'}[c]));
const num = v => { const n = Number(v); return v == null || v === '' || !Number.isFinite(n) ? '–' : String(n); };
const mk = (t, on) => on ? `<span class="mk">${esc(t)}</span>` : esc(t);
const pad = n => String(n).padStart(2, '0');
const fmtT = ms => { const d = new Date(Number(ms)); return `${pad(d.getUTCMonth()+1)}/${pad(d.getUTCDate())} ${pad(d.getUTCHours())}:${pad(d.getUTCMinutes())}`; };
const clip = (s, n) => String(s == null ? '' : s).slice(0, n || 20);
const own = (o, k) => !!o && typeof o === 'object' && Object.prototype.hasOwnProperty.call(o, k);
function hist(u) { try { history.replaceState(null, '', u || location.pathname + location.search); } catch (e) {} }

/* ================= rendering ================= */
const newSt = () => ({tab: 'pri', zone: '內圍', q: '', idx: [], cur: -1, from: 'pri', order: []});
let st = newSt();
const DEPT_H = {MO: 'MO 腫瘤內科', HEMA: 'HEMA 血液腫瘤'};
/* English outlined labels only (no Chinese on a patient): CRIT NEW DNR EOL; NF is expressed by the ANC chip */
function tags(p) {
  let h = '';
  if (p.crit) h += '<span class="tag t-CRIT">CRIT</span>';
  if (p.new) h += '<span class="tag t-NEW">NEW</span>';
  if (p.dnr) h += '<span class="tag t-DNR">DNR</span>';
  if (p.end) h += '<span class="tag t-EOL">EOL</span>';
  return h;
}
const chipHtml = it => `<span class="chip g${Number(it.g)}">${esc(it.txt)}</span>`;

/* recompute the priority items from P and drop ticks whose item is gone or changed -> true when the ticks changed */
function recalc() {
  ITEMS = priorityItems(P);
  const kept = pruneChecks(CHECKS, ITEMS), changed = kept.length !== CHECKS.length;
  CHECKS = kept;
  return changed;
}

const TAB_TITLE = {pri: '優先', all: '全部', todo: '待辦'};
/* 待辦 tab: the indexes of the patients whose note is marked 待辦 (left swipe), in P order */
const todoIdx = () => (P || []).map((p, i) => i).filter(i => (NOTES[P[i].chart] || {}).todo === true);
function renderTabs() {
  const open = patientGroups().filter(x => !x.done).length, td = todoIdx().length;
  $('.tb [data-tab=pri]').innerHTML = '優先' + (open ? `<span class="ct">${open}</span>` : '');
  $('.tb [data-tab=all]').textContent = `全部 ${P.length}`;
  $('.tb [data-tab=todo]').innerHTML = '待辦' + (td ? `<span class="ct">${td}</span>` : '');
  document.querySelectorAll('.tb button').forEach(b => b.classList.toggle('on', b.dataset.tab === st.tab));
  $('#ttl').textContent = TAB_TITLE[st.tab] || '優先';
}
function showTab(t) {
  st.tab = t;
  $('#pri').style.display = t === 'pri' ? '' : 'none';
  $('#all').style.display = t === 'all' ? '' : 'none';
  $('#todo').style.display = t === 'todo' ? '' : 'none';
  renderTabs();
  if (t === 'pri') renderPri(); else if (t === 'todo') renderTodo(); else renderAll();
}

/* one row per patient: all of that patient's priority items as chips; done when every item is ticked */
function patientGroups() {
  const by = new Map();
  ITEMS.forEach(it => { if (!by.has(it.pi)) by.set(it.pi, []); by.get(it.pi).push(it); });
  return Array.from(by.entries()).map(([pi, its]) => ({pi: pi, its: its, g: Math.min(...its.map(it => it.g)),
                                                       done: its.every(it => CHECKS.includes(it.id))}));
}
function renderPri() {
  const el = $('#pri');
  if (!ITEMS.length) { el.innerHTML = '<div class="empty">目前沒有需要優先處理的項目<small>門檻見「⋯」選單的「優先門檻」</small></div>'; return; }
  const groups = patientGroups(), open = groups.filter(x => !x.done), done = groups.filter(x => x.done);
  /* row: [✓] | bed / name / chart + attending | chips: 生命徵象 (g1) first, then the other colour blocks in fixed order, every row the same */
  const row = x => { const p = P[x.pi] || {}, its = x.its.slice().sort((a, b) => a.g - b.g);
    return `<div class="ck${x.done ? ' done' : ''}" role="checkbox" aria-checked="${x.done}" tabindex="0" data-pi="${Number(x.pi)}"><span class="cbx"></span><span class="idc"><span class="bed">${esc(p.bed)}</span><span class="nm">${esc(p.name)}</span><span class="pmeta">${esc(p.chart || '')}</span><span class="pmeta">${esc(p.vs || '')}</span></span><span class="pchips">${its.map(chipHtml).join('')}</span><button class="go" type="button" data-go="${Number(x.pi)}" aria-label="開啟病人頁">›</button></div>`; };
  let h = `<div class="pg"><span>${done.length} / ${groups.length} 人</span><div class="pgb"><span style="width:${Math.round(done.length / groups.length * 100)}%"></span></div></div>`;
  GROUPS.forEach(g => { const rows = open.filter(x => x.g === g.g);
    if (rows.length) h += `<div class="gh g${g.g}"><i></i>${g.name} · ${rows.length}</div>` + rows.map(row).join(''); });
  if (done.length) h += `<div class="donehd">已處理 ${done.length}</div>` + done.map(row).join('');
  el.innerHTML = h;
}
/* tick / untick every priority item of one patient (one row = one patient) */
function togglePatient(pi) {
  const ids = ITEMS.filter(it => it.pi === pi).map(it => it.id);
  const all = ids.length > 0 && ids.every(id => CHECKS.includes(id));
  CHECKS = all ? CHECKS.filter(id => !ids.includes(id)) : CHECKS.concat(ids.filter(id => !CHECKS.includes(id)));
  renderPri(); renderTabs();
  if ($('#detail').style.display === 'block' && st.cur >= 0) renderPend(st.order[st.cur]);
  return saveChecks();
}

function renderAll() {
  const q = st.q.trim().toLowerCase();
  $('#zone').innerHTML = ['內圍', '外圍'].map(z => `<button class="${st.zone === z ? 'on' : ''}" data-z="${z}">${z} ${P.filter(p => p.zone === z).length}</button>`).join('');
  st.idx = P.map((p, i) => i).filter(i => { const p = P[i]; return p.zone === st.zone && (!q || (p.bed + p.chart + p.name + p.dept).toLowerCase().includes(q)); });
  if (!st.idx.length) { $('#cards').innerHTML = '<div class="empty">沒有符合的病人</div>'; return; }
  const by = {};
  ITEMS.forEach(it => { (by[it.pi] = by[it.pi] || []).push(it); });
  let h = '', last = '';
  st.idx.forEach(i => {
    const p = P[i];
    if (p.dept !== last) { h += `<div class="sec">${esc(DEPT_H[p.dept] || p.dept)}</div>`; last = p.dept; }
    const all = by[i] || [], have = new Set(all.map(x => x.key));
    const chips = all.filter(x => x.key !== 'CRIT' && x.key !== 'NEW').map(chipHtml).join('');
    const mild = (Array.isArray(p.labs) ? p.labs : []).filter(l => l && l.abn && !have.has(l.l)).map(l => `${esc(l.l)} ${esc(labText(l))}${labArrow(l.l, l.v)}`);
    const r2 = chips + (mild.length ? `<span class="mild">${mild.slice(0, 3).join(' · ')}${mild.length > 3 ? ' +' + (mild.length - 3) : ''}</span>` : '');
    h += `<div class="pr" role="button" tabindex="0" data-i="${i}"><div class="r1"><span class="bed">${esc(p.bed)}</span><span class="nm">${esc(p.name)}</span><span class="id">${esc(p.chart)}</span><span class="sp"></span>${tags(p)}</div>${r2 ? `<div class="r2">${r2}</div>` : ''}</div>`;
  });
  $('#cards').innerHTML = h;
}

/* ---- tick state: memory copy CHECKS, stored encrypted (crypto.js sealChecks) under a subkey of the login key ---- */
/* key to seal with: Face ID = this month's PRF key if it was derived at login, else the entry period's; password = the kek */
function checksKey() {
  if (!REG) return null;
  if (REG.mode === 'x') {
    if (!KEYS) return null;
    const cur = period(new Date()), p = own(KEYS, cur) ? cur : Object.keys(KEYS)[0];
    return p ? {ikm: KEYS[p], mode: 'x', p: p} : null;
  }
  return KEK ? {ikm: KEK, mode: 'pw', p: null} : null;
}
/* -> string[] ([] when nothing stored or the key it was sealed with is gone, e.g. after a monthly rotation) */
async function loadChecks() {
  let rec = null;
  try { rec = await loadBlob('checks'); } catch (e) { rec = null; }
  if (!rec || !REG || rec.mode !== REG.mode) return [];
  const ikm = REG.mode === 'x' ? (KEYS && own(KEYS, rec.p) ? KEYS[rec.p] : null) : KEK;
  return (ikm && openChecks(ikm, rec)) || [];
}
async function saveChecks() {
  const k = checksKey();
  if (!k) return;
  const box = sealChecks(k.ikm, CHECKS);
  box.mode = k.mode; box.p = k.p;
  try { await saveBlob(box, 'checks'); } catch (e) { /* ticks stay in memory only */ }
}
function toggleCheck(id) {
  CHECKS = toggleId(CHECKS, id);
  renderPri(); renderTabs();
  if ($('#detail').style.display === 'block' && st.cur >= 0) renderPend(st.order[st.cur]);   // the patient page shows the same ticks
  return saveChecks();
}

/* ================= patient page ================= */
const STRIP_W = 340, STRIP_L = 92, STRIP_R = 334, STRIP_ROW = 46, STRIP_SPAN = 72 * 3600e3;
const STRIP_TRIG = {T: 'T', HR: 'HR', BP: 'SBP', SpO2: 'SpO2', RR: 'RR'};   // strip -> priority item key
let stripSel = null;                       // index into p.ser of the tapped time; null = latest values
const fin = v => v != null && v !== '' && Number.isFinite(Number(v)) ? Number(v) : null;
function latestIdx(ser, col) { for (let i = ser.length - 1; i >= 0; i--) if (Array.isArray(ser[i]) && fin(ser[i][col]) != null) return i; return -1; }
function stripText(spec, row) {
  if (!row) return '–';
  const n = fin(row[spec.col]);
  if (n == null) return '–';
  if (spec.key === 'BP') { const d = fin(row[spec.col + 1]); return d == null ? String(n) : `${n}/${d}`; }
  return spec.key === 'T' ? n.toFixed(1) : String(n);
}
/* five small multiples on one 72 h time axis; sel = index of the tapped row (values on the left follow it) */
const stripSer = p => { const N = Number(D.now); return cleanSer(p.ser, N - STRIP_SPAN, N + 3600e3); };   // only rows that can be drawn
function stripsSVG(p, sel) {
  const ser = stripSer(p);
  if (!ser.length) return '<div class="rd">72 小時內無生命徵象</div>';
  const N = Number(D.now), t0 = N - STRIP_SPAN, X = t => STRIP_L + (Number(t) - t0) / STRIP_SPAN * (STRIP_R - STRIP_L);
  const total = STRIP_ROW * stripSpec.length + 16, mine = ITEMS.filter(it => it.pi === P.indexOf(p));
  let s = `<svg class="vs" viewBox="0 0 ${STRIP_W} ${total}" xmlns="http://www.w3.org/2000/svg">`;
  const d0 = new Date(t0); d0.setUTCHours(0, 0, 0, 0);
  for (let t = d0.getTime(); t <= N; t += 86400e3) {                       // day lines
    if (t < t0) continue;
    const x = X(t), d = new Date(t);
    s += `<line class="gl" x1="${x}" x2="${x}" y1="2" y2="${total - 14}"/><text class="ax" x="${x + 2}" y="${total - 3}">${pad(d.getUTCMonth() + 1)}/${pad(d.getUTCDate())}</text>`;
  }
  stripSpec.forEach((spec, k) => {
    const yo = k * STRIP_ROW + 4, h = STRIP_ROW - 8, Y = v => yo + stripY(spec, v, h);
    s += `<rect class="band" x="${STRIP_L}" y="${Y(spec.bandHi)}" width="${STRIP_R - STRIP_L}" height="${Math.max(0, Y(spec.bandLo) - Y(spec.bandHi))}"/>`;
    const pts = ser.filter(r => Array.isArray(r) && fin(r[spec.col]) != null);
    if (spec.key === 'BP') pts.forEach(r => { const d = fin(r[spec.col + 1]); s += `<line class="bp" x1="${X(r[0])}" x2="${X(r[0])}" y1="${Y(r[spec.col])}" y2="${Y(d == null ? r[spec.col] : d)}"/>`; });
    else if (pts.length > 1) s += `<polyline class="ln" points="${pts.map(r => `${X(r[0])},${Y(r[spec.col])}`).join(' ')}"/>`;
    const li = latestIdx(ser, spec.col), trig = mine.find(it => it.key === STRIP_TRIG[spec.key]);
    if (li >= 0) s += `<circle class="dot${trig ? ' gv' : ''}" cx="${X(ser[li][0])}" cy="${Y(ser[li][spec.col])}" r="3"/>`;
    const row = sel != null && ser[sel] ? ser[sel] : (li >= 0 ? ser[li] : null);
    s += `<text class="sl" x="0" y="${yo + 11}">${spec.label}</text><text class="sv${sel == null && trig ? ' gv' : ''}" x="0" y="${yo + 34}">${stripText(spec, row)}</text>`;
  });
  if (sel != null && ser[sel]) s += `<line class="cur" x1="${X(ser[sel][0])}" x2="${X(ser[sel][0])}" y1="2" y2="${total - 14}"/>`;
  return s + '</svg>';
}
function renderStrips(p) {
  const box = $('#vsbox'); if (!box) return;
  box.innerHTML = stripsSVG(p, stripSel);
  const ser = stripSer(p);
  $('#read').textContent = !ser.length ? '' : stripSel != null && ser[stripSel] ? `${fmtT(ser[stripSel][0])} 的數值` : '最新值（點圖表看該時間點）';
}
/* tap = show that time's values (no dragging); tapping the label column goes back to the latest values */
function bindStrips(p) {
  const box = $('#vsbox'); if (!box) return;
  box.onclick = e => {
    const svg = box.querySelector('svg'), ser = stripSer(p);
    if (!svg || !ser.length) return;
    const r = svg.getBoundingClientRect(), vx = (e.clientX - r.left) / r.width * STRIP_W;
    if (vx < STRIP_L - 4) stripSel = null;
    else {
      const t = Number(D.now) - STRIP_SPAN + (vx - STRIP_L) / (STRIP_R - STRIP_L) * STRIP_SPAN;
      stripSel = 0; ser.forEach((q, i) => { if (Math.abs(q[0] - t) < Math.abs(ser[stripSel][0] - t)) stripSel = i; });
    }
    renderStrips(p);
  };
}

/* lab grid cell: normal = grey, mildly abnormal = bold + arrow, a priority item = the group's soft colour */
function labCell(l, it) {
  const cls = it ? 'p' + ({1: 'v', 2: 'n', 3: 'o'}[it.g] || 'o') : l.abn ? 'mild' : '';
  return `<div class="lc ${cls}"><div class="l">${esc(l.l)}${l.d ? ' <small>' + esc(l.d) + '</small>' : ''}</div><div class="v">${esc(labText(l))}${labArrow(l.l, l.v)}</div></div>`;
}
/* WBC arrives per uL ("2900"); the screens show it as 2.9k like the priority chip */
function labText(l) { const n = l.l === 'WBC' ? fin(l.v) : null; return n == null ? String(l.v) : (n / 1000).toFixed(1) + 'k'; }
function fold(title, small, inner, open) {
  return inner ? `<details class="tg"${open ? ' open' : ''}><summary>${title}<small>${small == null ? '' : esc(small)}</small></summary><div class="in">${inner}</div></details>` : '';
}
/* 「待處理」 block of the patient page: this patient's priority items, ticked in sync with the priority tab */
function renderPend(i) {
  const el = $('#pend'); if (!el) return;
  const its = ITEMS.filter(it => it.pi === i);
  el.style.display = its.length ? '' : 'none';
  el.innerHTML = its.length ? '<h3>待處理</h3>' + its.map(it => `<div class="ck pk${CHECKS.includes(it.id) ? ' done' : ''}" role="checkbox" aria-checked="${CHECKS.includes(it.id)}" tabindex="0" data-id="${esc(it.id)}"><span class="cbx"></span>${chipHtml(it)}</div>`).join('') : '';
}

function renderDetail(i, from) {
  const p = P[i];
  if (from) { st.from = from; st.order = from === 'pri' ? patientsInOrder(ITEMS) : st.idx.slice(); }
  st.cur = st.order.indexOf(i); hist('#p' + i); stripSel = null;
  $('#back').textContent = st.from === 'pri' ? '‹ 優先' : '‹ 全部';
  $('#dt').textContent = `${st.cur + 1} / ${st.order.length}`;
  const labs = Array.isArray(p.labs) ? p.labs : [], its = ITEMS.filter(it => it.pi === i), notes = Array.isArray(p.notes) ? p.notes : [];
  const wt = p.wt && p.wt.kg != null ? `${esc(p.wt.kg)} kg${p.wt.delta != null ? ` <small>${Number(p.wt.delta) > 0 ? '+' : ''}${esc(p.wt.delta)}</small>` : ''}` : '';
  /* IO: day's input / output in ml, the difference in brackets (1000 ml or more = red, as on the HIS handoff page) */
  const io = p.io && p.io.in != null ? `${esc(p.io.in)} / ${esc(p.io.out)} ml <small${Math.abs(Number(p.io.diff)) > 1000 ? ' class="gv"' : ''}>(${Number(p.io.diff) > 0 ? '+' : ''}${esc(p.io.diff)})</small>` : '';
  /* UO: urine output of the day in ml (sql_0035 urine rows only; not the same as the total output above) */
  const uo = p.uo != null ? `${esc(p.uo)} ml` : '';
  const props = [['病歷號', esc(p.chart)], ['科別', `${esc(p.dept)} · ${esc(p.zone)}`], ['主治', esc(p.vs)], ['入院', esc(p.adm)], ['體重', wt], ['IO 入/出', io], ['UO 尿量（今日）', uo], ['標記', tags(p)]].filter(r => r[1]);
  let h = `<div class="dh"><h2 class="ttl"><span class="b">${esc(p.bed)}</span>${esc(p.name)}</h2></div>
  <dl class="props">${props.map(r => `<dt>${r[0]}</dt><dd>${r[1]}</dd>`).join('')}</dl>
  <div class="swh">左滑：加入待辦 ・ 右滑：沒什麼問題（可復原）</div>
  <div class="blk" id="pend"></div>
  <div class="blk"><h3>生命徵象 · 72 小時</h3><div id="vsbox"></div><div class="rd" id="read"></div></div>`;
  const grid = (names, cols) => { const L = labs.filter(l => l && names.includes(l.l) && l.v); return L.length ? `<div class="lg c${cols}">${L.map(l => labCell(l, its.find(it => it.key === l.l))).join('')}</div>` : ''; };
  const hemo = grid(['WBC', 'ANC', 'Hb', 'PLT'], 4), chem = grid(['Cre', 'BUN', 'ALT', 'T-bil', 'INR', 'Na', 'K', 'Ca', 'LDH'], 3);
  if (hemo || chem || notes.length)
    h += `<div class="blk"><h3>檢驗 · 7 天內最新</h3>${hemo ? '<div class="sub2">Hemogram</div>' + hemo : ''}${chem ? '<div class="sub2">Chemistry</div>' + chem : ''}${notes.length ? `<div class="rd">${notes.map(esc).join(' · ')}</div>` : ''}</div>`;
  const objs = a => Array.isArray(a) ? a.filter(x => x && typeof x === 'object') : [];     // a null entry must not break the page
  const micro = p.micro && typeof p.micro === 'object' ? Object.entries(p.micro) : [];
  const nMicro = micro.reduce((n, e) => n + objs(e[1]).length, 0);
  /* culture results in one box per kind (細菌 / 病毒 / ...): left = status, right = the full HIS item name */
  const cbox = (title, n, inner) => inner ? `<div class="cbox"><div class="cbt">${esc(title)}<small>${n}</small></div>${inner}</div>` : '';
  const cx = micro.filter(([, rows]) => objs(rows).length).map(([k, rows]) => cbox(k, objs(rows).length, `<div class="mg">${objs(rows).map(r => `<span class="st">${r.pos ? `<span class="chip g3">${esc(r.t)}</span>` : esc(r.t)}</span><span class="it">${esc(r.i)}${Number(r.n) > 1 ? ' ×' + Number(r.n) : ''}</span>`).join('')}</div>`)).join('') + (p.fw ? `<div class="row">${mk('Fever work-up?', true)}</div>` : '');
  const today = Array.isArray(p.today) ? p.today : [];
  /* drugs: the flagged ones (meds) and the other active drugs (others) in one list, boxed by pharmacy category */
  const drugs = objs(p.meds).concat(objs(p.others)), PHARM = ['抗生素', '止痛藥', '抗凝血·抗血小板', '抗癌藥', '類固醇', '升壓劑', '腸胃藥', '其他'];
  const drugLi = m => `<li>${esc(m.n)}${m.freq ? ` <span class="sub">q${esc(m.freq)}</span>` : ''}${m.d ? ` <span class="sub">D${esc(m.d)}</span>` : ''}</li>`;
  const drugBoxes = PHARM.map(c => { const L = drugs.filter(m => (m.cat || '其他') === c); return L.length ? cbox(c, L.length, `<ul class="dl">${L.map(drugLi).join('')}</ul>`) : ''; }).join('');
  h += fold('培養（7 天）', nMicro ? nMicro + ' 筆' : '', cx, false)
     + fold('今日檢驗 / 影像', today.length, today.map(t => `<div class="row">${esc(t)}</div>`).join(''), false)
     + fold('目前處方', drugs.length, drugBoxes, true)
     + fold('交班與交代事項', '', p.memo ? `<div class="memo">${esc(p.memo)}</div>` : '', true)
     + fold('護理紀錄', p.nurs ? p.nurs.w : '', p.nurs ? `<div class="memo">${esc(p.nurs.t)}</div>` : '', false);
  h += '<div class="pn2"><button id="prev" type="button">‹ 上一位</button><button id="next" type="button">下一位 ›</button></div>';
  $('#db').innerHTML = h;
  renderPend(i); renderStrips(p); bindStrips(p); bindSwipe(p.chart);
  $('#prev').disabled = st.cur <= 0; $('#next').disabled = st.cur >= st.order.length - 1;
  $('#prev').onclick = () => go(-1); $('#next').onclick = () => go(1);
  $('#detail').style.display = 'block'; $('#detail').scrollTop = 0; document.body.style.overflow = 'hidden';
}
function go(d){const n=st.cur+d;if(n<0||n>=st.order.length)return;renderDetail(st.order[n])}
/* back to the tab the patient was opened from, at the row that was opened; a newer payload that arrived meanwhile is applied now */
function closeDetail(){$('#detail').style.display='none';document.body.style.overflow='';hist('');
 const from=st.from;let pi=st.order[st.cur];
 if(PENDING){const chart=(P[pi]||{}).chart,d=PENDING;PENDING=null;applyData(d);pi=P.findIndex(x=>x.chart===chart)}   // new data: find the patient again by chart number
 showTab(from);
 const el=from==='pri'?document.querySelector(`.ck .go[data-go="${Number(pi)}"]`):document.querySelector(`.pr[data-i="${Number(pi)}"]`);
 if(el)el.scrollIntoView({block:'center'})}

/* ---- menu / confirm box / toast ---- */
function toast(text){const t=$('#toast');t.textContent=text;t.classList.add('on');clearTimeout(toast.t);toast.t=setTimeout(()=>t.classList.remove('on'),3000)}
/* info = a notice with only an OK button */
function ask(text,info){return new Promise(res=>{$('#dtx').textContent=text;$('#dno').style.display=info?'none':'';const d=$('#dlg');d.classList.add('on');
 const fin=v=>{d.classList.remove('on');$('#dok').onclick=null;$('#dno').onclick=null;res(v)};
 $('#dok').onclick=()=>fin(true);$('#dno').onclick=()=>fin(false)})}
function helpText(){return priorityHelp().map(g=>g.name+'\n'+g.lines.map(l=>'・'+l).join('\n')).join('\n\n')+'\n\n每個項目各自一行，可打勾。'}
function openMenu(){$('#ver').textContent='值班 '+APP_V;$('#menu').classList.add('on')}
function closeMenu(){$('#menu').classList.remove('on')}

document.addEventListener('click',e=>{
 if(!P)return;
 const t=e.target;
 const tb=t.closest('[data-tab]');if(tb){showTab(tb.dataset.tab);window.scrollTo(0,0);return}
 const z=t.closest('[data-z]');if(z){st.zone=z.dataset.z;renderAll();return}
 const gb=t.closest('[data-go]');if(gb){renderDetail(+gb.dataset.go,'pri');return}
 const ck=t.closest('.ck');if(ck){if(ck.dataset.pi!==undefined)togglePatient(+ck.dataset.pi);else toggleCheck(ck.dataset.id);return}
 if(t.closest('#pdfall')){exportPdf(null);return}
 const tdo=t.closest('.tdo');if(tdo){openNote(+tdo.dataset.note);return}
 const pr=t.closest('.pr');if(pr){renderDetail(+pr.dataset.i,'all');return}
 if(t.closest('#mn')){openMenu();return}
 const ac=t.closest('[data-act]');
 if(ac){const a=ac.dataset.act;
  if(a==='lock'){closeMenu();lock()}else if(a==='clear'){closeMenu();clearLocal()}else if(a==='help'){closeMenu();ask(helpText(),true)}else if(a==='reopen')lock();return}
 if(t.id==='menu')closeMenu()});
$('#q').addEventListener('input',e=>{if(!P)return;st.q=e.target.value;renderAll()});
$('#back').onclick=closeDetail;
/* tick rows and patient rows are plain elements: Enter / Space on a focused one acts like a tap */
document.addEventListener('keydown',e=>{if((e.key==='Enter'||e.key===' ')&&e.target.matches&&e.target.matches('.ck,.pr')){e.preventDefault();e.target.click()}});
window.addEventListener('keydown',e=>{if($('#detail').style.display!=='block')return;if(e.key==='ArrowLeft')go(-1);if(e.key==='ArrowRight')go(1);if(e.key==='Escape')closeDetail()});

/* ================= screens ================= */
function show(id) {
  ['#boot', '#setup', '#pending', '#login', '#list'].forEach(s => { $(s).style.display = s === id ? '' : 'none'; });
  $('#foot').style.display = id === '#list' ? 'none' : '';
  if (id !== '#pending') stopGrantPoll();
}
/* retry = show the 「重試」 button (no data yet) */
function showBoot(text, retry) { $('#bt').textContent = text; $('#bretry').style.display = retry ? '' : 'none'; show('#boot'); }
async function retryBoot() {
  showBoot('下載資料中…');
  await syncData();
  if (BLOB) showLogin(); else showBoot('尚無資料，請連 4G 開啟以下載' + (NOTE ? '（' + NOTE + '）' : ''), true);
}
function showSetup(text) {
  show('#setup');
  $('#sb').disabled = false; $('#pb').disabled = false;
  $('#sx').style.display = 'none'; $('#sx').onclick = null;
  $('#sm').textContent = text || '';
}
const DENIED_MSG = '此帳號目前無權限開啟，請聯絡管理者';
let DENIED_SHOWN = false;
const FX_LABEL = '以 Face ID 開啟';
function fxBusy(on) { $('#fx').disabled = on; $('#fx').textContent = on ? '驗證中…' : FX_LABEL; }
function showLogin(text) {
  show('#login');
  const x = REG && REG.mode === 'x';
  $('#lx').style.display = x ? '' : 'none';
  $('#lf').style.display = x ? 'none' : '';
  fxBusy(false); $('#lb').disabled = false; DENIED_SHOWN = false;
  $('#lm').textContent = text || '';
  $('#lsub').textContent = BLOB && BLOB.stamp ? `資料 ${shortStamp(clip(BLOB.stamp))}${BLOB.count != null ? ' · ' + num(BLOB.count) + ' 人' : ''}` : '';
  renderSys();
}

/* hours since status.at ("YYYY-MM-DD HH:MM", PC local time = phone local time) or null */
function statusAgeH() {
  const m = STATUS && typeof STATUS.at === 'string' && /^(\d{4})-(\d{2})-(\d{2}) (\d{2}):(\d{2})$/.exec(STATUS.at);
  if (!m) return null;
  return (Date.now() - new Date(+m[1], +m[2] - 1, +m[3], +m[4], +m[5]).getTime()) / 3600e3;
}
/* duty day if the phone's own date is Sat/Sun, or the PC says so (holidays come from the PC's holiday file) */
function isDutyDay() {
  const wd = new Date().getDay();
  return wd === 0 || wd === 6 || !!(STATUS && STATUS.duty_day === true);
}
/* status line parts (HTML): computer status, plus "PC silent" / holiday-file warnings */
function statusParts() {
  if (!STATUS || !STATUS.at) return [];
  const age = statusAgeH();
  const s = STATUS, out = [`<span class="pc ${age != null && age >= STALE_H ? 'off' : s.ok ? '' : 'bad'}">電腦 ${esc(shortStamp(clip(s.at)))} ${s.ok ? '正常' : '異常'}${s.msg ? '：' + esc(clip(s.msg, 80)) : ''}</span>`];
  if (age != null && age >= STALE_H) out.push(`<span class="note">電腦已超過 ${Math.floor(age)} 小時未回報，可能未開機或程式已關閉</span>`);
  if (s.hol_warn === true) out.push(`<span class="note">假日檔讀取失敗，只依週六日執行</span>`);
  return out;
}
/* err:"auth" = the server read the access list and this key is not on it (definite rejection) */
const AUTH_MSG = '存取碼已被伺服器拒絕（可能已被停用），請先聯絡管理者確認；確定需重新登記時再按「清除本機資料」';
/* err:"unavailable" = the server could not read its access list (transient): never suggest clearing local data */
const UNAVAIL_MSG = '伺服器暫時無法使用，請稍後再試（本機資料仍可登入）';
/* login screen: data stamp + computer status + notices */
function loginSys() {
  const parts = [...statusParts()];
  if (NOTE) parts.push(`<span class="note">${esc(NOTE)}</span>`);
  $('#lsys').innerHTML = parts.join('');
  if ($('#login').style.display === 'none') return;
  if (AUTH_BAD) {                                             // the server rejected this access key: no way in from this screen
    fxBusy(false); $('#fx').disabled = true; $('#lb').disabled = true; $('#lm').textContent = DENIED_MSG; DENIED_SHOWN = true;
  } else if (DENIED_SHOWN) {                                  // approved again: open the screen up without waiting for new data
    fxBusy(false); $('#lb').disabled = false; if ($('#lm').textContent === DENIED_MSG) $('#lm').textContent = ''; DENIED_SHOWN = false;
  }
}
/* list header: data stamp, computer dot, 「請更新」, then one grey line per notice */
function renderMeta() {
  if (!D) return;
  const age = statusAgeH(), sAge = stampAgeH(D.stamp, Date.now()), busy = REQ_SENDING || !!POLL, parts = [];
  parts.push(`<span${sAge != null && sAge > 12 ? ' class="stale"' : ''}>資料 ${esc(shortStamp(clip(D.stamp)))}（${P.length}人）</span>`);
  if (STATUS && STATUS.at) parts.push(`<span class="pc ${age != null && age >= STALE_H ? 'off' : STATUS.ok ? '' : 'bad'}">電腦 ${esc(shortStamp(clip(STATUS.at)))}</span>`);
  if (isDutyDay()) parts.push(`<button id="rq" class="rq" type="button"${busy ? ' disabled' : ''}>${busy ? '等待更新…' : '請更新'}</button>`);
  $('#meta').innerHTML = parts.join('');
  const lines = [];
  if (STATUS && STATUS.ok === false && STATUS.msg) lines.push('電腦回報：' + clip(STATUS.msg, 80));
  if (STATUS && STATUS.hol_warn === true) lines.push('假日檔讀取失敗，只依週六日執行');
  if (!isDutyDay() && STATUS) lines.push('非值班日');
  if (REQ_MSG) lines.push(REQ_MSG);
  if (AUTH_BAD) lines.push(AUTH_MSG);
  if (NOTE) lines.push(NOTE);
  $('#nline').innerHTML = lines.map(l => `<div>${esc(l)}</div>`).join('');
  const b = $('#rq'); if (b) b.onclick = requestRefresh;
}
/* at most one banner (logic.js pickBanner decides which) */
function renderBanner() {
  const r = D ? pickBanner({statusAgeH: statusAgeH(), stampAgeH: stampAgeH(D.stamp, Date.now()), badStampIgnored: BANNER_CTX.badStampIgnored,
                            newKeyUnopenable: BANNER_CTX.newKeyUnopenable, pending: BANNER_CTX.pending}) : null;
  $('#banner').innerHTML = r ? `<span>${esc(r.text)}</span>${r.action === 'reopen' ? '<button type="button" data-act="reopen">重新開啟</button>' : ''}` : '';
}
function renderSys() { loginSys(); renderMeta(); renderBanner(); }
function authFailed() { AUTH_BAD = true; renderSys(); }

/* ================= network ================= */
async function getJSON(url) {
  const r = await fetch(url, {cache: 'no-store', credentials: 'omit'});
  if (!r.ok) throw new Error('HTTP ' + r.status);
  return r.json();
}
/* POST to the Apps Script. Local dev mode sends nothing: the body is kept in window.__LAST_POST__ for inspection. */
async function postJSON(body) {
  if (LOCAL) { window.__LAST_POST__ = body; console.info('[local] POST not sent', body); return {ok: true, local: true}; }
  const r = await fetch(EXEC_URL, {method: 'POST', headers: {'Content-Type': 'text/plain'}, body: JSON.stringify(body),
                                   credentials: 'omit', cache: 'no-store'});
  return r.json();
}

const decodeData = pt => { let d = null; try { d = JSON.parse(new TextDecoder().decode(pt)); } catch (e) { d = null; } pt.fill(0); return d; };
/* decrypted data is used only when it has patients and its inner stamp equals the plaintext outer stamp */
const dataOk = (d, blob) => !!d && Array.isArray(d.p) && typeof d.stamp === 'string' && d.stamp === blob.stamp;

/* Download the payload. Replace the stored one only with a valid v3 blob whose stamp is well-formed, not in the
 * future (> 1 day) and strictly newer; while logged in, only after it opened with the in-memory key and its inner
 * stamp matched. -> true when the stored blob was replaced. */
async function refreshData() {
  if (!REG || REG.state !== 'ok') return false;
  const session = SESSION;
  let j;
  try { j = await getJSON(dataUrl()); }
  catch (e) { NOTE = BLOB ? '離線：使用本機資料' : ''; renderSys(); return false; }
  if (j && j.ok === false && j.err === 'auth') { authFailed(); return false; }
  if (j && j.ok === false && j.err === 'unavailable') {
    NOTE = BLOB ? '伺服器暫時無法使用，使用本機資料，請稍後再試' : UNAVAIL_MSG;
    renderSys(); return false;
  }
  if (!j || j.ok === false || j.v !== 3 || !j.k || typeof j.k !== 'object') {
    NOTE = BLOB ? '雲端資料暫不可用，使用本機資料' : '雲端資料暫不可用';
    renderSys(); return false;
  }
  AUTH_BAD = false;
  const why = blobReplace(j.stamp, BLOB && BLOB.stamp, REG.badStamp, Date.now());
  if (why === 'stamp' || why === 'bad') {              // logged in: banner; logged out: the login screen has no banner, so a note
    BANNER_CTX.badStampIgnored = true;
    NOTE = D ? '' : why === 'stamp' ? `收到的資料時間異常（${clip(j.stamp)}），未取代本機資料`
                                    : `雲端資料（${clip(j.stamp)}）內外時間不一致，已拒收，等待電腦下一次更新`;
    renderSys(); return false;
  }
  NOTE = '';
  if (why === '') BANNER_CTX.badStampIgnored = false;
  if (why === 'old') { renderSys(); return false; }
  if (D) {
    const d = await openNewer(j);
    if (session !== SESSION) return false;                 // locked meanwhile: drop the plaintext, the next login downloads again
    if (!d) { BANNER_CTX.newKeyUnopenable = true; renderSys(); return false; }
    await keepBlob(j, true);
    if (session !== SESSION) return true;                  // locked while saving: the blob is stored, but nothing is shown
    if ($('#detail').style.display === 'block') { PENDING = d; BANNER_CTX.pending = true; }
    else applyData(d);
    renderSys();
    return true;
  }
  // logged out: the new blob cannot be checked yet; keep the last verified one as "prev" until a login verifies it
  if (BLOB && BLOB.stamp === REG.verified) { try { await saveBlob(BLOB, 'prev'); } catch (e) { /* ignore */ } }
  await keepBlob(j, false);
  renderSys();
  return true;
}
/* store j as the current blob; verified = it was just opened and its inner stamp matched (then "prev" can go) */
async function keepBlob(j, verified) {
  BLOB = j;
  try { await saveBlob(j); } catch (e) { NOTE = '無法存到本機（僅本次可用）'; }
  if (verified) await markVerified(j.stamp);
}
async function markVerified(stamp) {
  if (!REG) return;
  if (REG.verified === stamp && !REG.badStamp) return;
  REG.verified = stamp; delete REG.badStamp;
  try { await saveReg(REG); await removeBlob('prev'); } catch (e) { /* ignore */ }
}

/* Logged in and a newer blob arrived: open it with the keys kept since login -> data or null. */
async function openNewer(j) {
  const e = own(j.k, REG.acct) ? j.k[REG.acct] : null;
  let pt = null;
  if (REG.mode === 'x' && e && e.t === 'x' && KEYS && own(KEYS, e.p)) pt = await decryptV3X(j, REG.acct, KEYS[e.p]);
  else if (REG.mode === 'pw' && USER && KEK) {
    const pe = own(j.k, accountId(USER)) ? j.k[accountId(USER)] : null;
    if (pe && LOGIN_KEY === pe.s + '|' + pe.it) pt = await decryptV3Kek(j, accountId(USER), KEK);
  }
  if (!pt) return null;
  const d = decodeData(pt);
  return dataOk(d, j) ? d : null;
}

/* swap in newer decrypted data, keeping tab / zone / search; priority items are recomputed and stale ticks dropped */
function applyData(d) {
  D = d; D.p = D.p.filter(x => x && typeof x === 'object'); P = D.p; PENDING = null;
  st.idx = []; st.cur = -1;
  BANNER_CTX.pending = false; BANNER_CTX.newKeyUnopenable = false;
  REQ_MSG = `已載入新資料（${clip(D.stamp)}）`;
  stopPoll();
  if (recalc()) saveChecks();
  renderTabs(); renderPri(); renderAll(); renderSys();
}

async function refreshStatus() {
  if (!REG || REG.state !== 'ok') return;
  try {
    const s = await getJSON(statusUrl());
    if (s && s.ok === false && s.err === 'auth') authFailed();
    else if (!(s && s.err)) AUTH_BAD = false;                 // a normal reply: the server accepts the key again
    if (s && s.ok === false && s.err === 'unavailable') NOTE = UNAVAIL_MSG;    // keep the last status
    else {
      STATUS = (s && s.ok === false && !s.at) ? null : s;
      if (NOTE === UNAVAIL_MSG && STATUS) NOTE = '';
    }
  } catch (e) { /* keep last status */ }
  renderSys();
}

/* status first; download the (large) payload only when status reports a newer stamp or nothing is stored.
 * -> true when the stored blob was replaced. */
async function syncData() {
  await refreshStatus();
  if (!BLOB || (STATUS && stampNewer(STATUS.stamp, BLOB.stamp) && STATUS.stamp !== (REG && REG.badStamp))) return refreshData();
  return false;
}

function stopPoll() { if (POLL) clearInterval(POLL); POLL = null; }
/* after a successful 「請更新」: check status every 90 s for up to 20 min; stop once newer data is in */
function startPoll() {
  stopPoll();
  const until = Date.now() + POLL_MAX_MS;
  let busy = false;
  POLL = setInterval(async () => {
    if (!D || Date.now() > until) { stopPoll(); renderSys(); return; }
    if (busy) return;
    busy = true;
    try { if (await syncData()) stopPoll(); } finally { busy = false; }
  }, POLL_MS);
}

function reqAcct() { return REG.mode === 'pw' ? accountId(USER) : REG.acct; }

async function requestRefresh() {
  if (!AUTH || !REG) { REQ_MSG = '無法送出（缺少簽章金鑰，請重新登記）'; renderSys(); return; }
  REQ_SENDING = true; renderSys();
  try {
    const ts = Math.floor(Date.now() / 1000), acct = reqAcct();
    const j = await postJSON({a: 'refresh', k: REG.access, acct: acct, ts: ts, proof: await proofV3(AUTH, `${acct}|${ts}`)});
    if (j && j.err === 'auth') { authFailed(); REQ_MSG = AUTH_MSG; }
    else if (j && j.err === 'unavailable') REQ_MSG = UNAVAIL_MSG;
    else REQ_MSG = j && j.local ? '本機測試模式：不送出'
      : j && j.ok ? '已送出，約 5 分鐘後更新（若無更新，請確認名單上「可請求更新」為 Y）'
      : (j && j.err === 'rate' ? '請稍候 1 分鐘再試' : '送出失敗');
    if (j && j.ok) startPoll();
  } catch (e) {
    REQ_MSG = '無網路，無法送出';
  }
  REQ_SENDING = false;
  renderSys();
}

/* ================= passkey (WebAuthn PRF) ================= */
const testPrf = () => LOCAL && IS_LOCALHOST && typeof window.__TEST_PRF__ === 'function' ? window.__TEST_PRF__ : null;
const rnd = n => crypto.getRandomValues(new Uint8Array(n));
const prfErr = e => e && e.name === 'NotAllowedError' ? '已取消或逾時' : (e && e.message ? e.message : String(e));

/* -> {first: Uint8Array(32), second: Uint8Array(32)|null} PRF outputs for the two salts */
async function passkeyGet(credId, first, second) {
  const t = testPrf();
  if (t) return {first: t(first), second: second ? t(second) : null};
  if (!window.PublicKeyCredential || !navigator.credentials) throw new Error('此瀏覽器不支援 passkey');
  const a = await navigator.credentials.get({publicKey: {
    rpId: RP_ID, challenge: rnd(32), userVerification: 'required', timeout: 120000,
    allowCredentials: credId && credId !== 'test' ? [{type: 'public-key', id: b64d(credId)}] : [],
    extensions: {prf: {eval: second ? {first: first, second: second} : {first: first}}}}});
  const res = ((a.getClientExtensionResults() || {}).prf || {}).results;
  if (!res || !res.first) throw new Error('此裝置的 passkey 未提供金鑰（PRF），請改用備援密碼');
  return {first: new Uint8Array(res.first), second: second && res.second ? new Uint8Array(res.second) : null};
}
/* new passkey -> {priv: PRF(salt) as the X25519 private key, credId}, or {priv: null, credId, needGet: true} when
 * the platform evaluates PRF only on get(): the caller then needs a fresh tap (user activation) before passkeyGet,
 * since create() used up this one and Safari rejects a get() without it. */
async function passkeyCreate(user, name, salt) {
  const t = testPrf();
  if (t) return window.__TEST_PRF_GET_ONLY__ ? {priv: null, credId: 'test', needGet: true} : {priv: t(salt), credId: 'test'};
  if (!window.PublicKeyCredential || !navigator.credentials) throw new Error('此瀏覽器不支援 passkey');
  const cred = await navigator.credentials.create({publicKey: {
    rp: {id: RP_ID, name: '值班'},
    user: {id: rnd(16), name: user, displayName: name},
    challenge: rnd(32),
    pubKeyCredParams: [{type: 'public-key', alg: -7}, {type: 'public-key', alg: -257}],
    authenticatorSelection: {residentKey: 'required', requireResidentKey: true, userVerification: 'required'},
    attestation: 'none', timeout: 120000,
    extensions: {prf: {eval: {first: salt}}}}});
  const credId = b64e(new Uint8Array(cred.rawId));
  const prf = (cred.getClientExtensionResults() || {}).prf || {};
  if (prf.results && prf.results.first) return {priv: new Uint8Array(prf.results.first), credId: credId};
  if (prf.enabled === false) throw new Error('此裝置的 passkey 不支援 PRF，請改用備援密碼');
  return {priv: null, credId: credId, needGet: true};  // some platforms only evaluate PRF on get(): needs a new tap
}

/* ================= first-run setup: Face ID enrolment ================= */
const ENROLL_ERR = {rate: '登記人數過多，請 10 分鐘後再試', full: '登記佇列已滿，請聯絡管理者', 'not configured': '伺服器尚未設定，請聯絡管理者'};

async function enrollX(ev) {
  ev.preventDefault();
  const user = $('#su').value.trim(), name = $('#sn').value.trim(), msg = $('#sm');
  const n = Array.from(name).length;
  if (!user) { msg.textContent = '請輸入帳號'; return; }
  if (n < 1 || n > 20 || /[\u0000-\u001f\u007f‪-‮⁦-⁩]/.test(name)) { msg.textContent = '顯示姓名需 1–20 字'; return; }
  $('#sb').disabled = true; $('#pb').disabled = true;
  msg.textContent = '建立 passkey…';
  try {
    const per = period(new Date());
    const c = await passkeyCreate(user, name, prfSalt(per));
    if (c.needGet) {
      // PRF not returned by create(): a get() must come from a new user gesture, so ask for one more tap
      msg.textContent = 'passkey 已建立，請再按一次下方按鈕以 Face ID 完成登記';
      const bx = $('#sx');
      bx.style.display = ''; bx.disabled = false;
      $('#pb').disabled = false;                       // the backup-password route stays available meanwhile
      bx.onclick = async () => {                       // runs inside the click: fresh user activation for get()
        bx.disabled = true;
        msg.textContent = 'Face ID…';
        let r = null;
        try {
          r = await passkeyGet(c.credId, prfSalt(per), null);
          await submitEnrollX(user, name, per, r.first, c.credId);   // -> pending pane, or showSetup (hides #sx)
        } catch (e) {
          msg.textContent = '無法完成：' + prfErr(e) + '（可再按一次）';
          bx.disabled = false;
        } finally {
          if (r && r.first) r.first.fill(0);
        }
      };
      return;
    }
    await submitEnrollX(user, name, per, c.priv, c.credId);
  } catch (e) {
    showSetup('無法啟用：' + prfErr(e));
  }
}

/* enrolment key priv (wiped here) -> POST enroll -> pending state */
async function submitEnrollX(user, name, per, priv, credId) {
  let pub;
  try { pub = await x25519Pub(priv); } finally { priv.fill(0); }
  const acct = accountId(user), pubB64 = b64e(pub), code = await confirmCode(pub);
  const j = await postJSON({a: 'enroll', acct: acct, name: name, pub: pubB64, code: code, period: per});
  if (!j || !j.ok) { showSetup((j && ENROLL_ERR[j.err]) || '登記送出失敗，請稍後再試'); return; }
  REG = {v: 1, state: 'pending', mode: 'x', acct: acct, name: name, pub: pubB64, code: code, credId: credId,
         enrollP: per, at: Date.now()};
  await saveReg(REG);
  $('#su').value = ''; $('#sn').value = '';
  showPending();
}

function stopGrantPoll() { if (GPOLL) clearInterval(GPOLL); GPOLL = null; }
function showPending(text) {
  show('#pending');
  $('#pcode').textContent = REG.code.slice(0, 3) + ' ' + REG.code.slice(3);     // 6 digits shown as 3 + 3
  $('#pacct').textContent = `帳號雜湊前 6 碼 ${REG.acct.slice(0, 6)}，期別 ${REG.enrollP}`;
  $('#pfin').style.display = REG.grant ? '' : 'none';
  $('#pfin').disabled = false; $('#pchk').disabled = false;
  $('#pm').textContent = text || (REG.grant ? '已核可，請按「完成啟用」以 Face ID 確認' : '等待核可中…（每 60 秒自動檢查）');
  stopGrantPoll();
  if (!REG.grant) { GPOLL = setInterval(() => { if (document.visibilityState === 'visible') checkGrant(); }, GRANT_POLL_MS); checkGrant(); }
}
async function checkGrant() {
  if (!REG || REG.state !== 'pending' || REG.grant) return;
  let j;
  try { j = await getJSON(grantUrl(REG.acct)); }
  catch (e) { $('#pm').textContent = '無法連線，稍後自動再試'; return; }
  const g = j && j.ok === true && j.g && typeof j.g === 'object' ? j.g : null;
  if (!g || JSON.stringify(g) === REG.badGrant) {
    const t = new Date();
    $('#pm').textContent = `等待核可中…（${pad(t.getHours())}:${pad(t.getMinutes())} 已檢查）`;
    return;
  }
  REG.grant = g; REG.grantP = REG.enrollP;
  await saveReg(REG);
  showPending();
}
/* the grant box is sealed to the enrolment public key: Face ID (PRF of the enrolment period) opens it */
async function finishEnroll() {
  $('#pfin').disabled = true;
  $('#pm').textContent = 'Face ID…';
  let r = null;
  try {
    r = await passkeyGet(REG.credId, prfSalt(REG.grantP), null);
    const g = await openGrant(r.first, REG.grant);
    if (!g) {
      REG.badGrant = JSON.stringify(REG.grant); delete REG.grant; delete REG.grantP;
      await saveReg(REG);
      showPending('核可資料與這支手機的 passkey 不符（可能是舊登記），繼續等待新的核可');
      return;
    }
    REG.access = b64ue(g.access);
    g.access.fill(0); g.auth.fill(0);
    REG.grants = {}; REG.grants[REG.grantP] = REG.grant;
    delete REG.grant; delete REG.grantP;
    REG.state = 'ok'; delete REG.badGrant;
    await saveReg(REG);
    showBoot('啟用完成，下載資料中…');
    await syncData();
    if (BLOB) { showLogin(); toast('已核可'); }
    else { showBoot('啟用完成。電腦下次更新資料後即可登入' + (NOTE ? '（' + NOTE + '）' : ''), true); toast('已核可，下次更新後即可開啟'); }
  } catch (e) {
    showPending('無法完成：' + prfErr(e));
  } finally {
    if (r && r.first) r.first.fill(0);
  }
}
async function cancelEnroll() {
  if (!await ask('取消這次登記？')) return;
  stopGrantPoll();
  REG = null;
  try { await removeBlob('reg'); } catch (e) { /* ignore */ }
  showSetup();
}

/* ================= first-run setup: backup password ================= */
async function setupPw(ev) {
  ev.preventDefault();
  const msg = $('#sm'), user = $('#pu').value.trim(), pass = normPass($('#pp').value), key = $('#pk').value.trim();
  if (!/^[A-Za-z0-9_-]{22}$/.test(key) || b64ud(key).length !== 16) { msg.textContent = '存取碼格式不正確'; return; }
  $('#sb').disabled = true; $('#pb').disabled = true;
  msg.textContent = '下載資料中…';
  const reg = {v: 1, state: 'ok', mode: 'pw', acct: accountId(user), access: key};
  let j;
  try { j = await getJSON(LOCAL ? './data.json' : EXEC_URL + '?a=data&k=' + encodeURIComponent(key)); }
  catch (e) { showSetup('無法連線，請稍後再試'); return; }
  if (j && j.ok === false && j.err === 'auth') { showSetup('存取碼錯誤或已失效'); return; }
  if (j && j.ok === false && j.err === 'unavailable') { showSetup('伺服器暫時無法使用，請稍後再試'); return; }
  if (!j || j.v !== 3 || !j.k || typeof j.k !== 'object') { showSetup('雲端資料暫不可用'); return; }
  if (!stampOk(j.stamp, Date.now())) { showSetup(`收到的資料時間異常（${clip(j.stamp)}）`); return; }
  msg.textContent = '驗證中…';
  const r = await decryptV3PwKek(j, user, pass);
  if (!r) { showSetup('帳號或通關句錯誤（或資料尚未包含此帳號）'); $('#pp').value = ''; return; }
  const d = decodeData(r.pt);
  if (!dataOk(d, j)) { r.kek.fill(0); showSetup('資料內外時間不一致，未使用'); return; }
  REG = reg;
  await saveReg(REG);
  await keepBlob(j, true);
  $('#pu').value = ''; $('#pp').value = ''; $('#pk').value = '';
  await startPw(d, user, r.kek, j);
}

/* ================= login / lock ================= */
function startPw(d, user, kek, blob) {
  const e = blob.k[accountId(user)];
  KEK = kek; USER = user; LOGIN_KEY = e.s + '|' + e.it; AUTH = authFromKek(kek);
  return start(d);
}

async function loginPw(ev) {
  ev.preventDefault();
  const msg = $('#lm'), btn = $('#lb');
  if (!BLOB) { msg.textContent = '尚無資料'; return; }
  msg.textContent = '驗證中…'; btn.disabled = true;
  const user = $('#lu').value.trim(), pass = normPass($('#lp').value);
  $('#lp').value = '';
  const r = await decryptV3PwKek(BLOB, user, pass);
  if (!r) { msg.textContent = '帳號或通關句錯誤'; btn.disabled = false; return; }
  const d = decodeData(r.pt);
  if (!dataOk(d, BLOB)) { r.kek.fill(0); await rejectBlob(); return; }
  msg.textContent = '';
  await markVerified(BLOB.stamp);
  await startPw(d, user, r.kek, BLOB);
}

/* The stored blob's inner stamp differs from its plaintext stamp: do not use it. Remember its stamp (refreshData
 * refuses it until a different stamp arrives) and go back to the last verified blob ("prev"); no re-download. */
async function rejectBlob() {
  const bad = BLOB ? BLOB.stamp : '';
  REG.badStamp = bad;
  try { await saveReg(REG); } catch (e) { /* ignore */ }
  let prev = null;
  try { prev = await loadBlob('prev'); } catch (e) { prev = null; }
  if (prev && prev.v === 3 && prev.stamp !== bad) {
    BLOB = prev;
    try { await saveBlob(prev); await removeBlob('prev'); } catch (e) { /* ignore */ }
    showLogin(`新資料（${clip(bad)}）內外時間不一致，已改用前一份資料（${clip(prev.stamp)}），請再登入一次`);
    return;
  }
  BLOB = null;
  try { await removeBlob(); } catch (e) { /* ignore */ }
  showBoot(`資料（${clip(bad)}）內外時間不一致，已拒收；等待電腦下一次更新`, true);
}

/* Face ID: PRF(first = salt of the period this blob was wrapped for, second = salt of this month). The first key
 * opens the data; when the month moved on, the second key's public key is sent as a rotation signed with the auth
 * key from the grant. */
async function loginX() {
  const msg = $('#lm');
  if (!BLOB) { msg.textContent = '尚無資料'; return; }
  const e = own(BLOB.k, REG.acct) ? BLOB.k[REG.acct] : null;
  if (!e || e.t !== 'x' || !PERIOD_RE.test(String(e.p))) { msg.textContent = '資料中尚無您的 Face ID 登記（電腦下次更新資料後即可登入）'; return; }
  const cur = period(new Date());
  fxBusy(true); msg.textContent = '';
  let r;
  try { r = await passkeyGet(REG.credId, prfSalt(e.p), cur !== e.p ? prfSalt(cur) : null); }
  catch (err) { msg.textContent = '無法使用 Face ID：' + prfErr(err); fxBusy(false); return; }
  const wipe = () => { r.first.fill(0); if (r.second) r.second.fill(0); };
  const pt = await decryptV3X(BLOB, REG.acct, r.first);
  if (!pt) { wipe(); msg.textContent = 'Face ID 金鑰無法開啟資料（請確認使用登記時的 passkey）'; fxBusy(false); return; }
  const d = decodeData(pt);
  if (!dataOk(d, BLOB)) { wipe(); await rejectBlob(); return; }
  KEYS = {}; KEYS[e.p] = r.first;
  const rotate = !!r.second && cur !== e.p && b64e(r.first) !== b64e(r.second);
  if (r.second && cur !== e.p) KEYS[cur] = r.second;
  const grants = REG.grants || {};
  for (const gp of grantOrder(grants, [e.p, cur].filter(p => own(KEYS, p)))) {
    const g = await openGrant(KEYS[gp], grants[gp]);
    if (g) { AUTH = g.auth; g.access.fill(0); break; }
  }
  const pruned = pruneGrants(grants, e.p, cur);
  if (pruned !== grants) REG.grants = pruned;
  REG.verified = BLOB.stamp; delete REG.badStamp;
  try { await saveReg(REG); await removeBlob('prev'); } catch (err) { /* ignore */ }
  msg.textContent = '';
  const rotPriv = rotate ? KEYS[cur].slice() : null, rotAuth = AUTH ? AUTH.slice() : null;   // copies: lock() may wipe the globals
  await start(d);
  if (rotate) sendRotate(cur, rotPriv, rotAuth);
}

/* rotation request: newpub = X25519 public key of this month's PRF key, proof = HMAC(auth, acct|newpub|period|ts).
 * priv / auth are private copies (lock() may wipe the globals meanwhile). BEFORE the server can learn the new key,
 * the grant is sealed (on the phone) to the new public key and saved under REG.grants[cur]; the old period's grant
 * stays until a blob for the current period has opened (pruneGrants), so whichever period the next blob is wrapped
 * for, its key opens a grant. Unanswered / failed requests are retried at a later login. */
async function sendRotate(cur, priv, auth) {
  const reg = REG;
  try {
    if (!auth || reg.mode !== 'x') { REQ_MSG = '本月金鑰輪替未送出（無法開啟核可資料）'; renderSys(); return; }
    if (reg.rotP === cur && Date.now() - (reg.rotAt || 0) < ROT_RETRY_MS) return;
    const newpub = await x25519Pub(priv), nb = b64e(newpub);
    if (!own(reg.grants, cur)) {
      const access = b64ud(reg.access);
      const box = await sealGrant(newpub, access, auth);
      access.fill(0);
      if (REG !== reg) return;                               // local data cleared meanwhile
      const grants = Object.assign({}, reg.grants); grants[cur] = box;
      reg.grants = grants;
      await saveReg(reg);
    }
    if (REG !== reg) return;
    const ts = Math.floor(Date.now() / 1000);
    const proof = await proofV3(auth, `${reg.acct}|${nb}|${cur}|${ts}`);
    const j = await postJSON({a: 'rotate', k: reg.access, acct: reg.acct, ts: ts, proof: proof, newpub: nb, period: cur});
    if (REG !== reg) return;
    if (j && j.err === 'auth') { authFailed(); return; }
    if (!j || !j.ok) return;
    reg.rotP = cur; reg.rotAt = Date.now();
    await saveReg(reg);
    if (j.local) { REQ_MSG = `本機測試模式：輪替（${cur}）未送出`; renderSys(); }
    else if (D) toast('已更新個人金鑰');
  } catch (e) { /* retried at the next login */ }
  finally { priv.fill(0); if (auth) auth.fill(0); }
}

/* show the list for freshly decrypted data d; the keys (KEYS / KEK) must be set already: they unlock the stored ticks */
async function start(d) {
  D = d; P = D.p;
  D.p = D.p.filter(x => x && typeof x === 'object'); P = D.p;
  lastAct = Date.now();                                   // the login tap counts as activity (the listener only runs once D is set)
  st = newSt(); BANNER_CTX = {badStampIgnored: false, newKeyUnopenable: false, pending: false};
  $('#q').value = '';
  REQ_MSG = '';
  ITEMS = priorityItems(P);
  const ticks = await loadChecks();
  if (!D) return;                                         // locked while the ticks were loading
  CHECKS = pruneChecks(ticks, ITEMS);                     // against the items as they are now (a sync may have replaced the data meanwhile)
  NOTES = await loadNotes();                              // 待辦 notes: sealed with the same keys as the ticks
  if (!D) return;                                         // locked while the notes were loading
  show('#list');
  showTab('pri');
  renderSys();
  window.scrollTo(0, 0);
  bump();
}

/* Wipe plaintext and keys from memory and the DOM, back to the login screen (no reload: the blob stays). */
function lock() {
  SESSION++;
  clearTimeout(idleT);
  stopPoll();
  if (KEYS) Object.keys(KEYS).forEach(k => KEYS[k].fill(0));
  if (KEK) KEK.fill(0);
  if (AUTH) AUTH.fill(0);
  KEYS = null; KEK = null; AUTH = null; USER = null; LOGIN_KEY = null; D = null; P = null; PENDING = null;
  ITEMS = []; CHECKS = []; REQ_SENDING = false;
  NOTES = {}; UNDO = null; NOTE_I = -1; SW0 = null; clearTimeout(NOTE_T); SW_CHART = null;
  if (REC) { try { REC.stop(); } catch (e) { /* ignore */ } }   // onstop sees the new session and keeps nothing
  REC = null; RECCHUNKS = [];
  if (AUDIO) { AUDIO.pause(); AUDIO = null; }
  BANNER_CTX = {badStampIgnored: false, newKeyUnopenable: false, pending: false};
  st = newSt();
  ['#pri', '#cards', '#zone', '#db', '#meta', '#nline', '#banner', '#toast', '#dtx', '#todo', '#npd', '#npbar', '#printdoc'].forEach(s => { $(s).innerHTML = ''; $(s).textContent = ''; });
  $('#np').style.display = 'none'; document.body.style.overflow = '';
  $('#q').value = ''; $('#lp').value = ''; $('#lu').value = ''; REQ_MSG = '';
  $('.tb [data-tab=pri]').textContent = '優先'; $('.tb [data-tab=all]').textContent = '全部'; $('.tb [data-tab=todo]').textContent = '待辦';
  ['#menu', '#dlg', '#toast'].forEach(s => $(s).classList.remove('on'));
  $('#detail').style.display = 'none'; document.body.style.overflow = ''; hist('');
  if (!REG || REG.state !== 'ok') return;
  if (BLOB) showLogin(); else showBoot('尚無資料，請連 4G 開啟以下載', true);
}

async function clearLocal() {
  if (!await ask('清除這支手機上的所有值班資料（登記、存取碼、已下載資料）？之後需要重新登記。')) return;
  lock();
  stopGrantPoll();
  REG = null; BLOB = null; STATUS = null;
  await clearAll();
  location.replace(location.pathname + location.search);
}

let idleT = null, lastAct = Date.now();
function bump() {
  lastAct = Date.now();
  clearTimeout(idleT);
  if (D) idleT = setTimeout(lock, IDLE_MS);
}
['click', 'touchstart', 'keydown', 'scroll'].forEach(e => addEventListener(e, () => { if (D) bump(); }, {passive: true}));
document.addEventListener('visibilitychange', () => {
  if (document.visibilityState !== 'visible') {     // keep patient data out of the app-switcher snapshot
    document.documentElement.classList.add('hid');
    return;
  }
  // timers do not run while iOS has the app in the background: check the wall clock on return
  if (D && Date.now() - lastAct > IDLE_MS) lock();
  document.documentElement.classList.remove('hid');
  if (REG && REG.state === 'pending' && !REG.grant) checkGrant();
  if (navigator.onLine !== false) syncData().then(got => {
    if (got && !D && BLOB && REG && REG.state === 'ok' && $('#boot').style.display !== 'none') showLogin();
  });
});
$('#sf').addEventListener('submit', enrollX);
$('#pf').addEventListener('submit', setupPw);
$('#lf').addEventListener('submit', loginPw);
$('#fx').onclick = loginX;
$('#pfin').onclick = finishEnroll;
$('#pchk').onclick = () => { $('#pm').textContent = '檢查中…'; checkGrant(); };
$('#pcan').onclick = cancelEnroll;
$('#clr').onclick = clearLocal;
$('#bretry').onclick = retryBoot;
$('#swpw').onclick = () => { const f = $('#pf'); f.style.display = f.style.display === 'none' ? '' : 'none'; };

/* ================= 待辦清單: to-do notes, recordings, swipe, undo ================= */
/* NOTES = {chart: {todo, items, audio}} sealed as one blob (key "notes"); each recording is its own sealed blob ("audio:<id>").
 * Both use the tick subkey recipe (crypto.js sealBytes, label NOTE_INFO). Lock wipes the memory copy; 清除本機 drops the DB. */
const NOTE_ID = () => Date.now().toString(36) + Math.random().toString(36).slice(2, 7);
let NOTE_I = -1;        // patient index of the open notepad
let SW0 = null;         // touch start of a horizontal swipe on the patient page
async function loadNotes() {
  let rec = null;
  try { rec = await loadBlob('notes'); } catch (e) { rec = null; }
  if (!rec || !REG || rec.mode !== REG.mode) return {};
  const ikm = REG.mode === 'x' ? (KEYS && own(KEYS, rec.p) ? KEYS[rec.p] : null) : KEK;
  const pt = openBytes(ikm, rec, NOTE_INFO);
  if (!pt) return {};
  let o = null;
  try { o = JSON.parse(new TextDecoder().decode(pt)); } catch (e) { o = null; }
  pt.fill(0);
  return o && typeof o === 'object' && !Array.isArray(o) ? o : {};
}
async function saveNotes() {
  const k = checksKey();
  if (!k) return;
  const raw = new TextEncoder().encode(JSON.stringify(NOTES));
  const box = sealBytes(k.ikm, raw, NOTE_INFO);
  raw.fill(0);
  box.mode = k.mode; box.p = k.p;
  try { await saveBlob(box, 'notes'); } catch (e) { /* kept in memory only */ }
}
function putNote(chart, patch) { NOTES[chart] = Object.assign({}, NOTES[chart] || {}, patch); saveNotes(); }
const noteItems = chart => Array.isArray((NOTES[chart] || {}).items) ? NOTES[chart].items : [];
const noteAudio = chart => Array.isArray((NOTES[chart] || {}).audio) ? NOTES[chart].audio : [];

/* Tinder-style swipe on the patient page: the page follows the finger and tilts; past the threshold it flies off.
 * Left = 待辦: the notepad slides in (the patient is marked 待辦). Right = 沒問題: next patient. Both can be undone. */
let SW_CHART = null, SW_ON = false;
function bindSwipe(chart) {
  SW_CHART = chart;
  if (SW_ON) return;
  SW_ON = true;
  const el = $('#detail'), lab = $('#swl'), TH = 90, FLICK_PX = 40, FLICK_V = .45; // px, px, px/ms
  let s = null, dir = null;
  // 卡片跟著拇指的弧線走：水平位移為主，垂直位移只跟 35%，所以斜向甩動（左手左上、右手右上）也會往該側飛出
  const pose = (dx, dy) => `translateX(${dx}px) translateY(${dy * .35}px) rotate(${dx / 25}deg)`;
  const commit = (dx, dt) => Math.abs(dx) >= TH || (Math.abs(dx) >= FLICK_PX && Math.abs(dx) / Math.max(dt, 1) >= FLICK_V);
  const reset = anim => { el.style.transition = anim ? 'transform .22s ease, opacity .22s ease' : 'none'; el.style.transform = ''; el.style.opacity = ''; lab.className = 'swl'; };
  el.addEventListener('touchstart', e => {
    if (e.touches.length !== 1 || $('#np').style.display === 'block') { s = null; return; }
    const t = e.touches[0]; s = {x: t.clientX, y: t.clientY, t: Date.now()}; dir = null; el.style.transition = 'none';
  }, {passive: true});
  el.addEventListener('touchmove', e => {
    if (!s) return;
    const t = e.touches[0], dx = t.clientX - s.x, dy = t.clientY - s.y;
    // 水平分量 ≥ 垂直分量的 45% 就視為水平（弧線甩動）；幾乎純上下才當成捲動內容
    if (dir === null && (Math.abs(dx) > 8 || Math.abs(dy) > 8)) dir = Math.abs(dx) >= Math.abs(dy) * .45 ? 'h' : 'v';
    if (dir !== 'h') return;
    e.preventDefault();
    el.style.transform = pose(dx, dy);
    el.style.opacity = String(Math.max(.4, 1 - Math.abs(dx) / 600));
    const go = commit(dx, Date.now() - s.t);
    lab.textContent = dx < 0 ? '待辦' : '沒問題';
    lab.className = 'swl on ' + (dx < 0 ? 'l' : 'r') + (go ? ' go' : '');
  }, {passive: false});
  el.addEventListener('touchend', e => {
    const t = e.changedTouches && e.changedTouches[0], from = s; s = null;
    if (!from || dir !== 'h' || !t) { reset(false); return; }
    const dx = t.clientX - from.x, dy = t.clientY - from.y, dt = Date.now() - from.t;
    if (!commit(dx, dt)) { reset(true); return; }
    const left = dx < 0;
    el.style.transition = 'transform .22s ease, opacity .22s ease';
    el.style.transform = `translateX(${left ? -140 : 140}vw) translateY(${dy * .35}px) rotate(${left ? -18 : 18}deg)`; el.style.opacity = '0';
    lab.className = 'swl';
    setTimeout(() => { reset(false); swipeDone(SW_CHART, left); }, 220);
  }, {passive: true});
  el.addEventListener('touchcancel', () => { s = null; reset(true); }, {passive: true});
}
function swipeDone(chart, left) {
  const pi = st.order[st.cur];
  if (left) { setTodo(chart, true, null); const i = P.findIndex(p => p.chart === chart); openNote(i >= 0 ? i : pi, true); }
  else { setTodo(chart, false, pi); if (st.cur < st.order.length - 1) go(1); else closeDetail(); }
}
/* on = 待辦 / off = 沒問題. pi = the patient page to come back to when the 復原 button is used (right swipe) */
function setTodo(chart, on, pi) {
  if (!chart) return;
  const cur = NOTES[chart] || {}, changed = (cur.todo === true) !== on;
  if (!changed && on) return;
  UNDO = {chart: chart, before: NOTES[chart] ? JSON.stringify(NOTES[chart]) : null, pi: pi == null ? null : pi};
  if (changed) putNote(chart, {todo: on});
  renderTodo(); renderTabs();
  toastUndo(on ? '已加入待辦' : '沒問題');
}
function undoNotes() {
  const u = UNDO;
  if (!u) return;
  UNDO = null;
  if (u.before == null) delete NOTES[u.chart]; else NOTES[u.chart] = JSON.parse(u.before);
  saveNotes(); renderTodo(); renderTabs();
  $('#toast').classList.remove('on');
  if (NOTE_I >= 0 && !(NOTES[P[NOTE_I].chart] || {}).todo) closeNote();
  if (u.pi != null && $('#detail').style.display === 'block') renderDetail(u.pi);
}
/* toast with a 復原 button for 5 s (the pointer-events of the button are re-enabled in the CSS) */
function toastUndo(text) {
  const t = $('#toast');
  t.innerHTML = `<span>${esc(text)}</span><button type="button" id="undo">復原</button>`;
  t.classList.add('on');
  clearTimeout(toast.t);
  toast.t = setTimeout(() => { t.classList.remove('on'); UNDO = null; }, 5000);
  $('#undo').onclick = undoNotes;
}

const ymdLocal = ms => { const d = new Date(Number(ms)); return `${d.getMonth() + 1}/${d.getDate()}`; };
const hmLocal = ms => { const d = new Date(Number(ms)); return pad(d.getHours()) + ':' + pad(d.getMinutes()); };

/* 待辦 tab: identity, attending and the to-do text only, plus 輸出 PDF */
function renderTodo() {
  const el = $('#todo');
  if (!el || !P) return;
  const idx = todoIdx();
  if (!idx.length) { el.innerHTML = '<div class="empty">沒有待辦<small>在病人頁左滑即可加入待辦；右滑表示沒問題</small></div>'; return; }
  el.innerHTML = `<div class="tdh"><span>${idx.length} 位 · ${esc(ymdLocal(Date.now()))}</span><button id="pdfall" type="button">輸出 PDF</button></div>` + idx.map(i => { const p = P[i], open = noteItems(p.chart).filter(x => !x.done && x.t);
    return `<div class="tdo" role="button" tabindex="0" data-note="${i}"><div class="r1"><span class="bed">${esc(p.bed)}</span><span class="nm">${esc(p.name)}</span></div><div class="vs2">主治 ${esc(p.vs || '–')}</div>${open.length ? `<ul>${open.slice(0, 4).map(x => `<li>${esc(x.t)}</li>`).join('')}${open.length > 4 ? `<li class="sub">+${open.length - 4} 項</li>` : ''}</ul>` : '<div class="sub">尚無待辦文字</div>'}</div>`;
  }).join('');
}

/* notepad page: Apple-Notes style checklist (Enter = next check, done = strike-through and moves down) + record bar */
function openNote(i, slide) {
  if (!P || !P[i]) return;
  NOTE_I = i;
  $('#npt').textContent = `${P[i].bed} ${P[i].name}`;
  const np = $('#np');
  np.style.display = 'block'; document.body.style.overflow = 'hidden'; np.scrollTop = 0;
  np.classList.remove('slide');
  if (slide) { void np.offsetWidth; np.classList.add('slide'); }
  drawNote();
}
function closeNote() {
  commitNew();
  if (REC) { try { REC.stop(); } catch (e) { /* ignore */ } }
  $('#np').style.display = 'none'; NOTE_I = -1;
  if ($('#detail').style.display !== 'block') document.body.style.overflow = '';
  saveNotes(); renderTodo(); renderTabs();
}
function noteRow(x) {
  const t = esc(x.t);
  return `<li class="${x.done ? 'done' : ''}"><span class="cbx" data-ntoggle="${esc(x.id)}" role="checkbox" aria-checked="${!!x.done}"></span><input class="ni" data-id="${esc(x.id)}" type="text" enterkeyhint="next" maxlength="200" autocomplete="off" value="${t}"${x.done ? ' readonly' : ''}>${x.done ? `<button type="button" class="nd" data-ndel="${esc(x.id)}" aria-label="刪除">×</button>` : ''}</li>`;
}
/* focusId: an item id, '' = the empty line at the end, undefined = leave the focus alone */
function drawNote(focusId) {
  const p = P && P[NOTE_I];
  if (!p) return;
  const items = noteItems(p.chart), open = items.filter(x => !x.done), done = items.filter(x => x.done);
  $('#npd').innerHTML = `<div class="dh"><h2 class="ttl"><span class="b">${esc(p.bed)}</span>${esc(p.name)}</h2><div class="sub">主治 ${esc(p.vs || '–')} · ${esc(ymdLocal(Date.now()))}</div></div>
    <ul class="cl">${open.map(noteRow).join('')}<li class="new"><span class="cbx"></span><input class="ni" id="npnew" data-id="" type="text" enterkeyhint="done" maxlength="200" autocomplete="off" placeholder="新增待辦…"></li></ul>
    ${done.length ? `<div class="donehd">已完成 ${done.length}</div><ul class="cl dn">${done.map(noteRow).join('')}</ul>` : ''}`;
  drawBar();
  if (focusId === '') { const n = $('#npnew'); if (n) n.focus(); }
  else if (focusId) { const el = $('#npd').querySelector(`.ni[data-id="${CSS.escape(focusId)}"]`); if (el) { el.focus(); el.setSelectionRange(el.value.length, el.value.length); } }
}
function drawBar() {
  const p = P && P[NOTE_I], bar = $('#npbar');
  if (!p || !bar) return;
  const aud = noteAudio(p.chart);
  bar.innerHTML = (aud.length ? `<div class="chips">${aud.map(a => `<span class="ach"><button type="button" class="pl" data-play="${esc(a.id)}">▶ ${esc(ymdLocal(a.ts))} ${esc(hmLocal(a.ts))} · ${Number(a.s) || 0}s</button><button type="button" class="nd" data-adel="${esc(a.id)}" aria-label="刪除錄音">×</button></span>`).join('')}</div>` : '')
    + `<button id="rec" type="button" class="rec${REC ? ' on' : ''}">${REC ? '■ 停止錄音' : '● 錄音'}</button>`;
}
let NOTE_T = null;
const noteSaveSoon = () => { clearTimeout(NOTE_T); NOTE_T = setTimeout(saveNotes, 500); };
const newItem = t => ({id: NOTE_ID(), t: t || '', done: false, ts: Date.now()});
/* the empty line at the end becomes a real item (no redraw: a tap on another control must not be swallowed) */
function commitNew() {
  const p = P && P[NOTE_I], n = $('#npnew');
  if (!p || !n) return null;
  const t = n.value.trim();
  if (!t) return null;
  const it = newItem(t.slice(0, 200));
  putNote(p.chart, {items: noteItems(p.chart).concat([it])});
  n.value = '';
  return it;
}
function noteEdit(fn) { const p = P && P[NOTE_I]; if (!p) return; putNote(p.chart, {items: fn(noteItems(p.chart))}); }
function toggleNoteItem(id) { commitNew(); noteEdit(L => L.map(x => x.id === id ? Object.assign({}, x, {done: !x.done}) : x)); drawNote(); }
function delNoteItem(id) { noteEdit(L => L.filter(x => x.id !== id)); drawNote(); }
$('#npb').onclick = closeNote;
$('#npp').onclick = () => exportPdf(NOTE_I);
$('#npd').addEventListener('input', e => {
  const t = e.target, p = P && P[NOTE_I];
  if (!p || !t.classList.contains('ni') || !t.dataset.id) return;
  const it = noteItems(p.chart).find(x => x.id === t.dataset.id);
  if (it) { it.t = t.value.slice(0, 200); noteSaveSoon(); }
});
$('#npd').addEventListener('keydown', e => {
  const t = e.target, p = P && P[NOTE_I];
  if (!p || !t.classList.contains('ni')) return;
  const id = t.dataset.id;
  if (e.key === 'Enter') {
    e.preventDefault();
    if (!id) { const it = commitNew(); if (it) drawNote(''); else t.blur(); return; }
    if (!t.value.trim()) { t.blur(); return; }
    const L = noteItems(p.chart).slice(), at = L.findIndex(x => x.id === id), nx = newItem('');
    L.splice(at + 1, 0, nx); putNote(p.chart, {items: L}); drawNote(nx.id);
  } else if (e.key === 'Backspace' && id && t.value === '') {
    e.preventDefault();
    const L = noteItems(p.chart).filter(x => !x.done), at = L.findIndex(x => x.id === id);
    delNoteItem(id);
    drawNote(at > 0 ? L[at - 1].id : '');
  }
});
$('#npd').addEventListener('focusout', e => {       // an item left empty is dropped (no redraw: the next tap must work)
  const t = e.target, p = P && P[NOTE_I];
  if (!p || !t.classList || !t.classList.contains('ni') || !t.dataset.id || t.value.trim()) return;
  putNote(p.chart, {items: noteItems(p.chart).filter(x => x.id !== t.dataset.id)});
  const li = t.closest('li'); if (li) li.remove();
});
$('#npd').addEventListener('click', e => {
  const tg = e.target.closest('[data-ntoggle]'); if (tg) { toggleNoteItem(tg.dataset.ntoggle); return; }
  const dl = e.target.closest('[data-ndel]'); if (dl) delNoteItem(dl.dataset.ndel);
});
$('#npbar').addEventListener('click', e => {
  const t = e.target;
  if (t.id === 'rec') { commitNew(); toggleRec(); return; }
  const pl = t.closest('[data-play]'); if (pl) { playRec(pl.dataset.play); return; }
  const ad = t.closest('[data-adel]'); if (ad) delRec(ad.dataset.adel);
});

/* 輸出 PDF: a print sheet (bed, name, attending, to-do items, date); on the phone use Share / Print -> Save as PDF */
function exportPdf(only) {
  const idx = only != null && only >= 0 ? [only] : todoIdx();
  if (!idx.length) { toast('沒有待辦可輸出'); return; }
  commitNew();
  const sheet = $('#printdoc');
  sheet.innerHTML = `<h1>待辦事項 · ${esc(ymdLocal(Date.now()))}</h1>` + idx.map(i => { const p = P[i], its = noteItems(p.chart).filter(x => x.t);
    return `<section><div class="ph"><b>${esc(p.bed)}</b> ${esc(p.name)}<span>主治：${esc(p.vs || '–')}</span></div>${its.length ? `<ul>${its.map(x => `<li class="${x.done ? 'd' : ''}"><i>${x.done ? '☑' : '☐'}</i><span>${esc(x.t)}</span><small>${esc(ymdLocal(x.ts || Date.now()))}</small></li>`).join('')}</ul>` : '<p>（無待辦文字）</p>'}</section>`;
  }).join('');
  window.onafterprint = () => { sheet.innerHTML = ''; };
  setTimeout(() => { try { window.print(); } catch (e) { toast('此瀏覽器無法列印'); } }, 60);
}

/* recording: MediaRecorder; the blob is sealed before it is stored, and dropped when the session was locked meanwhile */
async function toggleRec() {
  if (REC) { try { REC.stop(); } catch (e) { /* ignore */ } return; }
  const p = P && P[NOTE_I];
  if (!p) return;
  if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia || typeof MediaRecorder === 'undefined') { toast('此瀏覽器不支援錄音'); return; }
  let stream;
  try { stream = await navigator.mediaDevices.getUserMedia({audio: true}); }
  catch (e) { toast('無法使用麥克風（請在設定允許）'); return; }
  const mime = ['audio/mp4', 'audio/webm;codecs=opus', 'audio/webm'].find(m => MediaRecorder.isTypeSupported(m)) || '';
  const session = SESSION, chart = p.chart;
  let rec;
  try { rec = new MediaRecorder(stream, mime ? {mimeType: mime} : {}); }
  catch (e) { stream.getTracks().forEach(t => t.stop()); toast('無法開始錄音'); return; }
  RECCHUNKS = []; RECT0 = Date.now(); REC = rec;
  rec.ondataavailable = e => { if (e.data && e.data.size) RECCHUNKS.push(e.data); };
  rec.onstop = () => {
    stream.getTracks().forEach(t => t.stop());
    const type = rec.mimeType || mime || 'audio/webm', chunks = RECCHUNKS, secs = Math.max(1, Math.round((Date.now() - RECT0) / 1000));
    REC = null; RECCHUNKS = [];
    if (NOTE_I >= 0) drawBar();
    if (session === SESSION && chunks.length) saveRecording(session, chart, new Blob(chunks, {type: type}), secs, type);
  };
  rec.start(1000);
  drawBar();
}
async function saveRecording(session, chart, blob, secs, type) {
  const k = checksKey();
  if (!k) return;
  const id = NOTE_ID();
  try {
    const bytes = new Uint8Array(await blob.arrayBuffer());
    const box = sealBytes(k.ikm, bytes, NOTE_INFO);
    bytes.fill(0);
    box.mode = k.mode; box.p = k.p; box.mime = type;
    if (session !== SESSION) return;                    // locked while encrypting: nothing is kept
    await saveBlob(box, 'audio:' + id);
    if (session !== SESSION) { try { await removeBlob('audio:' + id); } catch (e) { /* ignore */ } return; }
    putNote(chart, {audio: noteAudio(chart).concat([{id: id, ts: Date.now(), s: secs, mime: type}])});
  } catch (e) { toast('錄音儲存失敗'); return; }
  if (NOTE_I >= 0) drawBar();
}
async function playRec(id) {
  let box = null;
  try { box = await loadBlob('audio:' + id); } catch (e) { box = null; }
  const ikm = !box ? null : box.mode === 'x' ? (KEYS && own(KEYS, box.p) ? KEYS[box.p] : null) : KEK;
  const pt = openBytes(ikm, box, NOTE_INFO);
  if (!pt) { toast('無法開啟這段錄音'); return; }
  const url = URL.createObjectURL(new Blob([pt], {type: box.mime || 'audio/webm'}));
  pt.fill(0);
  if (AUDIO) AUDIO.pause();
  AUDIO = new Audio(url);
  AUDIO.onended = () => URL.revokeObjectURL(url);
  AUDIO.play().catch(() => toast('播放失敗'));
}
async function delRec(id) {
  if (!await ask('刪除這段錄音？')) return;
  const p = P && P[NOTE_I];
  if (!p) return;
  putNote(p.chart, {audio: noteAudio(p.chart).filter(a => a.id !== id)});
  try { await removeBlob('audio:' + id); } catch (e) { /* ignore */ }
  drawBar();
}

/* ================= boot ================= */
async function boot() {
  requestPersist();
  if ('serviceWorker' in navigator && !LOCAL) navigator.serviceWorker.register('sw.js').catch(() => {});
  try { REG = await loadReg(); } catch (e) { REG = null; }
  try { BLOB = await loadBlob(); } catch (e) { BLOB = null; NOTE = '無法讀取本機儲存'; }
  if (BLOB && BLOB.v !== 3) BLOB = null;                 // an old v2 blob from before the passkey update
  if (!REG || (REG.state !== 'pending' && REG.state !== 'ok')) { showSetup(); return; }
  if (REG.state === 'pending') { showPending(); return; }
  if (BLOB) { showLogin(); syncData(); return; }
  if (navigator.onLine === false) { showBoot('尚無資料，請連 4G 開啟以下載', true); return; }
  showBoot('下載資料中…');
  await syncData();
  if (BLOB) showLogin(); else showBoot('尚無資料，請連 4G 開啟以下載' + (NOTE ? '（' + NOTE + '）' : '') + (AUTH_BAD ? '。' + AUTH_MSG : ''), true);
}
boot();
