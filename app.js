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

const $ = s => document.querySelector(s);
const esc = s => String(s == null ? '' : s).replace(/[‪-‮⁦-⁩]/g, '')
  .replace(/[&<>"']/g, c => ({'&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'}[c]));
const num = v => { const n = Number(v); return v == null || v === '' || !Number.isFinite(n) ? '–' : String(n); };
const safeCol = c => /^#[0-9a-fA-F]{3,8}$/.test(String(c)) ? c : 'inherit';
const mk = (t, on) => on ? `<span class="mk">${esc(t)}</span>` : esc(t);
const pad = n => String(n).padStart(2, '0');
const fmtT = ms => { const d = new Date(Number(ms)); return `${pad(d.getUTCMonth()+1)}/${pad(d.getUTCDate())} ${pad(d.getUTCHours())}:${pad(d.getUTCMinutes())}`; };
const clip = (s, n) => String(s == null ? '' : s).slice(0, n || 20);
const own = (o, k) => !!o && typeof o === 'object' && Object.prototype.hasOwnProperty.call(o, k);
function hist(u) { try { history.replaceState(null, '', u || location.pathname + location.search); } catch (e) {} }

/* ================= rendering (from booklet_app.TEMPLATE) ================= */
let st = {zone: '內圍', chip: '全部', q: '', idx: [], cur: -1};
const CHIPS=[['全部',p=>true],['有異常',p=>p.vit.length||p.labs.some(l=>l.abn)],['病危',p=>p.crit],['Neutropenic fever',p=>p.nf],['新病人',p=>p.new],['DNR/末期',p=>p.dnr||p.end],['MO',p=>p.dept==='MO'],['HEMA',p=>p.dept==='HEMA']];
function abn(p){return p.vit.map(v=>v.t).concat(p.labs.filter(l=>l.abn).map(l=>l.l+' '+l.v)).concat(p.notes)}
function tags(p){let h='';
 if(p.crit)h+='<span class="badge">病危</span>';
 if(p.new)h+='<span class="badge new">新</span>';
 if(p.nf)h+='<span class="badge mk2">Neutropenic fever</span>';
 if(p.dnr)h+='<span class="badge mk2">DNR</span>';
 if(p.end)h+='<span class="badge mk2">末期</span>';
 return h}
function renderTop(){
 $('#zone').innerHTML=['內圍','外圍'].map(z=>`<button class="${st.zone===z?'on':''}" data-z="${z}">${z} ${P.filter(p=>p.zone===z).length}</button>`).join('');
 $('#chips').innerHTML=CHIPS.map(c=>`<button class="chip ${st.chip===c[0]?'on':''}" data-c="${esc(c[0])}">${esc(c[0])}</button>`).join('')}
function renderList(){
 const f=CHIPS.find(c=>c[0]===st.chip)[1], q=st.q.trim().toLowerCase();
 st.idx=P.map((p,i)=>i).filter(i=>{const p=P[i];return p.zone===st.zone&&f(p)&&(!q||(p.bed+p.chart+p.name+p.dept).toLowerCase().includes(q))});
 if(!st.idx.length){$('#cards').innerHTML='<div class="empty">沒有符合的病人</div>';return}
 let h='',last='';
 st.idx.forEach(i=>{const p=P[i];
  if(p.dept!==last){h+=`<div class="sec-h">${p.dept==='MO'?'腫瘤內科 MO':'血液腫瘤 HEMA'}</div>`;last=p.dept}
  const a=abn(p);
  h+=`<button class="card" data-i="${i}"><div class="r1"><span class="bed">${esc(p.bed)}</span><span class="id">${esc(p.chart)}</span><span>${esc(p.name)}</span>${tags(p)}</div>`+
     (a.length?`<div class="r2">${a.slice(0,4).map(x=>mk(x,true)).join(' · ')}${a.length>4?` <span class="sub">+${a.length-4}</span>`:''}</div>`:'')+`</button>`});
 $('#cards').innerHTML=h}
function chartSVG(p){
 const W=340,H=176,L=26,R=334,tT=18,tB=60,bT=68,bB=H-16,N=Number(D.now),t0=N-72*3600e3,sp=72*3600e3;
 const X=t=>L+(Number(t)-t0)/sp*(R-L), Yt=v=>tB-(Math.min(Math.max(Number(v),35),41)-35)/6*(tB-tT), Yb=v=>bB-(Math.min(Math.max(Number(v),0),180)-0)/180*(bB-bT);
 let s=`<svg id="ch" viewBox="0 0 ${W} ${H}" xmlns="http://www.w3.org/2000/svg" font-size="7.5" font-family="inherit">`;
 s+=`<rect x="${L}" y="${Yb(120)}" width="${R-L}" height="${Yb(80)-Yb(120)}" fill="#66bb6a" fill-opacity=".3"/>`;   // normal BP band 80-120 mmHg (light green, 30%)
 s+=`<rect x="${L}" y="${tT}" width="${R-L}" height="${tB-tT}" fill="none" stroke="var(--grid)"/><rect x="${L}" y="${bT}" width="${R-L}" height="${bB-bT}" fill="none" stroke="var(--grid)"/>`;
 const d0=new Date(t0);d0.setUTCHours(0,0,0,0);
 for(let t=d0.getTime();t<=N;t+=43200e3){if(t<t0)continue;const x=X(t),mid=new Date(t).getUTCHours()===0;
  s+=`<line x1="${x}" x2="${x}" y1="${tT}" y2="${bB}" stroke="var(--grid)" stroke-width="${mid?.7:.3}"/><text x="${x}" y="${H-4}" text-anchor="middle" fill="var(--sub)">${mid?pad(new Date(t).getUTCMonth()+1)+'/'+pad(new Date(t).getUTCDate()):'12h'}</text>`}
 [36,38,40].forEach(v=>s+=`<text x="${L-3}" y="${Yt(v)+2.5}" text-anchor="end" fill="var(--sub)">${v}</text>`);
 [50,100,150].forEach(v=>s+=`<text x="${L-3}" y="${Yb(v)+2.5}" text-anchor="end" fill="var(--sub)">${v}</text>`);
 const dash=(y)=>`<line x1="${L}" x2="${R}" y1="${y}" y2="${y}" stroke="var(--sub)" stroke-width=".5" stroke-dasharray="3 2"/>`;
 s+=dash(Yt(37.7))+dash(Yb(90))+dash(Yb(120));
 const line=(i,Y,col,r)=>{const pts=p.ser.filter(r=>r[i]!=null).map(r=>[X(r[0]),Y(r[i])]);
  if(pts.length>1)s+=`<polyline points="${pts.map(q=>q.join(',')).join(' ')}" fill="none" stroke="${col}" stroke-width="1.4"/>`;
  pts.forEach(q=>s+=`<circle cx="${q[0]}" cy="${q[1]}" r="${r}" fill="${col}"/>`)};
 p.ser.forEach(r=>{if(r[4]!=null&&r[5]!=null)s+=`<line x1="${X(r[0])}" x2="${X(r[0])}" y1="${Yb(r[4])}" y2="${Yb(r[5])}" stroke="var(--ink)" stroke-width="2.2"/>`});
 line(1,Yt,'var(--tp)',2.2);line(2,Yb,'var(--hr)',2);line(3,Yb,'var(--rr)',1.8);
 s+=`<line id="cur" x1="0" x2="0" y1="${tT}" y2="${bB}" stroke="var(--acc)" stroke-width="1" style="display:none"/>`;
 if(!p.ser.length)s+=`<text x="${(L+R)/2}" y="${(bT+bB)/2}" text-anchor="middle" fill="var(--sub)" font-size="10">72h 無生命徵象</text>`;
 s+=`</svg><div id="read" class="sub">點圖表看數值</div><div class="leg"><i style="color:var(--tp)">TP</i> °C(上)　<i style="color:var(--hr)">HR</i>　<i style="color:var(--rr)">RR</i>　<i>BP</i> 直條 = 舒張壓~收縮壓(下)　虛線: 37.7 / 90 / 120　<i style="color:#43a047">綠帶</i> 正常血壓 80~120</div>`;
 return s}
function bindChart(p){
 const svg=$('#ch');if(!svg||!p.ser.length)return;
 const N=Number(D.now),t0=N-72*3600e3,L=26,R=334;
 const show=ev=>{const r=svg.getBoundingClientRect(),cx=(ev.touches?ev.touches[0].clientX:ev.clientX);
  const vx=(cx-r.left)/r.width*340,t=t0+(vx-L)/(R-L)*72*3600e3;
  let best=p.ser[0];p.ser.forEach(q=>{if(Math.abs(q[0]-t)<Math.abs(best[0]-t))best=q});
  const x=L+(Number(best[0])-t0)/(72*3600e3)*(R-L),c=$('#cur');c.setAttribute('x1',x);c.setAttribute('x2',x);c.style.display='';
  $('#read').innerHTML=`<b>${esc(fmtT(best[0]))}</b>　TP ${num(best[1])}　HR ${num(best[2])}　RR ${num(best[3])}　BP ${best[4]!=null?num(best[4])+'/'+num(best[5]):'–'}　SpO₂ ${num(best[6])}`};
 svg.addEventListener('click',show);svg.addEventListener('touchmove',show,{passive:true})}
function box(title,inner,open){return inner?`<details class="box" ${open?'open':''}><summary>${title}</summary>${inner}</details>`:''}
function renderDetail(i){
 const p=P[i];st.cur=st.idx.indexOf(i);hist('#p'+i);
 $('#dt').textContent=`${st.cur+1} / ${st.idx.length}`;
 let h=`<div class="hd"><span class="bed">${esc(p.bed)}</span><span class="nm">${esc(p.name)}</span></div>
 <div class="meta">${esc(p.chart)} · ${esc(p.dept)}${p.vs?' · 主治 '+esc(p.vs):''}${p.adm?' · 入院 '+esc(p.adm):''}</div><div class="tags">${tags(p)}</div>`;
 h+=`<div class="box"><h3>生命徵象（3天）</h3>${chartSVG(p)}${p.vit.length?`<div class="row" style="margin-top:6px">${p.vit.map(v=>mk(v.t,true)+` <span class="sub">${esc(v.w)}</span>`).join(' · ')}</div>`:''}</div>`;
 const grid=(names,c4)=>{const L=p.labs.filter(l=>names.includes(l.l));return L.length?`<div class="labs${c4?' c4':''}">${L.map(l=>`<div class="lab">${esc(l.l)}${l.d?' <small>'+esc(l.d)+'</small>':''}<b class="${l.abn?'mk':''}">${esc(l.v)}</b></div>`).join('')}</div>`:''};
 const sec=(t,b)=>b?`<div class="sub2">${t}</div>${b}`:'';
 const mi=Object.entries(p.micro).map(([k,rows])=>`<div class="row k">${esc(k)}</div><div class="mg">${rows.map(r=>`<span class="st">${r.pos?mk(r.t,true):esc(r.t)}</span><span>${esc(r.i)}${Number(r.n)>1?' ×'+Number(r.n):''}</span>`).join('')}</div>`).join('')+(p.fw?`<div class="row">${mk('Fever work-up?',true)}</div>`:'');
 h+=box('檢驗（7天內最新）',sec('Hemogram',grid(['WBC','ANC','Hb','PLT'],true))
  +sec('Basic chems',grid(['Cre','BUN','ALT','T-bil','INR','Na','K','Ca','LDH'],false)+(p.notes.length?`<div class="row">${p.notes.map(n=>mk(n,true)).join(' · ')}</div>`:''))
  +sec('Culture report（7天）',mi),true);
 h+=box('今日檢驗 / 影像',p.today.map(t=>`<div class="row">${esc(t)}</div>`).join(''),true);
 h+=box('目前處方（Active）',(p.meds.length||p.others.length)?`<ul class="ml">${p.meds.map(m=>`<li class="med"><span class="c" style="color:${safeCol(m.col)}">[${esc(m.c)}]</span> ${esc(m.n)}${m.d?' D'+esc(m.d):''}</li>`).join('')}${p.others.map(o=>`<li class="sub">${esc(o)}</li>`).join('')}</ul>`:'',false);
 h+=box('交班與交代事項',p.memo?`<div class="memo">${esc(p.memo)}</div>`:'',false);
 h+=box('護理紀錄（最新）'+(p.nurs?' · '+esc(p.nurs.w):''),p.nurs?`<div class="memo">${esc(p.nurs.t)}</div>`:'',false);
 $('#db').innerHTML=h;bindChart(p);
 $('#detail').style.display='block';$('#detail').scrollTop=0;document.body.style.overflow='hidden'}
function go(d){const n=st.cur+d;if(n<0||n>=st.idx.length)return;renderDetail(st.idx[n])}
function closeDetail(){$('#detail').style.display='none';document.body.style.overflow='';hist('');
 if(PENDING){const d=PENDING;PENDING=null;applyData(d);return}   // pwa: newer data arrived while reading a patient
 const el=document.querySelector(`.card[data-i="${st.idx[st.cur]}"]`);if(el)el.scrollIntoView({block:'center'})}
document.addEventListener('click',e=>{
 if(!P)return;
 const z=e.target.closest('[data-z]');if(z){st.zone=z.dataset.z;renderTop();renderList();return}
 const c=e.target.closest('[data-c]');if(c){st.chip=c.dataset.c;renderTop();renderList();return}
 const k=e.target.closest('.card');if(k){renderDetail(+k.dataset.i)}});
$('#q').addEventListener('input',e=>{if(!P)return;st.q=e.target.value;renderList()});
$('#back').onclick=closeDetail;$('#prev').onclick=()=>go(-1);$('#next').onclick=()=>go(1);
window.addEventListener('keydown',e=>{if($('#detail').style.display!=='block')return;if(e.key==='ArrowLeft')go(-1);if(e.key==='ArrowRight')go(1);if(e.key==='Escape')closeDetail()});
let sx=0,sy=0;
$('#detail').addEventListener('touchstart',e=>{sx=e.touches[0].clientX;sy=e.touches[0].clientY},{passive:true});
$('#detail').addEventListener('touchend',e=>{if(e.target.closest('svg'))return;const dx=e.changedTouches[0].clientX-sx,dy=e.changedTouches[0].clientY-sy;
 if(Math.abs(dx)>70&&Math.abs(dx)>Math.abs(dy)*2)go(dx<0?1:-1)},{passive:true});

/* ================= screens ================= */
function show(id) {
  ['#boot', '#setup', '#pending', '#login', '#list'].forEach(s => { $(s).style.display = s === id ? '' : 'none'; });
  $('#foot').style.display = id === '#list' ? 'none' : '';
  if (id !== '#pending') stopGrantPoll();
}
function showBoot(text) { $('#boot').textContent = text; show('#boot'); }
function showSetup(text) {
  show('#setup');
  $('#sb').disabled = false; $('#pb').disabled = false;
  $('#sx').style.display = 'none'; $('#sx').onclick = null;
  $('#sm').textContent = text || '';
}
function showLogin(text) {
  show('#login');
  const x = REG && REG.mode === 'x';
  $('#lx').style.display = x ? '' : 'none';
  $('#lf').style.display = x ? 'none' : '';
  $('#fx').disabled = false; $('#lb').disabled = false;
  $('#lm').textContent = text || '';
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
  const s = STATUS, out = [`<span>電腦 ${esc(clip(s.at))} ${s.ok ? '正常' : '異常'}${s.msg ? '：' + esc(clip(s.msg, 80)) : ''}</span>`];
  const age = statusAgeH();
  if (age != null && age >= STALE_H) out.push(`<span class="note">電腦已超過 ${Math.floor(age)} 小時未回報，可能未開機或程式已關閉</span>`);
  if (s.hol_warn === true) out.push(`<span class="note">假日檔讀取失敗，只依週六日執行</span>`);
  return out;
}
/* err:"auth" = the server read the access list and this key is not on it (definite rejection) */
const AUTH_MSG = '存取碼已被拒（可能已被停用）。本機資料仍可登入；請先聯絡管理者確認，確定需重新登記時再按「清除本機資料」';
/* err:"unavailable" = the server could not read its access list (transient): never suggest clearing local data */
const UNAVAIL_MSG = '伺服器暫時無法使用，請稍後再試（本機資料仍可登入）';
function renderSys() {
  const parts = [];
  if (BLOB && BLOB.stamp) parts.push(`<span>資料 ${esc(clip(BLOB.stamp))}${BLOB.count != null ? '（' + num(BLOB.count) + '人）' : ''}</span>`);
  const stp = statusParts();
  parts.push(...stp);
  if (AUTH_BAD) parts.push(`<span class="note">${esc(AUTH_MSG)}</span>`);
  if (NOTE) parts.push(`<span class="note">${esc(NOTE)}</span>`);
  $('#lsys').innerHTML = parts.join('');
  if (!D) return;
  const lp = [...stp];
  if (isDutyDay()) lp.push(`<button id="rq">請更新</button>`);
  else if (STATUS) lp.push(`<span>非值班日（平日不自動更新）</span>`);
  if (REQ_MSG) lp.push(`<span class="note">${esc(REQ_MSG)}</span>`);
  if (AUTH_BAD) lp.push(`<span class="note">${esc(AUTH_MSG)}</span>`);
  if (NOTE) lp.push(`<span class="note">${esc(NOTE)}</span>`);
  $('#sys').innerHTML = lp.join('');
  const b = $('#rq'); if (b) b.onclick = requestRefresh;
}
function showBanner(text) { const b = $('#banner'); b.textContent = text; b.style.display = text ? '' : 'none'; }
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
  if (why === 'stamp') {
    NOTE = `收到的資料時間異常（${clip(j.stamp)}），未取代本機資料`;
    renderSys(); return false;
  }
  if (why === 'bad') {
    NOTE = `雲端資料（${clip(j.stamp)}）內外時間不一致，已拒收，等待電腦下一次更新`;
    renderSys(); return false;
  }
  NOTE = '';
  if (why === 'old') { renderSys(); return false; }
  if (D) {
    const d = await openNewer(j);
    if (!d) { showBanner(`有新版資料（${clip(j.stamp)}），登出後重新登入以查看`); renderSys(); return false; }
    await keepBlob(j, true);
    if ($('#detail').style.display === 'block') { PENDING = d; showBanner(`已下載新資料（${clip(d.stamp)}），返回清單即更新`); }
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

/* swap in newer decrypted data, keeping zone / chip / search */
function applyData(d) {
  D = d; P = D.p; PENDING = null;
  st.idx = []; st.cur = -1;
  $('#stamp').textContent = D.stamp;
  showBanner('');
  REQ_MSG = `已載入新資料（${clip(D.stamp)}）`;
  stopPoll();
  renderTop(); renderList(); renderSys();
}

async function refreshStatus() {
  if (!REG || REG.state !== 'ok') return;
  try {
    const s = await getJSON(statusUrl());
    if (s && s.ok === false && s.err === 'auth') authFailed();
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
    if (!D || Date.now() > until) { stopPoll(); return; }
    if (busy) return;
    busy = true;
    try { if (await syncData()) stopPoll(); } finally { busy = false; }
  }, POLL_MS);
}

function reqAcct() { return REG.mode === 'pw' ? accountId(USER) : REG.acct; }

async function requestRefresh() {
  if (!AUTH || !REG) { REQ_MSG = '無法送出（缺少簽章金鑰，請重新登記）'; renderSys(); return; }
  const b = $('#rq'); if (b) b.disabled = true;
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
  $('#pcode').textContent = REG.code;
  $('#pacct').textContent = `帳號雜湊前 6 碼 ${REG.acct.slice(0, 6)}，期別 ${REG.enrollP}`;
  $('#pfin').style.display = REG.grant ? '' : 'none';
  $('#pfin').disabled = false; $('#pchk').disabled = false;
  $('#pm').textContent = text || (REG.grant ? '已核可，請按「完成啟用」以 Face ID 確認' : '尚未核可（每 60 秒自動檢查）');
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
    $('#pm').textContent = `尚未核可（${pad(t.getHours())}:${pad(t.getMinutes())} 已檢查，每 60 秒自動檢查）`;
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
    if (BLOB) showLogin('啟用完成'); else showBoot('啟用完成。電腦下次更新資料後即可登入' + (NOTE ? '（' + NOTE + '）' : ''));
  } catch (e) {
    showPending('無法完成：' + prfErr(e));
  } finally {
    if (r && r.first) r.first.fill(0);
  }
}
async function cancelEnroll() {
  if (!confirm('取消這次登記？')) return;
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
  startPw(d, user, r.kek, j);
}

/* ================= login / lock ================= */
function startPw(d, user, kek, blob) {
  const e = blob.k[accountId(user)];
  KEK = kek; USER = user; LOGIN_KEY = e.s + '|' + e.it; AUTH = authFromKek(kek);
  start(d);
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
  startPw(d, user, r.kek, BLOB);
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
  showBoot(`資料（${clip(bad)}）內外時間不一致，已拒收；等待電腦下一次更新`);
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
  $('#fx').disabled = true; msg.textContent = 'Face ID…';
  let r;
  try { r = await passkeyGet(REG.credId, prfSalt(e.p), cur !== e.p ? prfSalt(cur) : null); }
  catch (err) { msg.textContent = '無法使用 Face ID：' + prfErr(err); $('#fx').disabled = false; return; }
  const wipe = () => { r.first.fill(0); if (r.second) r.second.fill(0); };
  const pt = await decryptV3X(BLOB, REG.acct, r.first);
  if (!pt) { wipe(); msg.textContent = 'Face ID 金鑰無法開啟資料（請確認使用登記時的 passkey）'; $('#fx').disabled = false; return; }
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
  start(d);
  if (rotate) sendRotate(cur, KEYS[cur].slice(), AUTH ? AUTH.slice() : null);
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
  } catch (e) { /* retried at the next login */ }
  finally { priv.fill(0); if (auth) auth.fill(0); }
}

function start(d) {
  D = d; P = D.p;
  st = {zone: '內圍', chip: '全部', q: '', idx: [], cur: -1};
  $('#q').value = '';
  $('#stamp').textContent = D.stamp;
  showBanner('');
  REQ_MSG = '';
  show('#list');
  renderTop(); renderList(); renderSys();
  bump();
}

/* Wipe plaintext and keys from memory and the DOM, back to the login screen (no reload: the blob stays). */
function lock() {
  clearTimeout(idleT);
  stopPoll();
  if (KEYS) Object.keys(KEYS).forEach(k => KEYS[k].fill(0));
  if (KEK) KEK.fill(0);
  if (AUTH) AUTH.fill(0);
  KEYS = null; KEK = null; AUTH = null; USER = null; LOGIN_KEY = null; D = null; P = null; PENDING = null;
  st = {zone: '內圍', chip: '全部', q: '', idx: [], cur: -1};
  $('#cards').innerHTML = ''; $('#db').innerHTML = ''; $('#zone').innerHTML = ''; $('#chips').innerHTML = '';
  $('#sys').innerHTML = ''; $('#stamp').textContent = ''; $('#q').value = ''; $('#lp').value = ''; $('#lu').value = '';
  showBanner(''); REQ_MSG = '';
  $('#detail').style.display = 'none'; document.body.style.overflow = ''; hist('');
  if (!REG || REG.state !== 'ok') return;
  if (BLOB) showLogin(); else showBoot('尚無資料，請連 4G 開啟以下載');
}

async function clearLocal() {
  if (!confirm('清除這支手機上的所有值班資料（登記、存取碼、已下載資料）？之後需要重新登記。')) return;
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
$('#lo').onclick = lock;

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
  if (navigator.onLine === false) { showBoot('尚無資料，請連 4G 開啟以下載'); return; }
  showBoot('下載資料中…');
  await syncData();
  if (BLOB) showLogin(); else showBoot('尚無資料，請連 4G 開啟以下載' + (NOTE ? '（' + NOTE + '）' : '') + (AUTH_BAD ? '。' + AUTH_MSG : ''));
}
boot();
