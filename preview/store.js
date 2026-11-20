/* 值班手冊 PWA - keeps the encrypted payload in IndexedDB (db "oncall", store "blob") so it survives app switching.
 * Stored: the encrypted blob (+ its plaintext stamp/count) under "current", and the registration under "reg"
 * ({state, mode, acct, access key, sealed grant box, ...}); never plaintext patient data, PRF keys or the auth key.
 * Exposes: saveBlob(obj[, key]) loadBlob([key]) -> obj|null  removeBlob([key])  saveReg loadReg  clearAll()
 *          requestPersist()  stampNewer(a, b)  stampOk(stamp, now) */
(function (G) {
  'use strict';
  const DB = 'oncall', STORE = 'blob', KEY = 'current';
  let dbp = null;

  function open() {
    if (dbp) return dbp;
    dbp = new Promise((resolve, reject) => {
      if (!G.indexedDB) { reject(new Error('IndexedDB unavailable')); return; }
      const rq = indexedDB.open(DB, 1);
      rq.onupgradeneeded = () => { if (!rq.result.objectStoreNames.contains(STORE)) rq.result.createObjectStore(STORE); };
      rq.onsuccess = () => resolve(rq.result);
      rq.onerror = () => reject(rq.error);
      rq.onblocked = () => reject(new Error('IndexedDB blocked'));
    });
    dbp.catch(() => { dbp = null; });   // allow a retry later
    return dbp;
  }

  async function tx(mode, fn) {
    const db = await open();
    return new Promise((resolve, reject) => {
      const t = db.transaction(STORE, mode), st = t.objectStore(STORE);
      const rq = fn(st);
      t.oncomplete = () => resolve(rq ? rq.result : undefined);
      t.onerror = () => reject(t.error);
      t.onabort = () => reject(t.error || new Error('transaction aborted'));
    });
  }

  const saveBlob = (obj, key) => tx('readwrite', st => st.put(obj, key || KEY)).then(() => undefined);
  const loadBlob = (key) => tx('readonly', st => st.get(key || KEY)).then(v => (v === undefined ? null : v));
  const removeBlob = (key) => tx('readwrite', st => st.delete(key || KEY)).then(() => undefined);

  const saveReg = obj => saveBlob(obj, 'reg');
  const loadReg = () => loadBlob('reg');

  /* 「清除本機資料」: drop the whole IndexedDB database and every Cache Storage entry (shell cache included). */
  async function clearAll() {
    try { if (dbp) (await dbp).close(); } catch (e) { /* ignore */ }
    dbp = null;
    await new Promise(resolve => {
      try {
        const rq = indexedDB.deleteDatabase(DB);
        rq.onsuccess = rq.onerror = rq.onblocked = () => resolve();
      } catch (e) { resolve(); }
    });
    try { if (G.caches) await Promise.all((await caches.keys()).map(k => caches.delete(k))); } catch (e) { /* ignore */ }
  }

  async function requestPersist() {
    try { if (navigator.storage && navigator.storage.persist) return await navigator.storage.persist(); } catch (e) { /* ignore */ }
    return false;
  }

  /* true when stamp a ("YYYY-MM-DD HH:MM") is strictly newer than b; the stored blob is replaced only then. */
  const stampNewer = (a, b) => typeof a === 'string' && a !== '' && a > String(b || '');

  /* stamp guard: a well-formed, real "YYYY-MM-DD HH:MM" (phone local time) no more than 1 day ahead of now.
   * A far-future stamp would otherwise freeze the phone on that blob (nothing could ever be "newer"). */
  const STAMP_RE = /^(\d{4})-(\d{2})-(\d{2}) (\d{2}):(\d{2})$/, STAMP_AHEAD_MS = 24 * 3600e3;
  function stampOk(stamp, now) {
    const m = typeof stamp === 'string' && STAMP_RE.exec(stamp);
    if (!m) return false;
    const [y, mo, d, h, mi] = m.slice(1).map(Number);
    const t = new Date(y, mo - 1, d, h, mi);
    if (t.getFullYear() !== y || t.getMonth() !== mo - 1 || t.getDate() !== d || t.getHours() !== h || t.getMinutes() !== mi) return false;
    const n = now instanceof Date ? now.getTime() : Number(now == null ? Date.now() : now);
    return Number.isFinite(n) && t.getTime() <= n + STAMP_AHEAD_MS;
  }

  /* May a downloaded blob with stamp s replace the stored one (stamp stored)? -> '' when yes, else the reason:
   * 'stamp' malformed / future, 'bad' the stamp a login already found inconsistent (inner != outer), 'old' not newer. */
  function blobReplace(s, stored, badStamp, now) {
    if (!stampOk(s, now)) return 'stamp';
    if (badStamp && s === badStamp) return 'bad';
    if (stored && !stampNewer(s, stored)) return 'old';
    return '';
  }

  const has = (o, k) => !!o && typeof o === 'object' && Object.prototype.hasOwnProperty.call(o, k);
  /* grants {period: sealed box}: the periods to try, in the order given (entry period first), that have a grant */
  const grantOrder = (grants, periods) => periods.filter((p, i) => has(grants, p) && periods.indexOf(p) === i);
  /* once a blob wrapped for the current period has opened, grants of older periods are no longer needed */
  const pruneGrants = (grants, opened, cur) => {
    if (opened !== cur || !has(grants, cur)) return grants;
    const out = {}; out[cur] = grants[cur]; return out;
  };

  Object.assign(G, {saveBlob, loadBlob, removeBlob, saveReg, loadReg, clearAll, requestPersist, stampNewer, stampOk,
                    blobReplace, grantOrder, pruneGrants});
})(self);
