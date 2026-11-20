/* 值班手冊 PWA - payload v3 decryption (mirrors x25519.py seal/open_sealed and booklet_crypto *_v3 byte for byte).
 * Pure-JS SHA-256 / HMAC / PBKDF2 / ChaCha20 / HKDF (ported from booklet_app.TEMPLATE); WebCrypto for X25519 and PBKDF2.
 * The old v2 (password-only) paths were removed: the relay writes v3 only.
 * No secrets live in this file. Exposes window.OC (and the same names as globals, classic script). */
(function (G) {
  'use strict';
  const b64d = s => { const b = atob(s), u = new Uint8Array(b.length); for (let i = 0; i < b.length; i++) u[i] = b.charCodeAt(i); return u; };
  const b64e = u => { let s = ''; for (let i = 0; i < u.length; i++) s += String.fromCharCode(u[i]); return btoa(s); };
  const utf8 = s => new TextEncoder().encode(s);
  const hex = u => Array.from(u, b => b.toString(16).padStart(2, '0')).join('');
  const cat = (...a) => { const o = new Uint8Array(a.reduce((n, x) => n + x.length, 0)); let p = 0; a.forEach(x => { o.set(x, p); p += x.length; }); return o; };
  const eq = (a, b) => { if (a.length !== b.length) return false; let d = 0; for (let i = 0; i < a.length; i++) d |= a[i] ^ b[i]; return d === 0; };
  const norm = user => String(user).trim().toLowerCase();   // accounts are case-insensitive (Python: user.strip().lower())

  const K256 = new Uint32Array([0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2]);
  const IV = [0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19];
  const W = new Uint32Array(64);
  function comp(h, blk, o) {
    for (let i = 0; i < 16; i++) W[i] = blk[o + i];
    for (let i = 16; i < 64; i++) { const a = W[i-15], b = W[i-2]; W[i] = (W[i-16] + (((a>>>7)|(a<<25)) ^ ((a>>>18)|(a<<14)) ^ (a>>>3)) + W[i-7] + (((b>>>17)|(b<<15)) ^ ((b>>>19)|(b<<13)) ^ (b>>>10))) | 0; }
    let a = h[0], b = h[1], c = h[2], d = h[3], e = h[4], f = h[5], g = h[6], hh = h[7];
    for (let i = 0; i < 64; i++) {
      const t1 = (hh + (((e>>>6)|(e<<26)) ^ ((e>>>11)|(e<<21)) ^ ((e>>>25)|(e<<7))) + ((e&f) ^ (~e&g)) + K256[i] + W[i]) | 0;
      const t2 = ((((a>>>2)|(a<<30)) ^ ((a>>>13)|(a<<19)) ^ ((a>>>22)|(a<<10))) + ((a&b) ^ (a&c) ^ (b&c))) | 0;
      hh = g; g = f; f = e; e = (d + t1) | 0; d = c; c = b; b = a; a = (t1 + t2) | 0;
    }
    h[0] += a; h[1] += b; h[2] += c; h[3] += d; h[4] += e; h[5] += f; h[6] += g; h[7] += hh;
  }
  function sha256(m) {
    const l = m.length, n = ((l + 9 + 63) >> 6) * 16, buf = new Uint8Array(n * 4); buf.set(m); buf[l] = 0x80;
    const dv = new DataView(buf.buffer), w = new Uint32Array(n); for (let i = 0; i < n; i++) w[i] = dv.getUint32(i * 4);
    w[n-2] = Math.floor(l / 0x20000000); w[n-1] = (l << 3) >>> 0;
    const h = new Uint32Array(IV); for (let o = 0; o < n; o += 16) comp(h, w, o);
    const out = new Uint8Array(32), d2 = new DataView(out.buffer); for (let i = 0; i < 8; i++) d2.setUint32(i * 4, h[i]); return out;
  }
  function hmac(key, msg) {
    const k = new Uint8Array(64); k.set(key.length > 64 ? sha256(key) : key);
    const i = new Uint8Array(64 + msg.length), o = new Uint8Array(96);
    for (let x = 0; x < 64; x++) { i[x] = k[x] ^ 0x36; o[x] = k[x] ^ 0x5c; }
    i.set(msg, 64); o.set(sha256(i), 64); return sha256(o);
  }
  function pbkdf2(pw, salt, it, dk) {
    const k = new Uint8Array(64); k.set(pw.length > 64 ? sha256(pw) : pw);
    const ip = new Uint8Array(64), op = new Uint8Array(64); for (let x = 0; x < 64; x++) { ip[x] = k[x] ^ 0x36; op[x] = k[x] ^ 0x5c; }
    const be = u => { const w = new Uint32Array(16), dv = new DataView(u.buffer); for (let i = 0; i < 16; i++) w[i] = dv.getUint32(i * 4); return w; };
    const hi = new Uint32Array(IV), ho = new Uint32Array(IV); comp(hi, be(ip), 0); comp(ho, be(op), 0);
    const out = new Uint8Array(dk), bw = new Uint32Array(16), hs = new Uint32Array(8);
    for (let blk = 1, pos = 0; pos < dk; blk++) {
      const sm = new Uint8Array(salt.length + 4); sm.set(salt); new DataView(sm.buffer).setUint32(salt.length, blk);
      const u1 = hmac(pw, sm), dv = new DataView(u1.buffer), uw = new Uint32Array(8); for (let i = 0; i < 8; i++) uw[i] = dv.getUint32(i * 4);
      const acc = Uint32Array.from(uw);
      for (let n = 1; n < it; n++) {
        bw.fill(0); bw.set(uw); bw[8] = 0x80000000; bw[15] = 768; hs.set(hi); comp(hs, bw, 0);
        bw.fill(0); bw.set(hs); bw[8] = 0x80000000; bw[15] = 768; uw.set(ho); comp(uw, bw, 0);
        for (let i = 0; i < 8; i++) acc[i] ^= uw[i];
      }
      const o = new Uint8Array(32), d2 = new DataView(o.buffer); for (let i = 0; i < 8; i++) d2.setUint32(i * 4, acc[i]);
      out.set(o.subarray(0, Math.min(32, dk - pos)), pos); pos += 32;
    }
    return out;
  }
  /* ChaCha20 (RFC 8439), block counter starts at 1 like booklet_crypto.chacha20_xor. */
  function chacha(key, nonce, data) {
    const out = new Uint8Array(data.length), st = new Uint32Array(16), x = new Uint32Array(16);
    st.set([0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]);
    const kd = new DataView(key.buffer, key.byteOffset, 32), nd = new DataView(nonce.buffer, nonce.byteOffset, 12);
    for (let i = 0; i < 8; i++) st[4 + i] = kd.getUint32(i * 4, true); st[12] = 1; for (let i = 0; i < 3; i++) st[13 + i] = nd.getUint32(i * 4, true);
    const rl = (v, n) => (v << n) | (v >>> (32 - n));
    const qr = (a, b, c, d) => { x[a] += x[b]; x[d] = rl(x[d] ^ x[a], 16); x[c] += x[d]; x[b] = rl(x[b] ^ x[c], 12); x[a] += x[b]; x[d] = rl(x[d] ^ x[a], 8); x[c] += x[d]; x[b] = rl(x[b] ^ x[c], 7); };
    for (let off = 0; off < data.length; off += 64) {
      x.set(st);
      for (let r = 0; r < 10; r++) { qr(0,4,8,12); qr(1,5,9,13); qr(2,6,10,14); qr(3,7,11,15); qr(0,5,10,15); qr(1,6,11,12); qr(2,7,8,13); qr(3,4,9,14); }
      for (let i = 0; i < 64 && off + i < data.length; i++) { const w = x[i >> 2] + st[i >> 2]; out[off + i] = data[off + i] ^ ((w >>> ((i & 3) * 8)) & 255); }
      st[12]++;
    }
    return out;
  }

  /* kek64 = PBKDF2-SHA256(norm(user) + "\0" + password, salt, it, 64 bytes)  == booklet_crypto.user_kek */
  async function deriveKek(user, pw, salt, it) {
    const pwb = utf8(norm(user) + '\x00' + pw);
    if (G.crypto && G.crypto.subtle) {
      try {
        const k = await crypto.subtle.importKey('raw', pwb, 'PBKDF2', false, ['deriveBits']);
        return new Uint8Array(await crypto.subtle.deriveBits({name: 'PBKDF2', hash: 'SHA-256', salt: salt, iterations: it}, k, 512));
      } catch (e) { /* fall through to pure JS */ }
    }
    await new Promise(r => setTimeout(r, 30));   // let the "驗證中…" message paint before the slow pure-JS loop
    return pbkdf2(pwb, salt, it, 64);
  }

  function accountId(user) { return hex(sha256(utf8('oncall-acct\x00' + norm(user)))).slice(0, 16); }

  const entry = (blob, acct) => blob && blob.k && Object.prototype.hasOwnProperty.call(blob.k, acct) ? blob.k[acct] : null;

  /* ================= payload v3 (mirrors x25519.py seal/open_sealed + booklet_crypto *_v3) ================= */
  const WRAP_INFO = utf8('oncall-wrap-v3'), GRANT_INFO = utf8('oncall-grant-v3');
  const ITERATIONS_PW = 600000, MAX_IT = 2 * ITERATIONS_PW;   // a blob asking for more is rejected (no DoS hang)
  const ACCESS_LEN = 16, AUTH_LEN = 32;
  const PKCS8_X25519 = new Uint8Array([0x30,0x2e,0x02,0x01,0x00,0x30,0x05,0x06,0x03,0x2b,0x65,0x6e,0x04,0x22,0x04,0x20]);
  const X = {name: 'X25519'};
  const b64ud = s => b64d(String(s).replace(/-/g, '+').replace(/_/g, '/') + '==='.slice((String(s).length + 3) % 4));
  const b64ue = u => b64e(u).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
  const bytesOf = v => typeof v === 'string' ? utf8(v) : v;
  const pad2 = n => String(n).padStart(2, '0');

  /* HKDF-SHA256 (RFC 5869) == x25519.hkdf_sha256 */
  function hkdf(ikm, salt, info, len) {
    const prk = hmac(salt && salt.length ? salt : new Uint8Array(32), ikm);
    let out = new Uint8Array(0), t = new Uint8Array(0);
    for (let i = 1; out.length < len; i++) { t = hmac(prk, cat(t, info, new Uint8Array([i]))); out = cat(out, t); }
    prk.fill(0);
    return out.slice(0, len);
  }

  /* WebCrypto X25519: the 32 raw bytes go in as PKCS#8 (RFC 8410); the scalar is clamped by WebCrypto like RFC 7748. */
  const importPriv = priv => crypto.subtle.importKey('pkcs8', cat(PKCS8_X25519, priv), X, true, ['deriveBits']);
  async function x25519Pub(priv) {
    if (!priv || priv.length !== 32) throw new Error('x25519 key must be 32 bytes');
    const jwk = await crypto.subtle.exportKey('jwk', await importPriv(priv));
    const pub = b64ud(jwk.x);
    if (pub.length !== 32) throw new Error('bad X25519 public key');
    return pub;
  }
  async function x25519Shared(priv, pub) {
    const pk = await crypto.subtle.importKey('raw', pub, X, false, []);
    const sh = new Uint8Array(await crypto.subtle.deriveBits({name: 'X25519', public: pk}, await importPriv(priv), 256));
    if (sh.every(b => b === 0)) throw new Error('low-order public key');
    return sh;
  }

  /* box {e, n, c, m} (standard base64) -> plaintext Uint8Array, or null on wrong key / wrong info / tampering / malformed. */
  async function openSealed(priv, box, info) {
    try {
      if (!box || typeof box !== 'object') return null;
      const E = b64d(box.e), n = b64d(box.n), c = b64d(box.c), m = b64d(box.m);
      if (E.length !== 32 || n.length !== 12) return null;
      const P = await x25519Pub(priv);
      const sh = await x25519Shared(priv, E);
      const okm = hkdf(sh, cat(E, P), bytesOf(info), 64);
      sh.fill(0);
      if (!eq(hmac(okm.subarray(32), cat(E, n, c)), m)) { okm.fill(0); return null; }
      const pt = chacha(okm.subarray(0, 32), n, c);
      okm.fill(0);
      return pt;
    } catch (err) {
      return null;
    }
  }

  /* == x25519.seal (fresh random ephemeral key + nonce). Used to re-seal the grant to a rotated public key on the phone. */
  async function sealBox(pub, pt, info) {
    const e = crypto.getRandomValues(new Uint8Array(32));
    const E = await x25519Pub(e);
    const sh = await x25519Shared(e, pub);
    e.fill(0);
    const okm = hkdf(sh, cat(E, pub), bytesOf(info), 64);
    sh.fill(0);
    const n = crypto.getRandomValues(new Uint8Array(12));
    const c = chacha(okm.subarray(0, 32), n, pt);
    const m = hmac(okm.subarray(32), cat(E, n, c));
    okm.fill(0);
    return {e: b64e(E), n: b64e(n), c: b64e(c), m: b64e(m)};
  }

  function entryV3(blob, acct, t) {
    if (!blob || blob.v !== 3) return null;
    const e = entry(blob, acct);
    return e && typeof e === 'object' && e.t === t ? e : null;
  }
  /* body = ChaCha20(dk[:32]) + HMAC(dk[32:], nonce || ct)  == booklet_crypto._open_body_v3 */
  function openBody(blob, dk) {
    if (!dk || dk.length !== 64) return null;
    const nonce = b64d(blob.n), ct = b64d(blob.c), mac = b64d(blob.m);
    if (!eq(hmac(dk.subarray(32), cat(nonce, ct)), mac)) return null;
    return chacha(dk.subarray(0, 32), nonce, ct);
  }

  /* x entry (passkey PRF key) -> plaintext Uint8Array or null  == booklet_crypto.decrypt_v3_x */
  async function decryptV3X(blob, acct, priv) {
    try {
      const e = entryV3(blob, acct, 'x');
      if (!e) return null;
      const dk = await openSealed(priv, {e: e.e, n: e.n, c: e.w, m: e.m}, WRAP_INFO);
      const pt = openBody(blob, dk);
      if (dk) dk.fill(0);
      return pt;
    } catch (err) {
      return null;
    }
  }

  /* unwrap the DK of pw entry e with kek64 and open the body -> plaintext or null. Does not touch kek. */
  function openPw(blob, e, kek) {
    const salt = b64d(e.s), wn = b64d(e.n), w = b64d(e.w), wm = b64d(e.m);
    if (!eq(hmac(kek.subarray(32), cat(salt, wn, w)), wm)) return null;
    const dk = chacha(kek.subarray(0, 32), wn, w);
    const pt = openBody(blob, dk);
    dk.fill(0);
    return pt;
  }
  /* pw entry -> {pt, kek64} or null. `pw` is used as given (the app normalises the passphrase with normPass first). */
  async function decryptV3PwKek(blob, user, pw) {
    let kek = null;
    try {
      const e = entryV3(blob, accountId(user), 'pw');
      if (!e) return null;
      const it = Number(e.it);
      if (!Number.isInteger(it) || it < 1 || it > MAX_IT) return null;
      kek = await deriveKek(user, pw, b64d(e.s), it);
      const pt = openPw(blob, e, kek);
      if (!pt) { kek.fill(0); return null; }
      return {pt: pt, kek: kek};
    } catch (err) {
      if (kek) kek.fill(0);
      return null;
    }
  }
  /* open a newer blob with the kek64 kept in memory since a password login (no PBKDF2); only while the PC keeps
   * the same salt/iterations for the account -> plaintext or null */
  async function decryptV3Kek(blob, acct, kek) {
    try {
      const e = entryV3(blob, acct, 'pw');
      if (!e || !kek || kek.length !== 64) return null;
      return openPw(blob, e, kek);
    } catch (err) {
      return null;
    }
  }
  /* == booklet_crypto.decrypt_v3_pw */
  async function decryptV3Pw(blob, user, pw) {
    const r = await decryptV3PwKek(blob, user, pw);
    if (!r) return null;
    r.kek.fill(0);
    return r.pt;
  }

  /* passphrase as typed -> canonical "word-word-word-word-word" (relay_users gen output form) */
  const normPass = s => String(s == null ? '' : s).trim().toLowerCase().split(/[\s\-]+/).filter(Boolean).join('-');

  /* password users sign requests with HMAC(kek64, "oncall-refresh")  == booklet_crypto.auth_key */
  const authFromKek = kek => hmac(kek, utf8('oncall-refresh'));

  /* grant box -> {access: 16 B, auth: 32 B} or null  == booklet_crypto.open_grant */
  async function openGrant(priv, box) {
    const pt = await openSealed(priv, box, GRANT_INFO);
    if (!pt) return null;
    if (pt.length !== ACCESS_LEN + AUTH_LEN) { pt.fill(0); return null; }
    const r = {access: pt.slice(0, ACCESS_LEN), auth: pt.slice(ACCESS_LEN)};
    pt.fill(0);
    return r;
  }
  /* access + auth -> grant box sealed to pub (same layout open_grant reads) */
  async function sealGrant(pub, access, auth) {
    if (access.length !== ACCESS_LEN || auth.length !== AUTH_LEN) throw new Error('bad grant key length');
    const pt = cat(access, auth);
    const box = await sealBox(pub, pt, GRANT_INFO);
    pt.fill(0);
    return box;
  }

  /* hex HMAC(auth, msg): refresh `${acct}|${ts}`, rotate `${acct}|${newpub_b64}|${period}|${ts}`  == refresh_proof_v3 */
  async function proofV3(auth, msg) { return hex(hmac(auth, utf8(msg))); }

  /* 6 digits = big-endian uint32 of sha256(pub)[:4] mod 1e6  == booklet_crypto.confirm_code */
  async function confirmCode(pub) {
    const h = sha256(pub);
    const v = ((h[0] << 24) | (h[1] << 16) | (h[2] << 8) | h[3]) >>> 0;
    return String(v % 1e6).padStart(6, '0');
  }

  const prfSalt = p => utf8('oncall-prf-v1|' + p);
  const period = d => { const x = d || new Date(); return x.getFullYear() + '-' + pad2(x.getMonth() + 1); };

  const api = {b64d, b64e, b64ud, b64ue, sha256, hmac, pbkdf2, chacha, hkdf, deriveKek, accountId,
               x25519Pub, openSealed, sealBox, decryptV3X, decryptV3Pw, decryptV3PwKek, decryptV3Kek, normPass, authFromKek,
               openGrant, sealGrant, proofV3, confirmCode, prfSalt, period, ITERATIONS_PW, MAX_IT};
  Object.assign(G, api);
  G.OC = api;
})(self);
