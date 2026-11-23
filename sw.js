/* Notes PWA service worker: cache-first for the app shell only. Bump SHELL_V whenever a shell file changes.
 * The Apps Script data/status responses (script.google.com / googleusercontent) are never cached here:
 * the encrypted payload lives in IndexedDB (store.js). */
const SHELL_V = 'v53';
const CACHE = 'oncall-shell-' + SHELL_V;
const SHELL = ['./', './index.html', './config.js', './crypto.js', './logic.js', './store.js', './app.js',
               './manifest.webmanifest', './icon-192.png', './icon-512.png',
               './apple-touch-icon.png', './icon.svg'];

self.addEventListener('install', e => {
  e.waitUntil(caches.open(CACHE).then(c => c.addAll(SHELL.map(u => new Request(u, {cache: 'reload'})))).then(() => self.skipWaiting()));
});

self.addEventListener('activate', e => {
  e.waitUntil(caches.keys()
    .then(keys => Promise.all(keys.filter(k => k !== CACHE).map(k => caches.delete(k))))
    .then(() => self.clients.claim()));
});

self.addEventListener('fetch', e => {
  const req = e.request;
  if (req.method !== 'GET') return;
  const url = new URL(req.url);
  if (/(^|\.)script\.google\.com$|googleusercontent\.com$/.test(url.hostname)) return;   // network only, never cached
  if (url.origin !== self.location.origin) return;
  const inShell = SHELL.some(p => new URL(p, self.registration.scope).pathname === url.pathname);
  if (!inShell) return;                                  // e.g. data.json / test.html / vectors.json: plain network
  e.respondWith(
    caches.open(CACHE).then(c => c.match(req, {ignoreSearch: true}))   // index.html?local=1 -> cached index.html
      .then(hit => hit || fetch(req))
  );
});
