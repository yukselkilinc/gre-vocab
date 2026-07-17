const CACHE_NAME = 'gre-vocab';
const ASSETS_TO_CACHE = [
  './',
  './index.html',
  './index.js',
  './index.css',
  './memory_palace.html',
  './database.js',
  './manifest.json',
  './icon.svg',
  './palace_icon.svg',
  'https://cdn.tailwindcss.com'
];

// Install Event: Cache assets
self.addEventListener('install', (event) => {
  event.waitUntil(
    caches.open(CACHE_NAME)
      .then((cache) => {
        return cache.addAll(ASSETS_TO_CACHE);
      })
  );
});

// Fetch Event: Serve from cache if offline
self.addEventListener('fetch', (event) => {
  event.respondWith(
    caches.match(event.request)
      .then((response) => {
        return response || fetch(event.request);
      })
  );
});

// Activate Event: Clean up old caches
self.addEventListener('activate', (event) => {
  event.waitUntil(
    caches.keys().then((cacheNames) => {
      return Promise.all(
        cacheNames.map((cache) => {
          if (cache !== CACHE_NAME) {
            return caches.delete(cache);
          }
        })
      );
    })
  );
});