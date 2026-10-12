import Aura from '@primeuix/themes/aura';

export default defineNuxtConfig({
  compatibilityDate: '2025-07-15',
  ssr: false,
  devtools: { enabled: false },
  css: ['primeicons/primeicons.css', '~/assets/main.css'],
  modules: ['@primevue/nuxt-module'],
  typescript: { typeCheck: true },
  app: { head: { title: 'Rust std autoharness', meta: [{ name: 'description', content: 'Official autoharness generation and skipped candidate functions for the Rust standard library.' }] } },
  nitro: { prerender: { routes: ['/', '/autoharness', '/functions'] } },
  primevue: { options: { theme: { preset: Aura, options: { darkModeSelector: '.my-app-dark' } } } }
});
