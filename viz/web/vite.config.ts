import { svelte } from '@sveltejs/vite-plugin-svelte'
import { defineConfig } from 'vite'

// https://vite.dev/config/
export default defineConfig({
  plugins: [svelte()],
  // Relative paths, so the build works under any base path (GitHub Pages).
  base: './',
  // The WebAssembly package is built into ../wasm/pkg.
  server: { fs: { allow: ['..'] } },
})
