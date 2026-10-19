import { fileURLToPath } from "node:url";
import stylexVite from "@stylexjs/unplugin/vite";
import { defineConfig } from "vite-plus";

const here = (path: string) => fileURLToPath(new URL(path, import.meta.url));

// The build writes the app into ../web, which is committed: build.rs embeds
// every file there into the eukhe binary, so cargo and Nix builds need no
// Node. build.rs knows these extensions only: html css js mjs json svg png
// ico woff2 webmanifest txt. So no source maps, and no inlined assets (the
// CSP permits fonts and scripts from the app itself only).
export default defineConfig({
  // The app is served under any path (`tailscale serve --set-path /eukhe`): every URL is relative.
  base: "./",
  publicDir: "public",
  fmt: { ignorePatterns: ["public/**"] },
  lint: {
    ignorePatterns: ["public/**"],
    plugins: ["typescript", "unicorn", "oxc", "import"],
    categories: { correctness: "error", suspicious: "error" },
    rules: {
      "typescript/no-explicit-any": "error",
      "typescript/no-non-null-assertion": "error",
      "no-var": "error",
      "prefer-const": "error",
      eqeqeq: "error",
      "typescript/no-floating-promises": "error",
      "typescript/no-misused-promises": "error",
      // The entry imports its stylesheet for its side effect.
      "import/no-unassigned-import": ["error", { allow: ["**/*.css"] }],
      // The bridge's JSON is typed where it is read (src/lib/types.ts); validating every
      // daemon value at runtime would duplicate the daemon's own schema.
      "typescript/no-unsafe-type-assertion": "off",
    },
    options: { typeAware: true, typeCheck: true },
  },
  plugins: [
    stylexVite({
      useCSSLayers: true,
      lightningcssOptions: { minify: true },
      devMode: "css-only",
    }),
  ],
  // `vp test`: component tests (colocated `*.test.tsx`) in a browser-like DOM.
  test: { environment: "happy-dom", include: ["src/**/*.test.{ts,tsx}"] },
  // Radix and markdown-to-jsx are written for React: they get Preact's
  // compatibility layer in its place (preactjs.com, "Aliasing React to Preact").
  resolve: {
    alias: [
      { find: /^react$/, replacement: "preact/compat" },
      { find: /^react-dom$/, replacement: "preact/compat" },
      { find: /^react-dom\/test-utils$/, replacement: "preact/test-utils" },
      { find: /^react\/jsx-runtime$/, replacement: "preact/jsx-runtime" },
      { find: /^react-style-singleton$/, replacement: here("./src/lib/style-singleton.ts") },
    ],
  },
  server: {
    host: "127.0.0.1",
    port: 47610,
    strictPort: true,
    // `vp dev` talks to an isolated dashboard: EUKHE_DASHBOARD=127.0.0.1:<port>.
    proxy: {
      "/api/ws": {
        target: `ws://${process.env.EUKHE_DASHBOARD ?? "127.0.0.1:47600"}`,
        ws: true,
        changeOrigin: true,
        rewriteWsOrigin: true,
      },
    },
  },
  build: {
    outDir: "../web",
    emptyOutDir: true,
    assetsDir: "assets",
    assetsInlineLimit: 0,
    sourcemap: false,
    modulePreload: { polyfill: false },
    reportCompressedSize: true,
    rollupOptions: {
      // Radix marks its modules "use client" for React Server Components; meaningless in this bundle.
      onwarn(warning, warn) {
        if (warning.code !== "MODULE_LEVEL_DIRECTIVE") warn(warning);
      },
    },
  },
});
