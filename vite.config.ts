import assert from "node:assert";
import { cp, mkdir, rm, writeFile } from "node:fs/promises";
import path from "node:path";
import stylexVite from "@stylexjs/unplugin/vite";
import { defineConfig, type Plugin } from "vite-plus";
import type * as RenderModule from "./src/render.tsx";

type Render = typeof RenderModule;

/** The renderer module, as the bundler hands it back untyped; its signature is `render.tsx`'s. */
function isRender(module: unknown): module is Render {
  return (
    typeof module === "object" &&
    module !== null &&
    "render" in module &&
    typeof module.render === "function" &&
    "favicon" in module &&
    typeof module.favicon === "string" &&
    "origin" in module &&
    typeof module.origin === "string"
  );
}

function renderModule(module: unknown): Render {
  if (!isRender(module)) throw new TypeError("src/render.tsx lacks the expected exports");
  return module;
}

const ssrOutDir = "node_modules/.site-ssr";

// StyleX hands over the CSS it has collected; each page inlines it, so there is no stylesheet.
const stylexPlugin: Plugin & { __stylexCollectCss?: () => string } = stylexVite({
  useCSSLayers: true,
  lightningcssOptions: { minify: true },
  devMode: "css-only",
});

const site: Plugin = {
  name: "site",
  configureServer(server) {
    server.watcher.on("change", (file) => {
      if (file.includes(`${path.sep}src${path.sep}`)) server.ws.send({ type: "full-reload" });
    });
    server.middlewares.use((request, response, next) => {
      const { pathname } = new URL(request.url ?? "/", "http://localhost");
      server
        .ssrLoadModule("/src/render.tsx")
        .then(async (module) => {
          const files = renderModule(module).render(stylexPlugin.__stylexCollectCss?.() ?? "");
          const name = pathname === "/" ? "index.html" : pathname.slice(1);
          const body = files[name];
          if (body === undefined) return next();
          const html = name.endsWith(".html");
          response.setHeader("Content-Type", html ? "text/html" : contentType(name));
          response.end(html ? await server.transformIndexHtml(pathname, body) : body);
        })
        .catch((error: unknown) => next(error));
    });
  },
};

function contentType(name: string): string {
  if (name.endsWith(".svg")) return "image/svg+xml";
  if (name.endsWith(".xml")) return "application/xml";
  if (name.endsWith(".md")) return "text/markdown; charset=utf-8";
  return "text/plain; charset=utf-8";
}

export default defineConfig({
  staged: { "*": "vp check --fix" },
  fmt: { ignorePatterns: ["src/content/**", "public/**"] },
  lint: {
    ignorePatterns: ["public/**"],
    plugins: ["typescript", "unicorn", "oxc", "import"],
    jsPlugins: [{ name: "vite-plus", specifier: "vite-plus/oxlint-plugin" }],
    categories: { correctness: "error", suspicious: "error" },
    rules: {
      "vite-plus/prefer-vite-plus-imports": "error",
      "typescript/no-explicit-any": "error",
      "typescript/no-non-null-assertion": "error",
      "typescript/consistent-type-assertions": ["error", { assertionStyle: "never" }],
      "typescript/consistent-type-definitions": ["error", "type"],
      "typescript/switch-exhaustiveness-check": "error",
      "typescript/no-floating-promises": "error",
      "typescript/no-misused-promises": "error",
      "no-var": "error",
      // StyleX names the hook that hands over its collected CSS.
      "no-underscore-dangle": ["error", { allow: ["__stylexCollectCss"] }],
      "prefer-const": "error",
      eqeqeq: "error",
    },
    options: { typeAware: true, typeCheck: true },
  },
  appType: "custom",
  server: { host: "127.0.0.1", port: 5175, strictPort: false },
  plugins: [stylexPlugin, site],
  environments: {
    ssr: {
      build: {
        outDir: ssrOutDir,
        emptyOutDir: true,
        copyPublicDir: false,
        rollupOptions: { input: "src/render.tsx" },
      },
    },
  },
  builder: {
    // Prerender: the SSR pass registers every StyleX rule; the pages inline the collected CSS.
    async buildApp(builder) {
      const { ssr } = builder.environments;
      assert(ssr);
      await builder.build(ssr);
      const css = stylexPlugin.__stylexCollectCss?.() ?? "";
      assert(css.length > 0, "StyleX collected no CSS");
      // The bundle this build just wrote; it does not exist when this config loads.
      const { render } = renderModule(await import(path.resolve(ssrOutDir, "render.js")));
      const outDir = "dist";
      await rm(outDir, { recursive: true, force: true });
      await cp("public", outDir, { recursive: true });
      await Promise.all(
        Object.entries(render(css)).map(async ([file, body]) => {
          await mkdir(path.dirname(path.join(outDir, file)), { recursive: true });
          await writeFile(path.join(outDir, file), body);
        }),
      );
    },
  },
});
