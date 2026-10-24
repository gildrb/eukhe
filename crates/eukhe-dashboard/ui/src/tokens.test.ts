// The files that cannot read the token source: the browser's theme color
// in index.html, the manifest and theme.js must be the palette's `bg`, and
// global.css must hold no literal (the lint rule eukhe/token-literals
// covers the scripts). The palettes and scales themselves are written by
// the compiled Bend core (eukhe-bend rules::tokens checks the file).

import { readFileSync } from "node:fs";
import { join } from "node:path";
import { expect, test } from "vite-plus/test";
import { literalIn } from "../lint/tokens.mjs";
import { darkPalette, lightPalette } from "./tokens.stylex.ts";

const UI = join(import.meta.dirname, "..");

test("the browser's theme color is the palette's bg", () => {
  const html = readFileSync(join(UI, "index.html"), "utf8");
  const manifest = JSON.parse(readFileSync(join(UI, "public/manifest.webmanifest"), "utf8")) as {
    background_color: string;
    theme_color: string;
  };
  const script = readFileSync(join(UI, "public/theme.js"), "utf8");
  expect({
    html: /<meta name="theme-color" content="([^"]*)"/.exec(html)?.[1],
    manifest: [manifest.background_color, manifest.theme_color],
    script: /dark \? '([^']*)' : '([^']*)'/.exec(script)?.slice(1),
  }).toEqual({
    html: darkPalette.bg,
    manifest: [darkPalette.bg, darkPalette.bg],
    script: [darkPalette.bg, lightPalette.bg],
  });
});

test("global.css holds no presentation literal", () => {
  const found: string[] = [];
  let fontFace = false;
  readFileSync(join(UI, "src/global.css"), "utf8")
    // Comments go, their lines stay: the line numbers hold.
    .replace(/\/\*[\s\S]*?\*\//g, (comment) => comment.replace(/[^\n]/g, ""))
    .split("\n")
    .forEach((line, at) => {
      // @font-face descriptors describe the font files, not the look.
      if (line.startsWith("@font-face")) fontFace = true;
      const what = fontFace ? null : literalIn(line);
      if (what) found.push(`src/global.css:${at + 1}: ${what}`);
      if (fontFace && line.startsWith("}")) fontFace = false;
    });
  expect(found).toEqual([]);
});
