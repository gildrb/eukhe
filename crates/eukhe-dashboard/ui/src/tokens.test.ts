// The token source against its Bend model and the files that cannot read
// it: bridge/bridge_tokens.bend must print the tables of tokens.stylex.ts
// (laws/tokens.bend states their rules), the browser's theme
// color in index.html, the manifest and theme.js must be the palette's
// `bg`, and global.css must hold no literal (the lint rule
// eukhe/token-literals covers the scripts).

import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { expect, test } from "vite-plus/test";
import { literalIn } from "../lint/tokens.mjs";
import { darkPalette, layer, lightPalette, space, type } from "./tokens.stylex.ts";

const UI = join(import.meta.dirname, "..");
const REPO = join(UI, "../../..");

/** A palette value as `R G B A` (channels 0..255, alpha in hundredths), `- - - -` for none. */
function channels(value: string | undefined): string {
  if (value === undefined) return "- - - -";
  const hex = /^#([0-9a-f]{2})([0-9a-f]{2})([0-9a-f]{2})$/i.exec(value);
  if (hex)
    return `${hex
      .slice(1)
      .map((part) => parseInt(part, 16))
      .join(" ")} 100`;
  const rgb = /^rgb\((\d+) (\d+) (\d+) \/ ([\d.]+)\)$/.exec(value);
  if (rgb) return `${rgb[1]} ${rgb[2]} ${rgb[3]} ${Math.round(Number(rgb[4]) * 100)}`;
  throw new Error(
    `the palette value ${value} is neither six hex digits nor an rgb color with alpha`,
  );
}

/** The px of a length token. */
function px(value: string): number {
  const found = /^(\d+)px$/.exec(value);
  if (!found) throw new Error(`${value} is not a whole px length`);
  return Number(found[1]);
}

/** The transcript bridge_tokens.bend prints, from tokens.stylex.ts. */
function transcript(): string {
  const light: Record<string, string> = lightPalette;
  const dark: Record<string, string> = darkPalette;
  const names = [...new Set([...Object.keys(light), ...Object.keys(dark)])];
  const lines = names.map(
    (name) => `color ${name} ${channels(light[name])} ${channels(dark[name])}`,
  );
  for (const [name, z] of Object.entries(layer)) lines.push(`layer ${name} ${z}`);
  for (const [name, value] of Object.entries(space)) lines.push(`space ${name} ${px(value)}`);
  const lengths = Object.entries(type).filter(([, value]) => value.endsWith("px"));
  for (const [name, value] of lengths) {
    if (!name.endsWith("Line")) lines.push(`type ${name} ${px(value)}`);
  }
  for (const [name, value] of lengths) {
    if (name.endsWith("Line")) lines.push(`line ${name} ${px(value)}`);
  }
  return `${lines.join("\n")}\n`;
}

test("the token tables equal bend/tokens.bend", (context) => {
  const bend = process.env.BEND ?? "bend";
  const dir = mkdtempSync(join(tmpdir(), "eukhe-tokens-"));
  const binary = join(dir, "bridge");
  const built = spawnSync(bend, [join(REPO, "bridge/bridge_tokens.bend"), "-o", binary], {
    encoding: "utf8",
  });
  if (built.error) {
    expect(
      process.env.EUKHE_REQUIRE_BEND,
      "EUKHE_REQUIRE_BEND is set but no `bend` is on PATH (or in $BEND)",
    ).toBeUndefined();
    console.warn(
      "SKIPPED the bridge to bend/tokens.bend: `bend` is not installed (https://bend-lang.com/install.sh, version 2.0.39)",
    );
    context.skip();
    return;
  }
  expect(
    built.status,
    `bend could not build bridge/bridge_tokens.bend:\n${built.stdout}${built.stderr}`,
  ).toBe(0);
  const ran = spawnSync(binary, { encoding: "utf8" });
  expect(ran.status, ran.stderr).toBe(0);
  expect(ran.stdout.trimEnd()).toBe(transcript().trimEnd());
}, 300_000);

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
