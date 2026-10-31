/**
 * The files the editor holds beside the page, gathered at build time: the license, eukhe's docs (at
 * a pinned commit, cached) and this site's Bend source. `render.tsx` puts the page (`index.md`)
 * first: the editor opens it.
 */
import { mkdir, readFile, readdir, writeFile } from "node:fs/promises";
import path from "node:path";

import type { SourceFile } from "../src/render.tsx";

/** eukhe's commit whose docs the editor holds (branch bend/all). */
const eukheCommit = "a5fab57152ed66d31598bae4e586ea2c914a42ca";
const docs = [
  "control.md",
  "daemon.md",
  "dashboard.md",
  "develop.md",
  "gateway.md",
  "harness.md",
  "inference.md",
  "install.md",
  "interface.md",
  "local-models.md",
  "memory.md",
  "runtime.md",
  "settings.md",
  "state.md",
  "tools.md",
  "usage.md",
  "workflows.md",
];

async function doc(root: string, name: string): Promise<string> {
  const cache = path.join(root, "node_modules/.cache/eukhe-docs", eukheCommit, name);
  try {
    return await readFile(cache, "utf8");
  } catch {
    const url = `https://raw.githubusercontent.com/gildrb/eukhe/${eukheCommit}/docs/${name}`;
    const response = await fetch(url);
    if (!response.ok) throw new Error(`${url}: ${response.status}`);
    const text = await response.text();
    await mkdir(path.dirname(cache), { recursive: true });
    await writeFile(cache, text);
    return text;
  }
}

async function bendFiles(root: string, dir: string): Promise<string[]> {
  const entries = await readdir(path.join(root, dir), { withFileTypes: true }).catch(() => []);
  const nested = await Promise.all(
    entries.map(async (entry) => {
      const relative = dir === "" ? entry.name : `${dir}/${entry.name}`;
      if (entry.isDirectory()) return bendFiles(root, relative);
      return entry.name.endsWith(".bend") ? [relative] : [];
    }),
  );
  return nested.flat();
}

/** Every file but the page, in path order. */
export async function gather(root: string): Promise<SourceFile[]> {
  const source = await Promise.all([
    ...["LAWS.bend", "PROOF.bend"].map(async (name) => ({
      path: name,
      text: await readFile(path.join(root, name), "utf8").catch(() => ""),
    })),
    ...[
      ...(await bendFiles(root, "vim")),
      ...(await bendFiles(root, "laws")),
      ...(await bendFiles(root, "proof")),
    ].map(async (name) => ({ path: name, text: await readFile(path.join(root, name), "utf8") })),
  ]);
  return [
    { path: "LICENSE", text: await readFile(path.join(root, "LICENSE"), "utf8"), plain: true },
    ...(await Promise.all(
      docs.map(async (name) => ({
        path: `docs/${name}`,
        text: await doc(root, name),
        plain: false,
      })),
    )),
    ...source.filter((file) => file.text !== "").map((file) => ({ ...file, plain: true })),
  ].toSorted((a, b) => (a.path < b.path ? -1 : a.path > b.path ? 1 : 0));
}
