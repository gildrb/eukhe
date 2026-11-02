/**
 * The files the editor holds beside the pages, gathered at build time: the license and this site's
 * Bend source. `render.tsx` puts the page (`index.md`) first: the editor opens it.
 */
import { readFile, readdir } from "node:fs/promises";
import path from "node:path";

import type { SourceFile } from "../src/render.tsx";

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
    ...source.filter((file) => file.text !== "").map((file) => ({ ...file, plain: true })),
  ].toSorted((a, b) => (a.path < b.path ? -1 : a.path > b.path ? 1 : 0));
}
