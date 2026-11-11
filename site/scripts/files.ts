/**
 * The files the editor holds beside the pages, gathered at build time: eukhe's files the README
 * links to (`src/content/eukhe/`, `scripts/eukhe.ts`), at their paths in eukhe's repository, so
 * the README's relative links open them. The README itself is the page (`index.md`).
 */
import { readFile, readdir } from "node:fs/promises";
import path from "node:path";

import type { SourceFile } from "../src/render.tsx";

/** Every file of eukhe's copy but its README, in path order. */
export async function gather(root: string): Promise<SourceFile[]> {
  const dir = path.join(root, "src/content/eukhe");
  const entries = await readdir(dir, { recursive: true, withFileTypes: true });
  const names = entries
    .filter((entry) => entry.isFile())
    .map((entry) =>
      path.relative(dir, path.join(entry.parentPath, entry.name)).split(path.sep).join("/"),
    )
    .filter((name) => name !== "README.md")
    .toSorted((a, b) => (a < b ? -1 : a > b ? 1 : 0));
  return Promise.all(
    names.map(async (name) => ({
      path: name,
      text: await readFile(path.join(dir, name), "utf8"),
      plain: true,
    })),
  );
}
