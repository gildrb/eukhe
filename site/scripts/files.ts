/**
 * The files the editor holds beside the pages, read at build time from the repository this site
 * lives in (`..`, Eukhe's checkout): the README's relative links and every file they reach, then
 * the links of each Markdown file reached, in turn, at their paths in the repository, so the
 * README's relative links open them. A linked folder, or a linked `README.md` (the index of its
 * folder), brings the whole folder. The README itself is the page (`index.md`, `src/source.ts`).
 * The files are the repository's tracked files (`git ls-files`), as they are in the work tree.
 */
import { execFileSync } from "node:child_process";
import { readFile } from "node:fs/promises";
import path from "node:path";

import type { SourceFile } from "../src/render.tsx";

/** The repository's tracked files, outside site/ (the site never serves itself). */
function tracked(repository: string): Set<string> {
  const out = execFileSync("git", ["-C", repository, "ls-files", "-z", "--", ":(exclude)site/"], {
    encoding: "utf8",
  });
  return new Set(out.split("\0").filter((name) => name !== ""));
}

/** The repository paths a Markdown file links to: folders end in "/". */
function links(file: string, markdown: string): string[] {
  const dir = path.posix.dirname(file);
  return [...markdown.matchAll(/\[[^\]]*\]\(([^)\s]+)\)/g)].flatMap(([, url]) => {
    if (url === undefined || /^([a-z][a-z0-9+.-]*:|\/|#)/i.test(url)) return [];
    const bare = url.replace(/[?#].*$/, "");
    const resolved = path.posix.normalize(path.posix.join(dir, bare));
    if (resolved.startsWith("../") || resolved === "..")
      throw new Error(`${file}: link ${url} leaves the repository`);
    return [bare.endsWith("/") && !resolved.endsWith("/") ? `${resolved}/` : resolved];
  });
}

/**
 * The files a link brings: a folder's, a README's folder's (the root README is the home page
 * alone), or the one file.
 */
function reach(blobs: Set<string>, file: string, link: string): string[] {
  const dir = path.posix.dirname(link);
  const folder = link.endsWith("/")
    ? link
    : path.posix.basename(link) === "README.md" && dir !== "."
      ? `${dir}/`
      : blobs.has(link)
        ? null
        : `${link}/`;
  const files =
    folder === null ? [link] : [...blobs].filter((name) => name.startsWith(folder)).toSorted();
  if (files.length === 0) throw new Error(`${file}: link ${link} reaches no tracked file`);
  return files;
}

/** The README's reach but the README itself, in path order; `root` is the site's directory. */
export async function gather(root: string): Promise<SourceFile[]> {
  const repository = path.resolve(root, "..");
  const blobs = tracked(repository);
  const reached = new Map<string, string>();
  const queue = ["README.md"];
  for (let next = queue.shift(); next !== undefined; next = queue.shift()) {
    if (reached.has(next)) continue;
    const text = await readFile(path.join(repository, next), "utf8");
    reached.set(next, text);
    if (next.endsWith(".md"))
      for (const link of links(next, text))
        queue.push(...reach(blobs, next, link).filter((name) => !reached.has(name)));
  }
  return [...reached]
    .filter(([name]) => name !== "README.md")
    .toSorted(([a], [b]) => (a < b ? -1 : a > b ? 1 : 0))
    .map(([name, text]) => ({ path: name, text, plain: true }));
}
