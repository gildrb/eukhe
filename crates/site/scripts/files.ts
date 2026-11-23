/**
 * The files the editor holds beside the pages, read at build time from the repository this site
 * lives in (`../..`, Eukhe's checkout): the README's relative links and every file they reach, then
 * the links of each Markdown file reached, in turn, at their paths in the repository, so the
 * README's relative links open them. A linked folder, or a linked `README.md` (the index of its
 * folder), brings the whole folder. The README itself is the page (`index.md`, `src/source.ts`).
 * The files are the repository's tracked files (`git ls-files`), as they are in the work tree.
 */
import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import { readFile } from "node:fs/promises";
import path from "node:path";

import type { SourceFile } from "../src/render.tsx";
import type { Shown } from "../src/rendered.ts";

/** The repository's tracked files, outside crates/site/ (the site never serves itself). */
function tracked(repository: string): Set<string> {
  const out = execFileSync(
    "git",
    ["-C", repository, "ls-files", "-z", "--", ":(exclude)crates/site/"],
    {
      encoding: "utf8",
    },
  );
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

/** An image the README shows (`<img src="media/x.webp">`): its repository path and its bytes. */
export type Image = { path: string; bytes: Buffer };

/** The repository paths of the README's `<img src>` attributes, in the README's order. */
export function imagePaths(markdown: string): string[] {
  return [...markdown.matchAll(/<img\b[^>]*\bsrc="([^"]+)"/g)].flatMap(([, url]) => {
    if (url === undefined || /^([a-z][a-z0-9+.-]*:|\/|#)/i.test(url)) return [];
    const resolved = path.posix.normalize(url);
    if (resolved.startsWith("../") || resolved === "..")
      throw new Error(`README.md: image ${url} leaves the repository`);
    return [resolved];
  });
}

/** The images the README shows, read from the repository; one it does not track fails the build. */
export async function images(root: string): Promise<Image[]> {
  const repository = path.resolve(root, "../..");
  const blobs = tracked(repository);
  const readme = await readFile(path.join(repository, "README.md"), "utf8");
  const paths = [...new Set(imagePaths(readme))];
  const missing = paths.filter((name) => !blobs.has(name));
  if (missing.length > 0) throw new Error(`README.md: images not tracked: ${missing.join(", ")}`);
  return Promise.all(
    paths.map(async (name) => ({ path: name, bytes: await readFile(path.join(repository, name)) })),
  );
}

/**
 * An image's width and height in pixels, from its header (GIF, PNG, extended WebP: every animated
 * one); another type fails the build.
 */
export function imageSize(image: Image): readonly [number, number] {
  const b = image.bytes;
  if (b.subarray(0, 4).toString("latin1") === "GIF8") return [b.readUInt16LE(6), b.readUInt16LE(8)];
  if (b.subarray(1, 4).toString("latin1") === "PNG")
    return [b.readUInt32BE(16), b.readUInt32BE(20)];
  if (b.subarray(8, 16).toString("latin1") === "WEBPVP8X")
    return [b.readUIntLE(24, 3) + 1, b.readUIntLE(27, 3) + 1];
  throw new Error(`${image.path}: not a GIF, a PNG or an extended WebP`);
}

/**
 * Where the site serves an image: beside its source, named by its content, so a changed image is a
 * new file and each file can be cached for good.
 */
export function servedPath(image: Image): string {
  const hash = createHash("sha256").update(image.bytes).digest("hex").slice(0, 12);
  return image.path.replace(/(\.[^./]+)$/, `.${hash}$1`);
}

/** The images as served, by the path the README names them by. */
export function shown(read: readonly Image[]): Shown {
  return Object.fromEntries(
    read.map((image) => {
      const [width, height] = imageSize(image);
      return [image.path, { src: `/${servedPath(image)}`, width, height }];
    }),
  );
}

/** The README's reach but the README itself, in path order; `root` is the site's directory. */
export async function gather(root: string): Promise<SourceFile[]> {
  const repository = path.resolve(root, "../..");
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
