/**
 * eukhe's files the site holds, as they are at one commit of eukhe's main branch, in
 * `src/content/eukhe/`: the README (the home page) and every file its relative links reach, then
 * the links of each Markdown file reached, in turn. A linked folder, or a linked `README.md` (the
 * index of its folder), brings the whole folder. `node scripts/eukhe.ts` writes them;
 * `node scripts/eukhe.ts --check` (part of the build) fails when they differ from main.
 */
import { mkdir, readFile, readdir, rm, writeFile } from "node:fs/promises";
import path from "node:path";

const repository = "gildrb/eukhe";
const target = path.join(import.meta.dirname, "../src/content/eukhe");

const token = process.env.GITHUB_TOKEN;
const headers: Record<string, string> = {
  Accept: "application/vnd.github+json",
  ...(token === undefined || token === "" ? {} : { Authorization: `Bearer ${token}` }),
};

async function json(url: string): Promise<unknown> {
  const response = await fetch(url, { headers, cache: "no-store" });
  if (!response.ok) throw new Error(`${url}: ${response.status}`);
  return response.json();
}

function field(value: unknown, key: string): unknown {
  if (typeof value !== "object" || value === null || !(key in value)) return undefined;
  return Object.getOwnPropertyDescriptor(value, key)?.value;
}

/** The commit main points to: every file comes from it, so the copy is one snapshot. */
const commitUrl = `https://api.github.com/repos/${repository}/commits/main`;
const head = field(await json(commitUrl), "sha");
if (typeof head !== "string" || !/^[0-9a-f]{40}$/.test(head))
  throw new Error(`${commitUrl}: no commit sha`);
const sha: string = head;

/** Every file path in the commit. */
const treeUrl = `https://api.github.com/repos/${repository}/git/trees/${sha}?recursive=1`;
const tree = await json(treeUrl);
const entries = field(tree, "tree");
if (field(tree, "truncated") !== false || !Array.isArray(entries))
  throw new Error(`${treeUrl}: no complete tree`);
const blobs = new Set(
  entries.flatMap((entry: unknown) => {
    const kind = field(entry, "type");
    const name = field(entry, "path");
    return kind === "blob" && typeof name === "string" ? [name] : [];
  }),
);

async function raw(file: string): Promise<string> {
  const url = `https://raw.githubusercontent.com/${repository}/${sha}/${file}`;
  const response = await fetch(url, { cache: "no-store" });
  if (!response.ok) throw new Error(`${url}: ${response.status}`);
  return response.text();
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
function reach(file: string, link: string): string[] {
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
  if (files.length === 0) throw new Error(`${file}: link ${link} reaches no file on main`);
  return files;
}

const copy = new Map<string, string>();
const queue = ["README.md"];
for (let next = queue.shift(); next !== undefined; next = queue.shift()) {
  if (copy.has(next)) continue;
  const text = await raw(next);
  copy.set(next, text);
  if (next.endsWith(".md"))
    for (const link of links(next, text))
      queue.push(...reach(next, link).filter((name) => !copy.has(name)));
}

async function local(dir: string): Promise<Map<string, string>> {
  const found = new Map<string, string>();
  const walk = async (relative: string): Promise<void> => {
    const items = await readdir(path.join(dir, relative), { withFileTypes: true }).catch(
      (error: unknown) => {
        if (error instanceof Error && "code" in error && error.code === "ENOENT") return [];
        throw error;
      },
    );
    for (const item of items) {
      const name = relative === "" ? item.name : `${relative}/${item.name}`;
      if (item.isDirectory()) await walk(name);
      else found.set(name, await readFile(path.join(dir, name), "utf8"));
    }
  };
  await walk("");
  return found;
}

if (process.argv.includes("--check")) {
  const have = await local(target);
  const differ = [...new Set([...have.keys(), ...copy.keys()])]
    .filter((name) => have.get(name) !== copy.get(name))
    .toSorted();
  if (differ.length > 0) {
    console.error(
      `src/content/eukhe/ differs from ${repository}@${sha.slice(0, 9)}: ${differ.join(", ")}. Run node scripts/eukhe.ts`,
    );
    process.exit(1);
  }
} else {
  await rm(target, { recursive: true, force: true });
  for (const [name, text] of copy) {
    await mkdir(path.dirname(path.join(target, name)), { recursive: true });
    await writeFile(path.join(target, name), text);
  }
  console.log(`src/content/eukhe/: ${copy.size} files from ${repository}@${sha.slice(0, 9)}`);
}
