/**
 * The home page is eukhe's README.md, as it is on eukhe's main branch. `src/content/README.md` is
 * its copy: `node scripts/readme.ts` writes it, `node scripts/readme.ts --check` (part of the build)
 * fails when it differs from the README on main, so the page never drifts from it.
 */
import { readFile, writeFile } from "node:fs/promises";
import path from "node:path";

const url = "https://raw.githubusercontent.com/gildrb/eukhe/main/README.md";
const copy = path.join(import.meta.dirname, "../src/content/README.md");

const response = await fetch(url, { cache: "no-store" });
if (!response.ok) throw new Error(`${url}: ${response.status}`);
const readme = await response.text();

if (process.argv.includes("--check")) {
  const local = await readFile(copy, "utf8").catch(() => "");
  if (local !== readme) {
    console.error(`src/content/README.md differs from ${url}: run node scripts/readme.ts`);
    process.exit(1);
  }
} else {
  await writeFile(copy, readme);
}
