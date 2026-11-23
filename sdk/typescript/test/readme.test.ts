/**
 * The README's code, as a consumer compiles it: every ```ts block that
 * imports "eukhe" type-checks under `strict`, so its error handling narrows
 * without casts.
 */
import assert from "node:assert/strict";
import { execFile } from "node:child_process";
import { mkdtemp, readFile, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { test } from "node:test";
import { fileURLToPath } from "node:url";
import { promisify } from "node:util";

const ROOT = fileURLToPath(new URL("..", import.meta.url));

test("the README's code compiles under strict", async () => {
  const readme = await readFile(join(ROOT, "README.md"), "utf8");
  const blocks = [...readme.matchAll(/^```ts\n(import [\s\S]*?)^```$/gm)].map((match) => match[1] ?? "");
  assert.ok(blocks.some((block) => block.includes("instanceof EukheError")), "the README shows the error pattern");
  const dir = await mkdtemp(join(tmpdir(), "eukhe-readme-"));
  const files = blocks.map((_, index) => join(dir, `block-${index}.ts`));
  await Promise.all(blocks.map((block, index) => writeFile(files[index] ?? "", block)));
  await writeFile(join(dir, "package.json"), JSON.stringify({ type: "module" }));
  await writeFile(
    join(dir, "tsconfig.json"),
    JSON.stringify({
      compilerOptions: {
        strict: true,
        target: "es2024",
        lib: ["es2024"],
        module: "nodenext",
        moduleResolution: "nodenext",
        types: ["node"],
        typeRoots: [join(ROOT, "node_modules", "@types")],
        paths: { eukhe: [join(ROOT, "src", "index.ts")] },
        allowImportingTsExtensions: true,
        noEmit: true,
        skipLibCheck: true,
      },
      files,
    }),
  );
  const tsc = join(ROOT, "node_modules", ".bin", "tsc");
  await promisify(execFile)(tsc, ["-p", join(dir, "tsconfig.json")]).catch((error: unknown) => {
    const output = execOutput(error);
    assert.fail(`README code does not compile:\n${output}`);
  });
});

function execOutput(error: unknown): string {
  if (typeof error === "object" && error !== null && "stdout" in error && typeof error.stdout === "string") return error.stdout;
  return String(error);
}
