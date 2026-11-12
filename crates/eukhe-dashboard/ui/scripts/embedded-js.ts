// The JavaScript Eukhe embeds (include_str! in the Rust crates, the dashboard's public/ files)
// is generated from TypeScript sources and committed, so the Rust build needs no Node. This
// script type-checks the sources (oxlint with tsgolint, each against the tsconfig.json next to
// it), erases their types, and writes the JavaScript (`generate`) or fails when a committed file
// differs (`check`). Run from crates/eukhe-dashboard/ui, after `npm ci`:
//   node scripts/embedded-js.ts generate|check
//
// Erasing types cuts the type syntax out of the source and keeps every other byte: the output is
// the source's code, comments and layout. A type declaration goes with its whole lines and the
// comment lines right above it. Each output is checked against oxc's own type erasure (the same
// program once both are parsed). The sources stay scripts: no import or export, no `as`, no
// non-null `!`, no enum, namespace or parameter property.
import { execFileSync } from "node:child_process";
import { readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { parseSync, transformSync, Visitor, type ESTree } from "vite/rolldown/utils";

/** A TypeScript source and the JavaScript generated from it, relative to the repository. */
type Source = { ts: string; js: string };

const UI = join(import.meta.dirname, "..");
const ROOT = join(UI, "../../..");
const SOURCES: Source[] = [
  {
    ts: "crates/eukhe-durable/src/codemode/sandbox/host.ts",
    js: "crates/eukhe-durable/src/codemode/sandbox/host.js",
  },
  {
    ts: "crates/eukhe-durable/src/codemode/sandbox/prelude.ts",
    js: "crates/eukhe-durable/src/codemode/sandbox/prelude.js",
  },
  {
    ts: "crates/eukhe-core/src/durable/workflow/prelude.ts",
    js: "crates/eukhe-core/src/durable/workflow/prelude.js",
  },
  {
    ts: "crates/eukhe-core/assets/export-html/template.ts",
    js: "crates/eukhe-core/assets/export-html/template.js",
  },
  {
    ts: "crates/eukhe-dashboard/ui/public-src/theme.ts",
    js: "crates/eukhe-dashboard/ui/public/theme.js",
  },
  {
    ts: "crates/eukhe-dashboard/ui/public-src/sw/sw.ts",
    js: "crates/eukhe-dashboard/ui/public/sw.js",
  },
];

/** A byte range of the source left out of the output. */
type Cut = { start: number; end: number };

class SourceError extends Error {}

/** The line and column of `at` in `code`, for messages. */
function position(code: string, at: number): string {
  const before = code.slice(0, at).split("\n");
  return `${before.length}:${(before.at(-1) ?? "").length + 1}`;
}

/** The start of the line holding `at`. */
function lineStart(code: string, at: number): number {
  return code.lastIndexOf("\n", at - 1) + 1;
}

/** The end of the line holding `at`, past its newline. */
function lineEnd(code: string, at: number): number {
  const newline = code.indexOf("\n", at);
  return newline === -1 ? code.length : newline + 1;
}

const blank = (text: string) => text.trim() === "";

/** `code` with the type syntax cut out. */
function eraseTypes(path: string, code: string): string {
  const parsed = parseSync(path, code, { lang: "ts", sourceType: "script", astType: "ts" });
  const [error] = parsed.errors;
  if (error) throw new SourceError(`${path}: ${error.codeframe ?? error.message}`);
  const cuts: Cut[] = [];
  const reject = (node: { start: number }, what: string) => {
    throw new SourceError(
      `${path}:${position(code, node.start)}: ${what} has no plain-JavaScript erasure`,
    );
  };
  // A declaration takes its whole lines when nothing else is on them, the comment lines right
  // above it, and one of the blank lines around it when there is one on each side.
  const cutDeclaration = (node: { start: number; end: number }) => {
    let start = node.start;
    let end = node.end;
    const first = lineStart(code, start);
    const last = lineEnd(code, end);
    if (blank(code.slice(first, start)) && blank(code.slice(end, last))) {
      start = first;
      end = last;
      for (let i = parsed.comments.length - 1; i >= 0; i -= 1) {
        const comment = parsed.comments[i];
        if (comment === undefined || comment.end > start) continue;
        const above = lineStart(code, comment.start);
        if (
          !/^[ \t]*\n$/.test(code.slice(comment.end, start)) ||
          !blank(code.slice(above, comment.start))
        )
          break;
        start = above;
      }
      const blankBefore = start === 0 || blank(code.slice(lineStart(code, start - 1), start));
      const next = lineEnd(code, end);
      if (blankBefore && end < code.length && blank(code.slice(end, next))) end = next;
    }
    cuts.push({ start, end });
  };
  const cut = (start: number, end: number) => cuts.push({ start, end });
  const thisParameter = (node: ESTree.Function) => {
    const [first, second] = node.params;
    if (first?.type === "Identifier" && first.name === "this")
      cut(first.start, second ? second.start : first.end);
  };
  new Visitor({
    TSTypeAnnotation: (node) => cut(node.start, node.end),
    TSTypeParameterDeclaration: (node) => cut(node.start, node.end),
    TSTypeParameterInstantiation: (node) => cut(node.start, node.end),
    TSTypeAliasDeclaration: cutDeclaration,
    TSDeclareFunction: cutDeclaration,
    TSModuleDeclaration: (node) =>
      node.declare ? cutDeclaration(node) : reject(node, "a namespace"),
    VariableDeclaration: (node) => {
      if (node.declare) cutDeclaration(node);
    },
    TSSatisfiesExpression: (node) => cut(node.expression.end, node.end),
    Identifier: (node) => {
      // An optional parameter (`name?: T`); oxc's typings leave `optional` out of parameters.
      const optional: unknown = Reflect.get(node, "optional");
      if (optional !== true) return;
      const question = code.indexOf("?", node.start + node.name.length);
      cut(question, question + 1);
    },
    FunctionDeclaration: thisParameter,
    FunctionExpression: thisParameter,
    TSInterfaceDeclaration: (node) => reject(node, "an interface (write a type)"),
    TSEnumDeclaration: (node) => reject(node, "an enum"),
    TSAsExpression: (node) => reject(node, "`as`"),
    TSTypeAssertion: (node) => reject(node, "a type assertion"),
    TSNonNullExpression: (node) => reject(node, "a non-null `!`"),
    TSParameterProperty: (node) => reject(node, "a parameter property"),
    TSExportAssignment: (node) => reject(node, "`export =`"),
    TSImportEqualsDeclaration: (node) => reject(node, "`import =`"),
    ClassDeclaration: (node) => {
      if (node.declare || node.abstract || (node.implements?.length ?? 0) > 0)
        reject(node, "a TypeScript class form");
    },
    PropertyDefinition: (node) => {
      if (
        node.declare ||
        node.definite ||
        node.optional ||
        node.override ||
        node.readonly ||
        node.accessibility
      ) {
        reject(node, "a TypeScript class member form");
      }
    },
    MethodDefinition: (node) => {
      if (node.override || node.optional || node.accessibility)
        reject(node, "a TypeScript class member form");
    },
  }).visit(parsed.program);
  // Cuts nest (a type inside a removed declaration): the outermost one stands.
  cuts.sort((a, b) => a.start - b.start || b.end - a.end);
  let out = "";
  let at = 0;
  for (const { start, end } of cuts) {
    if (end <= at) continue;
    out += code.slice(at, start);
    at = end;
  }
  return out + code.slice(at);
}

/** A program's syntax tree without positions and literal spellings, as text. */
function shape(path: string, code: string): string {
  const parsed = parseSync(path, code, { lang: "js", sourceType: "script", preserveParens: false });
  const [error] = parsed.errors;
  if (error) throw new SourceError(`${path}: ${error.codeframe ?? error.message}`);
  const ignored: Record<string, true> = {
    start: true,
    end: true,
    range: true,
    loc: true,
    raw: true,
  };
  return JSON.stringify(parsed.program, (key, value: unknown) =>
    Object.hasOwn(ignored, key) ? undefined : value,
  );
}

/** Fails unless `js` is the program oxc's type erasure makes of `ts`. */
function checkErasure(source: Source, ts: string, js: string): void {
  const erased = transformSync(source.ts, ts, {
    lang: "ts",
    sourceType: "script",
    target: "esnext",
  });
  const [error] = erased.errors;
  if (error) throw new SourceError(`${source.ts}: ${error.message}`);
  const want = shape(source.js, erased.code);
  const got = shape(source.js, js);
  if (want === got) return;
  let at = 0;
  while (want[at] === got[at]) at += 1;
  throw new SourceError(
    `${source.js}: the erased program differs from oxc's erasure of ${source.ts} near\n  ${got.slice(at - 80, at + 80)}\n  (oxc: ${want.slice(at - 80, at + 80)})`,
  );
}

/** Type-checks and lints `sources` against the tsconfig.json next to each. */
function typeCheck(sources: Source[]): void {
  const bin = join(UI, "node_modules/.bin");
  execFileSync(
    join(bin, "oxlint"),
    [
      "--type-aware",
      "--type-check",
      "--deny-warnings",
      "-c",
      join(UI, "scripts/embedded-js.oxlintrc.json"),
      ...sources.map((source) => source.ts),
    ],
    {
      cwd: ROOT,
      stdio: "inherit",
      env: { ...process.env, PATH: `${bin}:${process.env.PATH ?? ""}` },
    },
  );
}

/** `mode` over the sources named in `only` (repository paths), or every source. */
function main(mode: string | undefined, only: string[]): number {
  const sources =
    only.length === 0 ? SOURCES : SOURCES.filter((source) => only.includes(source.ts));
  const unknown = only.filter((path) => !SOURCES.some((source) => source.ts === path));
  if ((mode !== "generate" && mode !== "check") || unknown.length > 0) {
    console.error("usage: node scripts/embedded-js.ts generate|check [<source.ts>...]");
    return 2;
  }
  try {
    typeCheck(sources);
  } catch {
    console.error("embedded-js: the TypeScript sources do not check (above)");
    return 1;
  }
  const stale: string[] = [];
  for (const source of sources) {
    const ts = readFileSync(join(ROOT, source.ts), "utf8");
    let js: string;
    try {
      js = eraseTypes(source.ts, ts);
      checkErasure(source, ts, js);
    } catch (error) {
      if (!(error instanceof SourceError)) throw error;
      console.error(`embedded-js: ${error.message}`);
      return 1;
    }
    const target = join(ROOT, source.js);
    let committed = "";
    try {
      committed = readFileSync(target, "utf8");
    } catch {
      // A missing output is stale.
    }
    if (committed === js) continue;
    if (mode === "generate") writeFileSync(target, js);
    stale.push(source.js);
  }
  if (mode === "generate") {
    for (const path of stale) console.log(`wrote ${path}`);
    return 0;
  }
  if (stale.length === 0) return 0;
  for (const path of stale)
    console.error(`embedded-js: ${path} differs from what its TypeScript source generates`);
  console.error("embedded-js: run `make embedded-js` and commit the result");
  return 1;
}

process.exitCode = main(process.argv[2], process.argv.slice(3));
