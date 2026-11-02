// Drives the compiled Bend core (src/vim.mjs) with keys and prints each frame's
// cursor, ruler and command line. Usage: node scripts/vim-smoke.mjs "j j w G gg"
import fs from "node:fs";
import Vim from "../src/vim.mjs";

const list = (v) => {
  const out = [];
  while (v && !Array.isArray(v) && v.$ === "Con") {
    out.push(v.head);
    v = v.tail;
  }
  return Array.isArray(v) ? out.concat(v) : out;
};

const cons = (xs) => xs.reduceRight((tail, head) => ({ $: "Con", head, tail }), { $: "Nil" });
const page = fs.readFileSync(new URL("../src/content/README.md", import.meta.url), "utf8");
const files = cons([
  { $: "Buf", path: "index.md", lines: cons(page.replace(/\n$/, "").split("\n")) },
  { $: "Buf", path: "docs/install.md", lines: cons(["# Install", "", "curl it"]) },
  { $: "Buf", path: "LICENSE", lines: cons(["MIT License", "", "Copyright"]) },
]);
let st = Vim["Vim.init"](files, 40, 120);
const show = (label) => {
  const f = Vim["Vim.frame"](st);
  const float = f.float.$ === "Some" ? ` float=${f.float.value.width}x${f.float.value.height}` : "";
  console.log(
    `${label.padEnd(10)} cur=${f.cur.row},${f.cur.col} char=${JSON.stringify(f.char)} top=${f.top} status=${JSON.stringify(f.status.trim())} cmd=${JSON.stringify(f.cmd.trim())} hits=${list(f.hits).length}${float}`,
  );
};
show("init");
const keys = (process.argv[2] ?? "").split(" ").filter(Boolean);
for (const raw of keys) {
  const name = raw === "SPC" ? "<Space>" : raw;
  const t0 = performance.now();
  const step = Vim["Vim.step"](st, { $: "EvKey", name });
  const ms = (performance.now() - t0).toFixed(1);
  st = step.st;
  const act = step.act.$ === "Nothing" ? "" : ` act=${JSON.stringify(step.act)}`;
  show(`${name} ${ms}ms`);
  if (act) console.log("   ", act);
}
