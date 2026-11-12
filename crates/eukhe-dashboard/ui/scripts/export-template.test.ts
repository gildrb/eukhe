// The HTML export's page script (crates/eukhe-core/assets/export-html/template.ts) run the way an
// export file runs it: template.html with the vendored scripts and the generated template.js, in a
// happy-dom window, on the session data the exporters write (fixtures.ts, which the eukhe-core
// test export_html::fixtures writes).

import { readFileSync } from "node:fs";
import { join } from "node:path";
import { Window } from "happy-dom";
import { afterEach, describe, expect, test } from "vite-plus/test";
import { durable, legacy, live } from "../../../eukhe-core/assets/export-html/fixtures.ts";

const ASSETS = join(import.meta.dirname, "../../../eukhe-core/assets/export-html");

function asset(name: string): string {
  return readFileSync(join(ASSETS, name), "utf8");
}

const open: Window[] = [];

afterEach(async () => {
  for (const window of open.splice(0)) await window.happyDOM.close();
});

/** The export page of `data`, filled as export_html `generate_html` fills it (without the theme CSS). */
async function render(data: SessionExportData): Promise<Window> {
  const html = asset("template.html")
    .replace("{{CSS}}", "")
    .replace("{{SESSION_DATA}}", Buffer.from(JSON.stringify(data)).toString("base64"))
    .replace("{{MARKED_JS}}", () => asset("vendor/marked.min.js"))
    .replace("{{HIGHLIGHT_JS}}", () => asset("vendor/highlight.min.js"))
    .replace("{{JS}}", () => asset("template.js"));
  const window = new Window({
    url: "https://example.com/export.html",
    settings: {
      enableJavaScriptEvaluation: true,
      suppressInsecureJavaScriptEnvironmentWarning: true,
    },
  });
  open.push(window);
  const errors: unknown[] = [];
  window.addEventListener("error", (event) => errors.push(event));
  window.document.write(html);
  await window.happyDOM.waitUntilComplete();
  expect(errors).toEqual([]);
  return window;
}

/** The text of the elements `selector` matches, each with its whitespace collapsed. */
function texts(window: Window, selector: string): string[] {
  return [...window.document.querySelectorAll(selector)].map((element) =>
    (element.textContent ?? "").replace(/\s+/g, " ").trim(),
  );
}

describe("every producer's session renders", () => {
  test.each([
    ["legacy", legacy],
    ["durable", durable],
    ["live", live],
  ])("%s", async (_name, data) => {
    const window = await render(data);
    expect(texts(window, ".tree-node").length).toBeGreaterThan(0);
    expect(texts(window, "#messages > *").length).toBeGreaterThan(0);
  });
});

test("a command without an exit code shows no exit status, a failed one its code", async () => {
  const window = await render(legacy);
  const runs = texts(window, "#messages .tool-execution");
  const killed = runs.find((text) => text.includes("$ kill -9"));
  expect(killed).toBeDefined();
  expect(killed).not.toContain("(exit");
  expect(runs.find((text) => text.includes("$ false"))).toContain("(exit 1)");
  expect(runs.find((text) => text.includes("$ sleep 100"))).toContain("(cancelled)");
});

test("a durable compaction shows the context size before it, not 0", async () => {
  const window = await render(durable);
  expect(texts(window, "#messages .compaction-collapsed")).toEqual([
    `Compacted from ${(1200).toLocaleString()} tokens`,
  ]);
  expect(texts(window, ".tree-compaction")).toEqual(["[compaction: 1k tokens]"]);
});

test("a custom message shows its text, from blocks too, and nothing for no content", async () => {
  const blocks = texts(await render(legacy), "#messages .hook-message");
  expect(blocks.find((text) => text.includes("[blocks]"))).toContain("A note in blocks.");
  expect(blocks.join("\n")).not.toContain('"type"');

  const empty = texts(
    await render({
      ...durable,
      entries: durable.entries.map((entry) =>
        entry.type === "custom_message" && entry.customType === "note"
          ? { ...entry, content: null }
          : entry,
      ),
    }),
    "#messages .hook-message",
  );
  const note = empty.find((text) => text.includes("[note]"));
  expect(note).toBeDefined();
  expect(note).not.toContain("null");
});
