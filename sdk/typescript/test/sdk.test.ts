import assert from "node:assert/strict";
import { mkdtemp } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { test } from "node:test";
import { fileURLToPath } from "node:url";

import { Eukhe, NotInstalled, NotLoggedIn, Unsupported, UnknownModel, type EukheEvent } from "../src/index.ts";

const STUB = fileURLToPath(new URL("./fixtures/stub-agent.ts", import.meta.url));

async function stub(mode: "plain" | "eukhe" | "logged-out"): Promise<Eukhe> {
  return Eukhe.start({ cwd: await mkdtemp(join(tmpdir(), "eukhe-sdk-")), bin: STUB, env: { STUB_MODE: mode } });
}

async function collect(events: AsyncIterable<EukheEvent>): Promise<EukheEvent[]> {
  const seen: EukheEvent[] = [];
  for await (const event of events) seen.push(event);
  return seen;
}

test("a missing binary is NotInstalled, naming the install command", async () => {
  const missing = join(tmpdir(), "no-such-dir", "eukhe");
  await assert.rejects(Eukhe.start({ cwd: tmpdir(), bin: missing }), (error: unknown) => {
    assert.ok(error instanceof NotInstalled);
    assert.equal(error.$, "NotInstalled");
    assert.deepEqual(error.searched, [missing]);
    assert.equal(error.installCommand, "npx eukhe install");
    return true;
  });
});

test("an empty PATH and install dir is NotInstalled", async () => {
  const empty = await mkdtemp(join(tmpdir(), "eukhe-empty-"));
  const saved = { path: process.env["PATH"], bin: process.env["EUKHE_BIN"], dir: process.env["EUKHE_INSTALL_BIN_DIR"] };
  process.env["PATH"] = empty;
  delete process.env["EUKHE_BIN"];
  process.env["EUKHE_INSTALL_BIN_DIR"] = empty;
  try {
    await assert.rejects(Eukhe.start({ cwd: tmpdir() }), NotInstalled);
  } finally {
    process.env["PATH"] = saved.path;
    if (saved.bin !== undefined) process.env["EUKHE_BIN"] = saved.bin;
    if (saved.dir === undefined) delete process.env["EUKHE_INSTALL_BIN_DIR"];
    else process.env["EUKHE_INSTALL_BIN_DIR"] = saved.dir;
  }
});

test("a plain ACP agent streams typed events and refuses eukhe extensions as Unsupported", async () => {
  const eukhe = await stub("plain");
  try {
    assert.deepEqual(eukhe.extensions, { $: "PlainAcp" });
    const session = await eukhe.session();
    const events = await collect(session.prompt("hi"));
    assert.deepEqual(events, [
      { $: "Thinking", text: "thinking" },
      { $: "Plan", entries: [{ content: "answer", priority: "high", status: "in_progress" }] },
      { $: "ToolCallStart", id: "t1", title: "python", kind: "execute", input: { code: "1+1" } },
      { $: "ToolCallUpdate", id: "t1", title: null, content: null, output: undefined },
      { $: "ToolCallEnd", id: "t1", outcome: "completed", content: null, output: "2" },
      { $: "Text", text: 'model=["faux","faux-1"]' },
      { $: "TurnEnd", stopReason: "end_turn" },
    ]);
    for (const call of [() => session.budget.get(), () => session.undo(), () => session.diff(), () => session.effects()]) {
      await assert.rejects(call(), (error: unknown) => error instanceof Unsupported);
    }
    await assert.rejects(session.acceptance.get(), (error: unknown) => {
      assert.ok(error instanceof Unsupported);
      assert.equal(error.feature, "acceptance");
      return true;
    });
  } finally {
    await eukhe.close();
  }
});

test("session({model}) picks the model by provider/id and refuses an unknown one", async () => {
  const eukhe = await stub("plain");
  try {
    const session = await eukhe.session({ model: "faux/faux-2" });
    const text = (await collect(session.prompt("hi"))).flatMap((event) => (event.$ === "Text" ? [event.text] : []));
    assert.deepEqual(text, ['model=["faux","faux-2"]']);
    await assert.rejects(eukhe.session({ model: "faux/nope" }), (error: unknown) => {
      assert.ok(error instanceof UnknownModel);
      assert.deepEqual(error.available, ["faux/faux-1", "faux/faux-2"]);
      return true;
    });
  } finally {
    await eukhe.close();
  }
});

test("cancel ends the turn with TurnEnd cancelled, after its run report", async () => {
  const eukhe = await stub("eukhe");
  try {
    const session = await eukhe.session();
    const seen: EukheEvent[] = [];
    for await (const event of session.prompt("wait")) {
      seen.push(event);
      if (event.$ === "Text") await session.cancel();
    }
    assert.deepEqual(
      seen.slice(-2).map((event) => event.$),
      ["RunReport", "TurnEnd"],
    );
    assert.deepEqual(seen.at(-1), { $: "TurnEnd", stopReason: "cancelled" });
    const report = seen.at(-2);
    assert.ok(report?.$ === "RunReport");
    assert.equal(report.report.stopReason, "cancelled");
    assert.equal(report.report.answer, "done");
  } finally {
    await eukhe.close();
  }
});

test("leaving the loop early cancels the turn and frees the session", async () => {
  const eukhe = await stub("eukhe");
  try {
    const session = await eukhe.session();
    for await (const event of session.prompt("wait")) {
      if (event.$ === "Text") break;
    }
    const again = await collect(session.prompt("hi"));
    assert.deepEqual(again.at(-1), { $: "TurnEnd", stopReason: "end_turn" });
  } finally {
    await eukhe.close();
  }
});

test("a malformed run report fails the turn as AgentFailed and frees the session", async () => {
  const eukhe = await stub("eukhe");
  try {
    const session = await eukhe.session();
    await assert.rejects(collect(session.prompt("bad-report")), { $: "AgentFailed", method: "_eukhe/run_report" });
    const again = await collect(session.prompt("hi"));
    assert.deepEqual(again.at(-1), { $: "TurnEnd", stopReason: "end_turn" });
  } finally {
    await eukhe.close();
  }
});

test("eukhe extensions return parsed results and typed agent errors", async () => {
  const eukhe = await stub("eukhe");
  try {
    assert.equal(eukhe.extensions.$, "Eukhe");
    const session = await eukhe.session();
    assert.equal(await session.budget.get(), null);
    assert.deepEqual(await session.diff(), { diff: "", paths: [], skipped: [] });
    await assert.rejects(session.undo(), { $: "AgentFailed", code: -32603, data: { details: "nothing to undo", code: "nothing_to_undo" } });
    await assert.rejects(session.effects(), { $: "AgentFailed", method: "_eukhe/effects" });
    await assert.rejects(session.acceptance.get(), Unsupported);
  } finally {
    await eukhe.close();
  }
});

test("no provider login is NotLoggedIn with the login command", async () => {
  const eukhe = await stub("logged-out");
  try {
    await assert.rejects(eukhe.session(), (error: unknown) => {
      assert.ok(error instanceof NotLoggedIn);
      assert.deepEqual(error.login, {
        command: "eukhe",
        slashCommand: "/login",
        instructions: "Run eukhe in a terminal and type /login.",
      });
      return true;
    });
  } finally {
    await eukhe.close();
  }
});
