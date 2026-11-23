/**
 * The SDK against the real `eukhe acp` on the scripted faux provider (no
 * network). Runs when EUKHE_E2E_BIN names a built eukhe; set
 * EUKHE_KERNEL_PYTHON to the test kernel interpreter so sessions skip the
 * kernel download. Each test owns a sandboxed HOME and daemon socket and
 * stops that daemon when it ends.
 */
import assert from "node:assert/strict";
import { mkdtemp, writeFile } from "node:fs/promises";
import { connect } from "node:net";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { createInterface } from "node:readline";
import { test, type TestContext } from "node:test";

import { Eukhe, NotLoggedIn, type EukheEvent } from "../src/index.ts";

const BIN = process.env["EUKHE_E2E_BIN"];
const skip = BIN === undefined ? "EUKHE_E2E_BIN is not set" : false;

/** The daemon wire version the sandbox's shutdown frame speaks (eukhe-types DAEMON_PROTOCOL_VERSION). */
const DAEMON_PROTOCOL_VERSION = 7;

type Sandbox = { home: string; socket: string; env: Record<string, string> };

async function sandbox(t: TestContext, script: unknown): Promise<Sandbox> {
  const home = await mkdtemp(join(tmpdir(), "eukhe-sdk-e2e-"));
  const socket = join(home, "daemon.sock");
  const env: Record<string, string> = {
    HOME: home,
    EUKHE_DAEMON_SOCKET: socket,
    EUKHE_INTERNAL_WORKER_SUPERVISOR_LOST_EXIT_MS: "15000",
  };
  if (script !== null) {
    await writeFile(join(home, "script.json"), JSON.stringify(script));
    env["EUKHE_FAUX_SCRIPT"] = join(home, "script.json");
  }
  t.after(() => shutdownDaemon(socket));
  return { home, socket, env };
}

/** Stop the sandboxed supervisor (eukhe leaves its shared daemon running; a test owns its own). */
async function shutdownDaemon(socket: string): Promise<void> {
  const stream = connect(socket);
  const { promise: connected, resolve: opened, reject: refused } = Promise.withResolvers<boolean>();
  stream.once("connect", () => opened(true));
  stream.once("error", (error: NodeJS.ErrnoException) =>
    error.code === "ENOENT" || error.code === "ECONNREFUSED" ? opened(false) : refused(error),
  );
  if (!(await connected)) return;
  const id = "sdk-e2e-shutdown";
  stream.write(
    `${JSON.stringify({ type: "command", id, protocol: { name: "eukhe.daemon", version: DAEMON_PROTOCOL_VERSION }, command: { type: "shutdown" } })}\n`,
  );
  for await (const line of createInterface({ input: stream })) {
    const frame: unknown = JSON.parse(line);
    if (typeof frame === "object" && frame !== null && "id" in frame && frame.id === id) {
      assert.ok(!("error" in frame) || frame.error === undefined, `daemon shutdown refused: ${line}`);
      break;
    }
  }
  stream.destroy();
}

async function collect(events: AsyncIterable<EukheEvent>): Promise<EukheEvent[]> {
  const seen: EukheEvent[] = [];
  for await (const event of events) seen.push(event);
  return seen;
}

test("start, session, prompt with run report, cancel, close", { skip, timeout: 180_000 }, async (t) => {
  // Two tokens a second: the second answer is still streaming when the test cancels it.
  const box = await sandbox(t, {
    engine: "faux",
    tokensPerSecond: 2,
    responses: ["SDK-OK", "a slow answer that streams for a long while, one word after another, until cancelled"],
  });
  const eukhe = await Eukhe.start({ cwd: box.home, bin: BIN ?? "", env: box.env });
  try {
    assert.equal(eukhe.extensions.$, "Eukhe");
    const session = await eukhe.session();

    const first = await collect(session.prompt("Reply with exactly: SDK-OK"));
    const text = first.flatMap((event) => (event.$ === "Text" ? [event.text] : [])).join("");
    assert.equal(text, "SDK-OK");
    assert.deepEqual(first.at(-1), { $: "TurnEnd", stopReason: "end_turn" });
    const report = first.at(-2);
    assert.ok(report?.$ === "RunReport", `the turn ends with its run report: ${JSON.stringify(first)}`);
    assert.equal(report.report.stopReason, "end_turn");
    assert.equal(report.report.answer, "SDK-OK");
    assert.deepEqual(report.report.ran, []);

    const second: EukheEvent[] = [];
    for await (const event of session.prompt("Take your time.")) {
      second.push(event);
      if (event.$ === "Text" && second.filter((seen) => seen.$ === "Text").length === 1) await session.cancel();
    }
    assert.deepEqual(second.at(-1), { $: "TurnEnd", stopReason: "cancelled" });
    assert.ok(second.some((event) => event.$ === "RunReport" && event.report.stopReason === "cancelled"));

    const budget = await session.budget.get();
    assert.ok(budget === null || typeof budget.phase === "string");
    assert.deepEqual(await session.effects(), { ran: [], unknown: [] });
  } finally {
    await eukhe.close();
  }
});

test("no provider login is NotLoggedIn naming the login command", { skip, timeout: 120_000 }, async (t) => {
  const box = await sandbox(t, null);
  const eukhe = await Eukhe.start({ cwd: box.home, bin: BIN ?? "", env: box.env });
  try {
    await assert.rejects(eukhe.session(), (error: unknown) => {
      assert.ok(error instanceof NotLoggedIn, String(error));
      assert.equal(error.login.slashCommand, "/login");
      return true;
    });
  } finally {
    await eukhe.close();
  }
});
