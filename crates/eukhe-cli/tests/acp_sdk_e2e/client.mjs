// The client side of the `eukhe acp` acceptance test (main.rs here runs it,
// one scenario per process): the real @agentclientprotocol/sdk client,
// pinned by package-lock.json, drives the real binary over stdio, and ajv
// checks every `_eukhe/` payload against docs/embed/eukhe-acp.schema.json.
// A failed assertion exits non-zero with its message.

import assert from "node:assert/strict";
import { execFileSync, spawn } from "node:child_process";
import { existsSync, readFileSync } from "node:fs";
import { writeFile } from "node:fs/promises";
import { join } from "node:path";
import { Readable, Writable } from "node:stream";

import * as acp from "@agentclientprotocol/sdk";
import Ajv2020Module from "ajv/dist/2020.js";

function env(name) {
  const value = process.env[name];
  assert.ok(value, `${name} is set`);
  return value;
}

const BIN = env("EUKHE_BIN");
const SOCKET = env("EUKHE_ACP_SOCKET");
const WORKSPACE = env("EUKHE_ACP_WORKSPACE");

// The SDK only logs a frame it cannot parse or a handler that failed:
// every such line fails the scenario.
const sdkErrors = [];
const consoleError = console.error.bind(console);
console.error = (...args) => {
  sdkErrors.push(args.map((arg) => (typeof arg === "string" ? arg : JSON.stringify(arg))).join(" "));
  consoleError(...args);
};

// What the scenario did and received, one short line each: printed when
// it fails or hangs.
const trace = [];
function note(line) {
  trace.push(line.length > 300 ? `${line.slice(0, 300)}...` : line);
}
process.on("exit", (code) => {
  if (code !== 0) {
    consoleError(`acp-sdk-e2e trace (last 60):\n${trace.slice(-60).join("\n")}`);
  }
});

// The scenario's deadline: a hang fails with this message, not nextest's kill.
setTimeout(() => {
  consoleError("acp-sdk-e2e: the scenario did not finish within 3 minutes");
  process.exit(2);
}, 180_000).unref();

const Ajv2020 = Ajv2020Module.default ?? Ajv2020Module;
const ajv = new Ajv2020({ allErrors: true });
const schema = JSON.parse(readFileSync(env("EUKHE_ACP_SCHEMA"), "utf8"));
ajv.addSchema(schema);

/** Assert `value` matches the schema at `pointer` (below `$defs`). */
function validate(pointer, value) {
  const check = ajv.getSchema(`${schema.$id}#/$defs/${pointer}`);
  assert.ok(check, `the schema defines ${pointer}`);
  assert.ok(check(value), `${pointer}: ${ajv.errorsText(check.errors)}\n${JSON.stringify(value)}`);
}

/** Assert a `_eukhe/` request's params or result matches its schema. */
function validateRequest(method, part, value) {
  validate(`requests/properties/${method.replaceAll("/", "~1")}/${part}`, value);
}

/** The error a promise rejects with. */
async function rejection(promise, what) {
  try {
    const value = await promise;
    assert.fail(`${what} succeeded: ${JSON.stringify(value)}`);
  } catch (error) {
    if (error instanceof assert.AssertionError) {
      throw error;
    }
    return error;
  }
}

/** One `eukhe acp` process on the sandbox daemon, scripted by `script` (none: no model). */
function startAgent(script) {
  const childEnv = { ...process.env };
  delete childEnv.EUKHE_FAUX_SCRIPT;
  if (script) {
    childEnv.EUKHE_FAUX_SCRIPT = script;
  }
  const child = spawn(BIN, ["acp", "--daemon-socket", SOCKET], {
    cwd: WORKSPACE,
    env: childEnv,
    stdio: ["pipe", "pipe", "inherit"],
  });
  const exited = new Promise((resolve) => child.once("exit", (code, signal) => resolve({ code, signal })));
  const stream = acp.ndJsonStream(Writable.toWeb(child.stdin), Readable.toWeb(child.stdout));
  return { child, stream, exited };
}

/** The connection's agent side, each request and its answer traced. */
function traced(agent) {
  return {
    async request(method, params) {
      note(`-> ${method} ${JSON.stringify(params)}`);
      try {
        const result = await agent.request(method, params);
        note(`=> ${method} ${JSON.stringify(result)}`);
        return result;
      } catch (error) {
        note(`=> ${method} error ${error.code} ${error.message} ${JSON.stringify(error.data)}`);
        throw error;
      }
    },
  };
}

/** Assertions that failed inside a handler (the SDK would only log them). */
const handlerFailures = [];
function guarded(what, handle) {
  return (context) => {
    note(`<- ${what} ${JSON.stringify(context.params)}`);
    try {
      return handle(context);
    } catch (error) {
      handlerFailures.push(`${what}: ${error.message}`);
      note(`!! ${what}: ${error.message}`);
      throw error;
    }
  };
}

/**
 * A client app recording what the agent sends: `session/update`s, the
 * permission questions (each allowed), and, when `extensions`, the
 * `_eukhe/` notifications, each checked against the schema.
 */
function recordingClient({ extensions, onUpdate = () => {} }) {
  const log = { updates: [], permissions: [], reports: [], infos: [] };
  const app = acp
    .client({ name: "eukhe-acp-sdk-e2e" })
    .onNotification(
      "session/update",
      guarded("session/update", ({ params }) => {
        log.updates.push(params);
        onUpdate(params);
      }),
    )
    .onRequest(
      "session/request_permission",
      guarded("session/request_permission", ({ params }) => {
        log.permissions.push(params);
        return { outcome: { outcome: "selected", optionId: "allow" } };
      }),
    );
  if (extensions) {
    app
      .onNotification(
        "_eukhe/run_report",
        (params) => params,
        guarded("_eukhe/run_report", ({ params }) => {
          validate("runReport", params);
          log.reports.push(params);
        }),
      )
      .onNotification(
        "_eukhe/session_info",
        (params) => params,
        guarded("_eukhe/session_info", ({ params }) => {
          validate("sessionInfo", params);
          log.infos.push(params);
        }),
      );
  }
  return { app, log };
}

async function initialize(agent, clientCapabilities = {}) {
  const init = await agent.request("initialize", {
    protocolVersion: acp.PROTOCOL_VERSION,
    clientCapabilities,
    clientInfo: { name: "eukhe-acp-sdk-e2e", version: "1.0.0" },
  });
  assert.equal(init.protocolVersion, 1);
  return init;
}

/** End the connection: EOF, then the process exits 0. */
async function stop({ connection, child, exited }) {
  connection.close();
  child.stdin.end();
  const exit = await exited;
  assert.deepEqual(exit, { code: 0, signal: null }, "the agent exits 0 at EOF");
}

const updatesOf = (log, sessionId, kind) =>
  log.updates
    .filter((notification) => notification.sessionId === sessionId)
    .map((notification) => notification.update)
    .filter((update) => update.sessionUpdate === kind);

const textOf = (update) =>
  (update.content ?? [])
    .map((item) => item.content?.text ?? "")
    .join("\n");

/**
 * The whole embedding flow: initialize, session/new, the `_eukhe/`
 * budget and acceptance set, a prompt whose bash calls stream and push,
 * the run report, effects, diff, undo, close; then a fresh process
 * resumes the session by id and answers the next prompt.
 */
async function full() {
  const bashStream = env("EUKHE_ACP_BASH_STREAM");
  const bashPush = env("EUKHE_ACP_BASH_PUSH");
  const gate = env("EUKHE_ACP_GATE");
  let opened = false;
  const first = startAgent(env("EUKHE_ACP_SCRIPT"));
  const { app, log } = recordingClient({
    extensions: true,
    // The streamed script waits on the gate: it opens once its first line
    // reached the client while the call still runs.
    onUpdate: ({ update }) => {
      if (
        !opened &&
        update.sessionUpdate === "tool_call_update" &&
        update.status === "in_progress" &&
        textOf(update).includes("streamed-one")
      ) {
        opened = true;
        writeFile(gate, "go\n").catch((error) => consoleError("the gate did not open", error));
      }
    },
  });
  const connection = app.connect(first.stream);
  const agent = traced(connection.agent);
  const init = await initialize(agent);
  const eukhe = init.agentCapabilities._meta.eukhe;
  validate("capability", eukhe);
  assert.deepEqual(
    [...eukhe.features].sort(),
    ["acceptance", "budget", "diff", "effects", "run_report", "session_info", "undo"],
  );
  assert.equal(init.agentCapabilities.loadSession, true);
  assert.deepEqual(Object.keys(init.agentCapabilities.sessionCapabilities).sort(), [
    "close",
    "delete",
    "list",
    "resume",
  ]);

  const { sessionId } = await agent.request("session/new", { cwd: WORKSPACE, mcpServers: [] });
  assert.ok(sessionId);
  const ext = async (method, params) => {
    validateRequest(method, "params", params);
    const result = await agent.request(method, params);
    validateRequest(method, "result", result);
    return result;
  };

  // The budget and the checks for the next run, set before it.
  assert.deepEqual(await ext("_eukhe/budget/get", { sessionId }), { budget: null });
  const set = await ext("_eukhe/budget/set", { sessionId, limits: { tokens: 500000 } });
  assert.equal(set.budget.next.limits.tokens, 500000, JSON.stringify(set));
  const added = await ext("_eukhe/budget/add", { sessionId, amounts: { tokens: 1000 } });
  assert.equal(added.budget.next.added.tokens, 1000, JSON.stringify(added));
  await ext("_eukhe/acceptance/get", { sessionId });
  const acceptance = await ext("_eukhe/acceptance/set", {
    sessionId,
    checks: [{ kind: "command", command: "test -f note.txt" }],
    intent: false,
  });
  assert.equal(acceptance.acceptance.checks.length, 1, JSON.stringify(acceptance));

  const response = await agent.request("session/prompt", {
    sessionId,
    prompt: [{ type: "text", text: "write the note, then push" }],
  });
  assert.equal(response.stopReason, "end_turn");

  // The run report came before the response.
  assert.equal(log.reports.length, 1, JSON.stringify(log.reports));
  const report = log.reports[0];
  assert.equal(report.sessionId, sessionId);
  assert.equal(report.promptTurnId, 1);
  assert.equal(report.stopReason, "end_turn");
  assert.equal(report.answer, "Done: the note is written and pushed.");
  assert.equal(report.checks.length, 1, JSON.stringify(report));
  assert.equal(report.checks[0].kind, "command");
  assert.equal(report.checks[0].verdict, "confirmed", JSON.stringify(report));
  assert.equal(report.ran.length, 1, `the turn's one irreversible effect: ${JSON.stringify(report)}`);
  assert.ok(report.ran[0].command.includes("git push"), JSON.stringify(report.ran));
  assert.ok(report.ran[0].classes.includes("net"), JSON.stringify(report.ran));
  assert.deepEqual(report.unknown, []);
  assert.ok(log.infos.length > 0, "eukhe-only state rides _eukhe/session_info");
  assert.ok(
    log.updates.every(({ update }) => update._meta?.["com.eukhe"]?.budget === undefined),
    "no eukhe-only state rides session/update",
  );

  // The bash calls: their command as rawInput, the first one's output
  // streamed while it ran, the push asked and allowed.
  const calls = updatesOf(log, sessionId, "tool_call");
  assert.equal(calls.length, 2, JSON.stringify(calls));
  assert.equal(calls[0].rawInput.command, bashStream);
  assert.equal(calls[1].rawInput.command, bashPush);
  for (const call of calls) {
    assert.equal(call.kind, "execute");
    assert.ok(call.title, JSON.stringify(call));
  }
  const ofFirst = updatesOf(log, sessionId, "tool_call_update").filter(
    (update) => update.toolCallId === calls[0].toolCallId,
  );
  const streamed = ofFirst.find((update) => update.status === "in_progress" && textOf(update).includes("streamed-one"));
  assert.ok(streamed, `the output streamed while the call ran: ${JSON.stringify(ofFirst)}`);
  assert.ok(!textOf(streamed).includes("streamed-two"), "the streamed part came before the gate");
  const completed = ofFirst.find((update) => update.status === "completed");
  assert.ok(completed && textOf(completed).includes("streamed-two"), JSON.stringify(ofFirst));
  assert.equal(log.permissions.length, 1, JSON.stringify(log.permissions));
  assert.equal(log.permissions[0].toolCall.toolCallId, calls[1].toolCallId);
  execFileSync("git", ["--git-dir", "remote.git", "rev-parse", "--quiet", "--verify", "refs/heads/main"], {
    cwd: WORKSPACE,
  });

  // The acceptance check as a plan, completed once confirmed; the usage
  // and the commands a prompt may start with.
  const plans = updatesOf(log, sessionId, "plan");
  assert.ok(plans.length > 0, "the checks show as a plan");
  assert.deepEqual(
    plans.at(-1).entries.map((entry) => entry.status),
    ["completed"],
    JSON.stringify(plans),
  );
  assert.ok(updatesOf(log, sessionId, "usage_update").length > 0, "usage_update");
  assert.ok(updatesOf(log, sessionId, "available_commands_update").length > 0, "available_commands_update");

  // The effects ledger holds the report's effect; the turn's diff the
  // note; undo restores the note and names the push it cannot undo.
  const effects = await ext("_eukhe/effects", { sessionId });
  assert.deepEqual(
    effects.ran.map((effect) => effect.id),
    report.ran.map((effect) => effect.id),
  );
  const diff = await ext("_eukhe/diff", { sessionId, scope: "turn" });
  assert.ok(diff.paths.includes("note.txt"), JSON.stringify(diff));
  assert.ok(diff.diff.includes("+hello"), diff.diff);
  const budget = await ext("_eukhe/budget/get", { sessionId });
  assert.equal(budget.budget.limits.tokens, 501000, "the set limit plus the added tokens");
  assert.ok(budget.budget.spent.requests >= 1, JSON.stringify(budget));
  // The run's verdict stays on the check; the live label is the next
  // run's and starts over (`unverified`), the run's is in its report.
  const checks = await ext("_eukhe/acceptance/get", { sessionId });
  assert.equal(checks.acceptance.checks[0].result.verdict, "confirmed", JSON.stringify(checks));
  assert.equal(report.label, "checks_passed_not_certified");
  const undo = await ext("_eukhe/undo", { sessionId });
  assert.ok(undo.restored.includes("note.txt"), JSON.stringify(undo));
  assert.deepEqual(
    undo.notUndone.map((effect) => effect.id),
    report.ran.map((effect) => effect.id),
  );
  assert.ok(!existsSync(join(WORKSPACE, "note.txt")), "undo removed the note");

  // Errors: an unknown extension, bad params, an unknown session.
  const unknown = await rejection(agent.request("_eukhe/nothing", { sessionId }), "_eukhe/nothing");
  assert.equal(unknown.code, -32601);
  const bad = await rejection(agent.request("_eukhe/budget/set", { sessionId }), "budget/set without limits");
  assert.equal(bad.code, -32602);
  const missing = await rejection(
    agent.request("_eukhe/budget/get", { sessionId: "no-such-session" }),
    "budget/get of an unknown session",
  );
  assert.equal(missing.code, -32002);
  assert.deepEqual(missing.data, { sessionId: "no-such-session" });

  // The undone note would fail the check on the next run: clear it.
  const cleared = await ext("_eukhe/acceptance/set", { sessionId, checks: [], intent: false });
  assert.deepEqual(cleared.acceptance.checks, []);
  assert.deepEqual(await agent.request("session/close", { sessionId }), {});
  await stop({ connection, ...first });

  // A fresh process resumes the session by id and answers the next prompt.
  const second = startAgent(env("EUKHE_ACP_RESUME_SCRIPT"));
  const resumed = recordingClient({ extensions: true });
  const reconnection = resumed.app.connect(second.stream);
  const again = traced(reconnection.agent);
  await initialize(again);
  const listed = await again.request("session/list", { cwd: WORKSPACE });
  assert.ok(
    listed.sessions.some((session) => session.sessionId === sessionId),
    JSON.stringify(listed),
  );
  await again.request("session/resume", { sessionId, cwd: WORKSPACE, mcpServers: [] });
  const question = "are you still there?";
  const next = await again.request("session/prompt", {
    sessionId,
    prompt: [{ type: "text", text: question }],
  });
  assert.equal(next.stopReason, "end_turn");
  assert.equal(resumed.log.reports.length, 1);
  assert.equal(resumed.log.reports[0].sessionId, sessionId);
  // The scripted answer echoes the user text the model got: the resumed
  // history's first prompt (with the budget's note), then this one.
  const echoed = resumed.log.reports[0].answer;
  assert.ok(echoed.startsWith("write the note, then push") && echoed.endsWith(question), echoed);
  assert.deepEqual(await again.request("session/close", { sessionId }), {});
  await stop({ connection: reconnection, ...second });
}

/** A plain ACP client handles no `_eukhe/` method and still runs a turn. */
async function plain() {
  const agentProcess = startAgent(env("EUKHE_ACP_SCRIPT"));
  const { app, log } = recordingClient({ extensions: false });
  const connection = app.connect(agentProcess.stream);
  const agent = traced(connection.agent);
  await initialize(agent);
  const { sessionId } = await agent.request("session/new", { cwd: WORKSPACE, mcpServers: [] });
  const response = await agent.request("session/prompt", {
    sessionId,
    prompt: [{ type: "text", text: "hello" }],
  });
  assert.equal(response.stopReason, "end_turn");
  const said = updatesOf(log, sessionId, "agent_message_chunk")
    .map((update) => update.content.text)
    .join("");
  assert.equal(said, "plain answer");
  assert.deepEqual(await agent.request("session/close", { sessionId }), {});
  await stop({ connection, ...agentProcess });
}

/** No model provider logged in: the session start asks for a login. */
async function noLogin() {
  const agentProcess = startAgent(null);
  const { app } = recordingClient({ extensions: true });
  const connection = app.connect(agentProcess.stream);
  const agent = traced(connection.agent);
  const init = await initialize(agent, { auth: { terminal: true } });
  assert.deepEqual(
    init.authMethods.map((method) => method.id),
    ["eukhe-login", "eukhe-terminal-login"],
  );
  const refused = await rejection(
    agent.request("session/new", { cwd: WORKSPACE, mcpServers: [] }),
    "session/new without a login",
  );
  assert.equal(refused.code, -32000, String(refused));
  validate("authRequiredData", refused.data);
  assert.equal(refused.data.login.command, "eukhe login <provider>");
  assert.equal(refused.data.login.slashCommand, "/login");
  assert.deepEqual(
    refused.data.authMethods.map((method) => method.id),
    ["eukhe-login", "eukhe-terminal-login"],
  );
  const unauthenticated = await rejection(
    agent.request("authenticate", { methodId: "eukhe-login" }),
    "authenticate without a login",
  );
  assert.equal(unauthenticated.code, -32000);
  validate("authRequiredData", unauthenticated.data);
  const unknown = await rejection(agent.request("authenticate", { methodId: "nope" }), "an unknown auth method");
  assert.equal(unknown.code, -32602);
  await stop({ connection, ...agentProcess });
}

const scenarios = { full, plain, "no-login": noLogin };
const name = process.argv[2];
assert.ok(scenarios[name], `a scenario: ${Object.keys(scenarios).join(", ")}`);
await scenarios[name]();
assert.deepEqual(handlerFailures, [], "every handler's checks held");
assert.deepEqual(sdkErrors, [], "the SDK reported no invalid frame and no failed handler");
console.log(`ok ${name}`);
