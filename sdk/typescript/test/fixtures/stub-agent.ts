#!/usr/bin/env node
/**
 * A scripted ACP agent the unit tests spawn in place of `eukhe acp`.
 * STUB_MODE: "plain" (no eukhe extensions), "eukhe" (advertises and serves
 * them), "logged-out" (session/new answers eukhe's auth error).
 * `--version` prints STUB_VERSION and exits, as eukhe prints its version.
 */
import { Readable, Writable } from "node:stream";

import { agent, ndJsonStream, PROTOCOL_VERSION, RequestError, type AgentContext } from "@agentclientprotocol/sdk";

if (process.argv.includes("--version")) {
  console.log(process.env["STUB_VERSION"] ?? "");
  process.exit(0);
}

const mode = process.env["STUB_MODE"] ?? "plain";
const SESSION = "stub-session";
const MODELS = ['["faux","faux-1"]', '["faux","faux-2"]'];
const state = { model: MODELS[0] ?? "", cancel: (): void => {} };

const report = {
  promptTurnId: 1,
  answer: "done",
  label: "unverified",
  certified: false,
  checks: [],
  ran: [],
  unknown: [],
  left: [],
};

function update(client: AgentContext, body: Record<string, unknown>): Promise<void> {
  return client.notify("session/update", { sessionId: SESSION, update: body });
}

const sessionParams = (params: unknown): { sessionId: string } => {
  if (typeof params === "object" && params !== null && "sessionId" in params && typeof params.sessionId === "string") {
    return { sessionId: params.sessionId };
  }
  throw RequestError.invalidParams(params);
};

const app = agent({ name: "stub" })
  .onRequest("initialize", () => ({
    protocolVersion: PROTOCOL_VERSION,
    agentCapabilities:
      mode === "eukhe"
        ? { _meta: { eukhe: { version: "1.0", features: ["run_report", "budget", "undo", "diff", "effects"] } } }
        : {},
    agentInfo: { name: "stub", version: "0.0.0" },
  }))
  .onRequest("session/new", () => {
    if (mode === "logged-out") {
      throw new RequestError(-32000, "Authentication required", {
        login: { command: "eukhe", slashCommand: "/login", instructions: "Run eukhe in a terminal and type /login." },
      });
    }
    return {
      sessionId: SESSION,
      configOptions: [
        {
          id: "model",
          name: "Model",
          type: "select",
          currentValue: state.model,
          options: MODELS.map((value) => ({ value, name: value })),
        },
      ],
    };
  })
  .onRequest("session/set_config_option", ({ params }) => {
    if ("type" in params || !MODELS.includes(params.value)) throw RequestError.invalidParams(params);
    state.model = params.value;
    return { configOptions: [] };
  })
  .onRequest("session/prompt", async ({ params, client }) => {
    const text = params.prompt.flatMap((block) => (block.type === "text" ? [block.text] : [])).join("");
    await update(client, { sessionUpdate: "agent_thought_chunk", content: { type: "text", text: "thinking" } });
    await update(client, { sessionUpdate: "plan", entries: [{ content: "answer", priority: "high", status: "in_progress" }] });
    await update(client, { sessionUpdate: "tool_call", toolCallId: "t1", title: "python", kind: "execute", status: "pending", rawInput: { code: "1+1" } });
    await update(client, { sessionUpdate: "tool_call_update", toolCallId: "t1", status: "in_progress" });
    await update(client, { sessionUpdate: "tool_call_update", toolCallId: "t1", status: "completed", rawOutput: "2" });
    await update(client, { sessionUpdate: "agent_message_chunk", content: { type: "text", text: `model=${state.model}` } });
    const stopReason = text === "wait" ? await cancelled() : "end_turn";
    if (mode === "eukhe") {
      const sent = text === "bad-report" ? { sessionId: SESSION, stopReason } : { sessionId: SESSION, stopReason, ...report };
      await client.notify("_eukhe/run_report", sent);
    }
    return { stopReason };
  })
  .onNotification("session/cancel", () => state.cancel())
  .onRequest("_eukhe/budget/get", sessionParams, () => ({ budget: null }))
  .onRequest("_eukhe/diff", sessionParams, () => ({ diff: "", paths: [], skipped: [] }))
  .onRequest("_eukhe/undo", sessionParams, () => {
    throw new RequestError(-32603, "Internal error", { details: "nothing to undo", code: "nothing_to_undo" });
  })
  .onRequest("_eukhe/effects", sessionParams, () => ({ ran: [], unknown: "not a list" }));

function cancelled(): Promise<"cancelled"> {
  const { promise, resolve } = Promise.withResolvers<"cancelled">();
  state.cancel = () => resolve("cancelled");
  return promise;
}

app.connect(ndJsonStream(Writable.toWeb(process.stdout), Readable.toWeb(process.stdin)));
