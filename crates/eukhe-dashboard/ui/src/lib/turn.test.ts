// The live writing rate reads the daemon's count of the open reply's output
// tokens (`message_update.outputTokens`), never its character count.

import { expect, test } from "vite-plus/test";
import { liveRate, openSession, reduce } from "./turn.ts";
import type { Message, SessionEvent } from "./types.ts";

const reply = (text: string): Message => ({ role: "assistant", content: [{ type: "text", text }] });

const delta = (text: string, change: string, outputTokens?: number): SessionEvent => ({
  type: "message_update",
  message: reply(text),
  assistantMessageEvent: { type: "text_delta", delta: change },
  ...(outputTokens === undefined ? {} : { outputTokens }),
});

test("the live rate is the last count over the time from the first delta to it", () => {
  let session = openSession(
    {
      session: { id: "s", path: "/s" },
      state: null,
      summary: null,
      messages: null,
      cursor: null,
      replay: null,
    },
    null,
    0,
  );
  const events: [number, SessionEvent][] = [
    [0, { type: "agent_start" }],
    [10, { type: "message_start", message: reply(""), assistantMessageEvent: { type: "start" } }],
    [100, delta("Hel", "Hel", 1)],
    // An uncounted frame keeps the last count and its time.
    [400, delta("Hello, wor", "lo, wor")],
    [600, delta("Hello, world and more", "ld and more", 6)],
  ];
  const rates = events.map(([now, event]) => {
    session = reduce(session, event, now);
    return liveRate(session.turn);
  });
  // 6 tokens over the 500 ms from the first delta to their count.
  expect(rates).toEqual([null, null, null, null, 12]);
});
