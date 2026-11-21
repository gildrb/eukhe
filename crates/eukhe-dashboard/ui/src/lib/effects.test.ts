// The composer's own commands: `/effects`, `/undo` and `/diff [all]` run
// in the dashboard; other words after them answer the usage line; any
// other text goes to the agent.

import { expect, test } from "vite-plus/test";
import { parseCommand } from "./effects.ts";

test("the composer runs /effects, /undo and /diff itself", () => {
  expect(
    [
      "/effects",
      " /undo ",
      "/diff",
      "/diff ALL",
      "/diff all now",
      "/undo x",
      "/effects x",
      "/compact",
      "undo",
    ].map(parseCommand),
  ).toEqual([
    { name: "effects" },
    { name: "undo" },
    { name: "diff", all: false },
    { name: "diff", all: true },
    { name: "usage", text: "Usage: /diff [all]" },
    { name: "usage", text: "Usage: /undo" },
    { name: "usage", text: "Usage: /effects" },
    null,
    null,
  ]);
});
