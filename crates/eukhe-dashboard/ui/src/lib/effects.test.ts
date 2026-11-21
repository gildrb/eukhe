// The composer's own command: `/effects` runs in the dashboard; other
// words after it answer the usage line; any other text goes to the agent.

import { expect, test } from "vite-plus/test";
import { parseCommand } from "./effects.ts";

test("the composer runs /effects itself", () => {
  expect(["/effects", " /effects ", "/effects x", "/compact", "effects"].map(parseCommand)).toEqual(
    [
      { name: "effects" },
      { name: "effects" },
      { name: "usage", text: "Usage: /effects" },
      null,
      null,
    ],
  );
});
