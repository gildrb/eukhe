#!/usr/bin/env node
/**
 * Ask eukhe to do something in the current directory and print the turn.
 *   node examples/cli.ts "add a --verbose flag to the CLI"
 * Ctrl-C cancels the turn.
 */
import { Eukhe, EukheError } from "eukhe";

const prompt = process.argv.slice(2).join(" ");
if (prompt === "") {
  console.error('usage: node examples/cli.ts "<prompt>"');
  process.exit(2);
}

try {
  const eukhe = await Eukhe.start({ cwd: process.cwd() });
  try {
    const session = await eukhe.session();
    process.once("SIGINT", () => void session.cancel());
    for await (const event of session.prompt(prompt)) {
      switch (event.$) {
        case "Text":
          process.stdout.write(event.text);
          break;
        case "Thinking":
          break;
        case "ToolCallStart":
          console.error(`\n> ${event.title}`);
          break;
        case "ToolCallUpdate":
          break;
        case "ToolCallEnd":
          console.error(`< ${event.outcome}`);
          break;
        case "Plan":
          console.error(event.entries.map((entry) => `[${entry.status}] ${entry.content}`).join("\n"));
          break;
        case "RunReport":
          console.error(`\n${event.report.label}; irreversible effects: ${event.report.ran.length}`);
          break;
        case "TurnEnd":
          console.error(`(${event.stopReason})`);
          break;
        default: {
          const _: never = event;
          throw new Error(`unknown event ${JSON.stringify(_)}`);
        }
      }
    }
  } finally {
    await eukhe.close();
  }
} catch (error) {
  if (!(error instanceof EukheError)) throw error;
  switch (error.$) {
    case "NotInstalled":
      console.error(`eukhe is not installed; run: ${error.installCommand}`);
      break;
    case "TooOld":
      console.error(`eukhe ${error.found} is older than ${error.minimum}; run: ${error.updateCommand}`);
      break;
    case "NotLoggedIn":
      console.error(`eukhe has no model provider login; run: ${error.login.command}`);
      break;
    default:
      console.error(error.message);
  }
  process.exitCode = 1;
}
