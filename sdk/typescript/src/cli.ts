#!/usr/bin/env node
/**
 * `npx eukhe install [version]` installs the eukhe release; any other
 * arguments run the installed eukhe binary with them.
 */
import { spawn } from "node:child_process";
import { constants } from "node:os";

import { findEukhe } from "./discover.ts";
import { EukheError } from "./errors.ts";
import { install, InstallFailed } from "./install.ts";

const USAGE = `usage: eukhe install [version]   install the eukhe release (X.Y.Z; the newest by default)
       eukhe <args...>             run the installed eukhe with <args>`;

async function main(args: readonly string[]): Promise<number> {
  const [command, ...rest] = args;
  if (command === "install") {
    if (rest.some((arg) => arg === "-h" || arg === "--help")) {
      console.log(USAGE);
      return 0;
    }
    if (rest.length > 1) {
      console.error(USAGE);
      return 2;
    }
    await install({ ...(rest[0] === undefined ? {} : { version: rest[0] }), log: (line) => console.log(line) });
    return 0;
  }
  const bin = await findEukhe(undefined, process.env);
  const child = spawn(bin, args, { stdio: "inherit" });
  const { promise, resolve } = Promise.withResolvers<number>();
  child.once("exit", (code, signal) => resolve(code ?? 128 + (signal === null ? 0 : constants.signals[signal])));
  child.once("error", (error) => {
    console.error(`error: ${error.message}`);
    resolve(1);
  });
  return promise;
}

main(process.argv.slice(2)).then(
  (code) => {
    process.exitCode = code;
  },
  (error: unknown) => {
    if (error instanceof EukheError || error instanceof InstallFailed) console.error(`error: ${error.message}`);
    else console.error(error);
    process.exitCode = 1;
  },
);
