import { constants } from "node:fs";
import { access, realpath, stat } from "node:fs/promises";
import { homedir } from "node:os";
import { delimiter, join } from "node:path";
import { fileURLToPath } from "node:url";

import { NotInstalled } from "./errors.ts";

/** The environment the binary is looked up in (process.env by default). */
export type Env = Readonly<Record<string, string | undefined>>;

/** Where the binary was looked for, in order. */
type Candidate =
  | { $: "Explicit"; path: string }
  | { $: "Path"; path: string }
  | { $: "Installed"; path: string };

/**
 * The eukhe binary: `bin` (or EUKHE_BIN) when given, else the first `eukhe`
 * on PATH, else the release launcher in ~/.local/bin (EUKHE_INSTALL_BIN_DIR).
 * Throws {@link NotInstalled} naming every place it looked.
 */
export async function findEukhe(bin: string | undefined, env: Env): Promise<string> {
  const candidates = candidatesOf(bin, env);
  const self = await ownLauncher();
  for (const candidate of candidates) {
    if (await isUsable(candidate, self)) return candidate.path;
  }
  throw new NotInstalled(candidates.map((candidate) => candidate.path));
}

/** The release launcher path install writes: `<bin dir>/eukhe`. */
export function installedLauncher(env: Env): string {
  return join(env["EUKHE_INSTALL_BIN_DIR"] ?? join(homedir(), ".local", "bin"), "eukhe");
}

function candidatesOf(bin: string | undefined, env: Env): readonly Candidate[] {
  const fromEnv = env["EUKHE_BIN"];
  const explicit = bin ?? (fromEnv === undefined || fromEnv === "" ? undefined : fromEnv);
  if (explicit !== undefined) return [{ $: "Explicit", path: explicit }];
  const onPath = (env["PATH"] ?? "")
    .split(delimiter)
    .filter((dir) => dir !== "")
    .map((dir): Candidate => ({ $: "Path", path: join(dir, "eukhe") }));
  return [...onPath, { $: "Installed", path: installedLauncher(env) }];
}

/** An executable file; a PATH entry is skipped when it is this package's own `eukhe` bin. */
async function isUsable(candidate: Candidate, self: string): Promise<boolean> {
  if (!(await isExecutableFile(candidate.path))) return false;
  switch (candidate.$) {
    case "Explicit":
    case "Installed":
      return true;
    case "Path":
      return (await realpath(candidate.path)) !== self;
    default: {
      const _: never = candidate;
      return _;
    }
  }
}

async function isExecutableFile(path: string): Promise<boolean> {
  try {
    await access(path, constants.X_OK);
    return (await stat(path)).isFile();
  } catch {
    return false;
  }
}

/** This package's `eukhe` bin (npm links node_modules/.bin/eukhe to it). */
async function ownLauncher(): Promise<string> {
  const path = fileURLToPath(new URL("./cli.js", import.meta.url));
  try {
    return await realpath(path);
  } catch {
    return path;
  }
}
