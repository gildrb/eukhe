import { execFile } from "node:child_process";

import type { Env } from "./discover.ts";
import { MINIMUM_EUKHE_VERSION, NotInstalled, TooOld } from "./errors.ts";

/** How long `<bin> --version` may take (a version manager's shim resolves its tool first). */
const VERSION_TIMEOUT_MS = 10_000;

type Release = readonly [major: number, minor: number, patch: number];

const MINIMUM = releaseOf(MINIMUM_EUKHE_VERSION);

/**
 * Refuse an eukhe release older than {@link MINIMUM_EUKHE_VERSION} before
 * `acp` reaches it: an eukhe without the `acp` command takes it as a chat
 * prompt and spends a model request. `<bin> --version` runs in `cwd`, where
 * `eukhe acp` will, so a version manager's shim picks the same release.
 * Output that names no release (a source build's `X.Y.Z-dev`, another ACP
 * agent) passes.
 */
export async function requireMinimumVersion(bin: string, cwd: string, env: Env): Promise<void> {
  const reported = (await versionOutput(bin, cwd, env)).trim();
  const release = releaseOf(reported);
  if (release !== null && MINIMUM !== null && older(release, MINIMUM)) throw new TooOld(reported);
}

function versionOutput(bin: string, cwd: string, env: Env): Promise<string> {
  const { promise, resolve, reject } = Promise.withResolvers<string>();
  const child = execFile(
    bin,
    ["--version"],
    { cwd, env: { ...process.env, ...env }, timeout: VERSION_TIMEOUT_MS, encoding: "utf8" },
    (error, stdout) => {
      if (error === null) resolve(stdout);
      else if (error.code === "ENOENT" || error.code === "EACCES") reject(new NotInstalled([bin]));
      else resolve("");
    },
  );
  child.stdin?.end();
  return promise;
}

/** `X.Y.Z`, the version line of an eukhe release. */
function releaseOf(text: string): Release | null {
  const match = /^(\d+)\.(\d+)\.(\d+)$/.exec(text);
  if (match === null) return null;
  return [Number(match[1]), Number(match[2]), Number(match[3])];
}

function older(release: Release, than: Release): boolean {
  for (const [index, part] of release.entries()) {
    const other = than[index] ?? 0;
    if (part !== other) return part < other;
  }
  return false;
}
