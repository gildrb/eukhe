import { execFile } from "node:child_process";
import { createHash } from "node:crypto";
import { chmod, mkdir, mkdtemp, readdir, rename, rm, stat, writeFile } from "node:fs/promises";
import { homedir, tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { promisify } from "node:util";

import { z } from "zod";

import { installedLauncher, type Env } from "./discover.ts";

const run = promisify(execFile);

/** Where releases come from; tests point these at a local server. */
export type ReleaseSource = { releases: string; pin: string };

export const GITHUB: ReleaseSource = {
  releases: "https://github.com/gildrb/eukhe/releases",
  pin: "https://raw.githubusercontent.com/gildrb/eukhe/main/nix/release.json",
};

export type InstallOptions = {
  /** `X.Y.Z` (also `vX.Y.Z`, `eukhe-vX.Y.Z`); the newest release otherwise. */
  version?: string;
  env?: Env;
  source?: ReleaseSource;
  log?: (line: string) => void;
};

export type Installed = { version: string; payload: string; launcher: string };

/** A failed install step; the message says which. */
export class InstallFailed extends Error {
  readonly $ = "InstallFailed";
}

/**
 * Install an eukhe release the way install.sh does: download the archive for
 * this platform, check it against the release's SHA256SUMS (and the hash
 * pinned in nix/release.json for the newest release), unpack it to
 * ~/.local/share/eukhe/eukhe-<version> and write the ~/.local/bin/eukhe launcher.
 * Never uses root.
 */
export async function install(options: InstallOptions = {}): Promise<Installed> {
  const env = options.env ?? process.env;
  const source = options.source ?? GITHUB;
  const log = options.log ?? (() => {});
  const alias = platformAlias(process.platform, process.arch);
  const work = await mkdtemp(join(tmpdir(), "eukhe-install."));
  try {
    const sums = await sumsOf(source, options.version);
    const version = options.version === undefined ? newestVersion(sums, alias) : releaseVersion(options.version);
    const tarball = `eukhe-${version}-${alias}.tar.gz`;
    const expected = sums.get(tarball);
    if (expected === undefined) throw new InstallFailed(`${tarball} is not listed in SHA256SUMS`);
    const url = `${source.releases}/download/eukhe-v${version}/${tarball}`;
    log(`eukhe ${version} for ${alias}`);
    log(`downloading ${url}`);
    const archive = await download(url);
    const actual = createHash("sha256").update(archive).digest("hex");
    if (actual !== expected) {
      throw new InstallFailed(`checksum mismatch for ${tarball}\n  expected ${expected}\n  actual   ${actual}`);
    }
    await checkPin(source, version, tarball, archive, log);
    const archivePath = join(work, tarball);
    await writeFile(archivePath, archive);
    return await place(archivePath, version, env, log);
  } finally {
    await rm(work, { recursive: true, force: true });
  }
}

/** The release archive suffix of this platform (`darwin-arm64`, `linux-x64`, `linux-arm64`). */
export function platformAlias(platform: NodeJS.Platform, arch: string): string {
  if (platform === "linux" && arch === "x64") return "linux-x64";
  if (platform === "linux" && arch === "arm64") return "linux-arm64";
  if (platform === "darwin" && arch === "arm64") return "darwin-arm64";
  if (platform === "darwin") throw new InstallFailed(`no macOS build for '${arch}': eukhe is Apple Silicon only`);
  throw new InstallFailed(`unsupported platform ${platform}-${arch}: eukhe ships for Linux (x64, arm64) and macOS (arm64)`);
}

function releaseVersion(requested: string): string {
  const version = requested.replace(/^eukhe-v/, "").replace(/^v/, "");
  if (!/^\d+\.\d+\.\d+$/.test(version)) throw new InstallFailed(`not a release version: '${requested}' (expected X.Y.Z)`);
  return version;
}

/** SHA256SUMS of the requested release (the newest one by default), by file name. */
async function sumsOf(source: ReleaseSource, requested: string | undefined): Promise<ReadonlyMap<string, string>> {
  const url =
    requested === undefined
      ? `${source.releases}/latest/download/SHA256SUMS`
      : `${source.releases}/download/eukhe-v${releaseVersion(requested)}/SHA256SUMS`;
  const text = (await download(url)).toString("utf8");
  const sums = new Map<string, string>();
  for (const line of text.split("\n")) {
    const [hash, name] = line.trim().split(/\s+/);
    if (hash !== undefined && name !== undefined) sums.set(name.replace(/^\*/, ""), hash);
  }
  return sums;
}

/** The newest release's version: SHA256SUMS lists its archives by name. */
function newestVersion(sums: ReadonlyMap<string, string>, alias: string): string {
  const pattern = new RegExp(`^eukhe-(\\d+\\.\\d+\\.\\d+)-${alias}\\.tar\\.gz$`);
  for (const name of sums.keys()) {
    const version = pattern.exec(name)?.[1];
    if (version !== undefined) return version;
  }
  throw new InstallFailed(`the newest release lists no archive for ${alias}`);
}

async function download(url: string): Promise<Buffer> {
  const response = await fetch(url, { redirect: "follow" });
  if (!response.ok) throw new InstallFailed(`download failed (${response.status}): ${url}`);
  return Buffer.from(await response.arrayBuffer());
}

const Pin = z.object({
  version: z.string(),
  assets: z.record(z.string(), z.object({ url: z.string(), hash: z.string() })),
});

/** Cross-check the newest release against the hash nix/release.json pins on main. */
async function checkPin(
  source: ReleaseSource,
  version: string,
  tarball: string,
  archive: Buffer,
  log: (line: string) => void,
): Promise<void> {
  const pin = await readPin(source);
  if (pin === null) {
    log("warning: could not read nix/release.json: SHA256SUMS verification only");
    return;
  }
  if (pin.version !== version) {
    log(`pinned version ${version}: SHA256SUMS verified (nix/release.json holds ${pin.version})`);
    return;
  }
  const asset = Object.values(pin.assets).find((entry) => entry.url.endsWith(`/${tarball}`));
  if (asset === undefined) throw new InstallFailed(`nix/release.json ${version} has no hash for ${tarball}`);
  const actual = `sha256-${createHash("sha256").update(archive).digest("base64")}`;
  if (actual !== asset.hash) {
    throw new InstallFailed(`hash differs from nix/release.json on main\n  expected ${asset.hash}\n  actual   ${actual}`);
  }
  log("verified against SHA256SUMS and nix/release.json");
}

async function readPin(source: ReleaseSource): Promise<z.output<typeof Pin> | null> {
  try {
    const pin = Pin.safeParse(JSON.parse((await download(source.pin)).toString("utf8")));
    return pin.success ? pin.data : null;
  } catch {
    return null;
  }
}

/** Unpack, livecheck, move the payload in place, write the launcher, prune older payloads. */
async function place(archive: string, version: string, env: Env, log: (line: string) => void): Promise<Installed> {
  const root = env["EUKHE_INSTALL_ROOT"] ?? join(homedir(), ".local", "share", "eukhe");
  const launcher = installedLauncher(env);
  const payload = join(root, `eukhe-${version}`);
  const stage = join(root, `.stage-eukhe-${version}.${process.pid}`);
  await mkdir(stage, { recursive: true });
  await mkdir(dirname(launcher), { recursive: true });
  try {
    await run("tar", ["-xzf", archive, "-C", stage]);
    const reported = await versionOf(join(stage, "eukhe"));
    if (reported !== version) throw new InstallFailed(`binary reports '${reported}', expected '${version}'`);
    if ((await versionOf(join(payload, "eukhe")).catch(() => null)) === version) {
      log(`eukhe ${version} is already installed: kept ${payload}`);
    } else {
      await rm(payload, { recursive: true, force: true });
      await rename(stage, payload);
    }
  } finally {
    await rm(stage, { recursive: true, force: true });
  }
  const temporary = join(dirname(launcher), `.eukhe-installer.${process.pid}`);
  await writeFile(
    temporary,
    `#!/bin/sh\n# eukhe launcher written by install.sh; the payload sits beside itself\nexec "${payload}/eukhe" "$@"\n`,
  );
  await chmod(temporary, 0o755);
  await rename(temporary, launcher);
  await prune(root, payload);
  log(`installed eukhe ${version}\n  payload:  ${payload}\n  launcher: ${launcher}`);
  return { version, payload, launcher };
}

async function versionOf(binary: string): Promise<string> {
  try {
    return (await run(binary, ["--version"])).stdout.trim();
  } catch (error) {
    throw new InstallFailed(`${binary} does not run on this machine`, { cause: error });
  }
}

type Triple = [number, number, number];

/** Keep the current payload and the newest one before it (a daemon may still run from it). */
async function prune(root: string, current: string): Promise<void> {
  const older: { path: string; version: Triple }[] = [];
  for (const name of await readdir(root)) {
    const match = /^eukhe-(\d+)\.(\d+)\.(\d+)$/.exec(name);
    const path = join(root, name);
    if (match === null || path === current || !(await stat(path)).isDirectory()) continue;
    older.push({ path, version: [Number(match[1]), Number(match[2]), Number(match[3])] });
  }
  older.sort((a, b) => a.version[0] - b.version[0] || a.version[1] - b.version[1] || a.version[2] - b.version[2]);
  await Promise.all(older.slice(0, -1).map((entry) => rm(entry.path, { recursive: true, force: true })));
}
