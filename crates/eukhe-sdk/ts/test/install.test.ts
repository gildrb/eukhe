import assert from "node:assert/strict";
import { execFile } from "node:child_process";
import { createHash } from "node:crypto";
import { chmod, mkdir, mkdtemp, readFile, readdir, writeFile } from "node:fs/promises";
import { createServer, type Server } from "node:http";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { test } from "node:test";
import { promisify } from "node:util";

import { install, InstallFailed, platformAlias } from "../src/install.ts";

const run = promisify(execFile);
const alias = platformAlias(process.platform, process.arch);

/** A release archive whose `eukhe` prints `reports`, packed as the release workflow does. */
async function release(reports: string): Promise<Buffer> {
  const dir = await mkdtemp(join(tmpdir(), "eukhe-release-"));
  await writeFile(join(dir, "eukhe"), `#!/bin/sh\necho ${reports}\n`);
  await chmod(join(dir, "eukhe"), 0o755);
  await mkdir(join(dir, "rlm"));
  const archive = join(dir, "release.tar.gz");
  await run("tar", ["-czf", archive, "-C", dir, "eukhe", "rlm"]);
  return readFile(archive);
}

/** Serve `files` (path → body) on a local port. */
async function serve(files: ReadonlyMap<string, Buffer | string>): Promise<{ server: Server; base: string }> {
  const server = createServer((request, response) => {
    const body = files.get(request.url ?? "");
    response.writeHead(body === undefined ? 404 : 200).end(body);
  });
  const { promise, resolve } = Promise.withResolvers<void>();
  server.listen(0, "127.0.0.1", resolve);
  await promise;
  const address = server.address();
  assert.ok(address !== null && typeof address === "object");
  return { server, base: `http://127.0.0.1:${address.port}` };
}

function sha256(body: Buffer, encoding: "hex" | "base64"): string {
  return createHash("sha256").update(body).digest(encoding);
}

async function scenario(options: { reports: string; sumsHash?: string; pinHash?: string }) {
  const version = "9.9.9";
  const tarball = `eukhe-${version}-${alias}.tar.gz`;
  const archive = await release(options.reports);
  const sums = `${options.sumsHash ?? sha256(archive, "hex")}  ${tarball}\n`;
  const pin = JSON.stringify({
    version,
    assets: { here: { url: `https://example.invalid/${tarball}`, hash: options.pinHash ?? `sha256-${sha256(archive, "base64")}` } },
  });
  const { server, base } = await serve(
    new Map<string, Buffer | string>([
      ["/releases/latest/download/SHA256SUMS", sums],
      [`/releases/download/eukhe-v${version}/SHA256SUMS`, sums],
      [`/releases/download/eukhe-v${version}/${tarball}`, archive],
      ["/release.json", pin],
    ]),
  );
  const home = await mkdtemp(join(tmpdir(), "eukhe-home-"));
  const env = { EUKHE_INSTALL_ROOT: join(home, "share"), EUKHE_INSTALL_BIN_DIR: join(home, "bin") };
  return { server, env, home, source: { releases: `${base}/releases`, pin: `${base}/release.json` } };
}

test("install unpacks the newest release and writes a working launcher", async () => {
  const { server, env, home, source } = await scenario({ reports: "9.9.9" });
  try {
    const installed = await install({ env, source });
    assert.deepEqual(installed, {
      version: "9.9.9",
      payload: join(home, "share", "eukhe-9.9.9"),
      launcher: join(home, "bin", "eukhe"),
    });
    const { stdout } = await run(installed.launcher, ["--version"]);
    assert.equal(stdout.trim(), "9.9.9");
    assert.deepEqual((await readdir(join(home, "share"))).sort(), ["eukhe-9.9.9"]);
  } finally {
    server.close();
  }
});

test("install refuses an archive that differs from SHA256SUMS", async () => {
  const { server, env, source } = await scenario({ reports: "9.9.9", sumsHash: "0".repeat(64) });
  try {
    await assert.rejects(install({ env, source }), (error: unknown) => {
      assert.ok(error instanceof InstallFailed);
      assert.match(error.message, /checksum mismatch/);
      return true;
    });
  } finally {
    server.close();
  }
});

test("install refuses an archive that differs from the nix/release.json pin", async () => {
  const { server, env, source } = await scenario({ reports: "9.9.9", pinHash: "sha256-AAAA" });
  try {
    await assert.rejects(install({ env, source }), /hash differs from nix\/release.json/);
  } finally {
    server.close();
  }
});

test("install refuses a binary that reports another version", async () => {
  const { server, env, source } = await scenario({ reports: "1.0.0" });
  try {
    await assert.rejects(install({ env, source }), /binary reports '1.0.0', expected '9.9.9'/);
  } finally {
    server.close();
  }
});

test("install refuses a malformed version", async () => {
  await assert.rejects(install({ version: "latest" }), /not a release version/);
});
