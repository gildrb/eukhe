# Install

## curl

macOS (Apple Silicon), Linux (x64, arm64). No root.

```sh
curl -fsSL https://eukhe.com/install | sh
```

It installs the payload into `~/.local/share/eukhe/eukhe-<version>` and a
launcher into `~/.local/bin/eukhe`. It checks the download against the
release `SHA256SUMS` and, for the newest release, against the hash pinned
in `nix/release.json`. Re-running the command updates in place; it keeps
the previous payload for running daemons and prunes older ones. Pin a
version with `sh -s -- 0.10.41`; move the install with
`EUKHE_INSTALL_ROOT` and `EUKHE_INSTALL_BIN_DIR`. Uninstall:
`eukhe shutdown`, then remove those two paths.

`https://eukhe.com/install` redirects (302) to
`releases/latest/download/install.sh`. The installer that runs is the one
that CI released with the newest release, never an untested edit on `main`.
`https://eukhe.com/` gives the same redirect to a client that does not ask
for HTML (`curl`, `wget`); a browser gets the eukhe page. The Cloudflare
Worker `gildrb-products` (repository `gildrb/gildrb.com`, file
`worker/products.ts`) serves both redirects. `curl -L` follows the redirect.

The kernel needs `uv`, and the chat memory needs `git`; the installer
warns when either is missing. The Nix package supplies both.

## Nix

```sh
nix run github:gildrb/eukhe
```

## Home Manager

```nix
{
  inputs.eukhe.url = "github:gildrb/eukhe";

  # in the home configuration:
  imports = [ inputs.eukhe.homeManagerModules.default ];
  programs.eukhe = {
    enable = true;
    daemon.enable = true; # Linux: systemd user service
    settings.telemetry.enabled = false;
  };
}
```

`programs.eukhe.settings` is copied to `~/.eukhe/settings.json` at each
activation. `programs.eukhe.files` links files into `~/.eukhe`.

## mise

The newest GitHub release. eukhe tags are `eukhe-v<version>`. The
repository also holds the upstream `v*` tags.

```toml
[tools]
"github:gildrb/eukhe" = { version = "latest", version_prefix = "eukhe-v" }
```

## Source

```sh
cargo build --release --locked -p eukhe-cli
```

A source build reports `<series>-dev` (`eukhe --version`, for example
`0.10.0-dev`); only a release reports a release version.

## Versions and the daemon

Each daemon reports its build: `<version>+<commit>`, plus `.dirty.<hash>`
(a hash of the changes) when the sources differ from the commit, or
`<version>+src.<hash>` (a hash of the sources) when no commit is known, so
two builds of other sources never share a build. After an upgrade, the
next interactive `eukhe` start replaces an idle daemon of a lower
version, or a pre-rename `prime-agent` daemon on the socket. Release
versions have the semver order; a `-dev` build is below the releases of
its series. Background clients (`eukhe dashboard`, `eukhe gateway`, ACP)
never replace a running daemon. No client replaces a newer daemon or
another build of the same version; the client tells you, and
`eukhe shutdown` stops the daemon. A daemon with active work keeps
running until the next idle start. Sessions persist and reattach.
