# Install

## curl

macOS (Apple Silicon), Linux (x64, arm64). No root.

```sh
curl -fsSL https://eukhe.com/install | sh               # install, or update in place
curl -fsSL https://eukhe.com/install | sh -s -- 0.10.41 # pin a version
```

- Payload `~/.local/share/eukhe/eukhe-<version>`, launcher `~/.local/bin/eukhe`; move with `EUKHE_INSTALL_ROOT`, `EUKHE_INSTALL_BIN_DIR`.
- Verifies against the release `SHA256SUMS` and, for the newest release, the hash pinned in `nix/release.json`.
- Update keeps the previous payload for running daemons, prunes older ones.
- Uninstall: `eukhe shutdown`, remove both paths.
- Warns if `uv` (kernel) or `git` (chat memory) is missing; the Nix package supplies both.
- `https://eukhe.com/install` 302-redirects to `releases/latest/download/install.sh`: the installer CI released with the newest release, never untested `main`. `https://eukhe.com/` redirects the same for non-HTML clients (`curl`, `wget`); browsers get the eukhe page. Served by Cloudflare Worker `gildrb-products` (repo `gildrb/gildrb.com`, `worker/products.ts`). `curl -L` follows.

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

- `programs.eukhe.settings` → `~/.eukhe/settings.json`, copied at each activation.
- `programs.eukhe.files` links files into `~/.eukhe`.

## mise

Newest GitHub release. eukhe tags: `eukhe-v<version>`; upstream `v*` tags also exist.

```toml
[tools]
"github:gildrb/eukhe" = { version = "latest", version_prefix = "eukhe-v" }
```

## Source

```sh
cargo build --release --locked -p eukhe-cli  # eukhe --version reports <series>-dev, e.g. 0.10.0-dev; only a release reports a release version
```

## Versions and the daemon

- Build id: `<version>+<commit>`, plus `.dirty.<hash>` (hash of changes) if sources differ from the commit; `<version>+src.<hash>` (hash of sources) with no commit. Different sources never share an id.
- Order: semver for releases; `-dev` is below its series' releases.
- After an upgrade, the next interactive `eukhe` start replaces an idle lower-version daemon, or a pre-rename `prime-agent` daemon on the socket.
- Background clients (`eukhe dashboard`, `eukhe gateway`, ACP) never replace a daemon.
- No client replaces a newer daemon or another build of the same version; it tells you. `eukhe shutdown` stops the daemon.
- A busy daemon runs until the next idle start. Sessions persist and reattach.
