# Updates

`eukhe update` installs the newest release. An interactive start of an install made by the install command (`curl -fsSL https://eukhe.com/install | sh`) checks for a newer release in the background, downloads it and checks it as `eukhe update` does, and unpacks it beside the install. The running version stays in use until `/restart`.

- `/restart to apply the downloaded update` shows once in the session when the download is done.
- `/restart` switches the install to the new version and reopens the session on it. With no download waiting, it starts the same version again.
- The background service moves to the new version when no session holds work. A service with running work keeps running it: the session restarts on the new version when that version can attach to the service, else it stays on the running version and says to `/restart` once the work finishes. A later start moves the service once it is idle.
- `/restart` works in the terminal and in `eukhe gateway` (from the phone).

## What is not checked

- Installs another tool manages (Nix, Home Manager, mise, an app bundle, a cargo build) and installs this user cannot write: update them with their own tool or with `eukhe update`, which names the command.
- CI runs (`CI` set), offline mode (`--offline`, `EUKHE_OFFLINE=1`), and `eukhe -p`, `--mode json`, `--mode rpc` and the daemon alone.

## Turn the download off

In `~/.eukhe/settings.json`:

```json
{ "update": { "autoDownload": false } }
```
