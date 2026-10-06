# eukhe

eukhe is a coding agent with one endless chat as its memory.

eukhe is a fork of [Prime Agent](https://github.com/PrimeIntellect-ai/prime-agent)
by Prime Intellect. It is not affiliated with Prime Intellect or Victor Taelin.
Upstream remote: `upstream`. See [Attribution](#attribution).

## Changes from Prime Agent

- Memory: the [OptChat](https://gist.github.com/VictorTaelin/91837951a5ce5b38f341ec1ba1df6449)
  chat log is the default memory. Each root turn starts from the chat view.
  The daemon owns the log and runs the compactor.
- Name: binary `eukhe`, crates `eukhe-*`, env vars `EUKHE_*`, state in
  `~/.eukhe`. eukhe and Prime Agent can run on one machine. They do not share
  state.
- Install: Nix flake and Home Manager module. No install scripts.
- Update: through Nix. `eukhe update` does not download.
- Prompt cache: breakpoints on text blocks.

## Install

Run once:

```sh
nix run github:gildrb/eukhe
```

Home Manager:

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

Build from source:

```sh
cargo build --release --locked -p eukhe-cli
```

## Usage

```sh
cd /path/to/project
eukhe                      # start; run /login on first launch
eukhe agents               # list running, idle, and saved sessions
eukhe attach <agent>       # attach to a running session
eukhe --resume [path|id]   # resume a session
eukhe chat view            # show the memory view
eukhe chat status [--json] # show the chat log state
eukhe chat browse          # browse the chat log
eukhe chat import optmem [<memory-dir>]
eukhe chat import sessions <path>...
eukhe status               # show daemon state
eukhe doctor [--fix]       # check or repair the daemon
eukhe shutdown [--force]   # stop all agents and the daemon
```

After an upgrade, the next `eukhe` start replaces an idle daemon of another
version, or a pre-rename `prime-agent` daemon on the socket. A daemon with
active work keeps running until the next idle start; `eukhe shutdown`
restarts it sooner. Sessions persist and reattach.

> [!WARNING]
> eukhe runs model-generated Python and shell commands with your user
> permissions. It is not a sandbox. Use trusted repositories only.

## Develop

```sh
make check   # fmt, clippy, tests
```

Run tests with a clean environment. Inherited `EUKHE_*` variables point
test daemons at real state:

```sh
env -i HOME="$HOME" PATH="$PATH" USER="$USER" LANG="$LANG" cargo test --workspace
```

## Attribution

- [Prime Intellect](https://www.primeintellect.ai): Prime Agent, the code
  base of eukhe. Copyright (c) 2025-2026 Prime Intellect Ltd., MIT.
- [Mario Zechner](https://github.com/badlogic): the original code of the
  Prime Agent TypeScript product, which eukhe ports. Copyright (c) 2025 Mario
  Zechner, MIT.
- [Victor Taelin](https://github.com/VictorTaelin): the chat memory design,
  [OptChat](https://gist.github.com/VictorTaelin/91837951a5ce5b38f341ec1ba1df6449),
  and its predecessor [OptMem](https://github.com/VictorTaelin/OptMem). The
  memory prompts come from the OptChat specification.

## License

MIT. See [LICENSE](LICENSE). Prime Agent copyright stays with Prime
Intellect Ltd. and Mario Zechner.
