# Factory: library, TUI and settings

The authoring reference and API guide is `rlm.factory.help()` in the kernel (`FACTORY_HELP` in `eukhe-runtime/src/rlm/factory.py`). This file covers what lives outside the kernel.

## The opt-in gate

- The factory ships disabled. While it is off, every `rlm.factory` call except `help()` and every factory harness write refuses with `the factory is disabled; run /factory on to enable it`.
- `/factory on` and `/factory off` in the client persist the `factory.enabled` setting in the agent dir's settings.json. `/factory status` reports it.
- `/factory off` is refused while the session has live runs, and on a client that advertises lanes while the live-run count cannot be read.
- The daemon's `factory_activity` lane reads the same setting, so the TUI factory dock group and page appear only on a client started while the factory is enabled: after `/factory on`, restart the client.

## The machine library

- A machine is a `MACHINE.md` file, one directory per machine: YAML frontmatter (name, description, version, author) and one fenced `machine-spec` block with the JSON spec.
- Bundled seeds ship in the runtime package (`rlm/machines/<name>/MACHINE.md`): `builder`, `pr-manager`, `review-sweep`. `EUKHE_MACHINES_DIR` points that level at a team directory.
- The personal library lives under the agent dir.
- `eukhe factory list | import | export` manages the library.

## The TUI factory page

- The activity dock's `⚙ N factory` group (Enter or click) opens one live diagram per run, newest first.
- Up and down move the selection; Enter opens the selected run's actions (stop, or resume while paused); Esc closes.
