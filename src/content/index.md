EUKHE
CODING AGENT WITH A MEMORY OF ALL THINGS
2026 (ΧΧΔΔΠΙ)

~*~ εὐχή: a wish, a prayer ~*~

# INSTALL

```sh
curl -fsSL https://eukhe.com/install | sh
```

macOS (Apple Silicon), Linux (x64, arm64). Rerun to update.

Source: [github.com/gildrb/eukhe](https://github.com/gildrb/eukhe).
MIT.

# ABOUT EUKHE

eukhe is a coding agent whose memory is one endless chat log, shared
by all sessions. No empty new session. No compaction drops the
start. Each turn starts from a compact view of the full log.

> γραμμάτων τε συνθέσεις, μνήμην ἁπάντων, μουσομήτορ᾽ ἐργάνην.
> And the joining of letters: memory of all things, the Muses'
> mother, a worker. (Aeschylus, Prometheus Bound 460-461)

## OTHER INSTALLS

- Nix: `nix run github:gildrb/eukhe`
- Home Manager: `programs.eukhe.enable = true;`
- From source: `cargo build --release --locked -p eukhe-cli`
- More:
  [docs/install.md](https://github.com/gildrb/eukhe/blob/bend/all/docs/install.md)

## USE

```sh
cd /path/to/project
eukhe            # start; run /login at the first start
eukhe agents     # find and open sessions
eukhe gateway    # connect Signal on your phone to the session
eukhe dashboard  # open the session in a browser
```

## MEMORY

> κτῆμά τε ἐς αἰεὶ μᾶλλον ἢ ἀγώνισμα
> ἐς τὸ παραχρῆμα ἀκούειν ξύγκειται.
> It is set down as a possession for all time, not a piece to be
> heard for the moment. (Thucydides 1.22.4)

- Log: `~/.eukhe/chat/`, append-only.
- The compactor writes one-line summaries into a binary tree over
  the log.
- Each turn starts from the view: 64 KB to 128 KB of lines.
- `/memory`: the view. `/memory model`: the compaction model.
- Design: Victor Taelin's
  [OptChat](https://gist.github.com/VictorTaelin/91837951a5ce5b38f341ec1ba1df6449).

> οὔκουν μνήμης ἀλλὰ ὑπομνήσεως φάρμακον ηὗρες.
> Not a drug for memory, but for reminding, have you found.
> (Plato, Phaedrus 275a)

Plato's Thamus says it of writing. eukhe keeps both: the log is the
memory (μνήμη), the summaries are its reminders (ὑπομνήματα).

## LAWS

- The pure core is written in Bend and compiled into the binary.
- `LAWS.bend` states its laws. `PROOF.bend` proves them.
- The chat-memory planner runs as the compiled model. Rust holds no
  copy of it.

```sh
bend PROOF.bend  # ALL PROOFS CHECK
```

## AGENTS

- `rlm.spawn` in the agent's Python REPL starts subagents.
- `@name message`: message a family agent. `/agents`: list them.
- `/dynamic-workflow <request>`: one script fans out many subagents
  in phases.

## LIMITATIONS

- Runs model-written Python and shell with your permissions. No
  sandbox. Trusted repositories only.
- No Windows.

## ATTRIBUTION

- Fork of Prime Intellect's
  [Prime Agent](https://github.com/PrimeIntellect-ai/prime-agent),
  which ports Mario Zechner's TypeScript agent.
- Chat memory design: Victor Taelin's OptChat and
  [OptMem](https://github.com/VictorTaelin/OptMem).
- Not affiliated with Prime Intellect, Victor Taelin or Earendil.
- Made by [Gil Rodrigues](https://gildrb.com).
- More: [about](https://eukhe.com/about),
  [contact](https://eukhe.com/contact),
  [privacy](https://eukhe.com/privacy).
