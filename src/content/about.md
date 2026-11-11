EUKHE
ABOUT
2026

~*~ εὐχή: a wish, a prayer ~*~

# ABOUT EUKHE

Eukhe is the harness for the AGI era. The name is εὐχή, Greek for
wish. You wish how the agent should do the work, and Eukhe gets it
done that way.

> διὸ δὴ καὶ ὄκνος τις αὐτῶν ἅπτεσθαι, μὴ εὐχὴ δοκῇ εἶναι ὁ λόγος,
> ὦ φίλε ἑταῖρε.
> So there is some hesitation to touch these things, lest the
> argument seem a mere wish, my dear friend. (Plato, Republic 5.450d)

You write the wish as rules in `AGENTS.md`, as a goal and as commands
that must pass. When one of those commands fails, Eukhe gives its
output to the agent and runs another turn, and it repeats this until
every command passes or the run reaches a limit. A session is an
append-only log on disk, so it survives a crash and
`eukhe --continue` reopens it.

The `eukhe` command runs a coding agent in your terminal. The
`eukhe-sdk` Rust crate runs sessions inside your own process.

## PILLARS

Four pillars have laws with proofs today.

[Durable](spec/durable/) syncs every write of the session log to disk
before acknowledging it. A resumed session keeps every checkpoint and
has no task left running.

[Memory](spec/memory/) never deletes a message. Each request to the
model contains the newest messages in full and a one-line summary of
each older one, and the agent can read the full text of any
summarized message.

[RLM](spec/rlm/) (recursive language model) gives the agent a Python
REPL in which the conversation so far is a variable. The agent starts
a subagent there with a function call, and Eukhe refuses a call that
gives no reason.

[Autoresearch](spec/autoresearch/) improves a number you can measure
on your code, such as its speed or size. It runs the benchmark after
each change and keeps the change only if the number improved.

Loop is the code behind `--autonomous` and `--goal`. It has no
requirements, spec files or laws yet.

Planned and not built: hard budgets, verified completion,
exactly-once effects, capability security, replayable record,
orchestration at scale, stable SDK contract.

## LAWS

[spec/](spec/README.md) numbers what Eukhe's session log, memory,
subagents and tool calls must do. A law is a theorem that the core,
the part of Eukhe written in [Bend](https://bend-lang.com), meets
one of those requirements. `PROOF.bend` holds a proof of every law,
and the checked core is the code compiled into the binary you
install.

The proofs cover the Bend core and say nothing about what the model
writes. The Bend compiler, the C shim that links the core into the
binary and the Rust IO are trusted without proof.

## SDK

[`eukhe-sdk`](crates/eukhe-sdk/) is a Rust crate that runs sessions
inside your process. Its main calls are `open_session`, `prompt` and
`watch`.

[`eukhe-client`](crates/eukhe-client/) is a Rust crate that connects
to the Eukhe daemon (`eukhe --mode daemon`) over its socket. The
terminal UI and the web dashboard use it.

A program in any language starts `eukhe --mode <json|rpc|acp>` and
talks to it over stdio.

The crates are not on crates.io. Their API may change with any
release.

## WHO MAKES IT

Eukhe is made by Gil Rodrigues ([gildrb.com](https://gildrb.com)), a
designer and developer. It is a fork of Prime Intellect's
[Prime Agent](https://github.com/PrimeIntellect-ai/prime-agent), and its
chat memory follows Victor Taelin's OptChat and
[OptMem](https://github.com/VictorTaelin/OptMem). It is not affiliated
with Prime Intellect, Victor Taelin or Earendil.

## SOURCE

The source is public at
[github.com/gildrb/eukhe](https://github.com/gildrb/eukhe) under the MIT
license. Releases for macOS (Apple Silicon) and Linux (x64, arm64) are
built from it and published there.

## THIS SITE

eukhe.com shows the install command and Eukhe's README as it is on
GitHub, with Greek epigraphs of the site's own. On a computer the
page is a read-only Neovim whose core is written in Bend, with proven
laws; on a phone it is the same terminal, scrolled by touch.

More: [contact](/contact), [privacy](/privacy), [llms.txt](/llms.txt).
