# utok vocabulary data

The data files in this directory are copied unchanged from the upstream
tokenizer port credited in `THIRD-PARTY-NOTICES` (commit `c28b3e3`); the
tokenizer code in `../src/utok/` is ported from that port at the same
commit. The generator scripts named below belong to the upstream port and
live in its tools directory at that commit; eukhe does not carry them. To
refresh a blob, regenerate it in a checkout of the upstream port and copy
the result here (with the matching test fixtures from its fixtures
directory into `../fixtures/`).

`ctok_v3.bin.zst` and `ctok_v4_7.bin.zst` are **generated** — do not
hand-edit. They are compacted from the measured vocabulary files of
[sanderland/ctok](https://github.com/sanderland/ctok) v1.0.0 (revision
`df3b59b5e645289a5eadc8e24036b99d39c333c4`), MIT licensed — see
`LICENSE.ctok`. The vocabulary data is Sander Land's measurement work
("On the biology of Claude's tokenizer",
<https://tokencontributions.substack.com/p/on-the-biology-of-claudes-tokenizer>);
the Rust implementation in `../src/utok/claude/` is ported from the upstream
port.

ctok ships every piece with a `count_tokens` witness probe; compaction
drops that metadata, parses the public `⟨bow⟩the⟨eow⟩` key notation into the
compact C0 marker alphabet (single bytes `0x01`–`0x05`; safe because `nfc`
strips C0 controls from input), adds the glued contraction spellings, and
front-codes the sorted piece list into the version-2 binary format produced
by the upstream port's generator `gen-ctok-vocab.ts` (~4.7 MB of ctok JSON →
~254 KB front-coded → ~106 KB after zstd -19).

Regenerate the front-coded binaries, then compress them (in the upstream
port's tools directory):

```sh
bun gen-ctok-vocab.ts   # fetch ctok, emit raw bins into cache/
bun pack-ctok.ts        # zstd -19 into ../data/
```

If the ctok pin moves, also regenerate
`../src/utok/claude/testdata/fixtures.json` against the same ctok release
(see the fixture doc in `../src/utok/claude/mod.rs`).

The other `*.bin.zst` files here are the UTOK1 BPE rank tables packed by
the upstream port's per-family scripts in its tools directory (container format
and per-family split specs: `families.json` in this directory).

`jev_base.bin.zst` and `jev_whole.bin.zst` are **measured**, not downloaded:
TypeSafe publishes no tokenizer for Jev, so both sets were recovered from
the live System One API's `usage.input_tokens` (jev-1.13.0, 2026-09-23,
~639k probes). `jev_whole` holds the whole-word entries (a piece that
equals one costs 1); `jev_base` holds the base tokens the merge loop may
form. Both are o200k subsets stored at their o200k ranks, with every other
slot empty. Membership came from difference probes inside non-merging
padding (e.g. `cost("世" + x + "世") - 2`), byte fragments were fitted
against per-character probes, and pieces padding cannot isolate (space
runs, newline-final punctuation, rare fragments) were settled with probes
built to flip on each one. The result reproduces all 638,573 recorded
counts (`../fixtures/jev.json` pins 400 live counts). Regenerate the
blobs from the measured sets with (in the upstream port's tools directory):

```sh
bun pack-jev.ts   # cache/jev-1.13.vocab.json + cache/o200k_base.tiktoken → ../data/jev_*.bin.zst
```
