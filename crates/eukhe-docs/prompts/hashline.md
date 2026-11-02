Hashline patch of existing files (new files: `write`): one or more sections, each a header line then ops.

Header: `[PATH#TAG]` copied verbatim from the latest `read`/`grep`/edit output for that file, e.g. `[src/a.rs#3F9A]`. `TAG` is that file's 4-hex snapshot: NEVER invent or guess it; no tag yet → `read` or `grep` the file. `N`, `M`: line numbers from that output, never shifted by earlier ops.

Ops:
- `PUT N.=M:` replaces inclusive lines N–M with the `+` body (one line: `PUT N.=N:`).
- `PUT <N:` inserts before N (`PUT <1:` file head); `PUT >N:` after N (`PUT >$:` file tail).
- `CUT N.=M` deletes and captures, optionally as `@name`.
- `PUT <N @name`/`PUT >N @name` pastes at the gap (no `@name`: the anonymous `CUT`); `PUT N.=M @name` pastes over the range (name required). Pastes take no body; named registers persist across calls.
- `REM` deletes the file; `MV DEST` moves it after the section's edits (quote paths with spaces).

Rules:
- Body rows start `+`; a lone `+` is a blank line; the rest is verbatim, indent included. NEVER `-` rows or bare context: the range deletes, the body is the final content. Literal leading `-`/`+`: `+- item`/`++ item`. Range and body lengths are independent; delete with `CUT`, never an empty `PUT`.
- Touch only changed, displayed lines; `…`, `..` and collapsed `N-M:` rows are unseen: read them first. Split nonadjacent changes; additions use `PUT <N:`/`PUT >N:`, never a widened range. Never start or end a range mid-expression or mid-block.
- Each edit changes the tag and numbers: take the next ones from the edit response or a fresh `read`. Stale tag → re-read.
- Do not restyle unrelated code.

Example: `read` printed `[greet.py#A1B2]`, `1:def greet(name):` … `3:    print(msg)`:
```
[greet.py#A1B2]
PUT 1.=3:
+def greet(name):
+    print(f"Hi, {name}")
```
