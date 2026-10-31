# Proofs of LAWS.bend

`bend PROOF.bend` (and `--verdict`) checks every file PROOF.bend imports.
One file per law; lemmas in `base.bend` files. NEVER `@unsafe`, `?` holes,
or edits to LAWS.bend / LAWS.lock.

## What exists

| File                                    | Gives                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| --------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `proof/base.bend`                       | Bool/And/Or/Not, `LE`/`LT` (Data), Nat order, add/sub/min/max, `Nat.div2_twice`, `Nat.sub_chain`, `Nat.le_sub_of_add`, ...                                                                                                                                                                                                                                                                                                                                                   |
| `proof/base/final.bend`                 | `Final(s)`: rows >= 3, cols >= 12, cursor line/col on the text, `Band` for top (scrolloff) and left (sidescrolloff). `Final.of(x) : Final(Vim.final(x))` for EVERY x. `Fit.band`/`Fit.side` (View.fit/fit_side land in the band).                                                                                                                                                                                                                                            |
| `proof/base/reach.bend`                 | `Reach.step(s,e)`: `after(Vim.step(s,e)) == Vim.final(Reach.next(s,e))`; `Reach.run`: `Spec.run(..) == Vim.final(Reach.pre(evs, Vim.start(..)))`; `Reach.final` (Final of every run); `Reach.files_run` (`files == Files.some(fs, Nil)`); `Reach.rows_run`/`cols_run` (`S.St.rows(run) == Spec.rows(rows, evs)`); `Reach.snoc`; `Esc.mode` (Esc from any state gives Normal); `Reach.normal_mode`, `rows_normal`, `cols_normal`; `Keep.*`, `Field.*`, `Size.*` field lemmas. |
| `proof/base/text.bend`                  | `Cells.eq` (Text.cells = Spec.cells), `Chars.eq`, `Count.eq`, `Line.eq`, `Char.eq`, `String.eq_refl/eq_same`, `Fit.cells`, `Fitted.cells`, `Cut.cells`, `Drop.cells`.                                                                                                                                                                                                                                                                                                        |
| `proof/screen/base.bend`                | `Screen.on_text`, `Screen.scrolled` (settled editor in Normal mode on `Files.some(fs)`), `Files.spec` (`Spec.file(fs,i)` = the window's lines), mode-clash helpers `Mode.typing/picking`, `And3/6/7`.                                                                                                                                                                                                                                                                        |
| `proof/screen/parts.bend`, `frame.bend` | nums, hits, bar, Float.fit, Scr.inside, Scr.typed, statusline; per-mode frame facts.                                                                                                                                                                                                                                                                                                                                                                                         |

Pattern for a law over `Spec.run(fs, rows, cols, evs)`: rewrite
`Spec.rows/cols` with `Reach.rows_run/cols_run`, then prove the claim for
any `s` with `Final(s)` (and `files(s) == Files.some(fs, Nil)` when it reads
the files). For `Spec.normal`, use the `*_normal` lemmas and
`Reach.normal_mode`. To case on the mode, `match s` then `match mode`
(fields in binder order: s, win, then tgt/cur; a mode match must come
before tgt/cur — see `OnText.at`). For a step from a reached state use
`Reach.step` + `Keep.*`.

## Open laws: what each needs

Every motion/oil law starts from `n = Spec.normal(...)`: Final(n),
mode Normal, files invariant are already proven. Pend NoPend and count 0
after Esc are NOT yet proven: add `Esc.pend`/`Esc.count` next to
`Esc.mode` (reach.bend), same proof shape (match s, mode, pend; `{==}`).

### esc group

- **esc_closes**: `F.float(frame(n)) == None` from `Reach.normal_mode` +
  `Scr.float(s, Normal) = None` (rewrite mode). Code: screen.bend Scr.float.
- **oil_close**: `Spec.press(n, "<C-c>")` in Normal/NoPend: `Key.normal.hi(..27..)`
  → `Win.alt` when on a Dir; need `Win.alt` result tgt is a File:
  `Win.to(s, head(drop(opened, 0)))` — needs invariant "opened is nonempty"
  (opened starts `[0n]`, Opened.put only conses) or show `Win.to(s, None)`
  keeps a File tgt is false on Dir → **needs a reach invariant on
  `opened`** (by construction in Vim.keep, or a per-key proof). Code:
  core.bend Win.alt/Win.to/Opened.put, keys.bend 26/27.
- **esc_keeps**: tgt(normal) == tgt(run): Esc keeps `S.St.win` in every
  mode/pend (Key.in → set_mode/set_hl/set_pend only) and Vim.real/fit keep
  tgt when it is real (needs `Tgt.real(files(run), tgt(run)) == True`, i.e.
  the real_buffer invariant below). Lemma: `Esc.win(s): win(after(Key.in(s,
  mode(s), "<Esc>"))) == win(s)` (match s, mode, pend).
- **esc_idle** (new in LAWS): Esc in normal mode changes nothing on screen:
  frame(after(step(s,Esc))) == frame(s) for Normal s — Esc.win + set_hl only
  (check: Esc clears `hl`, which changes hits — read the law's exact claim).

### motion group (key_j, key_k, key_gg, key_G, key_0, key_dollar, key_h, key_l, col_j/k/gg/G)

Per key k: `after(step(n, EvKey{k})) == Vim.final(Reach.next(n, ...))` with
`Key.in_normal(n, k)` reducing via `Ex.find(Key.names(), k, 0)` (closed)
to `Key.normal.at(s, IDX, max(0,1)=1, 0)` once count = 0 and pend = NoPend
(needs Esc.pend/count). Then: Win.go_line / Win.go / Key.dollar →
`Win.settle`, and Vim.final re-settles (idempotent facts needed only for
line/col: `Move.clamp`, `Move.aim`, `Nat.min`). Lemmas:

- `Settle.cur(s)`: cursor after `Win.settle(s)` is `Move.clamp(lines, cur)`;
  `Final` already gives `line <= last`, so clamp of a clamped pos is itself.
- `Fit.cur(x)`: cursor of `Vim.final(x)` is `Move.clamp(lines(x), cur(x))`
  (from Final.win's expression) and tgt unchanged when real.
- at_line/at_col of the frame = cursor line/col (proved inside
  `OnText.parts`: `el`, `ec`; extract as standalone lemmas).
- col laws (A4): `Move.aim(ls, l, want)` vs `Spec.min(c, last)`; needs the
  invariant `want == Col{col}` or `End` with col at line end — **not
  guaranteed by Final**; either add to Vim.final (want normalized) or prove
  per key that `Win.go` sets want = Col{col}. Code: core.bend Win.go/go_line,
  move.bend Move.aim, keys.bend Key.dollar (sets End).
- j_view (new): read the law; uses View.fit's new `far_up`/`down` thresholds.

### mouse

- **click**: `Vim.click(n, Normal, r, c)` → `Win.go(s2, Pos{top+r, left+c-g})`
  then Vim.final; needs the same `Fit.cur` lemma and `Move.clamp` =
  `Spec.min(.., last)`; `Spec.min_eq` exists (screen/base.bend).
  Code: vim.bend Vim.click.

### oil group (oil_up_entry, oil_parent, oil_open, oil_back, oil_listing)

- Every Dir the window shows is real (`Tgt.real`, by construction:
  `Vim.real` in Vim.final). Listing lines come from `St.lines.at(s, Dir d)` =
  `Listing.find(dirs, d)` default `["../"]`; need invariant
  `dirs(run) == dirs(start)` (by construction like files: extend Vim.keep
  to restore dirs/folded, runtime-identical) and `Listing.find(Dirs.list(..),
  d)` starts with "../" (Oil.list = `"../" <> es`).
- oil_parent/oil_open: `Oil.here.at` (core.bend) with `Path.up`/`Path.dir`/
  `Path.child` vs `Spec.parent`/`Spec.dir`/`Spec.base` (string lemmas on
  `Path.dir.go`, `Path.up.go` vs `Spec.dir.go`, `Spec.drop_last`), and
  `Lines.index` finding `Spec.base(p)` in the listing (oil_listing helps).
- oil_back, oil_listing: new laws; read them first.

### buffers

- **real_buffer**: `Vim.final` now ends with `Vim.real` (vim.bend): the
  window shows `B.Tgt.real(files, tgt)` targets, else file 0. Needed:
  `Real.of(x): B.Tgt.real(files(x), tgt(Vim.final(x))) == True`
  (`Vim.fit` keeps tgt: match x; `Vim.real`: case on the Bool, False → File 0
  real since `0 < max(n, 1)`), and `B.Tgt.real(Files.some(fs, Nil), t) ==
  Spec.real(fs, t)`: `Files.len(Files.some(fs))` = `Spec.nfiles(fs)`
  (Files.some_go in screen/base.bend + a count lemma), `Spec.max_eq`
  (reach.bend), `B.Path.is_dir == Spec.ends_slash` (same recursion),
  `X.Text.prefix(d, p) == Spec.prefix(d, p)` (Text.prefix.go with ok=False
  stays False; inspect `Char.is_eq`).

### host (honest, urls)

- `Spec.act(Vim.step(run, e))` = act of the raw step (Vim.done keeps act).
  CopyText only from `Key.yank` (keys.bend: copies only when the line equals
  `E.Vim.install()`; prove `String.eq(line, install) == True → line ==
  install`, a String.eq_true lemma from U32/Word eq_true as in the bank).
  OpenUrl only from `E.Link.gx` (ex.bend): url cut from the cursor's line,
  which is a line of `Spec.file(fs, i)` (files invariant) — needs
  `within(cut, line)`-style lemmas; urls also needs the http(s) prefix test
  in Link.gx.

### Ex

- colon, ex_line: new laws (":" opens Typing{Colon,""}: cursor after it —
  Typing frame facts exist in frame.bend/parts.bend; ":5<CR>" → E.Line.run).
