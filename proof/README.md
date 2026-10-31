# Proofs of the laws (LAWS.bend, laws/vim/)

All 37 laws of laws/vim/ are proven: `bend PROOF.bend` and
`bend PROOF.bend --verdict` print ALL PROOFS CHECK. No law is open.

`bend PROOF.bend` (and `--verdict`) checks every file PROOF.bend imports.
One file per law; lemmas in `base.bend` files. NEVER `@unsafe`, `?` holes,
or edits to LAWS.bend, laws/ or LAWS.lock. A code change must keep every proof
green, `python3 scripts/vim-diff.py` at 22/24 exact and the law fuzz at 0
fails.

## What exists

| File                                        | Gives                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                        |
| ------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `proof/base.bend`                           | Bool/And/Or/Not, `LE`/`LT` (Data), Nat order, add/sub/min/max, `Nat.div2_twice`, `Nat.sub_chain`, `Nat.le_sub_of_add`, ...                                                                                                                                                                                                                                                                                                                                                                                                                   |
| `proof/base/final.bend`                     | `Final(s)`: rows >= 3, cols >= 12, cursor line/col on the text, `Band` for top (scrolloff) and left (sidescrolloff). `Final.of(x) : Final(Vim.final(x))` for EVERY x. `Fit.band`/`Fit.side` (View.fit/fit_side land in the band).                                                                                                                                                                                                                                                                                                            |
| `proof/base/reach.bend`                     | `Reach.step(s,e)`: `after(Vim.step(s,e)) == Vim.final(Reach.next(s,e))`; `Reach.run`: `Spec.run(..) == Vim.final(Reach.pre(evs, Vim.start(..)))`; `Reach.final` (Final of every run); `Reach.files_run` (`files == Files.some(fs, Nil)`); `Reach.dirs_run`; `Reach.rows_run`/`cols_run` (`S.St.rows(run) == Spec.rows(rows, evs)`); `Reach.snoc`; `Esc.mode` (Esc from any state gives Normal); `Reach.normal_mode`, `normal_pend`, `normal_count`, `normal_step`, `rows_normal`, `cols_normal`; `Keep.*`, `Field.*`, `Size.*` field lemmas. |
| `proof/base/text.bend`                      | `Cells.eq` (Text.cells = Spec.cells), `Chars.eq`, `Count.eq`, `Line.eq`, `Char.eq`, `String.eq_refl/eq_same`, `Fit.cells`, `Fitted.cells`, `Cut.cells`, `Drop.cells`.                                                                                                                                                                                                                                                                                                                                                                        |
| `proof/vim/screen/base.bend`                | `Screen.on_text`, `Screen.scrolled` (settled editor in Normal mode on `Files.some(fs)`), `Files.spec` (`Spec.file(fs,i)` = the window's lines), mode-clash helpers `Mode.typing/picking`, `And3/6/7`.                                                                                                                                                                                                                                                                                                                                        |
| `proof/vim/screen/parts.bend`, `frame.bend` | nums, hits, bar, Float.fit, Scr.inside, Scr.typed, statusline; per-mode frame facts.                                                                                                                                                                                                                                                                                                                                                                                                                                                         |

Pattern for a law over `Spec.run(fs, rows, cols, evs)`: rewrite
`Spec.rows/cols` with `Reach.rows_run/cols_run`, then prove the claim for
any `s` with `Final(s)` (and `files(s) == Files.some(fs, Nil)` when it reads
the files). For `Spec.normal`, use the `*_normal` lemmas and
`Reach.normal_mode`. To case on the mode, `match s` then `match mode`
(fields in binder order: s, win, then tgt/cur; a mode match must come
before tgt/cur — see `OnText.at`). For a step from a reached state use
`Reach.step` + `Keep.*`.

## Invariants built into the code

Every law starts from a reached editor: `Spec.run` or `n = Spec.normal(...)`.
What every reached editor holds by construction (vim/vim.bend), with its
lemmas in proof/base/reach.bend unless named:

- `Vim.final` resets pend/count outside Normal: `Reach.normal_pend` /
  `Reach.normal_count` give `pend(Spec.normal(..)) == NoPend`,
  `count(Spec.normal(..)) == 0n` (from `Esc.pend`/`Esc.count`,
  `Field.pend_final`, `Keep.pend`, `Pend.none`, `Count.zero`).
  `Reach.normal_step`: `Spec.normal(..) == Vim.final(Reach.next(Spec.run(..), Esc))`.
- `Vim.keep` restores files, folded, dirs (`Reach.dirs_run`: listings ==
  `S.St.dirs(Vim.start(..))`) and keeps `opened` nonempty (`Keep.opened`,
  `Field.opened_final`; `Vim.opened(Nil) = [0n]`).
- A Dir's lines default to `B.Oil.list(files, path)` when its listing is
  not found (core.bend St.lines.at); Win.leave records a file left in
  `opened` (Oil's Ctrl-c returns to it).
- View.fit's lower scrolloff is `View.so_dn(h)`: Final's top band is
  `Fin.hi(line, View.so_dn(h), last, h)`; `Fit.so_le_dn` gives so_in <= so_dn.
- `want` normalized in `Win.settle` (core.bend `Want.at`): kept when
  `Move.aim(ls, line, want) == col`, else `Col{col}` (A4): `Aim`/`Aim.of`
  in proof/vim/motion/base.bend.
- `Vim.real` in Vim.final: the window shows a real buffer: `Real.of(x)`,
  `Real.spec` in proof/vim/buffers/real.bend.
- Link.gx opens a URL only on a file window (ex.bend).

Proof-cost note: orient every rewrite `%e` as `e : {new == old}` with the
goal literally `P[old]`; otherwise bend normalizes `Spec.normal` (minutes).

## Proofs by group

### screen (cursor_ok, cursor_on_text, fits, edges, cmdline_cursor, scrolloff, scrolloff_any)

proof/vim/screen/*.bend, from `Final.of` and screen/base.bend, parts.bend, frame.bend.

### esc (esc_closes, oil_close, esc_keeps, esc_idle)

- `proof/vim/esc/base.bend`: `Settle.win` (Win.settle keeps a settled window),
  `Settle.self` (Vim.final keeps a settled normal-mode editor on a real
  buffer, up to want), `Esc.win` (Esc keeps the window), `Esc.final_tgt`,
  `Esc.real_run`.

### motion (key_j/k/gg/G/0/dollar/h/l, col_j/k/gg/G, j_view)

- `proof/vim/motion/base.bend`: proofs work on `Idle.mk(n)` (`Idle.eta`,
  `Ready.*`: the record with mode/count/pend written in, so a key
  computes); `Final.real` (Vim.final = Vim.fit on a real target);
  `GL.cur`/`GLJ.cur`/`Go.cur`/`Dol.cur`/`G1.cur` give the cursor after each
  motion; `AtLine`/`AtCol` read the frame back; `Aim.of` (want invariant).
- `proof/vim/motion/col_base.bend`: `VCol.press` (press = Vim.fit(keep(z, raw
  key)); converting a press directly runs `--verdict` out of fuel),
  `VCol.aim`/`VCol.of`/`VCol.tail` prove Claim.vcol for any want.
- `proof/vim/motion/j_view.bend`: `JV.top` (the two settles of j), `JV.fit`
  (View.fit from a top in line l's band to m <= l + 1: top, or hi(m);
  `JV.mid_eq` covers windows of at most two rows), `JV.collapse`.

### mouse (click)

- `proof/vim/mouse/click.bend`: `Ck.final(s, w)` and `Ck.frame(s, m)` are
  shape copies of Vim.final / Scr.frame: change them with those defs.

### oil (oil_up_entry, oil_parent, oil_open, oil_back, oil_listing)

- `proof/vim/oil/base.bend`: what a folder window shows (`Oil.vim_lines`,
  `Good`), `Oil.dash`/`Oil.ctrl_c` from a settled normal editor.
- `proof/vim/oil/path.bend`: `Path.dir_eq`/`Path.up_eq`/`Path.child_base` vs
  Spec.dir/parent/base, `Path.real_dir`.
- `proof/vim/oil/bag.bend`: an Oil listing holds exactly the folder's children.
- `proof/vim/oil/str.bend`: `Str.eq_true` (String.eq true -> equal) and
  Word/U32/Char eq_true.

### buffers (real_buffer, start_file)

- `proof/vim/buffers/real.bend`: `Real.of`, `Real.fit`, `Real.win`, `Real.spec`,
  `Prefix.eq` (Text.prefix = Spec.prefix), `Slash.eq`, `Char.eq_comm`.

### host (honest, urls)

- `proof/vim/host/honest.bend`, `urls.bend`: both project `A.Host.law`
  (`proof/vim/host/act.bend`): `Host.good(fs, act(Vim.step(run, e)))`, i.e.
  honest and url_ok together, by `Step.good` → `In.good` (every key path
  of Key.in; `Normal.good`/`Hi.good`/`G.good` enumerate key numbers).
  yy: `E.Vim.install()` computes to `Spec.install()`, no eq_true needed.
  gx: `Gx.good` (only on file windows: Link.gx tests `C.St.on_file`).
- `proof/vim/host/base.bend`: string lemmas (`Str.app_nil/assoc/rev_go/
  rev_app/rev_rev`), runs `Sub(u, s)` (s = a ++ u ++ b; `refl/trans/rev/
  cons/within`), `When.both`/`Pick.both` (a property of both branches),
  and `Gx.sub(line, c)`: the target gx cuts is a run of the line.

### Ex (colon, ex_line)

- `proof/vim/ex/colon.bend`: match the state, mode, pend (`Eb.Pend.clash` for a
  waiting key, from `Reach.normal_pend`); the Typing frame computes:
  `Colon.typed` (`Scr.typed(":", c) == ":"` for c >= 2), `Max.l`.
- `proof/vim/ex/ex_line.bend`: step lemmas over an ABSTRACT editor (unfolding
  three presses at once does not finish): `ExLine.real` (Vim.final on a
  real buffer is `ExLine.rf`, Vim.fit only), `ExLine.Same` (files, dirs,
  target) with `Same.trans/real`, `Lines.same`; `Press.eq/same/mode/line/
  final` for any key keeping the target; per key `Colon.*`, `Five.*`,
  `Cr.*`; `ExLine.at_line` (frame line == cursor line when settled, Normal);
  `Lines.spec`, `Want.eq`, `Min.idem/four`. Uses `Rb.Real.of`
  (proof/vim/buffers/real.bend).
- `proof/vim/ex/base.bend`: `Pend.If/clash`, `Max.l`.
