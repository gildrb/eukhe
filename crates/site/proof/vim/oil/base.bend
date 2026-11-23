# eukhe.com's Neovim: the editor facts the Oil laws share
# =======================================================
#
# What a folder's window shows: its listing as Oil makes it from the files
# (the listings the start found, Vim.keep keeps them). What "-" and Ctrl-c
# do from a settled editor in normal mode with no key waiting.

import Base
import ../../../vim/types.bend as T
import ../../../vim/text.bend as X
import ../../../vim/buf.bend as B
import ../../../vim/st.bend as S
import ../../../vim/core.bend as C
import ../../../vim/keys.bend as K
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../vim/move.bend as M
import ../../base.bend as L
import ../../base/reach.bend as Rc
import ./str.bend as Str
import ../buffers/real.bend as Rb

# The frame
# ---------

def Oil.frame_tgt(+s: T.St) -> {Laws.F.tgt(Vim.Vim.frame(s)) == S.Win.tgt(S.St.win(s)) : T.Tgt}:
  {==}

def Oil.vim_lines(+s: T.St) -> {Vim.Vim.lines(s) == B.Lines.some(C.St.lines.at(s, S.Win.tgt(S.St.win(s)))) : List<&2, String>}:
  {==}

# Listings
# --------

# every listing of ls is Oil's listing of its folder over files
def Good(ls: List<&2, T.Listing>, +files: List<&2, T.Buf>) -> Type:
  match ls:
    case Nil{}:
      Unit
    case Con{T.Listing{p, xs}, t}:
      {xs == B.Oil.list(files, p) : List<&2, String>} & Good(t, files)

def Good.dirs(ds: List<&2, String>, +files: List<&2, T.Buf>, +acc: List<&2, T.Listing>, h: Good(acc, files)) -> Good(Vim.Dirs.list(ds, files, acc), files):
  match ds:
    case Nil{}:
      h
    case Con{+d, t}:
      Good.dirs(t, files, T.Listing{d, B.Oil.list(files, d)} <> acc, ({==}, h))

def Good.hit(b: Bool, +p: String, +d: String, +xs: List<&2, String>, +t: List<&2, T.Listing>, +files: List<&2, T.Buf>, e: {String.eq(p, d) == b : Bool}, hx: {xs == B.Oil.list(files, p) : List<&2, String>},
  ih: {Maybe.default(&2, List<&2, String>, C.Listing.find(t, d), B.Oil.list(files, d)) == B.Oil.list(files, d) : List<&2, String>})
  -> {Maybe.default(&2, List<&2, String>, X.Bool.when(Maybe<&2, List<&2, String>>, b, u => C.Listing.find(t, d), u => Some{xs}), B.Oil.list(files, d)) == B.Oil.list(files, d) : List<&2, String>}:
  match b:
    case True{}:
      %Str.Str.eq_true(p, d, e) : {xs == B.Oil.list(files, _) : List<&2, String>}
      hx
    case False{}:
      ih

# a folder's listing found among good ones is Oil's listing of it
def Good.find(ls: List<&2, T.Listing>, +d: String, +files: List<&2, T.Buf>, h: Good(ls, files)) -> {Maybe.default(&2, List<&2, String>, C.Listing.find(ls, d), B.Oil.list(files, d)) == B.Oil.list(files, d) : List<&2, String>}:
  match ls:
    case Nil{}:
      {==}
    case Con{T.Listing{+p, +xs}, +t}:
      (hx, ht) = h
      Good.hit(String.eq(p, d), p, d, xs, t, files, {==}, hx, Good.find(t, d, files, ht))

# after any events, a folder's window shows Oil's listing of it over the
# files
def Oil.run_lines(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>, +d: String) -> {C.St.lines.at(Laws.Spec.run(fs, rows, cols, evs), T.Dir{d}) == B.Oil.list(B.Files.some(fs, Nil{}), d) : List<&2, String>}:
  +r = Laws.Spec.run(fs, rows, cols, evs)
  +files = B.Files.some(fs, Nil{})
  +st = Vim.Vim.start(fs, rows, cols)
  %Equal.sym(List<&2, T.Listing>, S.St.dirs(r), S.St.dirs(st), Rc.Reach.dirs_run(fs, rows, cols, evs)) : {Maybe.default(&2, List<&2, String>, C.Listing.find(_, d), B.Oil.list(S.St.files(r), d)) == B.Oil.list(files, d) : List<&2, String>}
  %Equal.sym(List<&2, T.Buf>, S.St.files(r), files, Rc.Reach.files_run(fs, rows, cols, evs)) : {Maybe.default(&2, List<&2, String>, C.Listing.find(S.St.dirs(st), d), B.Oil.list(_, d)) == B.Oil.list(files, d) : List<&2, String>}
  Good.find(S.St.dirs(st), d, files, Good.dirs(Vim.Dirs.all(files, [""]), files, Nil{}, Unit{}))

# Keys in normal mode
# -------------------

# a key pressed: the editor its step settles on
def Oil.press(+s: T.St, +k: String) -> {Laws.Spec.press(s, k) == Vim.Vim.final(Vim.Vim.keep(s, Laws.Spec.after(K.Key.in(s, S.St.mode(s), k)))) : T.St}:
  Rc.Reach.step(s, T.EvKey{k})

# the editor a key of its own sees in normal mode: no key waits, no count
def Oil.idle(s: T.St) -> T.St:
  S.St.set_count(S.St.set_pend(s, T.NoPend{}), 0n)

# "-" in normal mode with no key waiting: Oil.here
def Oil.dash(+s: T.St, hm: {S.St.mode(s) == T.Normal{} : T.Mode}, hp: {S.St.pend(s) == T.NoPend{} : T.Pend})
  -> {Laws.Spec.after(K.Key.in(s, S.St.mode(s), "-")) == C.Oil.here(Oil.idle(s)) : T.St}:
  %Equal.sym(T.Mode, S.St.mode(s), T.Normal{}, hm) : {Laws.Spec.after(K.Key.in(s, _, "-")) == C.Oil.here(Oil.idle(s)) : T.St}
  %Equal.sym(T.Pend, S.St.pend(s), T.NoPend{}, hp) : {Laws.Spec.after(K.Key.pend(Oil.idle(s), _, "-", S.St.count(s))) == C.Oil.here(Oil.idle(s)) : T.St}
  {==}

# Ctrl-c in normal mode with no key waiting: in Oil, Win.alt
def Oil.ctrl_c(+s: T.St, hm: {S.St.mode(s) == T.Normal{} : T.Mode}, hp: {S.St.pend(s) == T.NoPend{} : T.Pend})
  -> {Laws.Spec.after(K.Key.in(s, S.St.mode(s), "<C-c>")) == Bool.pick(T.St, C.St.on_file(Oil.idle(s)), Oil.idle(s), C.Win.alt(Oil.idle(s))) : T.St}:
  %Equal.sym(T.Mode, S.St.mode(s), T.Normal{}, hm) : {Laws.Spec.after(K.Key.in(s, _, "<C-c>")) == Bool.pick(T.St, C.St.on_file(Oil.idle(s)), Oil.idle(s), C.Win.alt(Oil.idle(s))) : T.St}
  %Equal.sym(T.Pend, S.St.pend(s), T.NoPend{}, hp) : {Laws.Spec.after(K.Key.pend(Oil.idle(s), _, "<C-c>", S.St.count(s))) == Bool.pick(T.St, C.St.on_file(Oil.idle(s)), Oil.idle(s), C.Win.alt(Oil.idle(s))) : T.St}
  {==}

# What the window shows
# ---------------------

def Oil.tgt(s: T.St) -> T.Tgt:
  S.Win.tgt(S.St.win(s))

def Oil.idle_tgt(s: T.St) -> {Oil.tgt(Oil.idle(s)) == Oil.tgt(s) : T.Tgt}:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Oil.keep_win(-s: T.St, st: T.St) -> {S.St.win(Vim.Vim.keep(s, st)) == S.St.win(st) : T.Win}:
  match st:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

# Vim.final keeps a real target
def Oil.fin_tgt(y: T.St, h: {B.Tgt.real(S.St.files(y), Oil.tgt(y)) == True{} : Bool}) -> {Oil.tgt(Vim.Vim.final(y)) == Oil.tgt(y) : T.Tgt}:
  match y:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          %Equal.sym(Bool, B.Tgt.real(files, tgt), True{}, h) : {S.Win.tgt(Bool.pick(T.Win, _, T.Win{tgt, cur, want, top, left}, T.Win{T.File{0n}, T.Pos{0n, 0n}, T.Col{0n}, 0n, 0n})) == tgt : T.Tgt}
          {==}

# a jump shows its target
def Oil.open_tgt(s: T.St, +t: T.Tgt, p: T.Pos) -> {Oil.tgt(C.Win.open(s, t, p)) == t : T.Tgt}:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      match win:
        case T.Win{tgt, cur, want, top, left}:
          match tgt:
            case T.File{i}:
              {==}
            case T.Dir{d}:
              {==}

# "-" from folder path shows the folder above it (the root stays)
def Oil.here_dir(+z: T.St, path: String, +e: {Oil.tgt(z) == T.Dir{path} : T.Tgt}) -> {Oil.tgt(C.Oil.here(z)) == T.Dir{B.Path.up(path)} : T.Tgt}:
  match path:
    case SNil{}:
      %Equal.sym(T.Tgt, Oil.tgt(z), T.Dir{SNil{}}, e) : {Oil.tgt(C.Oil.here.at(z, _)) == T.Dir{SNil{}} : T.Tgt}
      e
    case SCon{+h, +t}:
      +up = B.Path.up(SCon{h, t})
      %Equal.sym(T.Tgt, Oil.tgt(z), T.Dir{SCon{h, t}}, e) : {Oil.tgt(C.Oil.here.at(z, _)) == T.Dir{up} : T.Tgt}
      Oil.open_tgt(z, T.Dir{up}, T.Pos{C.Lines.index(C.St.lines.at(z, T.Dir{up}), B.Path.child(up, SCon{h, t}), 0n), 0n})

# after any events the window shows a real target
def Oil.run_real(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {B.Tgt.real(S.St.files(Laws.Spec.run(fs, rows, cols, evs)), Oil.tgt(Laws.Spec.run(fs, rows, cols, evs))) == True{} : Bool}:
  +x = Rc.Reach.pre(evs, Vim.Vim.start(fs, rows, cols))
  %Equal.sym(T.St, Laws.Spec.run(fs, rows, cols, evs), Vim.Vim.final(x), Rc.Reach.run(fs, rows, cols, evs)) : {B.Tgt.real(S.St.files(_), Oil.tgt(_)) == True{} : Bool}
  %Equal.sym(List<&2, T.Buf>, S.St.files(Vim.Vim.final(x)), S.St.files(x), Rc.Field.files_final(x)) : {B.Tgt.real(_, Oil.tgt(Vim.Vim.final(x))) == True{} : Bool}
  Rb.Real.of(x)

# Fields "-" keeps
# ----------------

def Oil.idle_files(s: T.St) -> {S.St.files(Oil.idle(s)) == S.St.files(s) : List<&2, T.Buf>}:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Oil.idle_mode(s: T.St) -> {S.St.mode(Oil.idle(s)) == S.St.mode(s) : T.Mode}:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Oil.idle_pend(s: T.St) -> {S.St.pend(Oil.idle(s)) == T.NoPend{} : T.Pend}:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Oil.idle_opened(s: T.St) -> {S.St.opened(Oil.idle(s)) == S.St.opened(s) : List<&2, Nat>}:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

# "-" keeps the mode and the waiting key, and puts the file it leaves first
# among those opened
def Oil.here_mode(z: T.St) -> {S.St.mode(C.Oil.here(z)) == S.St.mode(z) : T.Mode}:
  match z:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      match win:
        case T.Win{tgt, cur, want, top, left}:
          match tgt:
            case T.File{i}:
              {==}
            case T.Dir{path}:
              match path:
                case SNil{}:
                  {==}
                case SCon{h, t}:
                  {==}

def Oil.here_pend(z: T.St) -> {S.St.pend(C.Oil.here(z)) == S.St.pend(z) : T.Pend}:
  match z:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      match win:
        case T.Win{tgt, cur, want, top, left}:
          match tgt:
            case T.File{i}:
              {==}
            case T.Dir{path}:
              match path:
                case SNil{}:
                  {==}
                case SCon{h, t}:
                  {==}

def Oil.here_opened(z: T.St) -> {S.St.opened(C.Oil.here(z)) == C.Opened.put(S.St.opened(z), Oil.tgt(z)) : List<&2, Nat>}:
  match z:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      match win:
        case T.Win{tgt, cur, want, top, left}:
          match tgt:
            case T.File{i}:
              {==}
            case T.Dir{path}:
              match path:
                case SNil{}:
                  {==}
                case SCon{h, t}:
                  {==}

# "-" from file i shows its folder
def Oil.here_file(+z: T.St, +i: Nat, e: {Oil.tgt(z) == T.File{i} : T.Tgt}) -> {Oil.tgt(C.Oil.here(z)) == T.Dir{B.Path.dir(B.Buf.path(B.Files.at(S.St.files(z), i)))} : T.Tgt}:
  +path = B.Buf.path(B.Files.at(S.St.files(z), i))
  +dir = B.Path.dir(path)
  %Equal.sym(T.Tgt, Oil.tgt(z), T.File{i}, e) : {Oil.tgt(C.Oil.here.at(z, _)) == T.Dir{dir} : T.Tgt}
  Oil.open_tgt(z, T.Dir{dir}, T.Pos{C.Lines.index(C.St.lines.at(z, T.Dir{dir}), B.Path.child(dir, path), 0n), 0n})

def Oil.idle_dirs(s: T.St) -> {S.St.dirs(Oil.idle(s)) == S.St.dirs(s) : List<&2, T.Listing>}:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

# Listings over equal fields
# --------------------------

def Oil.good_eq(-s1: T.St, -s2: T.St, ed: {S.St.dirs(s1) == S.St.dirs(s2) : List<&2, T.Listing>}, ef: {S.St.files(s1) == S.St.files(s2) : List<&2, T.Buf>}, h: Good(S.St.dirs(s2), S.St.files(s2))) -> Good(S.St.dirs(s1), S.St.files(s1)):
  %Equal.sym(List<&2, T.Listing>, S.St.dirs(s1), S.St.dirs(s2), ed) : Good(_, S.St.files(s1))
  %Equal.sym(List<&2, T.Buf>, S.St.files(s1), S.St.files(s2), ef) : Good(S.St.dirs(s2), _)
  h

def Oil.lines_dir(+s: T.St, +d: String, h: Good(S.St.dirs(s), S.St.files(s))) -> {C.St.lines.at(s, T.Dir{d}) == B.Oil.list(S.St.files(s), d) : List<&2, String>}:
  Good.find(S.St.dirs(s), d, S.St.files(s), h)

# after any events the listings are Oil's
def Oil.run_good(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> Good(S.St.dirs(Laws.Spec.run(fs, rows, cols, evs)), S.St.files(Laws.Spec.run(fs, rows, cols, evs))):
  +files = B.Files.some(fs, Nil{})
  +st = Vim.Vim.start(fs, rows, cols)
  Oil.good_eq(Laws.Spec.run(fs, rows, cols, evs), st, Rc.Reach.dirs_run(fs, rows, cols, evs), Rc.Reach.files_run(fs, rows, cols, evs), Good.dirs(Vim.Dirs.all(files, [""]), files, Nil{}, Unit{}))

# The cursor's line
# -----------------

# Vim.real keeps a window on a real target
def Oil.real_keep(+fs: List<&2, T.Buf>, w: T.Win, h: {B.Tgt.real(fs, S.Win.tgt(w)) == True{} : Bool}) -> {Vim.Vim.real(fs, w) == w : T.Win}:
  match w:
    case T.Win{+tgt, +cur, +want, +top, +left}:
      %Equal.sym(Bool, B.Tgt.real(fs, tgt), True{}, h) : {Bool.pick(T.Win, _, T.Win{tgt, cur, want, top, left}, T.Win{T.File{0n}, T.Pos{0n, 0n}, T.Col{0n}, 0n, 0n}) == T.Win{tgt, cur, want, top, left} : T.Win}
      {==}

# Vim.fit pulls the cursor's line onto the text
def Oil.fit_line(y: T.St) -> {C.St.line(Vim.Vim.fit(S.St.set_win(S.St.set_count(S.St.set_pend(y, Vim.Vim.pend(S.St.mode(y), S.St.pend(y))), Vim.Vim.count(S.St.mode(y), S.St.count(y))), S.St.win(y)))) == Nat.min(C.St.line(y), M.Move.last_line(C.St.lines(y))) : Nat}:
  match y:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      match win:
        case T.Win{tgt, cur, want, top, left}:
          match tgt cur:
            case T.File{i} T.Pos{line, col}:
              {==}
            case T.Dir{d} T.Pos{line, col}:
              {==}

def Oil.fin_line(+y: T.St, h: {B.Tgt.real(S.St.files(y), Oil.tgt(y)) == True{} : Bool}) -> {C.St.line(Vim.Vim.final(y)) == Nat.min(C.St.line(y), M.Move.last_line(C.St.lines(y))) : Nat}:
  +y2 = S.St.set_count(S.St.set_pend(y, Vim.Vim.pend(S.St.mode(y), S.St.pend(y))), Vim.Vim.count(S.St.mode(y), S.St.count(y)))
  %Equal.sym(T.Win, Vim.Vim.real(S.St.files(y), S.St.win(y)), S.St.win(y), Oil.real_keep(S.St.files(y), S.St.win(y), h)) : {C.St.line(Vim.Vim.fit(S.St.set_win(y2, _))) == Nat.min(C.St.line(y), M.Move.last_line(C.St.lines(y))) : Nat}
  Oil.fit_line(y)

def Oil.keep_line(-s: T.St, st: T.St) -> {C.St.line(Vim.Vim.keep(s, st)) == C.St.line(st) : Nat}:
  match st:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

# a jump: the line asked for, pulled onto the target's text
def Oil.open_line(s: T.St, +t: T.Tgt, p: T.Pos) -> {C.St.line(C.Win.open(s, t, p)) == Nat.min(Nat.min(S.Pos.line(p), M.Move.last_line(C.St.lines.at(s, t))), M.Move.last_line(B.Lines.some(C.St.lines.at(s, t)))) : Nat}:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      match win:
        case T.Win{tgt, cur, want, top, left}:
          match tgt t p:
            case T.File{i} T.File{j} T.Pos{l, c}:
              {==}
            case T.File{i} T.Dir{d} T.Pos{l, c}:
              {==}
            case T.Dir{q} T.File{j} T.Pos{l, c}:
              {==}
            case T.Dir{q} T.Dir{d} T.Pos{l, c}:
              {==}

# "-" from file i: Oil on its folder, on its entry
def Oil.here_is(+z: T.St, +i: Nat, e: {Oil.tgt(z) == T.File{i} : T.Tgt}) -> {C.Oil.here(z) == C.Oil.on(z, B.Path.dir(B.Buf.path(B.Files.at(S.St.files(z), i))), B.Path.child(B.Path.dir(B.Buf.path(B.Files.at(S.St.files(z), i))), B.Buf.path(B.Files.at(S.St.files(z), i)))) : T.St}:
  +path = B.Buf.path(B.Files.at(S.St.files(z), i))
  +dir = B.Path.dir(path)
  %Equal.sym(T.Tgt, Oil.tgt(z), T.File{i}, e) : {C.Oil.here.at(z, _) == C.Oil.on(z, dir, B.Path.child(dir, path)) : T.St}
  {==}
