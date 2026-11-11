# eukhe.com's Neovim: the proof of LAW oil_open
# =============================================
#
# From file i (one of fs, with a name) in normal mode with no key waiting,
# "-" is Oil.on the file's folder D with the cursor on Lines.index of the
# file's entry: Win.open, then Vim.final. D is real (Path.real_dir) and
# B.Path.dir is Spec.dir (Path.dir_eq). The folder's lines are Oil's
# listing of it (the listings the start found); the entry, the spec's base
# name (Path.child_base), is in it (Bag.mem), so Lines.index finds it on a
# line of the listing, which every clamp of the cursor keeps.

import Base
import ../../../vim/types.bend as T
import ../../../vim/text.bend as X
import ../../../vim/buf.bend as B
import ../../../vim/st.bend as S
import ../../../vim/core.bend as C
import ../../../vim/keys.bend as K
import ../../../vim/move.bend as M
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/oil.bend as OilLaws
import ../../base.bend as L
import ../../base/text.bend as Tx
import ../../base/final.bend as Fi
import ../../base/reach.bend as Rc
import ../screen/base.bend as Sb
import ../buffers/real.bend as Rb
import ../ex/ex_line.bend as El
import ./str.bend as Str
import ./base.bend as O
import ./path.bend as Pa
import ./bag.bend as Bg
import ./back.bend as Bk

# Lines.index
# -----------

def Idx.sh(b: Bool, c: Bool, +t: List<&2, String>, +x: String, +k: Nat,
  ih1: {Bool.pick(Nat, c, C.Lines.index(t, x, 1n+k), Nat.add(1n+k, C.Lines.index(t, x, 0n))) == Nat.add(1n+k, C.Lines.index(t, x, 0n)) : Nat},
  ih2: {Bool.pick(Nat, c, C.Lines.index(t, x, 1n), Nat.add(1n, C.Lines.index(t, x, 0n))) == Nat.add(1n, C.Lines.index(t, x, 0n)) : Nat})
  -> {Bool.pick(Nat, Bool.or(b, c), X.Bool.when(Nat, b, u => C.Lines.index(t, x, 1n+k), u => k), Nat.add(k, X.Bool.when(Nat, b, u => C.Lines.index(t, x, 1n), u => 0n))) == Nat.add(k, X.Bool.when(Nat, b, u => C.Lines.index(t, x, 1n), u => 0n)) : Nat}:
  match b:
    case True{}:
      L.Nat.add_zero(k)
    case False{}:
      match c:
        case False{}:
          {==}
        case True{}:
          +i0 = C.Lines.index(t, x, 0n)
          %Equal.sym(Nat, C.Lines.index(t, x, 1n+k), Nat.add(1n+k, i0), ih1) : {_ == Nat.add(k, C.Lines.index(t, x, 1n)) : Nat}
          %Equal.sym(Nat, C.Lines.index(t, x, 1n), Nat.add(1n, i0), ih2) : {Nat.add(1n+k, i0) == Nat.add(k, _) : Nat}
          L.Nat.add_succ(k, i0)

# where x is in ls, its index from k is k past its index from 0
def Idx.shift(ls: List<&2, String>, +x: String, +k: Nat) -> {Bool.pick(Nat, Laws.Spec.has_line(x, ls), C.Lines.index(ls, x, k), Nat.add(k, C.Lines.index(ls, x, 0n))) == Nat.add(k, C.Lines.index(ls, x, 0n)) : Nat}:
  match ls:
    case Nil{}:
      {==}
    case Con{+hd, +t}:
      Idx.sh(String.eq(hd, x), Laws.Spec.has_line(x, t), t, x, k, Idx.shift(t, x, 1n+k), Idx.shift(t, x, 1n))

def Idx.ln(b: Bool, c: Bool, +hd: String, +t: List<&2, String>, +x: String, eb: {String.eq(hd, x) == b : Bool},
  ih: {Bool.or(Bool.not(c), String.eq(Laws.Spec.line(t, C.Lines.index(t, x, 0n)), x)) == True{} : Bool},
  sh: {Bool.pick(Nat, c, C.Lines.index(t, x, 1n), Nat.add(1n, C.Lines.index(t, x, 0n))) == Nat.add(1n, C.Lines.index(t, x, 0n)) : Nat})
  -> {Bool.or(Bool.not(Bool.or(b, c)), String.eq(Laws.Spec.line(Con{hd, t}, X.Bool.when(Nat, b, u => C.Lines.index(t, x, 1n), u => 0n)), x)) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      match c:
        case False{}:
          {==}
        case True{}:
          %Equal.sym(Nat, C.Lines.index(t, x, 1n), Nat.add(1n, C.Lines.index(t, x, 0n)), sh) : {String.eq(Laws.Spec.line(Con{hd, t}, _), x) == True{} : Bool}
          ih

# where x is in ls, Lines.index finds a line equal to it
def Idx.line(ls: List<&2, String>, +x: String) -> {Bool.or(Bool.not(Laws.Spec.has_line(x, ls)), String.eq(Laws.Spec.line(ls, C.Lines.index(ls, x, 0n)), x)) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{+hd, +t}:
      Idx.ln(String.eq(hd, x), Laws.Spec.has_line(x, t), hd, t, x, {==}, Idx.line(t, x), Idx.shift(t, x, 1n))

def Idx.lt_at(b: Bool, c: Bool, +t: List<&2, String>, +x: String,
  ih: {Bool.or(Bool.not(c), Nat.is_lt(C.Lines.index(t, x, 0n), Laws.Spec.count(t))) == True{} : Bool},
  sh: {Bool.pick(Nat, c, C.Lines.index(t, x, 1n), Nat.add(1n, C.Lines.index(t, x, 0n))) == Nat.add(1n, C.Lines.index(t, x, 0n)) : Nat})
  -> {Bool.or(Bool.not(Bool.or(b, c)), Nat.is_lt(X.Bool.when(Nat, b, u => C.Lines.index(t, x, 1n), u => 0n), 1n+Laws.Spec.count(t))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      match c:
        case False{}:
          {==}
        case True{}:
          %Equal.sym(Nat, C.Lines.index(t, x, 1n), Nat.add(1n, C.Lines.index(t, x, 0n)), sh) : {Nat.is_lt(_, 1n+Laws.Spec.count(t)) == True{} : Bool}
          ih

# and that line is in ls
def Idx.lt(ls: List<&2, String>, +x: String) -> {Bool.or(Bool.not(Laws.Spec.has_line(x, ls)), Nat.is_lt(C.Lines.index(ls, x, 0n), Laws.Spec.count(ls))) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{+hd, +t}:
      Idx.lt_at(String.eq(hd, x), Laws.Spec.has_line(x, t), t, x, Idx.lt(t, x), Idx.shift(t, x, 1n))

# p and (not p or q): q
def Imp.use(p: Bool, -q: Bool, hp: {p == True{} : Bool}, h: {Bool.or(Bool.not(p), q) == True{} : Bool}) -> {q == True{} : Bool}:
  match p:
    case True{}:
      h
    case False{}:
      L.Bool.false_true({q == True{} : Bool}, hp)

def Not.inv(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      L.Bool.false_true({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# Numbers
# -------

def Open.min_l(a: Nat, b: Nat, h: L.LE(a, b)) -> {Nat.min(a, b) == a : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      L.Bool.false_true({Nat.min(1n+p, 0n) == 1n+p : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, y => 1n+y, Nat.min(p, q), p, Open.min_l(p, q, h))

def Open.min3(+a: Nat, +l: Nat, h: L.LE(a, l)) -> {Nat.min(Nat.min(Nat.min(a, l), l), l) == a : Nat}:
  +e = Open.min_l(a, l, h)
  %Equal.sym(Nat, Nat.min(a, l), a, e) : {Nat.min(Nat.min(_, l), l) == a : Nat}
  %Equal.sym(Nat, Nat.min(a, l), a, e) : {Nat.min(_, l) == a : Nat}
  e

def Lt.pred(a: Nat, n: Nat, h: L.LT(a, n)) -> L.LE(a, Nat.sub(n, 1n)):
  match a n:
    case 0n 0n:
      L.Bool.false_true(L.LE(0n, Nat.sub(0n, 1n)), h)
    case 1n+p 0n:
      L.Bool.false_true(L.LE(1n+p, Nat.sub(0n, 1n)), h)
    case 0n 1n+q:
      L.Nat.le_zero(Nat.sub(1n+q, 1n))
    case 1n++p 1n++q:
      L.LE.cast_r(1n+p, q, Nat.sub(1n+q, 1n), Equal.sym(Nat, Nat.sub(q, 0n), q, L.Nat.sub_zero(q)), L.Nat.lt_le(p, q, h))

# File i and its entry
# --------------------

# the path of file i the editor holds is the spec's
def Open.path(+fs: List<&2, T.Buf>, -files: List<&2, T.Buf>, +i: Nat, hf: {files == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}) -> {B.Buf.path(B.Files.at(files, i)) == Laws.Spec.path(fs, i) : String}:
  %Equal.sym(List<&2, T.Buf>, files, B.Files.some(fs, Nil{}), hf) : {B.Buf.path(B.Files.at(_, i)) == Laws.Spec.path(fs, i) : String}
  %Equal.sym(List<&2, T.Buf>, B.Files.some(fs, Nil{}), List.reverse.go(&2, T.Buf, Nil{}, Sb.Files.norm(fs)), Sb.Files.some_go(fs, Nil{})) : {B.Buf.path(B.Files.at(_, i)) == Laws.Spec.path(fs, i) : String}
  Pa.Path.spec_path(fs, i)

# i is one of the files the editor holds
def Open.len(+fs: List<&2, T.Buf>, -files: List<&2, T.Buf>, -i: Nat, hf: {files == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, hlt: {Nat.is_lt(i, Laws.Spec.nfiles(fs)) == True{} : Bool}) -> {Nat.is_lt(i, B.Files.len(files)) == True{} : Bool}:
  %Equal.sym(List<&2, T.Buf>, files, B.Files.some(fs, Nil{}), hf) : {Nat.is_lt(i, B.Files.len(_)) == True{} : Bool}
  %Equal.sym(List<&2, T.Buf>, B.Files.some(fs, Nil{}), List.reverse.go(&2, T.Buf, Nil{}, Sb.Files.norm(fs)), Sb.Files.some_go(fs, Nil{})) : {Nat.is_lt(i, B.Files.len(_)) == True{} : Bool}
  %Equal.sym(Nat, B.Files.len.go(Sb.Files.norm(fs), 0n), Nat.add(0n, Laws.Spec.nfiles(fs)), Rb.Count.go(fs, 0n)) : {Nat.is_lt(i, _) == True{} : Bool}
  hlt

# its entry in its folder has a name
def Open.named(+fs: List<&2, T.Buf>, +files: List<&2, T.Buf>, +i: Nat, +hf: {files == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, hne: {String.is_empty(Laws.Spec.base(Laws.Spec.path(fs, i))) == False{} : Bool})
  -> {String.is_empty(B.Path.child(B.Path.dir(B.Buf.path(B.Files.at(files, i))), B.Buf.path(B.Files.at(files, i)))) == False{} : Bool}:
  +path = B.Buf.path(B.Files.at(files, i))
  %Equal.sym(String, B.Path.child(B.Path.dir(path), path), Laws.Spec.base(path), Pa.Path.child_base(path)) : {String.is_empty(_) == False{} : Bool}
  %Equal.sym(String, path, Laws.Spec.path(fs, i), Open.path(fs, files, i, hf)) : {String.is_empty(Laws.Spec.base(_)) == False{} : Bool}
  hne

# the folder's listing over files, and the entry of file i in it
def Open.lst(+files: List<&2, T.Buf>, +i: Nat) -> List<&2, String>:
  B.Oil.list(files, B.Path.dir(B.Buf.path(B.Files.at(files, i))))

def Open.nm(+files: List<&2, T.Buf>, +i: Nat) -> String:
  +path = B.Buf.path(B.Files.at(files, i))
  B.Path.child(B.Path.dir(path), path)

def Open.idx(+files: List<&2, T.Buf>, +i: Nat) -> Nat:
  C.Lines.index(Open.lst(files, i), Open.nm(files, i), 0n)

# After "-"
# ---------

def Open.q1(+fs: List<&2, T.Buf>, +n: T.St, +i: Nat, +e: {O.Oil.tgt(n) == T.File{i} : T.Tgt}, hr: {B.Tgt.real(S.St.files(n), O.Oil.tgt(n)) == True{} : Bool}, hf: {S.St.files(n) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>})
  -> {Laws.Spec.is_dir(O.Oil.tgt(Bk.Back.y1(n)), Laws.Spec.dir(Laws.Spec.path(fs, i))) == True{} : Bool}:
  +p = Laws.Spec.path(fs, i)
  +path = B.Buf.path(B.Files.at(S.St.files(n), i))
  %Equal.sym(T.Tgt, O.Oil.tgt(Bk.Back.y1(n)), T.Dir{Bk.Back.dir(n, i)}, Bk.Back.y1_tgt(n, i, e, hr)) : {Laws.Spec.is_dir(_, Laws.Spec.dir(p)) == True{} : Bool}
  %Equal.sym(String, path, p, Open.path(fs, S.St.files(n), i, hf)) : {String.eq(B.Path.dir(_), Laws.Spec.dir(p)) == True{} : Bool}
  %Equal.sym(String, B.Path.dir(p), Laws.Spec.dir(p), Pa.Path.dir_eq(p)) : {String.eq(_, Laws.Spec.dir(p)) == True{} : Bool}
  Tx.String.eq_refl(Laws.Spec.dir(p))

def Open.good_y1(+n: T.St, hg: O.Good(S.St.dirs(n), S.St.files(n))) -> O.Good(S.St.dirs(Bk.Back.y1(n)), S.St.files(Bk.Back.y1(n))):
  +y = Bk.Back.y(n)
  +h = C.Oil.here(O.Oil.idle(n))
  O.Oil.good_eq(Bk.Back.y1(n), n, Equal.trans(List<&2, T.Listing>, S.St.dirs(Bk.Back.y1(n)), S.St.dirs(y), S.St.dirs(n), Rc.Field.dirs_final(y), Rc.Keep.dirs(n, h)), Bk.Back.y1_files(n), hg)

# the window's lines after "-": the folder's listing
def Open.lines(+n: T.St, +i: Nat, +e: {O.Oil.tgt(n) == T.File{i} : T.Tgt}, hr: {B.Tgt.real(S.St.files(n), O.Oil.tgt(n)) == True{} : Bool}, hg: O.Good(S.St.dirs(n), S.St.files(n)))
  -> {Vim.Vim.lines(Bk.Back.y1(n)) == Open.lst(S.St.files(n), i) : List<&2, String>}:
  +y1 = Bk.Back.y1(n)
  +d = Bk.Back.dir(n, i)
  +ol = Open.lst(S.St.files(n), i)
  %Equal.sym(T.Tgt, O.Oil.tgt(y1), T.Dir{d}, Bk.Back.y1_tgt(n, i, e, hr)) : {B.Lines.some(C.St.lines.at(y1, _)) == ol : List<&2, String>}
  %Equal.sym(List<&2, String>, C.St.lines.at(y1, T.Dir{d}), B.Oil.list(S.St.files(y1), d), O.Oil.lines_dir(y1, d, Open.good_y1(n, hg))) : {B.Lines.some(_) == ol : List<&2, String>}
  %Equal.sym(List<&2, T.Buf>, S.St.files(y1), S.St.files(n), Bk.Back.y1_files(n)) : {B.Lines.some(B.Oil.list(_, d)) == ol : List<&2, String>}
  {==}

# the entry's index is on the listing
def Open.le(+files: List<&2, T.Buf>, +i: Nat, hmem: {Laws.Spec.has_line(Open.nm(files, i), Open.lst(files, i)) == True{} : Bool}) -> L.LE(Open.idx(files, i), M.Move.last_line(Open.lst(files, i))):
  +ol = Open.lst(files, i)
  +nm = Open.nm(files, i)
  +ix = Open.idx(files, i)
  +lt = Imp.use(Laws.Spec.has_line(nm, ol), Nat.is_lt(ix, Laws.Spec.count(ol)), hmem, Idx.lt(ol, nm))
  L.LE.cast_r(ix, Nat.sub(Laws.Spec.count(ol), 1n), Nat.sub(B.Lines.len(ol), 1n), Equal.cong(Nat, Nat, c => Nat.sub(c, 1n), Laws.Spec.count(ol), B.Lines.len(ol), Equal.sym(Nat, B.Lines.len(ol), Laws.Spec.count(ol), Tx.Count.eq(ol))), Lt.pred(ix, Laws.Spec.count(ol), lt))

# the cursor's line after "-": the entry's index
def Open.line(+n: T.St, +i: Nat, +hm: {S.St.mode(n) == T.Normal{} : T.Mode}, +e: {O.Oil.tgt(n) == T.File{i} : T.Tgt}, +hr: {B.Tgt.real(S.St.files(n), O.Oil.tgt(n)) == True{} : Bool}, hgz: O.Good(S.St.dirs(n), S.St.files(n)), hgy: O.Good(S.St.dirs(n), S.St.files(n)),
  hmem: {Laws.Spec.has_line(Open.nm(S.St.files(n), i), Open.lst(S.St.files(n), i)) == True{} : Bool})
  -> {Laws.Spec.at_line(Vim.Vim.frame(Bk.Back.y1(n))) == Open.idx(S.St.files(n), i) : Nat}:
  +z = O.Oil.idle(n)
  +h = C.Oil.here(z)
  +y = Bk.Back.y(n)
  +y1 = Bk.Back.y1(n)
  +fz = S.St.files(z)
  +fn = S.St.files(n)
  +ix = Open.idx(fn, i)
  +d = Bk.Back.dir(n, i)
  +dz = B.Path.dir(B.Buf.path(B.Files.at(fz, i)))
  +ez = Equal.trans(T.Tgt, O.Oil.tgt(z), O.Oil.tgt(n), T.File{i}, O.Oil.idle_tgt(n), e)
  gz = O.Oil.good_eq(z, n, O.Oil.idle_dirs(n), O.Oil.idle_files(n), hgz)
  gy = O.Oil.good_eq(y, n, Rc.Keep.dirs(n, h), Rc.Keep.files(n, h), hgy)
  +ls_y = M.Move.last_line(C.St.lines(y))
  %Equal.sym(Nat, Laws.Spec.at_line(Vim.Vim.frame(y1)), C.St.line(y1), El.ExLine.at_line(y1, Fi.Final.of(y), Bk.Back.y1_mode(n, hm))) : {_ == ix : Nat}
  %Equal.sym(Nat, C.St.line(y1), Nat.min(C.St.line(y), ls_y), O.Oil.fin_line(y, Bk.Back.real(n, i, e, hr))) : {_ == ix : Nat}
  %Equal.sym(Nat, C.St.line(y), C.St.line(h), O.Oil.keep_line(n, h)) : {Nat.min(_, ls_y) == ix : Nat}
  %Equal.sym(Nat, C.St.line(h), C.St.line(C.Oil.on(z, dz, Open.nm(fz, i))), Equal.cong(T.St, Nat, s => C.St.line(s), h, C.Oil.on(z, dz, Open.nm(fz, i)), O.Oil.here_is(z, i, ez))) : {Nat.min(_, ls_y) == ix : Nat}
  +lsz = C.St.lines.at(z, T.Dir{dz})
  %Equal.sym(Nat, C.St.line(C.Win.open(z, T.Dir{dz}, T.Pos{C.Lines.index(lsz, Open.nm(fz, i), 0n), 0n})), Nat.min(Nat.min(C.Lines.index(lsz, Open.nm(fz, i), 0n), M.Move.last_line(lsz)), M.Move.last_line(B.Lines.some(lsz))), O.Oil.open_line(z, T.Dir{dz}, T.Pos{C.Lines.index(lsz, Open.nm(fz, i), 0n), 0n})) : {Nat.min(_, ls_y) == ix : Nat}
  %Equal.sym(List<&2, String>, lsz, B.Oil.list(fz, dz), O.Oil.lines_dir(z, dz, gz)) : {Nat.min(Nat.min(Nat.min(C.Lines.index(_, Open.nm(fz, i), 0n), M.Move.last_line(_)), M.Move.last_line(B.Lines.some(_))), ls_y) == ix : Nat}
  %Equal.sym(List<&2, T.Buf>, fz, fn, O.Oil.idle_files(n)) : {Nat.min(Nat.min(Nat.min(C.Lines.index(Open.lst(_, i), Open.nm(_, i), 0n), M.Move.last_line(Open.lst(_, i))), M.Move.last_line(B.Lines.some(Open.lst(_, i)))), ls_y) == ix : Nat}
  +ol = Open.lst(fn, i)
  +l3 = Nat.min(Nat.min(ix, M.Move.last_line(ol)), M.Move.last_line(ol))
  %Equal.sym(T.Tgt, O.Oil.tgt(y), T.Dir{d}, Bk.Back.tgt(n, i, e)) : {Nat.min(l3, M.Move.last_line(B.Lines.some(C.St.lines.at(y, _)))) == ix : Nat}
  %Equal.sym(List<&2, String>, C.St.lines.at(y, T.Dir{d}), B.Oil.list(S.St.files(y), d), O.Oil.lines_dir(y, d, gy)) : {Nat.min(l3, M.Move.last_line(B.Lines.some(_))) == ix : Nat}
  %Equal.sym(List<&2, T.Buf>, S.St.files(y), fn, Rc.Keep.files(n, h)) : {Nat.min(l3, M.Move.last_line(B.Lines.some(B.Oil.list(_, d)))) == ix : Nat}
  Open.min3(ix, M.Move.last_line(ol), Open.le(fn, i, hmem))

def Open.q2(+fs: List<&2, T.Buf>, +n: T.St, +i: Nat, +hm: {S.St.mode(n) == T.Normal{} : T.Mode}, +e: {O.Oil.tgt(n) == T.File{i} : T.Tgt}, +hr: {B.Tgt.real(S.St.files(n), O.Oil.tgt(n)) == True{} : Bool}, +hf: {S.St.files(n) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, hg1: O.Good(S.St.dirs(n), S.St.files(n)), hg2: O.Good(S.St.dirs(n), S.St.files(n)), hg3: O.Good(S.St.dirs(n), S.St.files(n)),
  +hmem: {Laws.Spec.has_line(Open.nm(S.St.files(n), i), Open.lst(S.St.files(n), i)) == True{} : Bool})
  -> {String.eq(Laws.Spec.line(Vim.Vim.lines(Bk.Back.y1(n)), Laws.Spec.at_line(Vim.Vim.frame(Bk.Back.y1(n)))), Laws.Spec.base(Laws.Spec.path(fs, i))) == True{} : Bool}:
  +y1 = Bk.Back.y1(n)
  +fn = S.St.files(n)
  +ol = Open.lst(fn, i)
  +nm = Open.nm(fn, i)
  +ix = Open.idx(fn, i)
  +bp = Laws.Spec.base(Laws.Spec.path(fs, i))
  +path = B.Buf.path(B.Files.at(fn, i))
  %Equal.sym(List<&2, String>, Vim.Vim.lines(y1), ol, Open.lines(n, i, e, hr, hg1)) : {String.eq(Laws.Spec.line(_, Laws.Spec.at_line(Vim.Vim.frame(y1))), bp) == True{} : Bool}
  %Equal.sym(Nat, Laws.Spec.at_line(Vim.Vim.frame(y1)), ix, Open.line(n, i, hm, e, hr, hg2, hg3, hmem)) : {String.eq(Laws.Spec.line(ol, _), bp) == True{} : Bool}
  +hl = Imp.use(Laws.Spec.has_line(nm, ol), String.eq(Laws.Spec.line(ol, ix), nm), hmem, Idx.line(ol, nm))
  %Equal.sym(String, Laws.Spec.line(ol, ix), nm, Str.Str.eq_true(Laws.Spec.line(ol, ix), nm, hl)) : {String.eq(_, bp) == True{} : Bool}
  %Equal.sym(String, nm, Laws.Spec.base(path), Pa.Path.child_base(path)) : {String.eq(_, bp) == True{} : Bool}
  %Equal.sym(String, path, Laws.Spec.path(fs, i), Open.path(fs, fn, i, hf)) : {String.eq(Laws.Spec.base(_), bp) == True{} : Bool}
  Tx.String.eq_refl(bp)

# the entry is in the listing
def Open.mem(+fs: List<&2, T.Buf>, +n: T.St, +i: Nat, +hf: {S.St.files(n) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, hlt: {Nat.is_lt(i, Laws.Spec.nfiles(fs)) == True{} : Bool}, hne: {String.is_empty(Laws.Spec.base(Laws.Spec.path(fs, i))) == False{} : Bool})
  -> {Laws.Spec.has_line(Open.nm(S.St.files(n), i), Open.lst(S.St.files(n), i)) == True{} : Bool}:
  +fn = S.St.files(n)
  Bg.Bag.mem(B.Path.dir(B.Buf.path(B.Files.at(fn, i))), fn, i, Open.len(fs, fn, i, hf, hlt), Open.named(fs, fn, i, hf, hne))

# The law
# -------

def Open.Qs(+fs: List<&2, T.Buf>, +i: Nat, +s2: T.St) -> Bool:
  +p = Laws.Spec.path(fs, i)
  Bool.and(Laws.Spec.is_dir(Laws.F.tgt(Vim.Vim.frame(s2)), Laws.Spec.dir(p)), String.eq(Laws.Spec.line(Vim.Vim.lines(s2), Laws.Spec.at_line(Vim.Vim.frame(s2))), Laws.Spec.base(p)))

def Open.q(+fs: List<&2, T.Buf>, +n: T.St, +i: Nat, +hm: {S.St.mode(n) == T.Normal{} : T.Mode}, hp: {S.St.pend(n) == T.NoPend{} : T.Pend}, +e: {O.Oil.tgt(n) == T.File{i} : T.Tgt}, +hr: {B.Tgt.real(S.St.files(n), O.Oil.tgt(n)) == True{} : Bool}, +hf: {S.St.files(n) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>},
  hg1: O.Good(S.St.dirs(n), S.St.files(n)), hg2: O.Good(S.St.dirs(n), S.St.files(n)), hg3: O.Good(S.St.dirs(n), S.St.files(n)), hlt: {Nat.is_lt(i, Laws.Spec.nfiles(fs)) == True{} : Bool}, hne: {String.is_empty(Laws.Spec.base(Laws.Spec.path(fs, i))) == False{} : Bool})
  -> {Open.Qs(fs, i, Laws.Spec.press(n, "-")) == True{} : Bool}:
  +y1 = Bk.Back.y1(n)
  +p = Laws.Spec.path(fs, i)
  %Equal.sym(T.St, Laws.Spec.press(n, "-"), Vim.Vim.final(Vim.Vim.keep(n, Laws.Spec.after(K.Key.in(n, S.St.mode(n), "-")))), O.Oil.press(n, "-")) : {Open.Qs(fs, i, _) == True{} : Bool}
  %Equal.sym(T.St, Laws.Spec.after(K.Key.in(n, S.St.mode(n), "-")), C.Oil.here(O.Oil.idle(n)), O.Oil.dash(n, hm, hp)) : {Open.Qs(fs, i, Vim.Vim.final(Vim.Vim.keep(n, _))) == True{} : Bool}
  L.And.intro(Laws.Spec.is_dir(Laws.F.tgt(Vim.Vim.frame(y1)), Laws.Spec.dir(p)), String.eq(Laws.Spec.line(Vim.Vim.lines(y1), Laws.Spec.at_line(Vim.Vim.frame(y1))), Laws.Spec.base(p)),
    Open.q1(fs, n, i, e, hr, hf),
    Open.q2(fs, n, i, hm, e, hr, hf, hg1, hg2, hg3, Open.mem(fs, n, i, hf, hlt, hne)))

def Open.case(b: Bool, +fs: List<&2, T.Buf>, +n: T.St, +i: Nat, +hm: {S.St.mode(n) == T.Normal{} : T.Mode}, hp: {S.St.pend(n) == T.NoPend{} : T.Pend}, +e: {O.Oil.tgt(n) == T.File{i} : T.Tgt}, +hr: {B.Tgt.real(S.St.files(n), O.Oil.tgt(n)) == True{} : Bool}, +hf: {S.St.files(n) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>},
  hg1: O.Good(S.St.dirs(n), S.St.files(n)), hg2: O.Good(S.St.dirs(n), S.St.files(n)), hg3: O.Good(S.St.dirs(n), S.St.files(n)),
  +ep: {Bool.and(Nat.is_lt(i, Laws.Spec.nfiles(fs)), Bool.not(String.is_empty(Laws.Spec.base(Laws.Spec.path(fs, i))))) == b : Bool})
  -> {Bool.or(Bool.not(b), Open.Qs(fs, i, Laws.Spec.press(n, "-"))) == True{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      +lt = Nat.is_lt(i, Laws.Spec.nfiles(fs))
      +ne = Bool.not(String.is_empty(Laws.Spec.base(Laws.Spec.path(fs, i))))
      L.Or.r(Bool.not(True{}), Open.Qs(fs, i, Laws.Spec.press(n, "-")), Open.q(fs, n, i, hm, hp, e, hr, hf, hg1, hg2, hg3, L.And.l(lt, ne, ep), Not.inv(String.is_empty(Laws.Spec.base(Laws.Spec.path(fs, i))), L.And.r(lt, ne, ep))))

def Open.at(+fs: List<&2, T.Buf>, +n: T.St, +hm: {S.St.mode(n) == T.Normal{} : T.Mode}, hp: {S.St.pend(n) == T.NoPend{} : T.Pend}, +hr: {B.Tgt.real(S.St.files(n), O.Oil.tgt(n)) == True{} : Bool}, +hf: {S.St.files(n) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>},
  hg1: O.Good(S.St.dirs(n), S.St.files(n)), hg2: O.Good(S.St.dirs(n), S.St.files(n)), hg3: O.Good(S.St.dirs(n), S.St.files(n)), t: T.Tgt, +e: {O.Oil.tgt(n) == t : T.Tgt})
  -> {Laws.Claim.open.of(fs, n, t) == True{} : Bool}:
  match t:
    case T.Dir{path}:
      {==}
    case T.File{+i}:
      +prem = Bool.and(Nat.is_lt(i, Laws.Spec.nfiles(fs)), Bool.not(String.is_empty(Laws.Spec.base(Laws.Spec.path(fs, i)))))
      Open.case(prem, fs, n, i, hm, hp, e, hr, hf, hg1, hg2, hg3, {==})

def Open.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.open(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  +ev2 = Laws.Spec.snoc(evs, Laws.Spec.key("<Esc>"))
  Open.at(fs, n, Rc.Reach.normal_mode(fs, rows, cols, evs), Rc.Reach.normal_pend(fs, rows, cols, evs), O.Oil.run_real(fs, rows, cols, ev2), Rc.Reach.files_run(fs, rows, cols, ev2),
    O.Oil.run_good(fs, rows, cols, ev2), O.Oil.run_good(fs, rows, cols, ev2), O.Oil.run_good(fs, rows, cols, ev2), O.Oil.tgt(n), {==})

def OilLaws.oil_open(fs, rows, cols, evs):
  Open.law(fs, rows, cols, evs)
