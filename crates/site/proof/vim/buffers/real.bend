# eukhe.com's Neovim: the window shows a real buffer
# ==================================================
#
# Vim.final ends with Vim.real: the window keeps its target when
# B.Tgt.real holds of it, else it shows file 0, which is real too, and
# Vim.fit (Win.settle) keeps the target (Real.of). Over the files the
# start made of fs, B.Tgt.real is the spec's Spec.real (Real.spec).

import Base
import ../../../vim/types.bend as T
import ../../../vim/text.bend as X
import ../../../vim/buf.bend as B
import ../../../vim/st.bend as S
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../base.bend as L
import ../../base/reach.bend as Re
import ../screen/base.bend as Sb

# Vim.real
# --------

# file 0 is real over any files
def Real.zero(n: Nat) -> {Nat.is_lt(0n, Nat.max(n, 1n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# the window Vim.real picks shows a real target (e: whether tgt is real)
def Real.pick(+fs: List<&2, T.Buf>, +tgt: T.Tgt, b: Bool, -cur: T.Pos, -want: T.Want, -top: Nat, -left: Nat, e: {B.Tgt.real(fs, tgt) == b : Bool})
  -> {B.Tgt.real(fs, S.Win.tgt(Bool.pick(T.Win, b, T.Win{tgt, cur, want, top, left}, T.Win{T.File{0n}, T.Pos{0n, 0n}, T.Col{0n}, 0n, 0n}))) == True{} : Bool}:
  match b:
    case True{}:
      e
    case False{}:
      Real.zero(B.Files.len(fs))

# the window after Vim.real shows a real target
def Real.win(+fs: List<&2, T.Buf>, w: T.Win) -> {B.Tgt.real(fs, S.Win.tgt(Vim.Vim.real(fs, w))) == True{} : Bool}:
  match w:
    case T.Win{+tgt, cur, want, top, left}:
      Real.pick(fs, tgt, B.Tgt.real(fs, tgt), cur, want, top, left, {==})

# Vim.fit (Win.settle) keeps what the window shows
def Real.fit(+y: T.St) -> {S.Win.tgt(S.St.win(Vim.Vim.fit(y))) == S.Win.tgt(S.St.win(y)) : T.Tgt}:
  match y:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

# the settled editor shows a real target over its files
def Real.of(+x: T.St) -> {B.Tgt.real(S.St.files(x), S.Win.tgt(S.St.win(Vim.Vim.final(x)))) == True{} : Bool}:
  match x:
    case T.St{+files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      Real.win(files, win)

# Characters
# ----------

# a comparison seen from the other side
def Cmp.flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

def Flip.eq(c: Cmp) -> {Cmp.is_eq(Cmp.flip(c)) == Cmp.is_eq(c) : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def Flip.bool(a: Bool, b: Bool) -> {Bool.cmp(a, b) == Cmp.flip(Bool.cmp(b, a)) : Cmp}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      {==}

def Flip.fin(c: Cmp, a: Bool, b: Bool) -> {Word.cmp.fin(a, b, Cmp.flip(c)) == Cmp.flip(Word.cmp.fin(b, a, c)) : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Flip.bool(a, b)
    case GT{}:
      {==}

# comparing two words one way is comparing them the other way, flipped
def Flip.word(n: Nat, a: Word(n), b: Word(n)) -> {Word.cmp(n, a, b) == Cmp.flip(Word.cmp(n, b, a)) : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          %Equal.sym(Cmp, Word.cmp(p, at, bt), Cmp.flip(Word.cmp(p, bt, at)), Flip.word(p, at, bt)) : {Word.cmp.fin(ab, bb, _) == Cmp.flip(Word.cmp.fin(bb, ab, Word.cmp(p, bt, at))) : Cmp}
          Flip.fin(Word.cmp(p, bt, at), ab, bb)

# two characters are equal either way round
def Char.eq_comm(a: Char, b: Char) -> {Char.is_eq(a, b) == Char.is_eq(b, a) : Bool}:
  match a b:
    case Chr{U32{+wx}} Chr{U32{+wy}}:
      +c = Word.cmp(32n, wy, wx)
      Equal.trans(Bool, Cmp.is_eq(Word.cmp(32n, wx, wy)), Cmp.is_eq(Cmp.flip(c)), Cmp.is_eq(c), Equal.cong(Cmp, Bool, k => Cmp.is_eq(k), Word.cmp(32n, wx, wy), Cmp.flip(c), Flip.word(32n, wx, wy)), Flip.eq(c))

# B.Tgt.real is Spec.real
# -----------------------

# a prefix check that failed stays failed
def Prefix.fail(s: String, p: String) -> {X.Text.prefix.go(s, p, False{}) == False{} : Bool}:
  match s p:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, yt}:
      {==}
    case SCon{x, xt} SNil{}:
      {==}
    case SCon{x, xt} SCon{y, yt}:
      Prefix.fail(xt, Bool.pick(String, Char.is_eq(x, y), yt, ""))

def Prefix.step(xt: String, -yt: String, b: Bool, ih: {X.Text.prefix.go(xt, yt, True{}) == Laws.Spec.prefix(yt, xt) : Bool})
  -> {X.Text.prefix.go(xt, Bool.pick(String, b, yt, ""), b) == Bool.and(b, Laws.Spec.prefix(yt, xt)) : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      Prefix.fail(xt, "")

def Prefix.go(s: String, p: String) -> {X.Text.prefix.go(s, p, True{}) == Laws.Spec.prefix(p, s) : Bool}:
  match s p:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{+y, +yt}:
      {==}
    case SCon{+x, +xt} SNil{}:
      {==}
    case SCon{+x, +xt} SCon{+y, +yt}:
      %Char.eq_comm(x, y) : {X.Text.prefix.go(xt, Bool.pick(String, Char.is_eq(x, y), yt, ""), Char.is_eq(x, y)) == Bool.and(_, Laws.Spec.prefix(yt, xt)) : Bool}
      Prefix.step(xt, yt, Char.is_eq(x, y), Prefix.go(xt, yt))

# X.Text.prefix is the spec's
def Prefix.eq(p: String, s: String) -> {X.Text.prefix(p, s) == Laws.Spec.prefix(p, s) : Bool}:
  Prefix.go(s, p)

# a nonempty path is a folder's when its last character is "/"
def Slash.cons(t: String, h: Char) -> {B.Path.is_dir(SCon{h, t}) == Laws.Spec.ends_slash(SCon{h, t}) : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{h2, t2}:
      Slash.cons(t2, h2)

# B.Path.is_dir is Spec.ends_slash
def Slash.eq(s: String) -> {B.Path.is_dir(s) == Laws.Spec.ends_slash(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Slash.cons(t, h)

# the files held count the files given
def Count.go(fs: List<&2, T.Buf>, +acc: Nat) -> {B.Files.len.go(Sb.Files.norm(fs), acc) == Nat.add(acc, Laws.Spec.nfiles(fs)) : Nat}:
  match fs:
    case Nil{}:
      L.Nat.add_zero(acc)
    case Con{T.Buf{p, ls}, t}:
      Equal.trans(Nat, B.Files.len.go(Sb.Files.norm(t), 1n+acc), Nat.add(1n+acc, Laws.Spec.nfiles(t)), Nat.add(acc, 1n+Laws.Spec.nfiles(t)), Count.go(t, 1n+acc), L.Nat.add_succ(acc, Laws.Spec.nfiles(t)))

# a folder holds a file the editor holds when it holds one given
def Under.eq(+d: String, fs: List<&2, T.Buf>) -> {B.Files.under(d, Sb.Files.norm(fs)) == Laws.Spec.is_folder(d, fs) : Bool}:
  match fs:
    case Nil{}:
      {==}
    case Con{T.Buf{+p, ls}, t}:
      %Prefix.eq(d, p) : {Bool.or(X.Text.prefix(d, p), B.Files.under(d, Sb.Files.norm(t))) == Bool.or(_, Laws.Spec.is_folder(d, t)) : Bool}
      %Under.eq(d, t) : {Bool.or(X.Text.prefix(d, p), B.Files.under(d, Sb.Files.norm(t))) == Bool.or(X.Text.prefix(d, p), _) : Bool}
      {==}

# over the normalized files, B.Tgt.real is Spec.real
def Real.norm(+fs: List<&2, T.Buf>, t: T.Tgt) -> {B.Tgt.real(Sb.Files.norm(fs), t) == Laws.Spec.real(fs, t) : Bool}:
  match t:
    case T.File{+i}:
      %Equal.sym(Nat, B.Files.len.go(Sb.Files.norm(fs), 0n), Nat.add(0n, Laws.Spec.nfiles(fs)), Count.go(fs, 0n)) : {Nat.is_lt(i, Nat.max(_, 1n)) == Nat.is_lt(i, Laws.Spec.max(Laws.Spec.nfiles(fs), 1n)) : Bool}
      %Re.Spec.max_eq(Laws.Spec.nfiles(fs), 1n) : {Nat.is_lt(i, _) == Nat.is_lt(i, Laws.Spec.max(Laws.Spec.nfiles(fs), 1n)) : Bool}
      {==}
    case T.Dir{+d}:
      %Slash.eq(d) : {Bool.or(String.is_empty(d), Bool.and(B.Path.is_dir(d), B.Files.under(d, Sb.Files.norm(fs)))) == Bool.or(String.is_empty(d), Bool.and(_, Laws.Spec.is_folder(d, fs))) : Bool}
      %Under.eq(d, fs) : {Bool.or(String.is_empty(d), Bool.and(B.Path.is_dir(d), B.Files.under(d, Sb.Files.norm(fs)))) == Bool.or(String.is_empty(d), Bool.and(B.Path.is_dir(d), _)) : Bool}
      {==}

# over the files the start made of fs, B.Tgt.real is Spec.real
def Real.spec(+fs: List<&2, T.Buf>, +t: T.Tgt) -> {B.Tgt.real(B.Files.some(fs, Nil{}), t) == Laws.Spec.real(fs, t) : Bool}:
  %Equal.sym(List<&2, T.Buf>, B.Files.some(fs, Nil{}), List.reverse.go(&2, T.Buf, Nil{}, Sb.Files.norm(fs)), Sb.Files.some_go(fs, Nil{})) : {B.Tgt.real(_, t) == Laws.Spec.real(fs, t) : Bool}
  Real.norm(fs, t)
