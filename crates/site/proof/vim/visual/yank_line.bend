# eukhe.com's Neovim: the proof of LAW yank_line
# ==============================================
#
# On the editor after any events and an Esc (Idle.mk of it), Y on file i
# copies the cut of the file's text from where the cursor's line starts
# to where the next one starts (Vis.text): the line and its line break.

import Base
import ../../../vim/types.bend as T
import ../../../vim/text.bend as X
import ../../../vim/buf.bend as B
import ../../../vim/move.bend as M
import ../../../vim/st.bend as S
import ../../../vim/core.bend as C
import ../../../vim/visual.bend as Vi
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/visual.bend as VisualLaws
import ../../base.bend as L
import ../../base/final.bend as Fi
import ../../base/text.bend as Tx
import ../screen/base.bend as Sc
import ../motion/base.bend as Mo

# Text
# ----

def Drop.zero(s: String) -> {X.Text.drop(s, 0n) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

def Take.zero(s: String) -> {Vi.Vis.take(s, 0n) == SNil{} : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

def Take.nl(s: String) -> {Vi.Vis.take(String.append("\n", s), 1n) == "\n" : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      {==}

def Drop.app(a: String, +b: String, +k: Nat) -> {X.Text.drop(String.append(a, b), Nat.add(Vi.Vis.size(a), k)) == X.Text.drop(b, k) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      Drop.app(t, b, k)

def Take.app(a: String, +b: String, +k: Nat) -> {Vi.Vis.take(String.append(a, b), Nat.add(Vi.Vis.size(a), k)) == String.append(a, Vi.Vis.take(b, k)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{+h, t}:
      Equal.cong(String, String, x => SCon{h, x}, Vi.Vis.take(String.append(t, b), Nat.add(Vi.Vis.size(t), k)), String.append(t, Vi.Vis.take(b, k)), Take.app(t, b, k))

# Lines
# -----

# the text from where line l starts is the text of the lines from l
def Join.drop(l: Nat, ls: List<&2, String>) -> {X.Text.drop(Vi.Vis.join(ls), Vi.Vis.off(l, ls)) == Vi.Vis.join(B.Lines.drop(ls, l)) : String}:
  match l ls:
    case 0n Nil{}:
      {==}
    case 0n Con{+h, +t}:
      Drop.zero(Vi.Vis.join(Con{h, t}))
    case 1n+p Nil{}:
      {==}
    case 1n++p Con{+h, +t}:
      +rest = String.append("\n", Vi.Vis.join(t))
      %Equal.sym(String, X.Text.drop(String.append(h, rest), Nat.add(Vi.Vis.size(h), 1n+Vi.Vis.off(p, t))), X.Text.drop(rest, 1n+Vi.Vis.off(p, t)), Drop.app(h, rest, 1n+Vi.Vis.off(p, t))) : {_ == Vi.Vis.join(B.Lines.drop(t, p)) : String}
      Join.drop(p, t)

# the line after line l starts the line and its break later
def Off.succ(l: Nat, ls: List<&2, String>, h: L.LT(l, Laws.Spec.count(ls))) -> {Vi.Vis.off(1n+l, ls) == Nat.add(Vi.Vis.off(l, ls), 1n+Vi.Vis.size(B.Lines.at(ls, l))) : Nat}:
  match l ls:
    case 0n Nil{}:
      L.Bool.false_true({Vi.Vis.off(1n, Nil{}) == Nat.add(0n, 1n+Vi.Vis.size(SNil{})) : Nat}, h)
    case 0n Con{+hd, t}:
      L.Nat.add_comm(Vi.Vis.size(hd), 1n)
    case 1n+p Nil{}:
      L.Bool.false_true({Vi.Vis.off(2n+p, Nil{}) == Nat.add(0n, 1n+Vi.Vis.size(SNil{})) : Nat}, h)
    case 1n++p Con{+hd, +t}:
      +a = Vi.Vis.size(hd)
      +o = Vi.Vis.off(p, t)
      +n = {1n+Vi.Vis.size(B.Lines.at(t, p)) : Nat}
      +ih = Equal.cong(Nat, Nat, x => Nat.add(a, 1n+x), Vi.Vis.off(1n+p, t), Nat.add(o, n), Off.succ(p, t, h))
      Equal.trans(Nat, Nat.add(a, 1n+Vi.Vis.off(1n+p, t)), Nat.add(a, 1n+Nat.add(o, n)), Nat.add(Nat.add(a, 1n+o), n), ih, Equal.sym(Nat, Nat.add(Nat.add(a, 1n+o), n), Nat.add(a, Nat.add(1n+o, n)), L.Nat.add_assoc(a, 1n+o, n)))

def Lines.drop0(ls: List<&2, String>) -> {B.Lines.drop(ls, 0n) == ls : List<&2, String>}:
  match ls:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

# the lines from l, for a line l of ls: line l, then the rest
def Drop.at(l: Nat, ls: List<&2, String>, h: L.LT(l, Laws.Spec.count(ls))) -> {B.Lines.drop(ls, l) == Con{B.Lines.at(ls, l), B.Lines.drop(ls, 1n+l)} : List<&2, String>}:
  match l ls:
    case 0n Nil{}:
      L.Bool.false_true({B.Lines.drop(Nil{}, 0n) == Con{B.Lines.at(Nil{}, 0n), B.Lines.drop(Nil{}, 1n)} : List<&2, String>}, h)
    case 0n Con{+hd, t}:
      Equal.cong(List<&2, String>, List<&2, String>, x => Con{hd, x}, t, B.Lines.drop(t, 0n), Equal.sym(List<&2, String>, B.Lines.drop(t, 0n), t, Lines.drop0(t)))
    case 1n+p Nil{}:
      L.Bool.false_true({B.Lines.drop(Nil{}, 1n+p) == Con{B.Lines.at(Nil{}, 1n+p), B.Lines.drop(Nil{}, 2n+p)} : List<&2, String>}, h)
    case 1n+p Con{hd, t}:
      Drop.at(p, t, h)

def Pick.same(b: Bool, -p: T.Pos) -> {Bool.pick(T.Pos, b, p, p) == p : T.Pos}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# V's text of one line: the line and its line break
def Line.text(+ls: List<&2, String>, +l: Nat, +h: L.LT(l, Laws.Spec.count(ls))) -> {Vi.Vis.text(T.VLines{}, ls, T.Pos{l, 0n}, T.Pos{l, 0n}) == String.append(B.Lines.at(ls, l), "\n") : String}:
  +p = {T.Pos{l, 0n} : T.Pos}
  +j = Vi.Vis.join(ls)
  +o = Vi.Vis.off(l, ls)
  +line = B.Lines.at(ls, l)
  +n = {1n+Vi.Vis.size(line) : Nat}
  +jr = Vi.Vis.join(B.Lines.drop(ls, 1n+l))
  %Equal.sym(T.Pos, Bool.pick(T.Pos, Vi.Vis.le(p, p), p, p), p, Pick.same(Vi.Vis.le(p, p), p)) : {Vi.Vis.cut(j, Vi.Vis.ends(T.VLines{}, ls, _, Bool.pick(T.Pos, Vi.Vis.le(p, p), p, p))) == String.append(line, "\n") : String}
  %Equal.sym(T.Pos, Bool.pick(T.Pos, Vi.Vis.le(p, p), p, p), p, Pick.same(Vi.Vis.le(p, p), p)) : {Vi.Vis.cut(j, Vi.Vis.ends(T.VLines{}, ls, p, _)) == String.append(line, "\n") : String}
  %Equal.sym(Nat, Vi.Vis.off(1n+l, ls), Nat.add(o, n), Off.succ(l, ls, h)) : {Vi.Vis.take(X.Text.drop(j, o), Nat.sub(_, o)) == String.append(line, "\n") : String}
  %Equal.sym(Nat, Nat.sub(Nat.add(o, n), o), n, L.Nat.add_sub_l(o, n)) : {Vi.Vis.take(X.Text.drop(j, o), _) == String.append(line, "\n") : String}
  %Equal.sym(String, X.Text.drop(j, o), Vi.Vis.join(B.Lines.drop(ls, l)), Join.drop(l, ls)) : {Vi.Vis.take(_, n) == String.append(line, "\n") : String}
  %Equal.sym(List<&2, String>, B.Lines.drop(ls, l), Con{line, B.Lines.drop(ls, 1n+l)}, Drop.at(l, ls, h)) : {Vi.Vis.take(Vi.Vis.join(_), n) == String.append(line, "\n") : String}
  %L.Nat.add_comm(Vi.Vis.size(line), 1n) : {Vi.Vis.take(String.append(line, String.append("\n", jr)), _) == String.append(line, "\n") : String}
  %Equal.sym(String, Vi.Vis.take(String.append(line, String.append("\n", jr)), Nat.add(Vi.Vis.size(line), 1n)), String.append(line, Vi.Vis.take(String.append("\n", jr), 1n)), Take.app(line, String.append("\n", jr), 1n)) : {_ == String.append(line, "\n") : String}
  %Equal.sym(String, Vi.Vis.take(String.append("\n", jr), 1n), "\n", Take.nl(jr)) : {String.append(line, _) == String.append(line, "\n") : String}
  {==}

# The law
# -------

def YankLine.core(+fs: List<&2, T.Buf>, s: T.St, +hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, +fin: Fi.Final(Mo.Idle.mk(s))) -> {Laws.Claim.yank_line(fs, Mo.Idle.mk(s)) == True{} : Bool}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.Dir{+d}:
              {==}
            case T.File{+i}:
              +z = Mo.Idle.mk(T.St{files, folded, dirs, T.Win{T.File{i}, cur, want, top, left}, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat})
              +raw = B.Buf.lines(B.Files.at(files, i))
              +ls = B.Lines.some(raw)
              +line = C.St.line(z)
              +ple = Mo.Fin.line_le(z, fin)
              +ple2 = L.LE.cast_r(line, Nat.sub(B.Lines.len(ls), 1n), Nat.sub(Laws.Spec.count(ls), 1n), Equal.cong(Nat, Nat, x => Nat.sub(x, 1n), B.Lines.len(ls), Laws.Spec.count(ls), Tx.Count.eq(ls)), ple)
              +hlt = Sc.Nat.le_pred_lt(line, Laws.Spec.count(ls), ple2, Sc.Some.count(raw))
              +tx = Vi.Vis.text(T.VLines{}, ls, T.Pos{line, 0n}, T.Pos{line, 0n})
              %Equal.sym(Nat, Nat.add(top, Nat.sub(line, top)), line, Mo.AtLine(z, fin)) : {String.eq(tx, String.append(Laws.Spec.line(Laws.Spec.lines(fs, z), _), "\n")) == True{} : Bool}
              %Equal.sym(List<&2, String>, Laws.Spec.lines(fs, z), ls, Mo.Lines.spec(fs, z, hf)) : {String.eq(tx, String.append(Laws.Spec.line(_, line), "\n")) == True{} : Bool}
              %Tx.Line.eq(ls, line) : {String.eq(tx, String.append(_, "\n")) == True{} : Bool}
              Tx.String.eq_same(tx, String.append(B.Lines.at(ls, line), "\n"), Line.text(ls, line, hlt))

def YankLine.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.yank_line(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  %Equal.sym(T.St, n, Mo.Idle.mk(n), Mo.Ready.eta(fs, rows, cols, evs)) : {Laws.Claim.yank_line(fs, _) == True{} : Bool}
  YankLine.core(fs, n, Mo.Ready.files(fs, rows, cols, evs), Mo.Ready.fin(fs, rows, cols, evs))

def VisualLaws.yank_line(fs, rows, cols, evs):
  YankLine.law(fs, rows, cols, evs)
