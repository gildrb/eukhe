# eukhe.com's Neovim: the proof of LAW yank_char
# ==============================================
#
# On the editor after any events and an Esc (Idle.mk of it), v on file i
# starts a selection at the cursor and leaves the window as it was
# (Settle.vis); y then copies the cut of the file's text from the
# cursor's character to the next one: that character, or on an empty line
# its line break.

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
import ../esc/base.bend as Eb
import ./yank_line.bend as Yl

# The text
# --------

def Drop.add(s: String, a: Nat, +b: Nat) -> {X.Text.drop(s, Nat.add(a, b)) == X.Text.drop(X.Text.drop(s, a), b) : String}:
  match s a:
    case SNil{} _:
      {==}
    case SCon{h, t} 0n:
      {==}
    case SCon{h, t} 1n+p:
      Drop.add(t, p, b)

def One.of(c: Nat) -> {Nat.sub(1n+c, c) == 1n : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      One.of(p)

# the character at column c of a line and its break, c at most the line's
# length (the break itself at its length)
def Char.cut(l: String, +r: String, c: Nat, hc: L.LE(c, Laws.Spec.chars(l))) -> {Vi.Vis.take(X.Text.drop(String.append(l, String.append("\n", r)), c), 1n) == Laws.Spec.char_at(String.append(l, "\n"), c) : String}:
  match l c:
    case SNil{} 0n:
      Yl.Take.nl(r)
    case SNil{} 1n+p:
      L.Bool.false_true({Vi.Vis.take(X.Text.drop(String.append("\n", r), 1n+p), 1n) == Laws.Spec.char_at("\n", 1n+p) : String}, hc)
    case SCon{+h, t} 0n:
      Equal.cong(String, String, x => SCon{h, x}, Vi.Vis.take(String.append(t, String.append("\n", r)), 0n), SNil{}, Yl.Take.zero(String.append(t, String.append("\n", r))))
    case SCon{h, t} 1n+p:
      Char.cut(t, r, p, hc)

# v's text of one position: the character there, or the line break
def Char.text(+ls: List<&2, String>, +l: Nat, +c: Nat, +h: L.LT(l, Laws.Spec.count(ls)), hc: L.LE(c, Laws.Spec.chars(B.Lines.at(ls, l)))) -> {Vi.Vis.text(T.VChars{}, ls, T.Pos{l, c}, T.Pos{l, c}) == Laws.Spec.char_at(String.append(B.Lines.at(ls, l), "\n"), c) : String}:
  +p = {T.Pos{l, c} : T.Pos}
  +j = Vi.Vis.join(ls)
  +o = Vi.Vis.off(l, ls)
  +line = B.Lines.at(ls, l)
  +jr = Vi.Vis.join(B.Lines.drop(ls, 1n+l))
  +goal = String.append(line, "\n")
  %Equal.sym(T.Pos, Bool.pick(T.Pos, Vi.Vis.le(p, p), p, p), p, Yl.Pick.same(Vi.Vis.le(p, p), p)) : {Vi.Vis.cut(j, Vi.Vis.ends(T.VChars{}, ls, _, Bool.pick(T.Pos, Vi.Vis.le(p, p), p, p))) == Laws.Spec.char_at(goal, c) : String}
  %Equal.sym(T.Pos, Bool.pick(T.Pos, Vi.Vis.le(p, p), p, p), p, Yl.Pick.same(Vi.Vis.le(p, p), p)) : {Vi.Vis.cut(j, Vi.Vis.ends(T.VChars{}, ls, p, _)) == Laws.Spec.char_at(goal, c) : String}
  %Equal.sym(Nat, Nat.sub(Nat.add(o, 1n+c), Nat.add(o, c)), Nat.sub(1n+c, c), L.Nat.sub_cancel_l(o, 1n+c, c)) : {Vi.Vis.take(X.Text.drop(j, Nat.add(o, c)), _) == Laws.Spec.char_at(goal, c) : String}
  %Equal.sym(Nat, Nat.sub(1n+c, c), 1n, One.of(c)) : {Vi.Vis.take(X.Text.drop(j, Nat.add(o, c)), _) == Laws.Spec.char_at(goal, c) : String}
  %Equal.sym(String, X.Text.drop(j, Nat.add(o, c)), X.Text.drop(X.Text.drop(j, o), c), Drop.add(j, o, c)) : {Vi.Vis.take(_, 1n) == Laws.Spec.char_at(goal, c) : String}
  %Equal.sym(String, X.Text.drop(j, o), Vi.Vis.join(B.Lines.drop(ls, l)), Yl.Join.drop(l, ls)) : {Vi.Vis.take(X.Text.drop(_, c), 1n) == Laws.Spec.char_at(goal, c) : String}
  %Equal.sym(List<&2, String>, B.Lines.drop(ls, l), Con{line, B.Lines.drop(ls, 1n+l)}, Yl.Drop.at(l, ls, h)) : {Vi.Vis.take(X.Text.drop(Vi.Vis.join(_), c), 1n) == Laws.Spec.char_at(goal, c) : String}
  Char.cut(line, jr, c, hc)

# The editor
# ----------

# a visual-mode editor with window w
def Vis.at(files: List<&2, T.Buf>, folded: List<&2, List<&2, String>>, dirs: List<&2, T.Listing>, marks: List<&2, T.Pos>, spots: List<&2, T.Spot>, opened: List<&2, Nat>, bufs: List<&2, Nat>, back: List<&2, T.Win>, fwd: List<&2, T.Win>, count: Nat, pend: T.Pend, find: Maybe<&2, T.Find>, hl: Bool, opts: T.Opts, rows: Nat, cols: Nat, msg: String, stat: String, k: T.Vis, start: T.Pos, w: T.Win) -> T.St:
  T.St{files, folded, dirs, w, marks, spots, opened, bufs, back, fwd, T.Visual{k, start}, count, pend, find, hl, opts, rows, cols, msg, stat}

# Vim.final keeps a settled visual-mode editor on a real buffer, up to
# the column j and k aim for (Settle.self, in visual mode)
def Settle.vis(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +count: Nat, +pend: T.Pend, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String,
  +k: T.Vis, +start: T.Pos, +tgt: T.Tgt, +line: Nat, +col: Nat, +want: T.Want, +top: Nat, +left: Nat,
  fin: Fi.Final(Vis.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, pend, find, hl, opts, rows, cols, msg, stat, k, start, T.Win{tgt, T.Pos{line, col}, want, top, left})),
  hr: {B.Tgt.real(files, tgt) == True{} : Bool})
  -> {Vis.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, pend, find, hl, opts, rows, cols, msg, stat, k, start, T.Win{tgt, T.Pos{line, col}, C.Want.at(C.St.lines(Vis.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, pend, find, hl, opts, rows, cols, msg, stat, k, start, T.Win{tgt, T.Pos{line, col}, want, top, left})), T.Pos{line, col}, want), top, left})
      == Vim.Vim.final(Vis.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, pend, find, hl, opts, rows, cols, msg, stat, k, start, T.Win{tgt, T.Pos{line, col}, want, top, left})) : T.St}:
  match fin:
    case (e3, r1):
      match r1:
        case (e12, r2):
          match r2:
            case (el, r3):
              match r3:
                case (ec, r4):
                  match r4:
                    case (bt, bs):
                      +x = Vis.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, pend, find, hl, opts, rows, cols, msg, stat, k, start, T.Win{tgt, T.Pos{line, col}, want, top, left})
                      -xw = Vis.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, pend, find, hl, opts, rows, cols, msg, stat, k, start, T.Win{tgt, T.Pos{line, col}, C.Want.at(C.St.lines(x), T.Pos{line, col}, want), top, left})
                      %Eb.Esc.real_back(files, T.Win{tgt, T.Pos{line, col}, want, top, left}, hr) : {xw == Vim.Vim.fit(S.St.set_win(x, _)) : T.St}
                      %Eb.Esc.max_back(rows, 3n, e3) : {xw == C.Win.settle(S.St.set_cols(S.St.set_rows(x, _), Nat.max(cols, 12n))) : T.St}
                      %Eb.Esc.max_back(cols, 12n, e12) : {xw == C.Win.settle(S.St.set_cols(x, _)) : T.St}
                      %Eb.Settle.win(C.St.lines(x), C.St.h(x), C.St.w(x), tgt, line, col, want, top, left, el, ec, bt, bs) : {xw == S.St.set_win(x, _) : T.St}
                      {==}

# The law
# -------

def YankChar.core(+fs: List<&2, T.Buf>, s: T.St, +hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, +hr: {B.Tgt.real(S.St.files(s), S.Win.tgt(S.St.win(s))) == True{} : Bool}, +fin: Fi.Final(Mo.Idle.mk(s))) -> {Laws.Claim.yank_char(fs, Mo.Idle.mk(s)) == True{} : Bool}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{tgt, cur, +want, +top, +left}:
          match tgt:
            case T.Dir{+d}:
              {==}
            case T.File{+i}:
              match cur:
                case T.Pos{+line, +col}:
                  +w = {T.Win{T.File{i}, T.Pos{line, col}, want, top, left} : T.Win}
                  +z = Mo.Idle.mk(T.St{files, folded, dirs, w, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat})
                  +raw = B.Buf.lines(B.Files.at(files, i))
                  +ls = B.Lines.some(raw)
                  +p = {T.Pos{line, col} : T.Pos}
                  +op = Vim.Vim.opened(opened)
                  +v0 = Vis.at(files, folded, dirs, marks, spots, op, bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, p, w)
                  +v1 = Vis.at(files, folded, dirs, marks, spots, op, bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, p, T.Win{T.File{i}, p, C.Want.at(C.St.lines(v0), p, want), top, left})
                  +ple = Mo.Fin.line_le(z, fin)
                  +ple2 = L.LE.cast_r(line, Nat.sub(B.Lines.len(ls), 1n), Nat.sub(Laws.Spec.count(ls), 1n), Equal.cong(Nat, Nat, x => Nat.sub(x, 1n), B.Lines.len(ls), Laws.Spec.count(ls), Tx.Count.eq(ls)), ple)
                  +hlt = Sc.Nat.le_pred_lt(line, Laws.Spec.count(ls), ple2, Sc.Some.count(raw))
                  +lt = B.Lines.at(ls, line)
                  +pce = L.Nat.le_trans(col, Nat.sub(X.Text.len(lt), 1n), X.Text.len(lt), Mo.Fin.col_le(z, fin), L.Nat.sub_le(X.Text.len(lt), 1n))
                  +hce = L.LE.cast_r(col, X.Text.len(lt), Laws.Spec.chars(lt), Tx.Chars.eq(lt), pce)
                  +tx = Vi.Vis.text(T.VChars{}, ls, p, p)
                  +tgt0 = Laws.Spec.char_at(String.append(Laws.Spec.line(Laws.Spec.lines(fs, z), Laws.Spec.at_line(Vim.Vim.frame(z))), "\n"), Laws.Spec.at_col(Vim.Vim.frame(z)))
                  %Settle.vis(files, folded, dirs, marks, spots, op, bufs, back, fwd, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat, T.VChars{}, p, T.File{i}, line, col, want, top, left, fin, hr) : {Laws.Spec.copies(Laws.Spec.act(Vim.Vim.step(_, Laws.Spec.key("y"))), tgt0) == True{} : Bool}
                  %Equal.sym(Nat, Nat.add(top, Nat.sub(line, top)), line, Mo.AtLine(z, fin)) : {String.eq(tx, Laws.Spec.char_at(String.append(Laws.Spec.line(Laws.Spec.lines(fs, z), _), "\n"), Laws.Spec.at_col(Vim.Vim.frame(z)))) == True{} : Bool}
                  %Equal.sym(Nat, Nat.add(left, Nat.sub(Nat.add(C.St.g(z), Nat.sub(col, left)), C.St.g(z))), col, Mo.AtCol(z, fin)) : {String.eq(tx, Laws.Spec.char_at(String.append(Laws.Spec.line(Laws.Spec.lines(fs, z), line), "\n"), _)) == True{} : Bool}
                  %Equal.sym(List<&2, String>, Laws.Spec.lines(fs, z), ls, Mo.Lines.spec(fs, z, hf)) : {String.eq(tx, Laws.Spec.char_at(String.append(Laws.Spec.line(_, line), "\n"), col)) == True{} : Bool}
                  %Tx.Line.eq(ls, line) : {String.eq(tx, Laws.Spec.char_at(String.append(_, "\n"), col)) == True{} : Bool}
                  Tx.String.eq_same(tx, Laws.Spec.char_at(String.append(lt, "\n"), col), Char.text(ls, line, col, hlt, hce))

def YankChar.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.yank_char(fs, Laws.Spec.normal(fs, rows, cols, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  %Equal.sym(T.St, n, Mo.Idle.mk(n), Mo.Ready.eta(fs, rows, cols, evs)) : {Laws.Claim.yank_char(fs, _) == True{} : Bool}
  YankChar.core(fs, n, Mo.Ready.files(fs, rows, cols, evs), Mo.Ready.real(fs, rows, cols, evs), Mo.Ready.fin(fs, rows, cols, evs))

def VisualLaws.yank_char(fs, rows, cols, evs):
  YankChar.law(fs, rows, cols, evs)
