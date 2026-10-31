# eukhe.com's Neovim: the proof of LAW click
# ==========================================
#
# A click on text row r < rows - 2 in normal mode is Win.go to (top + r,
# left + c - gutter) (Vim.click), then Vim.final. The window keeps its
# target (it is real: Real.of), and the three clamps (Win.go, its settle,
# Vim.final's settle) give the cursor min(top + r, last) and min(left + c -
# gutter, that line's last column). A settled frame reads them back.

import Base
import ../../../vim/types.bend as T
import ../../../vim/text.bend as X
import ../../../vim/buf.bend as B
import ../../../vim/move.bend as M
import ../../../vim/view.bend as V
import ../../../vim/st.bend as S
import ../../../vim/core.bend as C
import ../../../vim/screen.bend as R
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/mouse.bend as MouseLaws
import ../../base.bend as L
import ../../base/final.bend as Fi
import ../../base/reach.bend as Re
import ../../base/text.bend as Tx
import ../screen/base.bend as Sc
import ../buffers/real.bend as Rb

# Logic
# -----

def Ck.imp(p: Bool, -q: Bool, f: {p == True{} : Bool} -> {q == True{} : Bool}) -> {Laws.Spec.implies(p, q) == True{} : Bool}:
  match p:
    case True{}:
      f({==})
    case False{}:
      {==}

def Ck.eq(+a: Nat, -b: Nat, e: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  %e : {Nat.is_eq(a, _) == True{} : Bool}
  L.Nat.eq_refl(a)

# Clamps
# ------

def Ck.min_idem(a: Nat, +b: Nat) -> {Nat.min(Nat.min(a, b), b) == Nat.min(a, b) : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.min(Nat.min(p, q), q), Nat.min(p, q), Ck.min_idem(p, q))

def Ck.min_idem3(+a: Nat, +b: Nat) -> {Nat.min(Nat.min(Nat.min(a, b), b), b) == Nat.min(a, b) : Nat}:
  Equal.trans(Nat, Nat.min(Nat.min(Nat.min(a, b), b), b), Nat.min(Nat.min(a, b), b), Nat.min(a, b), Ck.min_idem(Nat.min(a, b), b), Ck.min_idem(a, b))

# the column after three clamps onto lines ls: the first clamp's
def Ck.col_idem3(+ls: List<&2, String>, +a: Nat, +b: Nat)
  -> {Nat.min(Nat.min(Nat.min(b, M.Move.last_col(ls, Nat.min(a, M.Move.last_line(ls)))), M.Move.last_col(ls, Nat.min(Nat.min(a, M.Move.last_line(ls)), M.Move.last_line(ls)))), M.Move.last_col(ls, Nat.min(Nat.min(Nat.min(a, M.Move.last_line(ls)), M.Move.last_line(ls)), M.Move.last_line(ls)))) == Nat.min(b, M.Move.last_col(ls, Nat.min(a, M.Move.last_line(ls)))) : Nat}:
  +z = M.Move.last_line(ls)
  +l1 = Nat.min(a, z)
  +l2 = Nat.min(l1, z)
  +l3 = Nat.min(l2, z)
  +k = M.Move.last_col(ls, l1)
  %Equal.sym(Nat, l2, l1, Ck.min_idem(a, z)) : {Nat.min(Nat.min(Nat.min(b, k), M.Move.last_col(ls, _)), M.Move.last_col(ls, l3)) == Nat.min(b, k) : Nat}
  %Equal.sym(Nat, l3, l1, Ck.min_idem3(a, z)) : {Nat.min(Nat.min(Nat.min(b, k), k), M.Move.last_col(ls, _)) == Nat.min(b, k) : Nat}
  Ck.min_idem3(b, k)

# The click's editor
# ------------------

# Vim.real keeps a real window
def Ck.real_keep(+fs: List<&2, T.Buf>, w: T.Win, h: {B.Tgt.real(fs, S.Win.tgt(w)) == True{} : Bool}) -> {Vim.Vim.real(fs, w) == w : T.Win}:
  match w:
    case T.Win{+tgt, +cur, +want, +top, +left}:
      %Equal.sym(Bool, B.Tgt.real(fs, tgt), True{}, h) : {Bool.pick(T.Win, _, T.Win{tgt, cur, want, top, left}, T.Win{T.File{0n}, T.Pos{0n, 0n}, T.Col{0n}, 0n, 0n}) == T.Win{tgt, cur, want, top, left} : T.Win}
      {==}

# Vim.final with its window w in place of Vim.real's (its one copy here:
# keep it in step with vim/vim.bend)
def Ck.final(+s: T.St, w: T.Win) -> T.St:
  +s2 = S.St.set_count(S.St.set_pend(s, Vim.Vim.pend(S.St.mode(s), S.St.pend(s))), Vim.Vim.count(S.St.mode(s), S.St.count(s)))
  Vim.Vim.fit(S.St.set_win(s2, w))

# Vim.final of an editor on a real window keeps it
def Ck.final_real(+x: T.St, h: {B.Tgt.real(S.St.files(x), S.Win.tgt(S.St.win(x))) == True{} : Bool}) -> {Vim.Vim.final(x) == Ck.final(x, S.St.win(x)) : T.St}:
  Equal.cong(T.Win, T.St, z => Ck.final(x, z), Vim.Vim.real(S.St.files(x), S.St.win(x)), S.St.win(x), Ck.real_keep(S.St.files(x), S.St.win(x), h))

# the editor a click in the text gives, before Vim.final: Win.go to (a, b)
def Ck.x(+s: T.St, +a: Nat, +b: Nat) -> T.St:
  Vim.Vim.keep(s, C.Win.go(S.St.set_count(S.St.set_pend(s, T.NoPend{}), 0n), T.Pos{a, b}, False{}))

# and after it, on its real window
def Ck.fx(+s: T.St, +a: Nat, +b: Nat) -> T.St:
  Ck.final(Ck.x(s, a, b), S.St.win(Ck.x(s, a, b)))

def Ck.click_go(+s: T.St, +r: Nat, +c: Nat, hr: {Nat.is_lt(r, C.St.h(s)) == True{} : Bool})
  -> {Vim.Vim.click(s, T.Normal{}, r, c) == C.Win.go(S.St.set_count(S.St.set_pend(s, T.NoPend{}), 0n), T.Pos{Nat.add(S.Win.top(S.St.win(s)), r), Nat.add(S.Win.left(S.St.win(s)), Nat.sub(c, C.St.g(s)))}, False{}) : T.St}:
  +s2 = S.St.set_count(S.St.set_pend(s, T.NoPend{}), 0n)
  +go = C.Win.go(s2, T.Pos{Nat.add(S.Win.top(S.St.win(s)), r), Nat.add(S.Win.left(S.St.win(s)), Nat.sub(c, C.St.g(s)))}, False{})
  %Equal.sym(Bool, Nat.is_lt(r, C.St.h(s)), True{}, hr) : {X.Bool.when(T.St, _, u => s2, u => go) == go : T.St}
  {==}

def Ck.next(+s: T.St, +r: Nat, +c: Nat, hm: {S.St.mode(s) == T.Normal{} : T.Mode}, hr: {Nat.is_lt(r, C.St.h(s)) == True{} : Bool})
  -> {Re.Reach.next(s, T.EvClick{r, c}) == Ck.x(s, Nat.add(S.Win.top(S.St.win(s)), r), Nat.add(S.Win.left(S.St.win(s)), Nat.sub(c, C.St.g(s)))) : T.St}:
  +go = C.Win.go(S.St.set_count(S.St.set_pend(s, T.NoPend{}), 0n), T.Pos{Nat.add(S.Win.top(S.St.win(s)), r), Nat.add(S.Win.left(S.St.win(s)), Nat.sub(c, C.St.g(s)))}, False{})
  %Equal.sym(T.Mode, S.St.mode(s), T.Normal{}, hm) : {Vim.Vim.keep(s, Vim.Vim.click(s, _, r, c)) == Vim.Vim.keep(s, go) : T.St}
  Equal.cong(T.St, T.St, z => Vim.Vim.keep(s, z), Vim.Vim.click(s, T.Normal{}, r, c), go, Ck.click_go(s, r, c, hr))

def Ck.x_real(+s: T.St, +a: Nat, +b: Nat, h: {B.Tgt.real(S.St.files(s), S.Win.tgt(S.St.win(s))) == True{} : Bool})
  -> {B.Tgt.real(S.St.files(Ck.x(s, a, b)), S.Win.tgt(S.St.win(Ck.x(s, a, b)))) == True{} : Bool}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          h

def Ck.fx_tgt(+s: T.St, +a: Nat, +b: Nat) -> {S.Win.tgt(S.St.win(Ck.fx(s, a, b))) == S.Win.tgt(S.St.win(s)) : T.Tgt}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          {==}

def Ck.fx_mode(+s: T.St, +a: Nat, +b: Nat) -> {S.St.mode(Ck.fx(s, a, b)) == S.St.mode(s) : T.Mode}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          {==}

def Ck.fx_line(+s: T.St, +a: Nat, +b: Nat) -> {C.St.line(Ck.fx(s, a, b)) == Nat.min(a, M.Move.last_line(C.St.lines(s))) : Nat}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.File{+i}:
              Ck.min_idem3(a, M.Move.last_line(C.St.lines(T.St{files, folded, dirs, T.Win{T.File{i}, cur, want, top, left}, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat})))
            case T.Dir{+path}:
              Ck.min_idem3(a, M.Move.last_line(C.St.lines(T.St{files, folded, dirs, T.Win{T.Dir{path}, cur, want, top, left}, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat})))

def Ck.fx_col(+s: T.St, +a: Nat, +b: Nat) -> {C.St.col(Ck.fx(s, a, b)) == Nat.min(b, M.Move.last_col(C.St.lines(s), Nat.min(a, M.Move.last_line(C.St.lines(s))))) : Nat}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.File{+i}:
              Ck.col_idem3(C.St.lines(T.St{files, folded, dirs, T.Win{T.File{i}, cur, want, top, left}, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}), a, b)
            case T.Dir{+path}:
              Ck.col_idem3(C.St.lines(T.St{files, folded, dirs, T.Win{T.Dir{path}, cur, want, top, left}, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}), a, b)

def Ck.fin_fx(+s: T.St, +a: Nat, +b: Nat, h: {B.Tgt.real(S.St.files(s), S.Win.tgt(S.St.win(s))) == True{} : Bool}) -> Fi.Final(Ck.fx(s, a, b)):
  +x = Ck.x(s, a, b)
  %Ck.final_real(x, Ck.x_real(s, a, b, h)) : Fi.Final(_)
  Fi.Final.of(x)

# The frame
# ---------

# Scr.frame in mode m (its one copy here: keep it in step with
# vim/screen.bend)
def Ck.frame(+s: T.St, +m: T.Mode) -> T.Frame:
  +w = S.St.win(s)
  +ls = C.St.lines(s)
  +n = B.Lines.len(ls)
  +h = C.St.h(s)
  +numw = V.View.numw(S.St.opts(s), n)
  +nums = V.View.nums(h, S.St.opts(s), S.Win.top(w), C.St.line(s), Nat.sub(n, 1n), numw, C.St.on_file(s), C.St.g(s))
  +fl = R.Scr.float(s, m)
  T.Frame{S.Win.tgt(w), S.Win.top(w), S.Win.left(w), C.St.g(s), nums, R.Scr.inside(R.Scr.cell(s, m), fl), R.Scr.under(s, m), R.Scr.cmd(s, m), R.Scr.hits(s, R.Scr.lit(s, m)), V.View.bar(n, h, S.Win.top(w), Nat.sub(S.St.cols(s), 1n)), R.Scr.cl(m), R.Scr.status_of(s, m), fl}

# a settled editor in normal mode: the frame reads back the cursor's line
def Ck.frame_line(+y: T.St, fin: Fi.Final(y), hm: {S.St.mode(y) == T.Normal{} : T.Mode}) -> {Laws.Spec.at_line(Vim.Vim.frame(y)) == C.St.line(y) : Nat}:
  (f3, r1) = fin
  (f12, r2) = r1
  (fl, r3) = r2
  (fc, r4) = r3
  (bt, bl) = r4
  (bth, btl) = bt
  +h = V.View.text_rows(S.St.rows(y))
  %Equal.sym(T.Mode, S.St.mode(y), T.Normal{}, hm) : {Laws.Spec.at_line(Ck.frame(y, _)) == C.St.line(y) : Nat}
  L.Nat.add_sub(C.St.line(y), S.Win.top(S.St.win(y)), Sc.Win.top_le(C.St.line(y), V.View.so_in(h), S.Win.top(S.St.win(y)), btl))

# and its column
def Ck.frame_col(+y: T.St, fin: Fi.Final(y), hm: {S.St.mode(y) == T.Normal{} : T.Mode}) -> {Laws.Spec.at_col(Vim.Vim.frame(y)) == C.St.col(y) : Nat}:
  (f3, r1) = fin
  (f12, r2) = r1
  (fl, r3) = r2
  (fc, r4) = r3
  (bt, bl) = r4
  (blh, bll) = bl
  +g = C.St.g(y)
  +w = V.View.text_cols(S.St.cols(y), V.View.gutter(S.St.opts(y), B.Lines.len(C.St.lines(y)), C.St.on_file(y), S.St.cols(y)))
  +left = S.Win.left(S.St.win(y))
  +col = C.St.col(y)
  +d = Nat.sub(col, left)
  %Equal.sym(T.Mode, S.St.mode(y), T.Normal{}, hm) : {Laws.Spec.at_col(Ck.frame(y, _)) == col : Nat}
  Equal.trans(Nat, Nat.add(left, Nat.sub(Nat.add(g, d), g)), Nat.add(left, d), col, Equal.cong(Nat, Nat, z => Nat.add(left, z), Nat.sub(Nat.add(g, d), g), d, L.Nat.add_sub_l(g, d)), L.Nat.add_sub(col, left, Sc.Win.top_le(col, V.View.so_in(w), left, bll)))

def Ck.same_refl(t: T.Tgt) -> {Laws.Spec.same_tgt(t, t) == True{} : Bool}:
  match t:
    case T.File{+i}:
      L.Nat.eq_refl(i)
    case T.Dir{+p}:
      Tx.String.eq_refl(p)

# two editors on one target
def Ck.same_tgt(+s: T.St, +y: T.St, e: {S.Win.tgt(S.St.win(y)) == S.Win.tgt(S.St.win(s)) : T.Tgt}) -> {Laws.Spec.same_tgt(Laws.F.tgt(Vim.Vim.frame(s)), Laws.F.tgt(Vim.Vim.frame(y))) == True{} : Bool}:
  %Equal.sym(T.Tgt, S.Win.tgt(S.St.win(y)), S.Win.tgt(S.St.win(s)), e) : {Laws.Spec.same_tgt(S.Win.tgt(S.St.win(s)), _) == True{} : Bool}
  Ck.same_refl(S.Win.tgt(S.St.win(s)))

# The spec's terms
# ----------------

# the spec's lines of the window are the editor's
def Ck.spec_lines(+fs: List<&2, T.Buf>, +s: T.St, hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}) -> {Laws.Spec.lines(fs, s) == C.St.lines(s) : List<&2, String>}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.File{+i}:
              Sc.Files.spec(fs, files, i, hf)
            case T.Dir{+path}:
              {==}

def Ck.last_line(+ls: List<&2, String>) -> {Laws.Spec.last(Laws.Spec.count(ls)) == M.Move.last_line(ls) : Nat}:
  Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), Laws.Spec.count(ls), B.Lines.len(ls), Equal.sym(Nat, B.Lines.len(ls), Laws.Spec.count(ls), Tx.Count.eq(ls)))

def Ck.last_col(+ls: List<&2, String>, +l: Nat) -> {Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(ls, l))) == M.Move.last_col(ls, l) : Nat}:
  +at = B.Lines.at(ls, l)
  +e = Equal.trans(Nat, X.Text.len(at), Laws.Spec.chars(at), Laws.Spec.chars(Laws.Spec.line(ls, l)), Tx.Chars.eq(at), Equal.cong(String, Nat, z => Laws.Spec.chars(z), at, Laws.Spec.line(ls, l), Tx.Line.eq(ls, l)))
  Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), Laws.Spec.chars(Laws.Spec.line(ls, l)), X.Text.len(at), Equal.sym(Nat, X.Text.len(at), Laws.Spec.chars(Laws.Spec.line(ls, l)), e))

# The claim
# ---------

# a click on a text row of a settled editor in normal mode, on the files
# the start made of fs and a real window
def Ck.moved(+fs: List<&2, T.Buf>, +s: T.St, +r: Nat, +c: Nat, fin: Fi.Final(s), hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, +hm: {S.St.mode(s) == T.Normal{} : T.Mode},
  +hreal: {B.Tgt.real(S.St.files(s), S.Win.tgt(S.St.win(s))) == True{} : Bool}, hr: {Nat.is_lt(r, Nat.sub(S.St.rows(s), 2n)) == True{} : Bool})
  -> {Laws.Spec.moved(s, Laws.Spec.after(Vim.Vim.step(s, T.EvClick{r, c})), Laws.Spec.min(Nat.add(Laws.F.top(Vim.Vim.frame(s)), r), Laws.Spec.last(Laws.Spec.count(Laws.Spec.lines(fs, s)))), Laws.Spec.min(Nat.add(Laws.F.left(Vim.Vim.frame(s)), Nat.sub(c, Laws.F.gutter(Vim.Vim.frame(s)))), Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(Laws.Spec.lines(fs, s), Laws.Spec.min(Nat.add(Laws.F.top(Vim.Vim.frame(s)), r), Laws.Spec.last(Laws.Spec.count(Laws.Spec.lines(fs, s))))))))) == True{} : Bool}:
  +f = Vim.Vim.frame(s)
  +a = Nat.add(S.Win.top(S.St.win(s)), r)
  +b = Nat.add(S.Win.left(S.St.win(s)), Nat.sub(c, C.St.g(s)))
  +ls = C.St.lines(s)
  +sls = Laws.Spec.lines(fs, s)
  +z = M.Move.last_line(ls)
  +x = Ck.x(s, a, b)
  +y = Ck.fx(s, a, b)
  +ev = {T.EvClick{r, c} : T.Ev}
  +sp = Laws.Spec.after(Vim.Vim.step(s, ev))
  +sz = Laws.Spec.last(Laws.Spec.count(sls))
  +l = Laws.Spec.min(Nat.add(Laws.F.top(f), r), sz)
  +k = Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(sls, l)))
  +col = Laws.Spec.min(Nat.add(Laws.F.left(f), Nat.sub(c, Laws.F.gutter(f))), k)
  +lc = M.Move.last_col(ls, Nat.min(a, z))
  +esl = Ck.spec_lines(fs, s, hf)
  # the editor after the click
  +e1 = Equal.trans(T.St, sp, Vim.Vim.final(Re.Reach.next(s, ev)), Vim.Vim.final(x), Re.Reach.step(s, ev), Equal.cong(T.St, T.St, q => Vim.Vim.final(q), Re.Reach.next(s, ev), x, Ck.next(s, r, c, hm, hr)))
  +ey = Equal.trans(T.St, sp, Vim.Vim.final(x), y, e1, Ck.final_real(x, Ck.x_real(s, a, b, hreal)))
  +finy = Ck.fin_fx(s, a, b, hreal)
  +hmy = Equal.trans(T.Mode, S.St.mode(y), S.St.mode(s), T.Normal{}, Ck.fx_mode(s, a, b), hm)
  # its line
  +ez = Equal.trans(Nat, sz, Laws.Spec.last(Laws.Spec.count(ls)), z, Equal.cong(List<&2, String>, Nat, q => Laws.Spec.last(Laws.Spec.count(q)), sls, ls, esl), Ck.last_line(ls))
  +el = Equal.trans(Nat, l, Nat.min(a, sz), Nat.min(a, z), Sc.Spec.min_eq(a, sz), Equal.cong(Nat, Nat, q => Nat.min(a, q), sz, z, ez))
  +eline = Equal.trans(Nat, Laws.Spec.at_line(Vim.Vim.frame(y)), C.St.line(y), l, Ck.frame_line(y, finy, hmy), Equal.trans(Nat, C.St.line(y), Nat.min(a, z), l, Ck.fx_line(s, a, b), Equal.sym(Nat, l, Nat.min(a, z), el)))
  # its column
  +ek1 = Equal.cong(List<&2, String>, Nat, q => Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(q, l))), sls, ls, esl)
  +ek2 = Equal.cong(Nat, Nat, q => Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(ls, q))), l, Nat.min(a, z), el)
  +ek = Equal.trans(Nat, k, Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(ls, l))), lc, ek1, Equal.trans(Nat, Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(ls, l))), Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(ls, Nat.min(a, z)))), lc, ek2, Ck.last_col(ls, Nat.min(a, z))))
  +ec = Equal.trans(Nat, col, Nat.min(b, k), Nat.min(b, lc), Sc.Spec.min_eq(b, k), Equal.cong(Nat, Nat, q => Nat.min(b, q), k, lc, ek))
  +ecol = Equal.trans(Nat, Laws.Spec.at_col(Vim.Vim.frame(y)), C.St.col(y), col, Ck.frame_col(y, finy, hmy), Equal.trans(Nat, C.St.col(y), Nat.min(b, lc), col, Ck.fx_col(s, a, b), Equal.sym(Nat, col, Nat.min(b, lc), ec)))
  %Equal.sym(T.St, sp, y, ey) : {Laws.Spec.moved(s, _, l, col) == True{} : Bool}
  Sc.And3(Laws.Spec.same_tgt(Laws.F.tgt(f), Laws.F.tgt(Vim.Vim.frame(y))), Nat.is_eq(Laws.Spec.at_line(Vim.Vim.frame(y)), l), Nat.is_eq(Laws.Spec.at_col(Vim.Vim.frame(y)), col),
    Ck.same_tgt(s, y, Ck.fx_tgt(s, a, b)), Ck.eq(Laws.Spec.at_line(Vim.Vim.frame(y)), l, eline), Ck.eq(Laws.Spec.at_col(Vim.Vim.frame(y)), col, ecol))

# the claim for a settled editor in normal mode, on the files the start
# made of fs and a real window
def Ck.at(+fs: List<&2, T.Buf>, +s: T.St, +r: Nat, +c: Nat, fin: Fi.Final(s), hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, hm: {S.St.mode(s) == T.Normal{} : T.Mode},
  hreal: {B.Tgt.real(S.St.files(s), S.Win.tgt(S.St.win(s))) == True{} : Bool})
  -> {Laws.Claim.click(fs, s, S.St.rows(s), S.St.cols(s), r, c) == True{} : Bool}:
  +f = Vim.Vim.frame(s)
  +g = Laws.F.gutter(f)
  +sls = Laws.Spec.lines(fs, s)
  +l = Laws.Spec.min(Nat.add(Laws.F.top(f), r), Laws.Spec.last(Laws.Spec.count(sls)))
  +hit = Nat.is_lt(r, Nat.sub(S.St.rows(s), 2n))
  +rest = Bool.and(Nat.is_le(g, c), Nat.is_lt(c, S.St.cols(s)))
  Ck.imp(Bool.and(hit, rest), Laws.Spec.moved(s, Laws.Spec.after(Vim.Vim.step(s, T.EvClick{r, c})), l, Laws.Spec.min(Nat.add(Laws.F.left(f), Nat.sub(c, g)), Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(sls, l))))),
    h => Ck.moved(fs, s, r, c, fin, hf, hm, hreal, L.And.l(hit, rest, h)))

# the window after the events shows a real target (Real.of)
def Ck.real_run(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {B.Tgt.real(S.St.files(Laws.Spec.run(fs, rows, cols, evs)), S.Win.tgt(S.St.win(Laws.Spec.run(fs, rows, cols, evs)))) == True{} : Bool}:
  +x = Re.Reach.pre(evs, Vim.Vim.start(fs, rows, cols))
  %Equal.sym(T.St, Laws.Spec.run(fs, rows, cols, evs), Vim.Vim.final(x), Re.Reach.run(fs, rows, cols, evs)) : {B.Tgt.real(S.St.files(_), S.Win.tgt(S.St.win(_))) == True{} : Bool}
  %Equal.sym(List<&2, T.Buf>, S.St.files(Vim.Vim.final(x)), S.St.files(x), Re.Field.files_final(x)) : {B.Tgt.real(_, S.Win.tgt(S.St.win(Vim.Vim.final(x)))) == True{} : Bool}
  Rb.Real.of(x)

def Ck.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>, +r: Nat, +c: Nat) -> {Laws.Claim.click(fs, Laws.Spec.normal(fs, rows, cols, evs), Laws.Spec.rows(rows, evs), Laws.Spec.cols(cols, evs), r, c) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  +evs2 = Laws.Spec.snoc(evs, Laws.Spec.key("<Esc>"))
  %Re.Reach.rows_normal(fs, rows, cols, evs) : {Laws.Claim.click(fs, n, _, Laws.Spec.cols(cols, evs), r, c) == True{} : Bool}
  %Re.Reach.cols_normal(fs, rows, cols, evs) : {Laws.Claim.click(fs, n, S.St.rows(n), _, r, c) == True{} : Bool}
  Ck.at(fs, n, r, c, Re.Reach.final(fs, rows, cols, evs2), Re.Reach.files_run(fs, rows, cols, evs2), Re.Reach.normal_mode(fs, rows, cols, evs), Ck.real_run(fs, rows, cols, evs2))

def MouseLaws.click(fs, rows, cols, evs, r, c):
  Ck.law(fs, rows, cols, evs, r, c)
