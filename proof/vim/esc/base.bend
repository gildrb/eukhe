# eukhe.com's Neovim: lemmas of the Esc group
# ===========================================
#
# Win.settle keeps a window that is already settled (Settle.win): the
# cursor is on the text (Move.clamp keeps it), the first line is in the
# scrolloff band (View.fit keeps it, and it is at most View.max_top) and
# so is the first column (View.fit_side). So Vim.final keeps a settled
# normal-mode editor whose window shows a real buffer, up to the column j
# and k aim for (Settle.self). Esc keeps the window (Esc.win), and the
# target the window shows is the one Vim.real keeps (Esc.final_tgt).

import Base
import ../../../vim/types.bend as T
import ../../../vim/buf.bend as B
import ../../../vim/move.bend as M
import ../../../vim/view.bend as V
import ../../../vim/st.bend as S
import ../../../vim/core.bend as C
import ../../../vim/keys.bend as K
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../base.bend as L
import ../../base/final.bend as Fi
import ../../base/text.bend as Tx
import ../../base/reach.bend as Re
import ../buffers/real.bend as Rl

# Numbers
# -------

# a == min(a, b) when a <= b
def Esc.min_back(a: Nat, b: Nat, h: L.LE(a, b)) -> {a == Nat.min(a, b) : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      L.Bool.false_true({1n+p == Nat.min(1n+p, 0n) : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, Nat.min(p, q), Esc.min_back(p, q, h))

# a == max(a, b) when b <= a
def Esc.max_back(a: Nat, b: Nat, h: L.LE(b, a)) -> {a == Nat.max(a, b) : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      L.Bool.false_true({0n == Nat.max(0n, 1n+q) : Nat}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, Nat.max(p, q), Esc.max_back(p, q, h))

# a <= b: not a > b
def Esc.le_not_gt(a: Nat, b: Nat, h: L.LE(a, b)) -> {Nat.is_gt(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      L.Bool.false_true({Nat.is_gt(1n+p, 0n) == False{} : Bool}, h)
    case 1n+p 1n+q:
      Esc.le_not_gt(p, q, h)

# the first line with scrolloff so above line l is at most the one above
# a later line last
def Esc.lo_mono(so: Nat, +l: Nat, +last: Nat, h: L.LE(l, last)) -> L.LE(Fi.Fin.lo(l, so), Nat.sub(last, Nat.min(so, last))):
  match so l last:
    case 0n _ _:
      %Equal.sym(Nat, Nat.sub(l, 0n), l, L.Nat.sub_zero(l)) : L.LE(_, Nat.sub(last, 0n))
      %Equal.sym(Nat, Nat.sub(last, 0n), last, L.Nat.sub_zero(last)) : L.LE(l, _)
      h
    case 1n+s 0n _:
      L.Nat.le_zero(Nat.sub(last, Nat.min(1n+s, last)))
    case 1n+s 1n+p 0n:
      L.Bool.false_true(L.LE(Nat.sub(1n+p, Nat.min(1n+s, 1n+p)), Nat.sub(0n, Nat.min(1n+s, 0n))), h)
    case 1n+s 1n+p 1n+q:
      Esc.lo_mono(s, p, q, h)

# Bands
# -----

def Esc.band_lo(-t: Nat, -lo: Nat, -hi: Nat, b: Fi.Band(t, lo, hi)) -> L.LE(t, lo):
  match b:
    case (bh, bl):
      bl

# View.fit's and View.fit_side's choice when neither moves: t
def Esc.pick2_back(c1: Bool, c2: Bool, -up: Nat, -down: Nat, -t: Nat, e1: {c1 == False{} : Bool}, e2: {c2 == False{} : Bool}) -> {t == Bool.pick(Nat, c1, up, Bool.pick(Nat, c2, down, t)) : Nat}:
  match c1 c2:
    case True{} True{}:
      L.Bool.true_false({t == Bool.pick(Nat, True{}, up, Bool.pick(Nat, True{}, down, t)) : Nat}, e1)
    case True{} False{}:
      L.Bool.true_false({t == Bool.pick(Nat, True{}, up, Bool.pick(Nat, False{}, down, t)) : Nat}, e1)
    case False{} True{}:
      L.Bool.true_false({t == Bool.pick(Nat, False{}, up, Bool.pick(Nat, True{}, down, t)) : Nat}, e2)
    case False{} False{}:
      {==}

# View.fit keeps a first line in the band
def Esc.fit_back(+top: Nat, +l: Nat, +h: Nat, +last: Nat, b: Fi.Band(top, Fi.Fin.lo(l, V.View.so_in(h)), Fi.Fin.hi(l, V.View.so_dn(h), last, h))) -> {top == V.View.fit(top, l, h, last) : Nat}:
  match b:
    case (bh, bl):
      +so = V.View.so_in(h)
      -half = Nat.div(Nat.sub(h, 1n), 2n)
      +lo = Nat.sub(l, Nat.min(so, l))
      +hi = Nat.sub(Nat.add(l, Nat.min(V.View.so_dn(h), Nat.sub(last, l))), Nat.sub(h, 1n))
      -mid = Nat.min(Nat.sub(l, half), Nat.sub(last, Nat.min(last, Nat.sub(h, 1n))))
      -up = Bool.pick(Nat, Nat.is_gt(Nat.sub(top, lo), half), mid, lo)
      -down = Bool.pick(Nat, Nat.is_gt(Nat.sub(hi, top), half), mid, hi)
      Esc.pick2_back(Nat.is_lt(lo, top), Nat.is_gt(hi, top), up, down, top, L.Nat.le_not_lt(lo, top, bl), Esc.le_not_gt(hi, top, bh))

# View.fit_side keeps a first column in the band
def Esc.side_back(+left: Nat, +c: Nat, +w: Nat, +last: Nat, b: Fi.Band(left, Fi.Fin.lo(c, V.View.so_in(w)), Fi.Fin.hi(c, V.View.so_in(w), last, w))) -> {left == V.View.fit_side(left, c, w, last) : Nat}:
  match b:
    case (bh, bl):
      +so = V.View.so_in(w)
      -half = Nat.div(w, 2n)
      +lo = Nat.sub(c, Nat.min(so, c))
      +hi = Nat.sub(Nat.add(c, Nat.min(so, Nat.sub(last, c))), Nat.sub(w, 1n))
      -mid = Nat.sub(c, half)
      -back = Bool.pick(Nat, Nat.is_gt(Nat.sub(left, lo), half), mid, lo)
      -ahead = Bool.pick(Nat, Nat.is_gt(Nat.sub(hi, left), half), mid, hi)
      Esc.pick2_back(Nat.is_lt(lo, left), Nat.is_gt(hi, left), back, ahead, left, L.Nat.le_not_lt(lo, left, bl), Esc.le_not_gt(hi, left, bh))

# Move.clamp keeps a cursor on the text
def Esc.clamp_back(+ls: List<&2, String>, +line: Nat, +col: Nat, el: L.LE(line, M.Move.last_line(ls)), ec: L.LE(col, M.Move.last_col(ls, line))) -> {T.Pos{line, col} == M.Move.clamp(ls, T.Pos{line, col}) : T.Pos}:
  %Esc.min_back(line, M.Move.last_line(ls), el) : {T.Pos{line, col} == T.Pos{_, Nat.min(col, M.Move.last_col(ls, _))} : T.Pos}
  %Esc.min_back(col, M.Move.last_col(ls, line), ec) : {T.Pos{line, col} == T.Pos{line, _} : T.Pos}
  {==}

# Win.settle keeps a settled window (up to the column j and k aim for)
def Settle.win(+ls: List<&2, String>, +h: Nat, +w: Nat, -tgt: T.Tgt, +line: Nat, +col: Nat, -want: T.Want, +top: Nat, +left: Nat,
  +el: L.LE(line, M.Move.last_line(ls)), ec: L.LE(col, M.Move.last_col(ls, line)),
  +bt: Fi.Band(top, Fi.Fin.lo(line, V.View.so_in(h)), Fi.Fin.hi(line, V.View.so_dn(h), M.Move.last_line(ls), h)),
  bs: Fi.Band(left, Fi.Fin.lo(col, V.View.so_in(w)), Fi.Fin.hi(col, V.View.so_in(w), M.Move.last_col(ls, line), w)))
  -> {T.Win{tgt, T.Pos{line, col}, C.Want.at(ls, T.Pos{line, col}, want), top, left} == T.Win{tgt, M.Move.clamp(ls, T.Pos{line, col}), C.Want.at(ls, M.Move.clamp(ls, T.Pos{line, col}), want), V.View.fit(Nat.min(top, V.View.max_top(h, M.Move.last_line(ls))), S.Pos.line(M.Move.clamp(ls, T.Pos{line, col})), h, M.Move.last_line(ls)), V.View.fit_side(left, S.Pos.col(M.Move.clamp(ls, T.Pos{line, col})), w, M.Move.last_col(ls, S.Pos.line(M.Move.clamp(ls, T.Pos{line, col}))))} : T.Win}:
  -p = {T.Pos{line, col} : T.Pos}
  -ll = M.Move.last_line(ls)
  -mt = V.View.max_top(h, ll)
  -lhs = {T.Win{tgt, p, C.Want.at(ls, p, want), top, left} : T.Win}
  +hmt = L.Nat.le_trans(top, Fi.Fin.lo(line, V.View.so_in(h)), V.View.max_top(h, M.Move.last_line(ls)), Esc.band_lo(top, Fi.Fin.lo(line, V.View.so_in(h)), Fi.Fin.hi(line, V.View.so_dn(h), M.Move.last_line(ls), h), bt), Esc.lo_mono(V.View.so_in(h), line, M.Move.last_line(ls), el))
  %Esc.clamp_back(ls, line, col, el, ec) : {lhs == T.Win{tgt, _, C.Want.at(ls, _, want), V.View.fit(Nat.min(top, mt), S.Pos.line(_), h, ll), V.View.fit_side(left, S.Pos.col(_), w, M.Move.last_col(ls, S.Pos.line(_)))} : T.Win}
  %Esc.min_back(top, V.View.max_top(h, M.Move.last_line(ls)), hmt) : {lhs == T.Win{tgt, p, C.Want.at(ls, p, want), V.View.fit(_, line, h, ll), V.View.fit_side(left, col, w, M.Move.last_col(ls, line))} : T.Win}
  %Esc.fit_back(top, line, h, M.Move.last_line(ls), bt) : {lhs == T.Win{tgt, p, C.Want.at(ls, p, want), _, V.View.fit_side(left, col, w, M.Move.last_col(ls, line))} : T.Win}
  %Esc.side_back(left, col, w, M.Move.last_col(ls, line), bs) : {lhs == T.Win{tgt, p, C.Want.at(ls, p, want), top, _} : T.Win}
  {==}

# The editor
# ----------

# a normal-mode editor with window w
def Esc.at(files: List<&2, T.Buf>, folded: List<&2, List<&2, String>>, dirs: List<&2, T.Listing>, marks: List<&2, T.Pos>, spots: List<&2, T.Spot>, opened: List<&2, Nat>, bufs: List<&2, Nat>, back: List<&2, T.Win>, fwd: List<&2, T.Win>, count: Nat, pend: T.Pend, find: Maybe<&2, T.Find>, hl: Bool, opts: T.Opts, rows: Nat, cols: Nat, msg: String, stat: String, w: T.Win) -> T.St:
  T.St{files, folded, dirs, w, marks, spots, opened, bufs, back, fwd, T.Normal{}, count, pend, find, hl, opts, rows, cols, msg, stat}

# Vim.real keeps a window that shows a real buffer
def Esc.real_back(+fs: List<&2, T.Buf>, w: T.Win, hr: {B.Tgt.real(fs, S.Win.tgt(w)) == True{} : Bool}) -> {w == Vim.Vim.real(fs, w) : T.Win}:
  match w:
    case T.Win{+tgt, cur, want, top, left}:
      %Equal.sym(Bool, B.Tgt.real(fs, tgt), True{}, hr) : {T.Win{tgt, cur, want, top, left} == Bool.pick(T.Win, _, T.Win{tgt, cur, want, top, left}, T.Win{T.File{0n}, T.Pos{0n, 0n}, T.Col{0n}, 0n, 0n}) : T.Win}
      {==}

# Vim.final keeps a settled normal-mode editor on a real buffer, up to
# the column j and k aim for
def Settle.self(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +opened: List<&2, Nat>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +count: Nat, +pend: T.Pend, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String,
  +tgt: T.Tgt, +line: Nat, +col: Nat, +want: T.Want, +top: Nat, +left: Nat,
  fin: Fi.Final(Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, pend, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left})),
  hr: {B.Tgt.real(files, tgt) == True{} : Bool})
  -> {Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, pend, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, C.Want.at(C.St.lines(Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, pend, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left})), T.Pos{line, col}, want), top, left})
      == Vim.Vim.final(Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, pend, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left})) : T.St}:
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
                      +x = Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, pend, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, want, top, left})
                      -xw = Esc.at(files, folded, dirs, marks, spots, opened, bufs, back, fwd, count, pend, find, hl, opts, rows, cols, msg, stat, T.Win{tgt, T.Pos{line, col}, C.Want.at(C.St.lines(x), T.Pos{line, col}, want), top, left})
                      %Esc.real_back(files, T.Win{tgt, T.Pos{line, col}, want, top, left}, hr) : {xw == Vim.Vim.fit(S.St.set_win(x, _)) : T.St}
                      %Esc.max_back(rows, 3n, e3) : {xw == C.Win.settle(S.St.set_cols(S.St.set_rows(x, _), Nat.max(cols, 12n))) : T.St}
                      %Esc.max_back(cols, 12n, e12) : {xw == C.Win.settle(S.St.set_cols(x, _)) : T.St}
                      %Settle.win(C.St.lines(x), C.St.h(x), C.St.w(x), tgt, line, col, want, top, left, el, ec, bt, bs) : {xw == S.St.set_win(x, _) : T.St}
                      {==}

# Targets
# -------

def Esc.same_refl(t: T.Tgt) -> {Laws.Spec.same_tgt(t, t) == True{} : Bool}:
  match t:
    case T.File{+i}:
      L.Nat.eq_refl(i)
    case T.Dir{+p}:
      Tx.String.eq_refl(p)

# Vim.fit keeps the target Vim.real picks
def Esc.final_tgt(+x: T.St) -> {S.Win.tgt(Vim.Vim.real(S.St.files(x), S.St.win(x))) == S.Win.tgt(S.St.win(Vim.Vim.final(x))) : T.Tgt}:
  match x:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

def Esc.keep_win(+s: T.St, +st: T.St) -> {S.St.win(st) == S.St.win(Vim.Vim.keep(s, st)) : T.Win}:
  match st:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      {==}

# Esc from any mode, waiting key or count keeps the window
def Esc.win(s: T.St) -> {S.St.win(s) == S.St.win(Laws.Spec.after(K.Key.in(s, S.St.mode(s), "<Esc>"))) : T.Win}:
  match s:
    case T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}:
      match mode:
        case T.Normal{}:
          match pend:
            case T.NoPend{}:
              {==}
            case T.PendG{}:
              {==}
            case T.PendZ{}:
              {==}
            case T.PendLead{}:
              {==}
            case T.PendLeadF{}:
              {==}
            case T.PendY{}:
              {==}
        case T.Typing{kind, text}:
          {==}
        case T.Picking{kind, q, its, n, sel, top, pv, levels}:
          {==}

# the editor after any events shows a real buffer
def Esc.real_run(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {B.Tgt.real(S.St.files(Laws.Spec.run(fs, rows, cols, evs)), S.Win.tgt(S.St.win(Laws.Spec.run(fs, rows, cols, evs)))) == True{} : Bool}:
  +x = Re.Reach.pre(evs, Vim.Vim.start(fs, rows, cols))
  %Equal.sym(T.St, Laws.Spec.run(fs, rows, cols, evs), Vim.Vim.final(x), Re.Reach.run(fs, rows, cols, evs)) : {B.Tgt.real(S.St.files(_), S.Win.tgt(S.St.win(_))) == True{} : Bool}
  %Equal.sym(List<&2, T.Buf>, S.St.files(Vim.Vim.final(x)), S.St.files(x), Re.Field.files_final(x)) : {B.Tgt.real(_, S.Win.tgt(S.St.win(Vim.Vim.final(x)))) == True{} : Bool}
  Rl.Real.of(x)
