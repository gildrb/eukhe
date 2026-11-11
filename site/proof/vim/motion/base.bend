# eukhe.com's Neovim: what the motions do to a settled editor
# ===========================================================
#
# The motion laws (proof/motion/*.bend) press a key in normal mode after
# an Esc. Idle.mk spells that editor out as a record with its mode, count
# and waiting key written in (Idle.eta: the editor is that record), so a
# key pressed on it computes. Vim.final is Vim.fit on a real target
# (Final.real); the lemmas here give the cursor, the target and the lines
# after Vim.fit of each motion (GL.cur, Go.cur, ...), and read the
# frame's line and column back (AtLine, AtCol).

import Base
import ../../../vim/types.bend as T
import ../../../vim/text.bend as X
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
import ../../base/reach.bend as Re
import ../../base/text.bend as Tx
import ../screen/base.bend as Sb
import ../buffers/real.bend as Rl

# Nat
# ---

# min(a, b) == a when a <= b
def Min.eq_l(a: Nat, b: Nat, h: L.LE(a, b)) -> {Nat.min(a, b) == a : Nat}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      L.Bool.false_true({Nat.min(1n+p, 0n) == 1n+p : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.min(p, q), p, Min.eq_l(p, q, h))

def Min.idem(+a: Nat, +b: Nat) -> {Nat.min(Nat.min(a, b), b) == Nat.min(a, b) : Nat}:
  Min.eq_l(Nat.min(a, b), b, L.Nat.min_le_r(a, b))

# a + 1 is 1 + a
def Plus1(+a: Nat) -> {Nat.add(a, 1n) == 1n+a : Nat}:
  Equal.trans(Nat, Nat.add(a, 1n), 1n+Nat.add(a, 0n), 1n+a, Equal.sym(Nat, 1n+Nat.add(a, 0n), Nat.add(a, 1n), L.Nat.add_succ(a, 0n)), Equal.cong(Nat, Nat, x => 1n+x, Nat.add(a, 0n), a, L.Nat.zero_r(a)))

# a == b gives a test that says so
def Eq.true(+a: Nat, +b: Nat, e: {a == b : Nat}) -> {Nat.is_eq(a, b) == True{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {Nat.is_eq(_, b) == True{} : Bool}
  L.Nat.eq_refl(b)

# Targets
# -------

def Same.refl(t: T.Tgt) -> {Laws.Spec.same_tgt(t, t) == True{} : Bool}:
  match t:
    case T.File{+i}:
      L.Nat.eq_refl(i)
    case T.Dir{+p}:
      Tx.String.eq_refl(p)

# what s2's window shows is what s1's shows
def Same.tgt(+s1: T.St, +s2: T.St, e: {S.Win.tgt(S.St.win(s2)) == S.Win.tgt(S.St.win(s1)) : T.Tgt}) -> {Laws.Spec.same_tgt(Laws.F.tgt(Vim.Vim.frame(s1)), Laws.F.tgt(Vim.Vim.frame(s2))) == True{} : Bool}:
  %Equal.sym(T.Tgt, S.Win.tgt(S.St.win(s2)), S.Win.tgt(S.St.win(s1)), e) : {Laws.Spec.same_tgt(S.Win.tgt(S.St.win(s1)), _) == True{} : Bool}
  Same.refl(S.Win.tgt(S.St.win(s1)))

# Positions
# ---------

def Cl2(+ls: List<&2, String>, p: T.Pos) -> T.Pos:
  M.Move.clamp(ls, M.Move.clamp(ls, p))

def Cl3(+ls: List<&2, String>, p: T.Pos) -> T.Pos:
  M.Move.clamp(ls, Cl2(ls, p))

# the column want gives is on the line
def Aim.le(+ls: List<&2, String>, +l: Nat, w: T.Want) -> L.LE(M.Move.aim(ls, l, w), M.Move.last_col(ls, l)):
  match w:
    case T.Col{+n}:
      L.Nat.min_le_r(n, M.Move.last_col(ls, l))
    case T.End{}:
      L.Nat.le_refl(M.Move.last_col(ls, l))

# a position on the text stays where it is
def Clamp.on(+ls: List<&2, String>, +l: Nat, +c: Nat, hl: L.LE(l, M.Move.last_line(ls)), hc: L.LE(c, M.Move.last_col(ls, l))) -> {M.Move.clamp(ls, T.Pos{l, c}) == T.Pos{l, c} : T.Pos}:
  +last = M.Move.last_line(ls)
  %Equal.sym(Nat, Nat.min(l, last), l, Min.eq_l(l, last, hl)) : {T.Pos{_, Nat.min(c, M.Move.last_col(ls, _))} == T.Pos{l, c} : T.Pos}
  Equal.cong(Nat, T.Pos, x => T.Pos{l, x}, Nat.min(c, M.Move.last_col(ls, l)), c, Min.eq_l(c, M.Move.last_col(ls, l), hc))

def Cl2.on(+ls: List<&2, String>, +p: T.Pos, +h: {M.Move.clamp(ls, p) == p : T.Pos}) -> {Cl2(ls, p) == p : T.Pos}:
  %Equal.sym(T.Pos, M.Move.clamp(ls, p), p, h) : {M.Move.clamp(ls, _) == p : T.Pos}
  h

def Cl3.on(+ls: List<&2, String>, +p: T.Pos, +h: {M.Move.clamp(ls, p) == p : T.Pos}) -> {Cl3(ls, p) == p : T.Pos}:
  %Equal.sym(T.Pos, Cl2(ls, p), p, Cl2.on(ls, p, h)) : {M.Move.clamp(ls, _) == p : T.Pos}
  h

# The editor in normal mode, spelled out
# --------------------------------------

def Idle.mk(+s: T.St) -> T.St:
  T.St{S.St.files(s), S.St.folded(s), S.St.dirs(s), S.St.win(s), S.St.marks(s), S.St.spots(s), S.St.opened(s), S.St.bufs(s), S.St.back(s), S.St.fwd(s), T.Normal{}, 0n, T.NoPend{}, S.St.find(s), S.St.hl(s), S.St.opts(s), S.St.rows(s), S.St.cols(s), S.St.msg(s), S.St.stat(s)}

# an editor in normal mode, no count, no key waiting is Idle.mk of itself
def Idle.eta(s: T.St, hm: {S.St.mode(s) == T.Normal{} : T.Mode}, hp: {S.St.pend(s) == T.NoPend{} : T.Pend}, hc: {S.St.count(s) == 0n : Nat}) -> {s == Idle.mk(s) : T.St}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      %hm : {T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat} == T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, _, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat} : T.St}
      %hc : {T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat} == T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, _, T.NoPend{}, find, hl, opts, rows, cols, msg, stat} : T.St}
      %hp : {T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat} == T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, _, find, hl, opts, rows, cols, msg, stat} : T.St}
      {==}

# Settling
# --------

def Fin.pick(b: Bool, -y: T.St, -w: T.Win, -w0: T.Win, hb: {b == True{} : Bool}) -> {Vim.Vim.fit(S.St.set_win(y, Bool.pick(T.Win, b, w, w0))) == Vim.Vim.fit(S.St.set_win(y, w)) : T.St}:
  match b:
    case True{}:
      {==}
    case False{}:
      L.Bool.false_true({Vim.Vim.fit(S.St.set_win(y, w0)) == Vim.Vim.fit(S.St.set_win(y, w)) : T.St}, hb)

# Vim.final of a normal-mode editor on a real target is Vim.fit
def Final.real(+y: T.St, hr: {B.Tgt.real(S.St.files(y), S.Win.tgt(S.St.win(y))) == True{} : Bool}, hm: {S.St.mode(y) == T.Normal{} : T.Mode}) -> {Vim.Vim.final(y) == Vim.Vim.fit(y) : T.St}:
  match y:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          match mode:
            case T.Normal{}:
              Fin.pick(B.Tgt.real(files, tgt), T.St{files, folded, dirs, T.Win{tgt, cur, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Normal{}, count, pend, find, hl, opts, rows, cols, msg, stat}, T.Win{tgt, cur, want, top, left}, T.Win{T.File{0n}, T.Pos{0n, 0n}, T.Col{0n}, 0n, 0n}, hr)
            case T.Typing{+k, +t}:
              Sb.Mode.typing({Vim.Vim.final(T.St{files, folded, dirs, T.Win{tgt, cur, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Typing{k, t}, count, pend, find, hl, opts, rows, cols, msg, stat}) == Vim.Vim.fit(T.St{files, folded, dirs, T.Win{tgt, cur, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Typing{k, t}, count, pend, find, hl, opts, rows, cols, msg, stat}) : T.St}, k, t, hm)
            case T.Picking{+k, +q, +its, +n, +sel, +ptop, +pv, +levels}:
              Sb.Mode.picking({Vim.Vim.final(T.St{files, folded, dirs, T.Win{tgt, cur, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Picking{k, q, its, n, sel, ptop, pv, levels}, count, pend, find, hl, opts, rows, cols, msg, stat}) == Vim.Vim.fit(T.St{files, folded, dirs, T.Win{tgt, cur, want, top, left}, marks, spots, opened, bufs, back, fwd, T.Picking{k, q, its, n, sel, ptop, pv, levels}, count, pend, find, hl, opts, rows, cols, msg, stat}) : T.St}, k, q, its, n, sel, ptop, pv, levels, hm)

# a key press settles: its editor is settled
def Press.final(+x: T.St, +key: String) -> Fi.Final(Laws.Spec.press(x, key)):
  %Equal.sym(T.St, Laws.Spec.after(Vim.Vim.step(x, T.EvKey{key})), Vim.Vim.final(Re.Reach.next(x, T.EvKey{key})), Re.Reach.step(x, T.EvKey{key})) : Fi.Final(_)
  Fi.Final.of(Re.Reach.next(x, T.EvKey{key}))

# The lines
# ---------

# the spec's lines are the window's, on the files the start made of fs
def Lines.spec(+fs: List<&2, T.Buf>, +x: T.St, hf: {S.St.files(x) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}) -> {Laws.Spec.lines(fs, x) == C.St.lines(x) : List<&2, String>}:
  match x:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.File{+i}:
              Sb.Files.spec(fs, files, i, hf)
            case T.Dir{+path}:
              {==}

# the spec's last column of line l is the editor's
def LastCol.eq(+ls: List<&2, String>, +l: Nat) -> {Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(ls, l))) == M.Move.last_col(ls, l) : Nat}:
  %Tx.Line.eq(ls, l) : {Nat.sub(Laws.Spec.chars(_), 1n) == M.Move.last_col(ls, l) : Nat}
  %Tx.Chars.eq(B.Lines.at(ls, l)) : {Nat.sub(_, 1n) == M.Move.last_col(ls, l) : Nat}
  {==}

# the spec's last line is the editor's
def LastLine.eq(+ls: List<&2, String>) -> {Laws.Spec.last(Laws.Spec.count(ls)) == M.Move.last_line(ls) : Nat}:
  %Tx.Count.eq(ls) : {Nat.sub(_, 1n) == M.Move.last_line(ls) : Nat}
  {==}

# The frame
# ---------

# the frame's line (first line + row) is the cursor's
def AtLine(+t: T.St, fin: Fi.Final(t)) -> {Nat.add(S.Win.top(S.St.win(t)), Nat.sub(C.St.line(t), S.Win.top(S.St.win(t)))) == C.St.line(t) : Nat}:
  (f3, r1) = fin
  (f12, r2) = r1
  (fl, r3) = r2
  (fc, r4) = r3
  (bt, bl) = r4
  (bth, btl) = bt
  +line = C.St.line(t)
  +top = S.Win.top(S.St.win(t))
  L.Nat.add_sub(line, top, Sb.Win.top_le(line, V.View.so_in(V.View.text_rows(S.St.rows(t))), top, btl))

# the frame's column (first column + cell past the gutter) is the cursor's
def AtCol(+t: T.St, fin: Fi.Final(t)) -> {Nat.add(S.Win.left(S.St.win(t)), Nat.sub(Nat.add(C.St.g(t), Nat.sub(C.St.col(t), S.Win.left(S.St.win(t)))), C.St.g(t))) == C.St.col(t) : Nat}:
  (f3, r1) = fin
  (f12, r2) = r1
  (fl, r3) = r2
  (fc, r4) = r3
  (bt, bl) = r4
  (blh, bll) = bl
  +col = C.St.col(t)
  +left = S.Win.left(S.St.win(t))
  +g = C.St.g(t)
  +y = Nat.sub(col, left)
  +w = V.View.text_cols(S.St.cols(t), V.View.gutter(S.St.opts(t), B.Lines.len(C.St.lines(t)), C.St.on_file(t), S.St.cols(t)))
  %Equal.sym(Nat, Nat.sub(Nat.add(g, y), g), y, L.Nat.add_sub_l(g, y)) : {Nat.add(left, _) == col : Nat}
  L.Nat.add_sub(col, left, Sb.Win.top_le(col, V.View.so_in(w), left, bll))

# What the keys do to the cursor
# ------------------------------

# j k: Win.go_line
def GL.cur(+z: T.St, +l: Nat) -> {S.Win.cur(S.St.win(Vim.Vim.fit(Vim.Vim.keep(z, C.Win.go_line(z, l))))) == Cl3(C.St.lines(z), T.Pos{Nat.min(l, M.Move.last_line(C.St.lines(z))), M.Move.aim(C.St.lines(z), Nat.min(l, M.Move.last_line(C.St.lines(z))), S.Win.want(S.St.win(z)))}) : T.Pos}:
  match z:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.File{+i}:
              {==}
            case T.Dir{+path}:
              {==}

# G gg: a jump, then Win.go_line (from an editor whose key waited)
def GLJ.cur(+z: T.St, +l: Nat) -> {S.Win.cur(S.St.win(Vim.Vim.fit(Vim.Vim.keep(z, C.Win.go_line(C.Win.jump(S.St.set_count(S.St.set_pend(z, T.NoPend{}), 0n)), l))))) == Cl3(C.St.lines(z), T.Pos{Nat.min(l, M.Move.last_line(C.St.lines(z))), M.Move.aim(C.St.lines(z), Nat.min(l, M.Move.last_line(C.St.lines(z))), S.Win.want(S.St.win(z)))}) : T.Pos}:
  match z:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.File{+i}:
              {==}
            case T.Dir{+path}:
              {==}

# 0 h l: Win.go
def Go.cur(+z: T.St, +p: T.Pos) -> {S.Win.cur(S.St.win(Vim.Vim.fit(Vim.Vim.keep(z, C.Win.go(z, p, False{}))))) == Cl3(C.St.lines(z), p) : T.Pos}:
  match z:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.File{+i}:
              {==}
            case T.Dir{+path}:
              {==}

# $: Key.dollar
def Dol.cur(+z: T.St, +l: Nat) -> {S.Win.cur(S.St.win(Vim.Vim.fit(Vim.Vim.keep(z, K.Key.dollar(z, l))))) == Cl2(C.St.lines(z), T.Pos{Nat.min(l, M.Move.last_line(C.St.lines(z))), M.Move.last_col(C.St.lines(z), Nat.min(l, M.Move.last_line(C.St.lines(z))))}) : T.Pos}:
  match z:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.File{+i}:
              {==}
            case T.Dir{+path}:
              {==}

# the first g: g waits
def G1.cur(+z: T.St) -> {S.Win.cur(S.St.win(Vim.Vim.fit(Vim.Vim.keep(z, S.St.set_count(S.St.set_pend(z, T.PendG{}), 0n))))) == M.Move.clamp(C.St.lines(z), S.Win.cur(S.St.win(z))) : T.Pos}:
  match z:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.File{+i}:
              {==}
            case T.Dir{+path}:
              {==}

# The column j and k aim for (A4)
# -------------------------------

# the cursor's column is the one its want gives on its line
def Aim(+s: T.St) -> Data:
  {C.St.col(s) == M.Move.aim(C.St.lines(s), C.St.line(s), S.Win.want(S.St.win(s))) : Nat}

def Want.pick(+ls: List<&2, String>, +l: Nat, +c: Nat, +w: T.Want, b: Bool, e: {Nat.is_eq(M.Move.aim(ls, l, w), c) == b : Bool}, hc: L.LE(c, M.Move.last_col(ls, l)))
  -> {c == M.Move.aim(ls, l, Bool.pick(T.Want, b, w, T.Col{c})) : Nat}:
  match b:
    case True{}:
      Equal.sym(Nat, M.Move.aim(ls, l, w), c, L.Nat.eq_true(M.Move.aim(ls, l, w), c, e))
    case False{}:
      Equal.sym(Nat, Nat.min(c, M.Move.last_col(ls, l)), c, Min.eq_l(c, M.Move.last_col(ls, l), hc))

# Want.at gives the column of a clamped position
def Want.clamp(+ls: List<&2, String>, cur: T.Pos, +w: T.Want) -> {S.Pos.col(M.Move.clamp(ls, cur)) == M.Move.aim(ls, S.Pos.line(M.Move.clamp(ls, cur)), C.Want.at(ls, M.Move.clamp(ls, cur), w)) : Nat}:
  match cur:
    case T.Pos{+line, +col}:
      +l = Nat.min(line, M.Move.last_line(ls))
      +c = Nat.min(col, M.Move.last_col(ls, l))
      Want.pick(ls, l, c, w, Nat.is_eq(M.Move.aim(ls, l, w), c), {==}, L.Nat.min_le_r(col, M.Move.last_col(ls, l)))

def Aim.settle(+z: T.St) -> {C.St.col(C.Win.settle(z)) == M.Move.aim(C.St.lines(z), C.St.line(C.Win.settle(z)), S.Win.want(S.St.win(C.Win.settle(z)))) : Nat}:
  match z:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      Want.clamp(C.St.lines(T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, mode, count, pend, find, hl, opts, rows, cols, msg, stat}), S.Win.cur(win), S.Win.want(win))

def Settle.lines(+z: T.St) -> {C.St.lines(C.Win.settle(z)) == C.St.lines(z) : List<&2, String>}:
  match z:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.File{+i}:
              {==}
            case T.Dir{+path}:
              {==}

def Aim.fit(+y: T.St) -> Aim(Vim.Vim.fit(y)):
  +z = S.St.set_cols(S.St.set_rows(y, Nat.max(S.St.rows(y), V.View.min_rows())), Nat.max(S.St.cols(y), V.View.min_cols()))
  %Equal.sym(List<&2, String>, C.St.lines(C.Win.settle(z)), C.St.lines(z), Settle.lines(z)) : {C.St.col(C.Win.settle(z)) == M.Move.aim(_, C.St.line(C.Win.settle(z)), S.Win.want(S.St.win(C.Win.settle(z)))) : Nat}
  Aim.settle(z)

# every settled editor aims at its column
def Aim.of(+x: T.St) -> Aim(Vim.Vim.final(x)):
  +x2 = S.St.set_count(S.St.set_pend(x, Vim.Vim.pend(S.St.mode(x), S.St.pend(x))), Vim.Vim.count(S.St.mode(x), S.St.count(x)))
  Aim.fit(S.St.set_win(x2, Vim.Vim.real(S.St.files(x), S.St.win(x))))

# Facts carried to Idle.mk
# ------------------------

def Idle.fin(+s: T.St, hm: {S.St.mode(s) == T.Normal{} : T.Mode}, hp: {S.St.pend(s) == T.NoPend{} : T.Pend}, hc: {S.St.count(s) == 0n : Nat}, fin: Fi.Final(s)) -> Fi.Final(Idle.mk(s)):
  %Idle.eta(s, hm, hp, hc) : Fi.Final(_)
  fin

def Idle.aim(+s: T.St, hm: {S.St.mode(s) == T.Normal{} : T.Mode}, hp: {S.St.pend(s) == T.NoPend{} : T.Pend}, hc: {S.St.count(s) == 0n : Nat}, a: Aim(s)) -> Aim(Idle.mk(s)):
  %Idle.eta(s, hm, hp, hc) : Aim(_)
  a

# The editor after evs and an Esc
# -------------------------------

def Ready.eta(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Spec.normal(fs, rows, cols, evs) == Idle.mk(Laws.Spec.normal(fs, rows, cols, evs)) : T.St}:
  Idle.eta(Laws.Spec.normal(fs, rows, cols, evs), Re.Reach.normal_mode(fs, rows, cols, evs), Re.Reach.normal_pend(fs, rows, cols, evs), Re.Reach.normal_count(fs, rows, cols, evs))

def Ready.fin(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> Fi.Final(Idle.mk(Laws.Spec.normal(fs, rows, cols, evs))):
  Idle.fin(Laws.Spec.normal(fs, rows, cols, evs), Re.Reach.normal_mode(fs, rows, cols, evs), Re.Reach.normal_pend(fs, rows, cols, evs), Re.Reach.normal_count(fs, rows, cols, evs), Re.Reach.final(fs, rows, cols, Laws.Spec.snoc(evs, Laws.Spec.key("<Esc>"))))

def Ready.files(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {S.St.files(Laws.Spec.normal(fs, rows, cols, evs)) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}:
  Re.Reach.files_run(fs, rows, cols, Laws.Spec.snoc(evs, Laws.Spec.key("<Esc>")))

def Ready.real(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {B.Tgt.real(S.St.files(Laws.Spec.normal(fs, rows, cols, evs)), S.Win.tgt(S.St.win(Laws.Spec.normal(fs, rows, cols, evs)))) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  +x = Re.Reach.next(Laws.Spec.run(fs, rows, cols, evs), T.EvKey{"<Esc>"})
  %Equal.sym(T.St, n, Vim.Vim.final(x), Re.Reach.normal_step(fs, rows, cols, evs)) : {B.Tgt.real(S.St.files(_), S.Win.tgt(S.St.win(_))) == True{} : Bool}
  %Equal.sym(List<&2, T.Buf>, S.St.files(Vim.Vim.final(x)), S.St.files(x), Re.Field.files_final(x)) : {B.Tgt.real(_, S.Win.tgt(S.St.win(Vim.Vim.final(x)))) == True{} : Bool}
  Rl.Real.of(x)

def Ready.aim0(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> Aim(Laws.Spec.normal(fs, rows, cols, evs)):
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  +x = Re.Reach.next(Laws.Spec.run(fs, rows, cols, evs), T.EvKey{"<Esc>"})
  %Equal.sym(T.St, n, Vim.Vim.final(x), Re.Reach.normal_step(fs, rows, cols, evs)) : Aim(_)
  Aim.of(x)

def Ready.aim(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> Aim(Idle.mk(Laws.Spec.normal(fs, rows, cols, evs))):
  Idle.aim(Laws.Spec.normal(fs, rows, cols, evs), Re.Reach.normal_mode(fs, rows, cols, evs), Re.Reach.normal_pend(fs, rows, cols, evs), Re.Reach.normal_count(fs, rows, cols, evs), Ready.aim0(fs, rows, cols, evs))

# The claims
# ----------

# t shows z's target with the frame's line at line
def ML.of(+fs: List<&2, T.Buf>, +z: T.St, +t: T.St, +line: Nat, ht: {S.Win.tgt(S.St.win(t)) == S.Win.tgt(S.St.win(z)) : T.Tgt}, hl: {Laws.Spec.at_line(Vim.Vim.frame(t)) == line : Nat})
  -> {Laws.Spec.moved_line(z, t, line) == True{} : Bool}:
  L.And.intro(Laws.Spec.same_tgt(Laws.F.tgt(Vim.Vim.frame(z)), Laws.F.tgt(Vim.Vim.frame(t))), Nat.is_eq(Laws.Spec.at_line(Vim.Vim.frame(t)), line), Same.tgt(z, t, ht), Eq.true(Laws.Spec.at_line(Vim.Vim.frame(t)), line, hl))

# ... and the frame's column at col
def MV.of(+fs: List<&2, T.Buf>, +z: T.St, +t: T.St, +line: Nat, +col: Nat, ht: {S.Win.tgt(S.St.win(t)) == S.Win.tgt(S.St.win(z)) : T.Tgt}, hl: {Laws.Spec.at_line(Vim.Vim.frame(t)) == line : Nat}, hc: {Laws.Spec.at_col(Vim.Vim.frame(t)) == col : Nat})
  -> {Laws.Spec.moved(z, t, line, col) == True{} : Bool}:
  +a = Nat.is_eq(Laws.Spec.at_line(Vim.Vim.frame(t)), line)
  +b = Nat.is_eq(Laws.Spec.at_col(Vim.Vim.frame(t)), col)
  L.And.intro(Laws.Spec.same_tgt(Laws.F.tgt(Vim.Vim.frame(z)), Laws.F.tgt(Vim.Vim.frame(t))), Bool.and(a, b), Same.tgt(z, t, ht), L.And.intro(a, b, Eq.true(Laws.Spec.at_line(Vim.Vim.frame(t)), line, hl), Eq.true(Laws.Spec.at_col(Vim.Vim.frame(t)), col, hc)))

# a settled cursor is on a line, and on a character of it
def Fin.line_le(+t: T.St, fin: Fi.Final(t)) -> L.LE(C.St.line(t), M.Move.last_line(C.St.lines(t))):
  (f3, r1) = fin
  (f12, r2) = r1
  (fl, r3) = r2
  fl

def Fin.col_le(+t: T.St, fin: Fi.Final(t)) -> L.LE(C.St.col(t), M.Move.last_col(C.St.lines(t), C.St.line(t))):
  (f3, r1) = fin
  (f12, r2) = r1
  (fl, r3) = r2
  (fc, r4) = r3
  fc

# three clamps of p are q when one is and q stays
def Cl3.step(+ls: List<&2, String>, +p: T.Pos, +q: T.Pos, h1: {M.Move.clamp(ls, p) == q : T.Pos}, +h2: {M.Move.clamp(ls, q) == q : T.Pos}) -> {Cl3(ls, p) == q : T.Pos}:
  %Equal.sym(T.Pos, M.Move.clamp(ls, p), q, h1) : {M.Move.clamp(ls, M.Move.clamp(ls, _)) == q : T.Pos}
  %Equal.sym(T.Pos, M.Move.clamp(ls, q), q, h2) : {M.Move.clamp(ls, _) == q : T.Pos}
  h2

# a position on a line of the text: its column pulled onto the line
def Clamp.line(+ls: List<&2, String>, +line: Nat, +c: Nat, hl: L.LE(line, M.Move.last_line(ls))) -> {M.Move.clamp(ls, T.Pos{line, c}) == T.Pos{line, Nat.min(c, M.Move.last_col(ls, line))} : T.Pos}:
  +last = M.Move.last_line(ls)
  %Equal.sym(Nat, Nat.min(line, last), line, Min.eq_l(line, last, hl)) : {T.Pos{_, Nat.min(c, M.Move.last_col(ls, _))} == T.Pos{line, Nat.min(c, M.Move.last_col(ls, line))} : T.Pos}
  {==}

# the last column of the frame's line, as the spec reads it (on Idle.mk(s),
# whose frame computes in normal mode)
def Col.target(+fs: List<&2, T.Buf>, +s: T.St, hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, fin: Fi.Final(Idle.mk(s)))
  -> {Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(Laws.Spec.lines(fs, Idle.mk(s)), Laws.Spec.at_line(Vim.Vim.frame(Idle.mk(s)))))) == M.Move.last_col(C.St.lines(Idle.mk(s)), C.St.line(Idle.mk(s))) : Nat}:
  +z = Idle.mk(s)
  +ls = C.St.lines(z)
  +line = C.St.line(z)
  %Equal.sym(Nat, Nat.add(S.Win.top(S.St.win(z)), Nat.sub(line, S.Win.top(S.St.win(z)))), line, AtLine(z, fin)) : {Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(Laws.Spec.lines(fs, z), _))) == M.Move.last_col(ls, line) : Nat}
  %Equal.sym(List<&2, String>, Laws.Spec.lines(fs, z), ls, Lines.spec(fs, z, hf)) : {Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(_, line))) == M.Move.last_col(ls, line) : Nat}
  LastCol.eq(ls, line)
