# eukhe.com's Neovim: the column a vertical motion keeps (A4)
# ===========================================================
#
# Claim.vcol compares the column before and after a motion. Every
# settled editor's column is Move.aim of its want on its line (Mo.Aim),
# and j, k, gg and G go to a line at Move.aim of that same want (GL.cur,
# GLJ.cur): VCol.aim proves the claim for any want, VCol.of carries it
# from the frames to those columns.

import Base
import ../../../vim/types.bend as T
import ../../../vim/move.bend as M
import ../../../vim/st.bend as S
import ../../../vim/core.bend as C
import ../../../vim/buf.bend as B
import ../../../vim/keys.bend as K
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../base.bend as L
import ../screen/base.bend as Sb
import ../../base/reach.bend as Re
import ./base.bend as Mo

# what Claim.vcol tests, of the column c on a line whose last is last,
# the column bc after the motion and the column want it should keep
def VCol.Q(+c: Nat, +last: Nat, +bc: Nat, +want: Nat) -> Bool:
  Bool.pick(Bool, Nat.is_lt(c, last), Nat.is_eq(bc, want), Nat.is_le(want, bc))

def VCol.lt_self(a: Nat) -> {Nat.is_lt(a, a) == False{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      VCol.lt_self(p)

def VCol.pick_tt(c: Bool) -> {Bool.pick(Bool, c, True{}, True{}) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# a want of column n, on lines whose last columns are A (before) and B
def VCol.col(+n: Nat, +A: Nat, +B: Nat) -> {VCol.Q(Nat.min(n, A), A, Nat.min(n, B), Nat.min(Nat.min(n, A), B)) == True{} : Bool}:
  match n A B:
    case 0n 0n _:
      {==}
    case 0n 1n+a _:
      {==}
    case 1n+p 0n 0n:
      {==}
    case 1n+p 0n 1n+b:
      {==}
    case 1n+p 1n+a 0n:
      VCol.pick_tt(Nat.is_lt(Nat.min(p, a), a))
    case 1n+p 1n+a 1n+b:
      VCol.col(p, a, b)

# a want of the line's end
def VCol.end(+A: Nat, +B: Nat) -> {VCol.Q(A, A, B, Nat.min(A, B)) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_lt(A, A), False{}, VCol.lt_self(A)) : {Bool.pick(Bool, _, Nat.is_eq(B, Nat.min(A, B)), Nat.is_le(Nat.min(A, B), B)) == True{} : Bool}
  L.Nat.min_le_r(A, B)

# any want: from line l0 to line m of ls
def VCol.aim(+ls: List<&2, String>, +l0: Nat, +m: Nat, w: T.Want) -> {VCol.Q(M.Move.aim(ls, l0, w), M.Move.last_col(ls, l0), M.Move.aim(ls, m, w), Nat.min(M.Move.aim(ls, l0, w), M.Move.last_col(ls, m))) == True{} : Bool}:
  match w:
    case T.Col{+n}:
      VCol.col(n, M.Move.last_col(ls, l0), M.Move.last_col(ls, m))
    case T.End{}:
      VCol.end(M.Move.last_col(ls, l0), M.Move.last_col(ls, m))

# the claim, from what the two frames read: the column before is the one
# want w gives on line l0 of ls, the line after is m of the same lines,
# and the column after is the one w gives there
def VCol.of(+fs: List<&2, T.Buf>, +z: T.St, +t: T.St, +ls: List<&2, String>, +l0: Nat, +m: Nat, +w: T.Want,
  e_c: {Laws.Spec.at_col(Vim.Vim.frame(z)) == M.Move.aim(ls, l0, w) : Nat},
  e_l0: {Laws.Spec.at_line(Vim.Vim.frame(z)) == l0 : Nat},
  e_ls1: {Laws.Spec.lines(fs, z) == ls : List<&2, String>},
  e_ls2: {Laws.Spec.lines(fs, t) == ls : List<&2, String>},
  e_m: {Laws.Spec.at_line(Vim.Vim.frame(t)) == m : Nat},
  e_bc: {Laws.Spec.at_col(Vim.Vim.frame(t)) == M.Move.aim(ls, m, w) : Nat})
  -> {Laws.Claim.vcol(fs, z, t) == True{} : Bool}:
  +a = Vim.Vim.frame(z)
  +b = Vim.Vim.frame(t)
  +c0 = M.Move.aim(ls, l0, w)
  +bc = M.Move.aim(ls, m, w)
  %Equal.sym(Nat, Laws.Spec.at_col(a), c0, e_c) : {VCol.Q(_, Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(Laws.Spec.lines(fs, z), Laws.Spec.at_line(a)))), Laws.Spec.at_col(b), Laws.Spec.min(_, Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(Laws.Spec.lines(fs, t), Laws.Spec.at_line(b)))))) == True{} : Bool}
  %Equal.sym(Nat, Laws.Spec.at_line(a), l0, e_l0) : {VCol.Q(c0, Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(Laws.Spec.lines(fs, z), _))), Laws.Spec.at_col(b), Laws.Spec.min(c0, Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(Laws.Spec.lines(fs, t), Laws.Spec.at_line(b)))))) == True{} : Bool}
  %Equal.sym(List<&2, String>, Laws.Spec.lines(fs, z), ls, e_ls1) : {VCol.Q(c0, Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(_, l0))), Laws.Spec.at_col(b), Laws.Spec.min(c0, Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(Laws.Spec.lines(fs, t), Laws.Spec.at_line(b)))))) == True{} : Bool}
  %Equal.sym(List<&2, String>, Laws.Spec.lines(fs, t), ls, e_ls2) : {VCol.Q(c0, Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(ls, l0))), Laws.Spec.at_col(b), Laws.Spec.min(c0, Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(_, Laws.Spec.at_line(b)))))) == True{} : Bool}
  %Equal.sym(Nat, Laws.Spec.at_line(b), m, e_m) : {VCol.Q(c0, Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(ls, l0))), Laws.Spec.at_col(b), Laws.Spec.min(c0, Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(ls, _))))) == True{} : Bool}
  %Equal.sym(Nat, Laws.Spec.at_col(b), bc, e_bc) : {VCol.Q(c0, Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(ls, l0))), _, Laws.Spec.min(c0, Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(ls, m))))) == True{} : Bool}
  %Equal.sym(Nat, Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(ls, l0))), M.Move.last_col(ls, l0), Mo.LastCol.eq(ls, l0)) : {VCol.Q(c0, _, bc, Laws.Spec.min(c0, Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(ls, m))))) == True{} : Bool}
  %Equal.sym(Nat, Laws.Spec.last(Laws.Spec.chars(Laws.Spec.line(ls, m))), M.Move.last_col(ls, m), Mo.LastCol.eq(ls, m)) : {VCol.Q(c0, M.Move.last_col(ls, l0), bc, Laws.Spec.min(c0, _)) == True{} : Bool}
  %Equal.sym(Nat, Laws.Spec.min(c0, M.Move.last_col(ls, m)), Nat.min(c0, M.Move.last_col(ls, m)), Sb.Spec.min_eq(c0, M.Move.last_col(ls, m))) : {VCol.Q(c0, M.Move.last_col(ls, l0), bc, _) == True{} : Bool}
  VCol.aim(ls, l0, m, w)

# The editors
# -----------

# a position on the text is its own clamp
def VCol.clamp_self(+ls: List<&2, String>, p: T.Pos, hl: L.LE(S.Pos.line(p), M.Move.last_line(ls)), hc: L.LE(S.Pos.col(p), M.Move.last_col(ls, S.Pos.line(p)))) -> {M.Move.clamp(ls, p) == p : T.Pos}:
  match p:
    case T.Pos{+l, +c}:
      Mo.Clamp.on(ls, l, c, hl, hc)

# j k: Win.go_line keeps the lines
def VCol.gl_lines(+z: T.St, +l: Nat) -> {C.St.lines(Vim.Vim.fit(Vim.Vim.keep(z, C.Win.go_line(z, l)))) == C.St.lines(z) : List<&2, String>}:
  match z:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.File{+i}:
              {==}
            case T.Dir{+path}:
              {==}

# G gg: a jump, then Win.go_line, keeps the lines
def VCol.glj_lines(+z: T.St, +l: Nat) -> {C.St.lines(Vim.Vim.fit(Vim.Vim.keep(z, C.Win.go_line(C.Win.jump(S.St.set_count(S.St.set_pend(z, T.NoPend{}), 0n)), l)))) == C.St.lines(z) : List<&2, String>}:
  match z:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.File{+i}:
              {==}
            case T.Dir{+path}:
              {==}

# the first g keeps the lines
def VCol.g1_lines(+z: T.St) -> {C.St.lines(Vim.Vim.fit(Vim.Vim.keep(z, S.St.set_count(S.St.set_pend(z, T.PendG{}), 0n)))) == C.St.lines(z) : List<&2, String>}:
  match z:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.File{+i}:
              {==}
            case T.Dir{+path}:
              {==}

# the claim for a motion that settles at Vim.fit(y), y a Win.go_line to
# line l over lines ls with want w (GL.cur, GLJ.cur), from an editor z on
# line l0 of ls at the column w gives
def VCol.tail(+fs: List<&2, T.Buf>, +z: T.St, +y: T.St, +ls: List<&2, String>, +l0: Nat, +l: Nat, +w: T.Want,
  e_c: {Laws.Spec.at_col(Vim.Vim.frame(z)) == M.Move.aim(ls, l0, w) : Nat},
  e_l0: {Laws.Spec.at_line(Vim.Vim.frame(z)) == l0 : Nat},
  e_ls1: {Laws.Spec.lines(fs, z) == ls : List<&2, String>},
  ecur: {S.Win.cur(S.St.win(Vim.Vim.fit(y))) == Mo.Cl3(ls, T.Pos{Nat.min(l, M.Move.last_line(ls)), M.Move.aim(ls, Nat.min(l, M.Move.last_line(ls)), w)}) : T.Pos},
  elines: {C.St.lines(Vim.Vim.fit(y)) == ls : List<&2, String>},
  e_lt: {Laws.Spec.lines(fs, Vim.Vim.fit(y)) == C.St.lines(Vim.Vim.fit(y)) : List<&2, String>},
  e_mt: {Laws.Spec.at_line(Vim.Vim.frame(Vim.Vim.fit(y))) == C.St.line(Vim.Vim.fit(y)) : Nat},
  e_ct: {Laws.Spec.at_col(Vim.Vim.frame(Vim.Vim.fit(y))) == C.St.col(Vim.Vim.fit(y)) : Nat})
  -> {Laws.Claim.vcol(fs, z, Vim.Vim.fit(y)) == True{} : Bool}:
  +t = Vim.Vim.fit(y)
  +last = M.Move.last_line(ls)
  +m = Nat.min(l, last)
  +a = M.Move.aim(ls, m, w)
  +p = {T.Pos{m, a} : T.Pos}
  +cl = Mo.Cl3.on(ls, p, Mo.Clamp.on(ls, m, a, L.Nat.min_le_r(l, last), Mo.Aim.le(ls, m, w)))
  +ecur2 = Equal.trans(T.Pos, S.Win.cur(S.St.win(t)), Mo.Cl3(ls, p), p, ecur, cl)
  +eline = Equal.cong(T.Pos, Nat, q => S.Pos.line(q), S.Win.cur(S.St.win(t)), p, ecur2)
  +ecol = Equal.cong(T.Pos, Nat, q => S.Pos.col(q), S.Win.cur(S.St.win(t)), p, ecur2)
  +e_m = Equal.trans(Nat, Laws.Spec.at_line(Vim.Vim.frame(t)), C.St.line(t), m, e_mt, eline)
  +e_bc = Equal.trans(Nat, Laws.Spec.at_col(Vim.Vim.frame(t)), C.St.col(t), a, e_ct, ecol)
  +e_ls2 = Equal.trans(List<&2, String>, Laws.Spec.lines(fs, t), C.St.lines(t), ls, e_lt, elines)
  VCol.of(fs, z, t, ls, l0, m, w, e_c, e_l0, e_ls1, e_ls2, e_m, e_bc)

# a key whose step from x is st, kept on a real target in normal mode,
# settles at Vim.fit (Reach.step, Final.real)
def VCol.press(+x: T.St, +k: String, +st: T.St, e_st: {Laws.Spec.after(K.Key.in(x, S.St.mode(x), k)) == st : T.St},
  hr: {B.Tgt.real(S.St.files(Vim.Vim.keep(x, st)), S.Win.tgt(S.St.win(Vim.Vim.keep(x, st)))) == True{} : Bool}, hm: {S.St.mode(Vim.Vim.keep(x, st)) == T.Normal{} : T.Mode})
  -> {Laws.Spec.press(x, k) == Vim.Vim.fit(Vim.Vim.keep(x, st)) : T.St}:
  +y = Vim.Vim.keep(x, st)
  +raw = Laws.Spec.after(K.Key.in(x, S.St.mode(x), k))
  +e0 = Re.Reach.step(x, T.EvKey{k})
  +e2 = Equal.cong(T.St, T.St, q => Vim.Vim.final(Vim.Vim.keep(x, q)), raw, st, e_st)
  Equal.trans(T.St, Laws.Spec.press(x, k), Vim.Vim.final(Vim.Vim.keep(x, raw)), Vim.Vim.fit(y), e0, Equal.trans(T.St, Vim.Vim.final(Vim.Vim.keep(x, raw)), Vim.Vim.final(y), Vim.Vim.fit(y), e2, Mo.Final.real(y, hr, hm)))
