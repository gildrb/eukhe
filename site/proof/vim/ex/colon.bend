# eukhe.com's Neovim: the proof of LAW colon
# ==========================================
#
# ":" in normal mode with no waiting key opens the command line,
# Typing{Colon, ""}; Vim.final keeps the mode, so the frame puts the
# cursor on the last row, one cell in, after the ":" the command line
# shows (the screen has at least 12 columns).

import Base
import ../../../vim/types.bend as T
import ../../../vim/text.bend as X
import ../../../vim/st.bend as S
import ../../../vim/screen.bend as R
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/ex.bend as ExLaws
import ../../base.bend as L
import ../../base/final.bend as Fi
import ../../base/reach.bend as Re
import ../screen/base.bend as Sc
import ../screen/parts.bend as Pa
import ./base.bend as Eb

# ":" on a command line of at least 2 columns shows whole
def Colon.typed(c: Nat, h: L.LE(2n, c)) -> {R.Scr.typed(":", c) == ":" : String}:
  match c:
    case 0n:
      L.Bool.false_true({R.Scr.typed(":", 0n) == ":" : String}, h)
    case 1n:
      L.Bool.false_true({R.Scr.typed(":", 1n) == ":" : String}, h)
    case 2n+k:
      {==}

# the cursor one cell in
def Colon.col(+c: Nat, h: L.LE(2n, c)) -> {Nat.is_eq(X.Text.cells(R.Scr.typed(":", c)), 1n) == True{} : Bool}:
  %Equal.sym(String, R.Scr.typed(":", c), ":", Colon.typed(c, h)) : {Nat.is_eq(X.Text.cells(_), 1n) == True{} : Bool}
  {==}

# the command line shows ":"
def Colon.cmd(+c: Nat, h: L.LE(2n, c)) -> {String.eq(R.Scr.typed(":", c), ":") == True{} : Bool}:
  %Equal.sym(String, R.Scr.typed(":", c), ":", Colon.typed(c, h)) : {String.eq(_, ":") == True{} : Bool}
  {==}

# the frame after ":" on a screen of rows (at least 3) x cols
def Colon.screen(+rows: Nat, +cols: Nat, h3: L.LE(3n, rows))
  -> {Bool.and(Bool.and(Nat.is_eq(Nat.sub(Nat.max(rows, 3n), 1n), Nat.sub(rows, 1n)), Nat.is_eq(X.Text.cells(R.Scr.typed(":", Nat.max(cols, 12n))), 1n)), String.eq(R.Scr.typed(":", Nat.max(cols, 12n)), ":")) == True{} : Bool}:
  +c = Nat.max(cols, 12n)
  +h2 = L.Nat.le_trans(2n, 12n, c, {==}, L.Nat.le_max_r(cols, 12n))
  +hr = Pa.Eq.of(Nat.sub(Nat.max(rows, 3n), 1n), Nat.sub(rows, 1n), Equal.cong(Nat, Nat, z => Nat.sub(z, 1n), Nat.max(rows, 3n), rows, Eb.Max.l(rows, 3n, h3)))
  L.And.intro(Bool.and(Nat.is_eq(Nat.sub(Nat.max(rows, 3n), 1n), Nat.sub(rows, 1n)), Nat.is_eq(X.Text.cells(R.Scr.typed(":", c)), 1n)), String.eq(R.Scr.typed(":", c), ":"),
    L.And.intro(Nat.is_eq(Nat.sub(Nat.max(rows, 3n), 1n), Nat.sub(rows, 1n)), Nat.is_eq(X.Text.cells(R.Scr.typed(":", c)), 1n), hr, Colon.col(c, h2)), Colon.cmd(c, h2))

# a settled editor in normal mode, no key waiting: ":" opens the command line
def Colon.of(+s: T.St, fin: Fi.Final(s), hm: {S.St.mode(s) == T.Normal{} : T.Mode}, hp: {S.St.pend(s) == T.NoPend{} : T.Pend}) -> {Laws.Claim.colon(s, S.St.rows(s)) == True{} : Bool}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match mode:
        case T.Normal{}:
          match pend:
            case T.NoPend{}:
              (f3, r1) = fin
              Colon.screen(rows, cols, f3)
            case T.PendG{}:
              Eb.Pend.clash({Laws.Claim.colon(T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Normal{}, count, T.PendG{}, find, hl, opts, rows, cols, msg, stat}, rows) == True{} : Bool}, T.PendG{}, hp)
            case T.PendZ{}:
              Eb.Pend.clash({Laws.Claim.colon(T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Normal{}, count, T.PendZ{}, find, hl, opts, rows, cols, msg, stat}, rows) == True{} : Bool}, T.PendZ{}, hp)
            case T.PendLead{}:
              Eb.Pend.clash({Laws.Claim.colon(T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Normal{}, count, T.PendLead{}, find, hl, opts, rows, cols, msg, stat}, rows) == True{} : Bool}, T.PendLead{}, hp)
            case T.PendLeadF{}:
              Eb.Pend.clash({Laws.Claim.colon(T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Normal{}, count, T.PendLeadF{}, find, hl, opts, rows, cols, msg, stat}, rows) == True{} : Bool}, T.PendLeadF{}, hp)
            case T.PendY{}:
              Eb.Pend.clash({Laws.Claim.colon(T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Normal{}, count, T.PendY{}, find, hl, opts, rows, cols, msg, stat}, rows) == True{} : Bool}, T.PendY{}, hp)
        case T.Typing{kind, text}:
          Sc.Mode.typing({Laws.Claim.colon(T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Typing{kind, text}, count, pend, find, hl, opts, rows, cols, msg, stat}, rows) == True{} : Bool}, kind, text, hm)
        case T.Picking{k, q, its, n, sel, top, pv, levels}:
          Sc.Mode.picking({Laws.Claim.colon(T.St{files, folded, dirs, win, marks, spots, opened, bufs, back, fwd, T.Picking{k, q, its, n, sel, top, pv, levels}, count, pend, find, hl, opts, rows, cols, msg, stat}, rows) == True{} : Bool}, k, q, its, n, sel, top, pv, levels, hm)

def Colon.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.colon(Laws.Spec.normal(fs, rows, cols, evs), Laws.Spec.rows(rows, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  %Re.Reach.rows_normal(fs, rows, cols, evs) : {Laws.Claim.colon(n, _) == True{} : Bool}
  Colon.of(n, Re.Reach.final(fs, rows, cols, Laws.Spec.snoc(evs, Laws.Spec.key("<Esc>"))), Re.Reach.normal_mode(fs, rows, cols, evs), Re.Reach.normal_pend(fs, rows, cols, evs))

def ExLaws.colon(fs, rows, cols, evs):
  Colon.law(fs, rows, cols, evs)
