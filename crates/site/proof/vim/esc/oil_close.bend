# eukhe.com's Neovim: the proof of LAW oil_close
# ==============================================
#
# After an Esc the editor is in normal mode with no key waiting
# (Reach.normal_mode, Reach.normal_pend), so Ctrl-c is key 27 of
# Key.normal.hi: on a file it stays, on a listing it goes (Win.alt) to the
# head of the files opened, which Vim.keep keeps nonempty (Vim.opened):
# a file either way (CloseCc.at). Vim.real then keeps a file a file
# (CloseIs.real), and Vim.fit keeps the target (Esc.final_tgt).

import Base
import ../../../vim/types.bend as T
import ../../../vim/buf.bend as B
import ../../../vim/st.bend as S
import ../../../vim/core.bend as C
import ../../../vim/keys.bend as K
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/esc.bend as EscLaws
import ../../base.bend as L
import ../../base/reach.bend as Re
import ./base.bend as Eb

# Vim.real keeps a file a file
def CloseIs.pick(b: Bool, -i: Nat, -cur: T.Pos, -want: T.Want, -top: Nat, -left: Nat) -> {Laws.Spec.is_file(S.Win.tgt(Bool.pick(T.Win, b, T.Win{T.File{i}, cur, want, top, left}, T.Win{T.File{0n}, T.Pos{0n, 0n}, T.Col{0n}, 0n, 0n}))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def CloseIs.real(+fs: List<&2, T.Buf>, w: T.Win, h: {Laws.Spec.is_file(S.Win.tgt(w)) == True{} : Bool}) -> {Laws.Spec.is_file(S.Win.tgt(Vim.Vim.real(fs, w))) == True{} : Bool}:
  match w:
    case T.Win{tgt, cur, want, top, left}:
      match tgt:
        case T.File{+i}:
          CloseIs.pick(B.Tgt.real(fs, T.File{i}), i, cur, want, top, left)
        case T.Dir{p}:
          L.Bool.false_true({Laws.Spec.is_file(S.Win.tgt(Vim.Vim.real(fs, T.Win{T.Dir{p}, cur, want, top, left}))) == True{} : Bool}, h)

# Win.alt from a listing, the files opened nonempty: a file
def CloseCc.dir(+files: List<&2, T.Buf>, +folded: List<&2, List<&2, String>>, +dirs: List<&2, T.Listing>, +p: String, +cur: T.Pos, +want: T.Want, +top: Nat, +left: Nat, +marks: List<&2, T.Pos>, +spots: List<&2, T.Spot>, +bufs: List<&2, Nat>, +back: List<&2, T.Win>, +fwd: List<&2, T.Win>, +mode: T.Mode, +find: Maybe<&2, T.Find>, +hl: Bool, +opts: T.Opts, +rows: Nat, +cols: Nat, +msg: String, +stat: String, o: List<&2, Nat>)
  -> {Laws.Spec.is_file(S.Win.tgt(S.St.win(C.Win.alt(T.St{files, folded, dirs, T.Win{T.Dir{p}, cur, want, top, left}, marks, spots, Vim.Vim.opened(o), bufs, back, fwd, mode, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat})))) == True{} : Bool}:
  match o:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

# Ctrl-c in normal mode, no key waiting, the files opened nonempty
def CloseCc.at(+s: T.St, +o: List<&2, Nat>, ho: {S.St.opened(s) == Vim.Vim.opened(o) : List<&2, Nat>})
  -> {Laws.Spec.is_file(S.Win.tgt(S.St.win(Bool.pick(T.St, C.St.on_file(S.St.set_count(S.St.set_pend(s, T.NoPend{}), 0n)), S.St.set_count(S.St.set_pend(s, T.NoPend{}), 0n), C.Win.alt(S.St.set_count(S.St.set_pend(s, T.NoPend{}), 0n)))))) == True{} : Bool}:
  match s:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.File{i}:
              {==}
            case T.Dir{+p}:
              %Equal.sym(List<&2, Nat>, opened, Vim.Vim.opened(o), ho) : {Laws.Spec.is_file(S.Win.tgt(S.St.win(C.Win.alt(T.St{files, folded, dirs, T.Win{T.Dir{p}, cur, want, top, left}, marks, spots, _, bufs, back, fwd, mode, 0n, T.NoPend{}, find, hl, opts, rows, cols, msg, stat})))) == True{} : Bool}
              CloseCc.dir(files, folded, dirs, p, cur, want, top, left, marks, spots, bufs, back, fwd, mode, find, hl, opts, rows, cols, msg, stat, o)

def CloseCc.of(+s: T.St, hm: {S.St.mode(s) == T.Normal{} : T.Mode}, hp: {S.St.pend(s) == T.NoPend{} : T.Pend}, +o: List<&2, Nat>, ho: {S.St.opened(s) == Vim.Vim.opened(o) : List<&2, Nat>})
  -> {Laws.Spec.is_file(S.Win.tgt(S.St.win(Laws.Spec.after(K.Key.in(s, S.St.mode(s), "<C-c>"))))) == True{} : Bool}:
  %Equal.sym(T.Mode, S.St.mode(s), T.Normal{}, hm) : {Laws.Spec.is_file(S.Win.tgt(S.St.win(Laws.Spec.after(K.Key.in(s, _, "<C-c>"))))) == True{} : Bool}
  %Equal.sym(T.Pend, S.St.pend(s), T.NoPend{}, hp) : {Laws.Spec.is_file(S.Win.tgt(S.St.win(Laws.Spec.after(K.Key.pend(S.St.set_count(S.St.set_pend(s, T.NoPend{}), 0n), _, "<C-c>", S.St.count(s)))))) == True{} : Bool}
  CloseCc.at(s, o, ho)

# the files opened after evs and an Esc: Vim.opened of the Esc step's
def OilClose.opened(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {S.St.opened(Laws.Spec.normal(fs, rows, cols, evs)) == Vim.Vim.opened(S.St.opened(Laws.Spec.after(K.Key.in(Laws.Spec.run(fs, rows, cols, evs), S.St.mode(Laws.Spec.run(fs, rows, cols, evs)), "<Esc>")))) : List<&2, Nat>}:
  +r = Laws.Spec.run(fs, rows, cols, evs)
  +ste = Laws.Spec.after(K.Key.in(r, S.St.mode(r), "<Esc>"))
  +n = Re.Reach.next(r, {T.EvKey{"<Esc>"} : T.Ev})
  %Equal.sym(T.St, Laws.Spec.normal(fs, rows, cols, evs), Vim.Vim.final(n), Re.Reach.normal_step(fs, rows, cols, evs)) : {S.St.opened(_) == Vim.Vim.opened(S.St.opened(ste)) : List<&2, Nat>}
  Equal.trans(List<&2, Nat>, S.St.opened(Vim.Vim.final(n)), S.St.opened(n), Vim.Vim.opened(S.St.opened(ste)), Re.Field.opened_final(n), Re.Keep.opened(r, ste))

# the window Ctrl-c leaves after evs and an Esc shows a file
def OilClose.win(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Spec.is_file(S.Win.tgt(S.St.win(Re.Reach.next(Laws.Spec.normal(fs, rows, cols, evs), {T.EvKey{"<C-c>"} : T.Ev})))) == True{} : Bool}:
  +nn = Laws.Spec.normal(fs, rows, cols, evs)
  +stc = Laws.Spec.after(K.Key.in(nn, S.St.mode(nn), "<C-c>"))
  +r = Laws.Spec.run(fs, rows, cols, evs)
  +ste = Laws.Spec.after(K.Key.in(r, S.St.mode(r), "<Esc>"))
  %Eb.Esc.keep_win(nn, stc) : {Laws.Spec.is_file(S.Win.tgt(_)) == True{} : Bool}
  CloseCc.of(nn, Re.Reach.normal_mode(fs, rows, cols, evs), Re.Reach.normal_pend(fs, rows, cols, evs), S.St.opened(ste), OilClose.opened(fs, rows, cols, evs))

def OilClose.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Spec.is_file(Laws.F.tgt(Vim.Vim.frame(Laws.Spec.press(Laws.Spec.normal(fs, rows, cols, evs), "<C-c>")))) == True{} : Bool}:
  +nn = Laws.Spec.normal(fs, rows, cols, evs)
  +cc = {T.EvKey{"<C-c>"} : T.Ev}
  +m = Re.Reach.next(nn, cc)
  %Equal.sym(T.St, Laws.Spec.after(Vim.Vim.step(nn, cc)), Vim.Vim.final(m), Re.Reach.step(nn, cc)) : {Laws.Spec.is_file(S.Win.tgt(S.St.win(_))) == True{} : Bool}
  %Eb.Esc.final_tgt(m) : {Laws.Spec.is_file(_) == True{} : Bool}
  CloseIs.real(S.St.files(m), S.St.win(m), OilClose.win(fs, rows, cols, evs))

def EscLaws.oil_close(fs, rows, cols, evs):
  OilClose.law(fs, rows, cols, evs)
