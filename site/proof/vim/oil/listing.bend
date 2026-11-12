# eukhe.com's Neovim: the proof of LAW oil_listing
# ================================================
#
# A folder's window shows Oil's listing of it over the files
# (Oil.run_lines); that listing holds each file's entry in the folder
# (Bag.covers) and, after "../", only entries of files (Bag.only).

import Base
import ../../../vim/types.bend as T
import ../../../vim/buf.bend as B
import ../../../vim/st.bend as S
import ../../../vim/core.bend as C
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/oil.bend as OilLaws
import ../../base.bend as L
import ../screen/base.bend as Sb
import ./base.bend as O
import ./bag.bend as Bg

def Listing.at(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>, t: T.Tgt, e: {S.Win.tgt(S.St.win(Laws.Spec.run(fs, rows, cols, evs))) == t : T.Tgt})
  -> {Laws.Claim.listing.of(fs, Laws.Spec.run(fs, rows, cols, evs), t) == True{} : Bool}:
  match t:
    case T.File{i}:
      {==}
    case T.Dir{+d}:
      +s = Laws.Spec.run(fs, rows, cols, evs)
      +ls = B.Oil.list(Sb.Files.norm(fs), d)
      %Equal.sym(T.Tgt, S.Win.tgt(S.St.win(s)), T.Dir{d}, e) : {Bool.and(Laws.Spec.covers(d, fs, B.Lines.some(C.St.lines.at(s, _))), Laws.Spec.only(d, Laws.Spec.tail(B.Lines.some(C.St.lines.at(s, _))), fs)) == True{} : Bool}
      %Equal.sym(List<&2, String>, C.St.lines.at(s, T.Dir{d}), B.Oil.list(B.Files.some(fs, Nil{}), d), O.Oil.run_lines(fs, rows, cols, evs, d)) : {Bool.and(Laws.Spec.covers(d, fs, B.Lines.some(_)), Laws.Spec.only(d, Laws.Spec.tail(B.Lines.some(_)), fs)) == True{} : Bool}
      %Equal.sym(List<&2, T.Buf>, B.Files.some(fs, Nil{}), List.reverse.go(&2, T.Buf, Nil{}, Sb.Files.norm(fs)), Sb.Files.some_go(fs, Nil{})) : {Bool.and(Laws.Spec.covers(d, fs, B.Lines.some(B.Oil.list(_, d))), Laws.Spec.only(d, Laws.Spec.tail(B.Lines.some(B.Oil.list(_, d))), fs)) == True{} : Bool}
      L.And.intro(Laws.Spec.covers(d, fs, ls), Laws.Spec.only(d, Laws.Spec.tail(ls), fs), Bg.Bag.covers(d, fs), Bg.Bag.only(d, fs))

def Listing.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.listing(fs, Laws.Spec.run(fs, rows, cols, evs)) == True{} : Bool}:
  +s = Laws.Spec.run(fs, rows, cols, evs)
  Listing.at(fs, rows, cols, evs, S.Win.tgt(S.St.win(s)), {==})

def OilLaws.oil_listing(fs, rows, cols, evs):
  Listing.law(fs, rows, cols, evs)
