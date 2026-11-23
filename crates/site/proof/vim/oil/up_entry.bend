# eukhe.com's Neovim: the proof of LAW oil_up_entry
# =================================================
#
# A folder's window shows Oil's listing of it (Oil.run_lines), and Oil's
# listings start with "../" (B.Oil.list).

import Base
import ../../../vim/types.bend as T
import ../../../vim/buf.bend as B
import ../../../vim/st.bend as S
import ../../../vim/core.bend as C
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/oil.bend as OilLaws
import ./base.bend as O

def UpEntry.at(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>, t: T.Tgt)
  -> {Bool.pick(Bool, Laws.Spec.is_file(t), True{}, String.eq(Laws.Spec.head(B.Lines.some(C.St.lines.at(Laws.Spec.run(fs, rows, cols, evs), t))), "../")) == True{} : Bool}:
  match t:
    case T.File{i}:
      {==}
    case T.Dir{+d}:
      %Equal.sym(List<&2, String>, C.St.lines.at(Laws.Spec.run(fs, rows, cols, evs), T.Dir{d}), B.Oil.list(B.Files.some(fs, Nil{}), d), O.Oil.run_lines(fs, rows, cols, evs, d)) : {String.eq(Laws.Spec.head(B.Lines.some(_)), "../") == True{} : Bool}
      {==}

def UpEntry.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.up_entry(Laws.Spec.run(fs, rows, cols, evs)) == True{} : Bool}:
  +s = Laws.Spec.run(fs, rows, cols, evs)
  UpEntry.at(fs, rows, cols, evs, S.Win.tgt(S.St.win(s)))

def OilLaws.oil_up_entry(fs, rows, cols, evs):
  UpEntry.law(fs, rows, cols, evs)
