# eukhe.com's Neovim: the proof of LAW scrolloff
# ==============================================
#
# After any events and an Esc the editor is settled, in normal mode, on
# the files the start made of fs: View.fit kept the window's first line
# in the band (proof/base/final.bend), so 'scrolloff' holds
# (Screen.scrolled).

import Base
import ../../vim/types.bend as T
import ../../vim/st.bend as S
import ../../LAWS.bend as Laws
import ../base/reach.bend as Re
import ./base.bend as Sc

def Scrolloff.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Spec.scrolled(fs, Laws.Spec.normal(fs, rows, cols, evs), Laws.Spec.rows(rows, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  +evs2 = Laws.Spec.snoc(evs, Laws.Spec.key("<Esc>"))
  %Re.Reach.rows_normal(fs, rows, cols, evs) : {Laws.Spec.scrolled(fs, n, _) == True{} : Bool}
  Sc.Screen.scrolled(fs, n, Re.Reach.final(fs, rows, cols, evs2), Re.Reach.files_run(fs, rows, cols, evs2), Re.Reach.normal_mode(fs, rows, cols, evs))

def Laws.scrolloff(fs, rows, cols, evs):
  Scrolloff.law(fs, rows, cols, evs)
