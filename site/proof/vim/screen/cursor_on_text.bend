# eukhe.com's Neovim: the proof of LAW cursor_on_text
# ===================================================
#
# After any events and an Esc the editor is settled (Reach.final), in
# normal mode (Reach.normal_mode), on the files the start made of fs
# (Reach.files_run) and the screen the events asked for: Screen.on_text.

import Base
import ../../../vim/types.bend as T
import ../../../vim/st.bend as S
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/screen.bend as ScreenLaws
import ../../base/reach.bend as Re
import ./base.bend as Sc

def OnText.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Spec.on_text(fs, Laws.Spec.normal(fs, rows, cols, evs), Laws.Spec.rows(rows, evs), Laws.Spec.cols(cols, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  +evs2 = Laws.Spec.snoc(evs, Laws.Spec.key("<Esc>"))
  %Re.Reach.rows_normal(fs, rows, cols, evs) : {Laws.Spec.on_text(fs, n, _, Laws.Spec.cols(cols, evs)) == True{} : Bool}
  %Re.Reach.cols_normal(fs, rows, cols, evs) : {Laws.Spec.on_text(fs, n, S.St.rows(n), _) == True{} : Bool}
  Sc.Screen.on_text(fs, n, Re.Reach.final(fs, rows, cols, evs2), Re.Reach.files_run(fs, rows, cols, evs2), Re.Reach.normal_mode(fs, rows, cols, evs))

def ScreenLaws.cursor_on_text(fs, rows, cols, evs):
  OnText.law(fs, rows, cols, evs)
