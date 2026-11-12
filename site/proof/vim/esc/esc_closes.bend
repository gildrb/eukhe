# eukhe.com's Neovim: the proof of LAW esc_closes
# ===============================================
#
# After an Esc the editor is in normal mode (Reach.normal_mode), and the
# frame's float is Scr.float of the mode: None in normal mode.

import Base
import ../../../vim/types.bend as T
import ../../../vim/st.bend as S
import ../../../vim/screen.bend as R
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/esc.bend as EscLaws
import ../../base/reach.bend as Re

def EscCloses.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.F.float(Vim.Vim.frame(Laws.Spec.normal(fs, rows, cols, evs))) == None{} : Maybe<&2, T.Float>}:
  -n = Laws.Spec.normal(fs, rows, cols, evs)
  %Equal.sym(T.Mode, S.St.mode(n), T.Normal{}, Re.Reach.normal_mode(fs, rows, cols, evs)) : {R.Scr.float(n, _) == None{} : Maybe<&2, T.Float>}
  {==}

def EscLaws.esc_closes(fs, rows, cols, evs):
  EscCloses.law(fs, rows, cols, evs)
