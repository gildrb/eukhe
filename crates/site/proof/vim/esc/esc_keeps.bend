# eukhe.com's Neovim: the proof of LAW esc_keeps
# ==============================================
#
# The editor after evs and an Esc is Vim.final of the Esc step from the
# run (Reach.normal_step). Esc keeps the window in every mode (Esc.win),
# Vim.keep keeps it, and Vim.final shows the target Vim.real picks
# (Esc.final_tgt), which keeps the run's: it is real (Esc.real_run).

import Base
import ../../../vim/types.bend as T
import ../../../vim/st.bend as S
import ../../../vim/keys.bend as K
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/esc.bend as EscLaws
import ../../base/reach.bend as Re
import ./base.bend as Eb

def EscKeeps.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Spec.same_tgt(Laws.F.tgt(Vim.Vim.frame(Laws.Spec.run(fs, rows, cols, evs))), Laws.F.tgt(Vim.Vim.frame(Laws.Spec.normal(fs, rows, cols, evs)))) == True{} : Bool}:
  +r = Laws.Spec.run(fs, rows, cols, evs)
  +esc = {T.EvKey{"<Esc>"} : T.Ev}
  +st = Laws.Spec.after(K.Key.in(r, S.St.mode(r), "<Esc>"))
  +n = Re.Reach.next(r, esc)
  -tr = S.Win.tgt(S.St.win(r))
  %Equal.sym(T.St, Laws.Spec.normal(fs, rows, cols, evs), Vim.Vim.final(n), Re.Reach.normal_step(fs, rows, cols, evs)) : {Laws.Spec.same_tgt(tr, S.Win.tgt(S.St.win(_))) == True{} : Bool}
  %Eb.Esc.final_tgt(n) : {Laws.Spec.same_tgt(tr, _) == True{} : Bool}
  %Equal.sym(List<&2, T.Buf>, S.St.files(n), S.St.files(r), Re.Keep.files(r, st)) : {Laws.Spec.same_tgt(tr, S.Win.tgt(Vim.Vim.real(_, S.St.win(n)))) == True{} : Bool}
  %Eb.Esc.keep_win(r, st) : {Laws.Spec.same_tgt(tr, S.Win.tgt(Vim.Vim.real(S.St.files(r), _))) == True{} : Bool}
  %Eb.Esc.win(r) : {Laws.Spec.same_tgt(tr, S.Win.tgt(Vim.Vim.real(S.St.files(r), _))) == True{} : Bool}
  %Eb.Esc.real_back(S.St.files(r), S.St.win(r), Eb.Esc.real_run(fs, rows, cols, evs)) : {Laws.Spec.same_tgt(tr, S.Win.tgt(_)) == True{} : Bool}
  Eb.Esc.same_refl(S.Win.tgt(S.St.win(r)))

def EscLaws.esc_keeps(fs, rows, cols, evs):
  EscKeeps.law(fs, rows, cols, evs)
