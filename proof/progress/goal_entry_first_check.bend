# eukhe: the proof of LAW goal_entry_first_check
# PROOF: the spelled request is the one goal_entry answers; with no prior,
# judge starts the count.

import Base
import ../../bend/ffi_progress.bend as FPr
import ../../bend/progress.bend as Pr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/progress.bend as Progress
import ../base/nat.bend as LNat
import ./base.bend as LA

def Progress.goal_entry_first_check(t, cap, work, h):
  Equal.sym(String, FPr.put_goal(Pr.judge(t, cap, None{}, work), ""), FPr.ffi(Progress.gs_spell_req(Progress.gs.Req{t, cap, None{}, work})), LA.pe.answer(t, cap, None{}, work, h))
