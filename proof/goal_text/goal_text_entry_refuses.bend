# eukhe: the proof of LAW goal_text_entry_refuses
#
# PROOF: every answer opens with a Nat, never 'E' (gte.answer_ok); so an answer that opens with 'E' is the one error form.

import Base
import ../../bend/goal_text.bend as Gt
import ../../bend/ffi_goal_text.bend as FGt
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/goal_text.bend as GoalText
import ./base/entry.bend as LE
import ../base/staging.bend as LStg

def gtf.refuse(d: Wr.Dec<FGt.Req>, bad: {LawsBase.wire_opens_err(FGt.ffi.got(d)) == True{} : Bool}) -> {FGt.ffi.got(d) == Wr.err("goal_text: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FGt.answer(q) == Wr.err("goal_text: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FGt.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FGt.answer(q)), True{}, bad), LE.gte.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def GoalText.goal_text_entry_refuses(s, bad):
  gtf.refuse(FGt.get_req(s), bad)
