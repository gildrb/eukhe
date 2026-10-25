# eukhe: the proof of LAW goal_text_entry_exact
#
# PROOF: each decoder stage answers Got only for the spec's spelling of its value (gtx.*, from wire_nat_exact, wire_str_exact, wire_bool_exact), the lengths within the wire; a value is answered only for a request read whole (gtx.top).

import Base
import ../../bend/goal_text.bend as Gt
import ../../bend/ffi_goal_text.bend as FGt
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/goal_text.bend as GoalText
import ./base/entry.bend as LE
import ../base/wire_dec.bend as LD

def GoalText.goal_text_entry_exact(s, ok):
  LE.gtx.top(s, FGt.get_req(s), LE.gtx.req_at(s, Wr.get_nat(s), LD.dcw.nat(s)), ok)
