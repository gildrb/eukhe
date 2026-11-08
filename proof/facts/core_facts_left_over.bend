# eukhe: the proof of LAW core_facts_left_over

import Base
import ../../bend/ffi_facts.bend as FFx
import ../../bend/wire.bend as Wr
import ../../laws/facts/budgets.bend as FactsBudgets
import ./base.bend as LA

def FactsBudgets.core_facts_left_over(q, c, rest, h):
  %LA.pc.f_req(q, SCon{c, rest}, h) : {FFx.ffi.go(_) == Wr.err("budget request: input left over") : String}
  {==}
