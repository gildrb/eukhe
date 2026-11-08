# eukhe: the proof of LAW core_facts_google

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_facts.bend as FFx
import ../../laws/facts/budgets.bend as FactsBudgets
import ./base.bend as LA

def FactsBudgets.core_facts_google(rule, c, l, h):
  %LA.pc.f_req(FFx.Google{rule, c, l}, "", h) : {FFx.ffi.go(_) == FFx.put_gb(Fx.gbudget(rule, c, l), "") : String}
  {==}
