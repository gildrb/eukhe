# eukhe: the proof of LAW context_extend_exact

import Base
import ../../bend/context_order.bend as Co
import ../../laws/context_order.bend as ContextOrder
import ./base.bend as LACo

# PROOF of LAW context_extend_exact: the test is the spec's (co.rederive), and so are the kept indices, the added messages (co.keeps, co.added) and the plan (co.plan).

def ContextOrder.context_extend_exact(ads, open):
  %LACo.co.rederive(ads) : {Co.extend(ads, open) == ContextOrder.extend_spec.pick(_, ads, open) : Co.Extended}
  LACo.co.ext.pick(Co.rederive(ads), ads, open)
