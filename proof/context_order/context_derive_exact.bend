# eukhe: the proof of LAW context_derive_exact

import Base
import ../../bend/context_order.bend as Co
import ../../laws/context_order.bend as ContextOrder
import ./base.bend as LACo

# PROOF of LAW context_derive_exact: the parts and the messages are the spec's entry by entry (co.parts, co.msgs_of: the contributions, co.contribute, co.contributed), and the plan of the messages is the spec's (co.plan).

def ContextOrder.context_derive_exact(mark, es):
  %LACo.co.parts(mark, es) : {Co.derive(mark, es) == Co.Derived{_, ContextOrder.plan_spec(ContextOrder.msgs_spec(mark, es))} : Co.Derived}
  %LACo.co.msgs_of(mark, es) : {Co.derive(mark, es) == Co.Derived{Co.parts(mark, es), ContextOrder.plan_spec(_)} : Co.Derived}
  %LACo.co.plan(Co.msgs(mark, es)) : {Co.derive(mark, es) == Co.Derived{Co.parts(mark, es), _} : Co.Derived}
  {==}
