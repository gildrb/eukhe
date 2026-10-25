# eukhe: the proof of LAW gateway_never_waits

import Base
import ../../bend/approvals.bend as Am
import ../../laws/approvals/route.bend as Approvals

# The gateway rule
# ----------------

def pa.never_waits(+above: List<&2, Am.Desk>) -> {Am.route(Am.Phone{} <> above) == Am.Out{Nil{}, Am.Ruled{0n}} : Am.Out}:
  {==}

# (G5) A session that runs only from the phone gateway never waits

def Approvals.gateway_never_waits(above):
  pa.never_waits(above)
