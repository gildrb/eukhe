# eukhe: the proof of LAW left_to_the_gateway

import Base
import ../../bend/approvals.bend as Am
import ../../laws/approvals.bend as Approvals

def pa.left_to_gateway(+above: List<&2, Am.Desk>) -> {Am.route(Am.PhoneLeft{} <> above) == Am.Out{[0n], Am.Ruled{0n}} : Am.Out}:
  {==}

def Approvals.left_to_the_gateway(above):
  pa.left_to_gateway(above)
