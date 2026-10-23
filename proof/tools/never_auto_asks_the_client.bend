# eukhe: the proof of LAW never_auto_asks_the_client

import Base
import ../../bend/approvals.bend as Am
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./base.bend as LA

def pa.never_auto_asks(+auto: List<&2, Nat>, +es: List<&2, Nat>, +c: Nat, has: {Tl.elem(es, c) == True{} : Bool}, held: {Nat.is_le(4n, c) == True{} : Bool}, +yes: Bool, +above: List<&2, Am.Desk>) -> {Am.gate(auto, es, Am.Says{yes} <> above) == Am.Routed{Am.Out{[0n], Am.Answered{0n, yes}}, Am.yes.fate(yes)} : Am.Gated}:
  LA.pa.never_auto(auto, es, c, has, held, Am.Says{yes} <> above)

def Tools.never_auto_asks_the_client(auto, es, c, has, held, yes, above):
  pa.never_auto_asks(auto, es, c, has, held, yes, above)
