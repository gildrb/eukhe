# eukhe: the proof of LAW optchat_entry_malformed_exact
# The entry reads every input as the laws' reader does (LAF.oe.read); an
# input it does not read whole keeps the chat (LAF.oe.no).

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_optchat.bend as FOc
import ../../laws/optchat.bend as Optchat
import ./base/ffi_optchat.bend as LAF

def Optchat.optchat_entry_malformed_exact(cfg, s, i, no):
  %LAF.oe.read(Wr.get_nat(i)) : {FOc.step.ev(cfg, s, _) == (FOc.Live{cfg, s}, SCon{'E', SCon{' ', "optchat: malformed event"}}) : FOc.St & String}
  LAF.oe.no(cfg, s, Optchat.oc_read.go(Wr.get_nat(i)), no)
