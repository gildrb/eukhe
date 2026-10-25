# eukhe: the proof of LAW optchat_entry_open_malformed_exact
# The entry reads every open as the laws' reader does (LAO.oo.read); an
# open it does not read whole is refused (LAO.oo.no).

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_optchat.bend as FOc
import ../../laws/optchat.bend as Optchat
import ./base/open.bend as LAO

def Optchat.optchat_entry_open_malformed_exact(i, no):
  %LAO.oo.read(i) : {FOc.open.go(_) == (FOc.Refused{}, SCon{'E', SCon{' ', "optchat: malformed open"}}) : FOc.St & String}
  LAO.oo.no(Optchat.oc_read_open.cfg(Optchat.oc_read_cfg.ph(Wr.get_nat(i))), no)
