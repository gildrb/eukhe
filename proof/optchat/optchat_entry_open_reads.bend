# eukhe: the proof of LAW optchat_entry_open_reads
# The entry reads every open as the laws' reader does (LAO.oo.read); an
# open read whole runs the laws' open (LAO.oo.whole).

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_optchat.bend as FOc
import ../../laws/optchat.bend as Optchat
import ./base/open.bend as LAO

def Optchat.optchat_entry_open_reads(i, o, got):
  %LAO.oo.read(i) : {FOc.open.go(_) == Optchat.oc_open_model(o) : FOc.St & String}
  LAO.oo.whole(Optchat.oc_read_open.cfg(Optchat.oc_read_cfg.ph(Wr.get_nat(i))), o, got)
