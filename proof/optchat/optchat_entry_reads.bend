# eukhe: the proof of LAW optchat_entry_reads
# The entry reads every input as the laws' reader does (LAF.oe.read); a
# whole request runs as the laws' model asks (LAF.oe.whole).

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_optchat.bend as FOc
import ../../laws/optchat.bend as Optchat
import ./base/ffi_optchat.bend as LAF

def Optchat.optchat_entry_reads(cfg, s, i, q, got):
  %LAF.oe.read(Wr.get_nat(i)) : {FOc.step.ev(cfg, s, _) == (FOc.Live{cfg, Optchat.oc_next(cfg, s, q)}, Optchat.oc_reply(cfg, s, q)) : FOc.St & String}
  LAF.oe.whole(cfg, s, Optchat.oc_read.go(Wr.get_nat(i)), q, got)
