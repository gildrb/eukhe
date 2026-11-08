# eukhe: the proof of LAW run_entry_reads
#
# PROOF: the laws' speller is the entry's encoder (rex.w_ask) and the
# laws' reader its decoder (rex.ask), which reads a request that fits
# back (LARun.rk.rt_ask).

import Base
import ../../bend/ffi_run.bend as FRn
import ../../bend/wire.bend as Wr
import ./base.bend as LARun
import ../../laws/run/spec.bend as RunSpec
import ./base/entry.bend as LARunEntry

def RunSpec.run_entry_reads(a, rest, h):
  %LARunEntry.rex.w_ask(a, rest) : {RunSpec.re.r_ask(_) == Wr.Got{a, rest} : Wr.Dec<FRn.Ask>}
  %LARunEntry.rex.ask(FRn.put_ask(a, rest)) : {_ == Wr.Got{a, rest} : Wr.Dec<FRn.Ask>}
  LARun.rk.rt_ask(a, rest, h)
