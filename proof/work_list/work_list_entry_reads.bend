# eukhe: the proof of LAW work_list_entry_reads
#
# PROOF: the spec's spelling of the items is the list encoder's
# (LA.wlb.bools, LLog.pe.put_list), and a list of Bools whose count fits
# reads back with the rest untouched (LLog.pe.rt).

import Base
import ../../bend/ffi_work_list.bend as FWl
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/work_list.bend as WorkList
import ../log/base.bend as LLog
import ./base.bend as LA

def WorkList.work_list_entry_reads(done, rest, h):
  %LA.wlb.bools(done, rest) : {Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_nat(List.length(&2, Bool, done), _)) == Wr.Got{done, rest} : Wr.Dec<List<&2, Bool>>}
  %LLog.pe.put_list(done, rest) : {Wr.get_list(~Bool, ~Wr.get_bool, _) == Wr.Got{done, rest} : Wr.Dec<List<&2, Bool>>}
  LLog.pe.rt(done, rest, h)
