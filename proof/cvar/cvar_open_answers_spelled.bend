# eukhe: the proof of LAW cvar_open_answers_spelled
#
# PROOF: the spelled table is the entry's own encoding (cvs.table), which
# reads back whole (pvf.table_rt of cvar_ffi_open).

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../../laws/cvar/entry.bend as CvarEntry
import ./base/spell.bend as LS
import ./cvar_ffi_open.bend as PCvarFfiOpen

def CvarEntry.cvar_open_answers_spelled(bs, as, fits):
  %LS.cvs.table(bs, as, "") : {FCv.open(_) == (FCv.Table{bs, as}, "") : FCv.St & String}
  Equal.cong(Wr.Dec<FCv.St>, FCv.St & String, d => FCv.open.go(d), FCv.get_table(FCv.put_table(bs, as, "")), Wr.Got{FCv.Table{bs, as}, ""}, PCvarFfiOpen.pvf.table_rt(bs, as, "", fits))
