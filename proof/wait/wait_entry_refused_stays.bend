# eukhe: the proof of LAW wait_entry_refused_stays
# An open answered with an error form opened the refused state
# (wait_entry_open_refused); the refused state answers every step with
# the refused error and stays refused (induction on the inputs).

import Base
import ../../bend/wait.bend as Wt
import ../../bend/ffi_wait_race.bend as FWt
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wait.bend as WaitLaws
import ./base.bend as LA
import ./wait_entry_open_refused.bend as PWaitEntryOpenRefused

def rs.shut(ins: List<&2, String>) -> {WaitLaws.ww_replies(ins, FWt.Shut{}) == WaitLaws.ww_copies(List.length(&2, String, ins), WaitLaws.ww_refused()) : List<&2, String>}:
  match ins:
    case Nil{}:
      {==}
    case i <> +rest:
      %rs.shut(rest) : {WaitLaws.ww_replies(i <> rest, FWt.Shut{}) == WaitLaws.ww_refused() <> _ : List<&2, String>}
      {==}

def WaitLaws.wait_entry_refused_stays(s, ins, bad):
  %Equal.sym(FWt.St & String, FWt.open(s), (FWt.Shut{}, WaitLaws.ww_bad_open()), WaitLaws.wait_entry_open_refused(s, bad)) : {WaitLaws.ww_replies(ins, WaitLaws.ww_state(_)) == WaitLaws.ww_copies(List.length(&2, String, ins), WaitLaws.ww_refused()) : List<&2, String>}
  rs.shut(ins)
