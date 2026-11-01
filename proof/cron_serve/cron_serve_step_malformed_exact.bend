# eukhe: the proof of LAW cron_serve_step_malformed_exact
# The entry's step is ce_entry (LCE.pe.entry), which keeps the runs and
# answers the error form when the laws' reader finds no whole event.

import Base
import ../../bend/ffi_cron_serve.bend as FC
import ../../laws/cron_serve/entry.bend as CronServeEntry
import ./base/entry.bend as LCE

def CronServeEntry.cron_serve_step_malformed_exact(runs, s, no):
  Equal.trans(FC.St & String, FC.step(FC.Open{runs}, s), CronServeEntry.ce_entry.at(runs, CronServeEntry.ce_read_ev(s)), (FC.Open{runs}, CronServeEntry.ce_err_event()), LCE.pe.entry(FC.Open{runs}, s), LCE.pe.at_none(runs, CronServeEntry.ce_read_ev(s), no))
