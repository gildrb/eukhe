# eukhe: the proof of LAW cron_serve_step_reads
# The entry's step is ce_entry (LCE.pe.entry); on a whole event ce_entry
# runs the code, which is the spec (cron_serve_exact, cron_serve_end_exact).

import Base
import ../../bend/ffi_cron_serve.bend as FC
import ../../laws/cron_serve/entry.bend as CronServeEntry
import ./base/entry.bend as LCE

def CronServeEntry.cron_serve_step_reads(runs, s, e, got):
  LCE.pe.step_reads(runs, s, e, got)
