# eukhe: the proof of LAW cron_serve_due_exact_input
# The call reads every input as the laws' reader does (LCE.pe.ask).

import Base
import ../../bend/ffi_cron_serve.bend as FC
import ../../laws/cron_serve/entry.bend as CronServeEntry
import ./base/entry.bend as LCE

def CronServeEntry.cron_serve_due_exact_input(s):
  LCE.pe.ask(s)
