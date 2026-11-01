# eukhe: the proof of LAW cron_serve_is_entry
# The entry reads every input as the laws' reader does, stage by stage,
# and writes the laws' spelling (LCE.pe.entry).

import Base
import ../../bend/ffi_cron_serve.bend as FC
import ../../laws/cron_serve/entry.bend as CronServeEntry
import ./base/entry.bend as LCE

def CronServeEntry.cron_serve_is_entry(st, s):
  LCE.pe.entry(st, s)
