# eukhe: the proof of LAW cron_serve_due_answers
# The call answers as the laws' reader reads (LCE.pe.ask), which reads back
# every question Rust writes (LCE.pe.ask_rt).

import Base
import ../../bend/ffi_cron_serve.bend as FC
import ../../laws/cron_serve/entry.bend as CronServeEntry
import ./base/entry.bend as LCE

def CronServeEntry.cron_serve_due_answers(now, f, fits):
  Equal.trans(String, FC.ffi(CronServeEntry.ce_spell_ask(now, f)), CronServeEntry.ce_ask(CronServeEntry.ce_read_ask(CronServeEntry.ce_spell_ask(now, f))), CronServeEntry.ce_due(now, f), LCE.pe.ask(CronServeEntry.ce_spell_ask(now, f)), LCE.pe.ask_rt(now, f, fits))
