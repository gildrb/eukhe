# eukhe: the proof of LAW cron_serve_step_answers
# Every event Rust writes reads back (LCE.pe.ev_rt); a whole event steps
# the runs as the spec (LCE.pe.step_reads).

import Base
import ../../bend/ffi_cron_serve.bend as FC
import ../../laws/cron_serve/entry.bend as CronServeEntry
import ./base/entry.bend as LCE

def CronServeEntry.cron_serve_step_answers(runs, e, fits):
  LCE.pe.step_reads(runs, CronServeEntry.ce_spell_ev(e), e, LCE.pe.ev_rt(e, fits))
