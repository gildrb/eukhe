# eukhe: the proof of LAW cron_serve_open_refuses
# A nonempty open reads as not empty; the refused stepper answers alone.

import Base
import ../../bend/ffi_cron_serve.bend as FC
import ../../laws/cron_serve/entry.bend as CronServeEntry

def pfo.shut(+s: String, ne: {String.is_empty(s) == False{} : Bool}) -> {FC.open(s) == (FC.Shut{}, SCon{'E', SCon{' ', "cron_serve: malformed open"}}) : FC.St & String}:
  %Equal.sym(Bool, String.is_empty(s), False{}, ne) : {FC.open.fin(_) == (FC.Shut{}, SCon{'E', SCon{' ', "cron_serve: malformed open"}}) : FC.St & String}
  {==}

def CronServeEntry.cron_serve_open_refuses(s, ne, e):
  (pfo.shut(s, ne), {==})
