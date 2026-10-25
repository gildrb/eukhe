# eukhe: the proof of LAW cron_entry_fits_example
# A claim's verdict carries no number: it fits.

import Base
import ../../bend/cron_store.bend as CS
import ../../laws/cron.bend as Cron

def Cron.cron_entry_fits_example():
  (CS.AskClear{CS.Mine{True{}}}, {==})
