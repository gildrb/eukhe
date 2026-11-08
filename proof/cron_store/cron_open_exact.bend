# eukhe: the proof of LAW cron_open_exact
# A case split on the Bool.
import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../laws/cron_store.bend as CronStore

def CronStore.cron_open_exact(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}
