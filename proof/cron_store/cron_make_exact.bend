# eukhe: the proof of LAW cron_make_exact
# Both sides compute the same job.
import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../laws/cron_store.bend as CronStore

def CronStore.cron_make_exact(at):
  {==}
