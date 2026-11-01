# eukhe: the proof of LAW cron_serve_end_exact
# The end of a run is drop_str, which is the spec's sv_out.

import Base
import ../../laws/cron_serve/serve.bend as CronServe
import ./base/exact.bend as LSx

def CronServe.cron_serve_end_exact(d, runs):
  LSx.sx.out(d, runs)
