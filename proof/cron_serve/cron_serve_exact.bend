# eukhe: the proof of LAW cron_serve_exact
# Part by part (proof/cron_serve/base/exact.bend): each walk over the
# records by induction, each per-job decision by its cron_store law.

import Base
import ../../laws/cron_serve/serve.bend as CronServe
import ./base/exact.bend as LSx

def CronServe.cron_serve_exact(runs, me, disk, op):
  LSx.sx.serve(runs, me, disk, op)
