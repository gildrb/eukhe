# eukhe: the proof of LAW headless_exit_aborted_fails
#
# PROOF: above the transcript every cause has code 1 (hx.facts_fail, hx.run_fails), and the PAborted entry is a cause of its own, code 1.

import Base
import ../../bend/headless_exit.bend as Hx
import ../../laws/headless_exit.bend as HeadlessExit
import ./base.bend as LAHeadlessExit

def HeadlessExit.headless_exit_aborted_fails(cf, w, r, c, a, ba):
  LAHeadlessExit.hx.facts_fail(cf, w, r, Hx.PAborted{}, c, a, ba, LAHeadlessExit.hx.run_fails(r, Hx.PAborted{}, c, a, ba, {==}))
