# eukhe: the proof of LAW child_repeat_is_no_work

import Base
import ../../laws/progress.bend as Progress
import ./base.bend as LA

# (H6, H7, M5, L5) Progress is new work; what the harness changes or drops is reported

def Progress.child_repeat_is_no_work(seen, loop, within):
  LA.pp.repeat(seen, loop, within)
