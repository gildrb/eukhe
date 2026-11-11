# eukhe: the proof of LAW sweep_takes_leftover_sorts

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA
import ./sweep_reaches_every_depth.bend as PSweepReachesEveryDepth

def Staging.sweep_takes_leftover_sorts(pre, i, post):
  (Staging.sweep_reaches_every_depth(pre, i, Sg.Leftover{}, post, {==}), (Staging.sweep_reaches_every_depth(pre, i, Sg.Lock{False{}}, post, {==}), {==}))
