# eukhe: the proof of LAW infer_threshold_limit_at
# (1 + w) - a <= t is 1 + w <= a + t, which is w < a + t; and 2 + a + w <= t
# is 1 + a + w < t (LAThreshold.gt.above).

import Base
import ../../laws/infer_threshold.bend as InferThreshold
import ./base.bend as LAThreshold

def InferThreshold.infer_threshold_limit_at(w, r, t):
  LAThreshold.gt.above(w, r, t)
