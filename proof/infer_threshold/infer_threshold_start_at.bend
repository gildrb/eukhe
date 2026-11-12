# eukhe: the proof of LAW infer_threshold_start_at
# x - c <= t is x <= c + t, and the limit test at c + t is t + r + c > w
# (LAThreshold.gt.above_by).

import Base
import ../../laws/infer_threshold.bend as InferThreshold
import ./base.bend as LAThreshold

def InferThreshold.infer_threshold_start_at(w, r, c, t):
  LAThreshold.gt.above_by(w, r, c, t)
