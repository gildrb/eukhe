# eukhe: the proof of LAW wf_cat_exact

import Base
import ../../laws/workflow/model.bend as Workflow
import ./base.bend as LA

def Workflow.wf_cat_exact(xs, ys, rs, ss):
  (LA.pw.cat(xs, ys), LA.pw.rcat(rs, ss))
