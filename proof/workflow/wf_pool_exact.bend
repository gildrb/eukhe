# eukhe: the proof of LAW wf_pool_exact

import Base
import ../../laws/workflow/model.bend as Workflow
import ./base.bend as LA

def Workflow.wf_pool_exact(cap, p):
  ({==}, LA.pw.size_exact(p))
