# eukhe: the proof of LAW wf_step_exact

import Base
import ../../laws/workflow.bend as Workflow
import ./base.bend as LA

def Workflow.wf_step_exact(e, p):
  LA.pw.step_exact(e, p)
