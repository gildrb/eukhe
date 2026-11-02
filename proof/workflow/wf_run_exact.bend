# eukhe: the proof of LAW wf_run_exact

import Base
import ../../laws/workflow.bend as Workflow
import ./base.bend as LA

def Workflow.wf_run_exact(es, p):
  LA.pw.run_exact(es, p)
