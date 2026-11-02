# eukhe: the proof of LAW wf_results_exact

import Base
import ../../laws/workflow.bend as Workflow
import ./base.bend as LA

def Workflow.wf_results_exact(o, os):
  (LA.pw.result(o), LA.pw.results(os))
