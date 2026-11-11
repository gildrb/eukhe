# eukhe: the proof of LAW wf_spawns_exact

import Base
import ../../laws/workflow/model.bend as Workflow
import ./base.bend as LA

def Workflow.wf_spawns_exact(n, p):
  LA.pw.spawns_exact(n, p)
