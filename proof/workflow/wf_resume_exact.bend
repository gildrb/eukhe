# eukhe: the proof of LAW wf_resume_exact

import Base
import ../../laws/workflow/model.bend as Workflow
import ./base.bend as LA

def Workflow.wf_resume_exact(k, cache, keys):
  (LA.pw.member(k, cache), (LA.pw.cost(k, cache), LA.pw.resumed(cache, keys)))
