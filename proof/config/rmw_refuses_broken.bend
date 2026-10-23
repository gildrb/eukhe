# eukhe: the proof of LAW rmw_refuses_broken

import Base
import ../../bend/config.bend as Cf
import ../../LAWS.bend as Laws

# LAW rmw_refuses_broken
def pcf.rmw_refuses_broken(e: Cf.Edit) -> {Cf.rmw(Cf.Broken{}, e) == Cf.Refused{} : Cf.Write}:
  {==}

# (H1-H4, M3, M7) Config documents, trust and the saved default model

def Laws.rmw_refuses_broken(e):
  pcf.rmw_refuses_broken(e)
