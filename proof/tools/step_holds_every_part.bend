# eukhe: the proof of LAW step_holds_every_part

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

# (G2) Shell classification

def Laws.step_holds_every_part(pre, p, post, c, has):
  LA.ps.step_holds_every_part(pre, p, post, c, has)
