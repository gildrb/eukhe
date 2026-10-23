# eukhe: the proof of LAW rec_redo_is_noted

import Base
import ../../bend/run.bend as Rn
import ../../LAWS.bend as Laws

def redo_is_noted(-pass: Rn.Reply) -> {Rn.Act.reply(Rn.Redo{}, pass) == Rn.Error{False{}, True{}} : Rn.Reply}:
  {==}

def Laws.rec_redo_is_noted(pass):
  redo_is_noted(pass)
