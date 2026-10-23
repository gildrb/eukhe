# eukhe: the proof of LAW tokens_space_ascends

import Base
import ../../bend/tokens.bend as Tk
import ../../LAWS.bend as Laws

def tokens_space_ascends() -> {Tk.ascends(Tk.space()) == True{} : Bool}:
  {==}

def Laws.tokens_space_ascends():
  tokens_space_ascends()
