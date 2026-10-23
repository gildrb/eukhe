# eukhe: the proof of LAW tokens_space_ascends

import Base
import ../../bend/tokens.bend as Tk
import ../../laws/tokens.bend as Tokens

def tokens_space_ascends() -> {Tk.ascends(Tk.space()) == True{} : Bool}:
  {==}

def Tokens.tokens_space_ascends():
  tokens_space_ascends()
