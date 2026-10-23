# eukhe: the proof of LAW tokens_type_ascends

import Base
import ../../bend/tokens.bend as Tk
import ../../laws/tokens.bend as Tokens

def tokens_type_ascends() -> {Bool.and(Tk.ascends(Tk.sizes()), Tk.ascends(Tk.lines())) == True{} : Bool}:
  {==}

def Tokens.tokens_type_ascends():
  tokens_type_ascends()
