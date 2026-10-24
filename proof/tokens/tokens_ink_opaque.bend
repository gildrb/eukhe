# eukhe: the proof of LAW tokens_ink_opaque

import Base
import ../../bend/tokens.bend as Tk
import ../../laws/tokens.bend as Tokens

def Tokens.tokens_ink_opaque(m):
  match m:
    case Tk.Light{}:
      {==}
    case Tk.Dark{}:
      {==}
