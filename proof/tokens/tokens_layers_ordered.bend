# eukhe: the proof of LAW tokens_layers_ordered

import Base
import ../../bend/tokens.bend as Tk
import ../../laws/tokens.bend as Tokens

# The scales
# ----------

def tokens_layers_ordered() -> {Tk.ascends(Tk.layers()) == True{} : Bool}:
  {==}

def Tokens.tokens_layers_ordered():
  tokens_layers_ordered()
