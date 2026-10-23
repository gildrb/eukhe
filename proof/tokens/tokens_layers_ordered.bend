# eukhe: the proof of LAW tokens_layers_ordered

import Base
import ../../bend/tokens.bend as Tk
import ../../LAWS.bend as Laws

# The scales
# ----------

def tokens_layers_ordered() -> {Tk.ascends(Tk.layers()) == True{} : Bool}:
  {==}

def Laws.tokens_layers_ordered():
  tokens_layers_ordered()
