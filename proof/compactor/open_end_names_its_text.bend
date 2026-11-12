# eukhe: the proof of LAW open_end_names_its_text
# With no tries the line ends with its input cut; with some it asks.

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor

def Compactor.open_end_names_its_text(t, node, input):
  match t:
    case 0n:
      {==}
    case 1n+q:
      Unit{}
