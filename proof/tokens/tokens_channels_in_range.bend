# eukhe: the proof of LAW tokens_channels_in_range

import Base
import ../../bend/tokens.bend as Tk
import ../../laws/tokens.bend as Tokens

def Tokens.tokens_channels_in_range(m):
  match m:
    case Tk.Light{}:
      {==}
    case Tk.Dark{}:
      {==}
