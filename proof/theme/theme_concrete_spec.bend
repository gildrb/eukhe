# eukhe: the proof of LAW theme_concrete_spec: one case per value

import Base
import ../../bend/theme/file.bend as TFile
import ../../laws/theme.bend as Theme

def Theme.theme_concrete_spec(v):
  match v:
    case TFile.Dflt{}:
      {==}
    case TFile.Idx{i}:
      {==}
    case TFile.Hex{c}:
      {==}
