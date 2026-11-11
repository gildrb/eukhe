# eukhe: the proof of LAW theme_parse_tokens: the palette of a file that
# reads is its values over the 59 tokens

import Base
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/palette.bend as TPalette
import ../../laws/theme.bend as Theme
import ./base/parse.bend as PP

def Theme.theme_parse_tokens(f, nm, cols, pg, cd, io, h):
  %Equal.sym(TPalette.Parsed, TPalette.parse(f), PP.pp.parsed(cols, pg, cd, io), PP.pp.painted(f, nm, cols, pg, cd, io, h)) : {List.length(&2, TFile.Val, Theme.th.vals(_)) == 59n : Nat}
  {==}
