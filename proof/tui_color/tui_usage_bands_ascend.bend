# eukhe: the proof of LAW tui_usage_bands_ascend

import Base
import ../../bend/tui_color.bend as TC
import ../../laws/tui_color.bend as TuiColor

# The usage bands
# ---------------

def tui_usage_bands_ascend() -> {TC.ascend(TC.bands()) == True{} : Bool}:
  {==}

def TuiColor.tui_usage_bands_ascend():
  tui_usage_bands_ascend()
