# eukhe: the proof of LAW theme_ffi_left_over
# The request reads back whole and leaves the input after it
# (LTTrip.tt.req); the entry's end check finds that input and refuses.

import Base
import ../../bend/ffi_theme.bend as FTh
import ../../spec/theme/read.bend as Tr
import ../../laws/theme.bend as Theme
import ./base/ffi_trip.bend as LTTrip

def Theme.theme_ffi_left_over(r, fits, c, x):
  %LTTrip.tt.req(r, SCon{c, x}, fits) : {FTh.run(_) == Tr.refused() : String}
  {==}
