# eukhe: the proof of LAW selection_ffi_left_over

import Base
import ../../bend/selection.bend as M
import ../../bend/ffi_selection.bend as F
import ../../bend/wire.bend as Wr
import ../../laws/selection.bend as Selection
import ./selection_ffi_decides.bend as PSelectionFfiDecides

# the input reads back (PSelectionFfiDecides.ent.ev) with rest left over;
# the end check is "rest is empty", False here
def Selection.selection_ffi_left_over(s, e, rest, h, more):
  %Equal.sym(Wr.Dec<M.Ev>, F.get_ev(Selection.sl_spell_ev(e, rest)), Wr.Got{e, rest}, PSelectionFfiDecides.ent.ev(e, rest, h)) : {F.step.ev(s, _) == (F.Live{s}, Wr.err("selection: input left over")) : F.St & String}
  %Equal.sym(Bool, String.is_empty(rest), False{}, more) : {F.step.end(_, s, e) == (F.Live{s}, Wr.err("selection: input left over")) : F.St & String}
  {==}
