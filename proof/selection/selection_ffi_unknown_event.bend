# eukhe: the proof of LAW selection_ffi_unknown_event

import Base
import ../../bend/selection.bend as M
import ../../bend/ffi_selection.bend as F
import ../../bend/wire.bend as Wr
import ../../laws/selection.bend as Selection
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire
import ../wire/wire_nat_too_long.bend as PWireNatTooLong

# A tag that fits reads back and no input has it; a tag too long for the
# wire does not read at all (LAW wire_nat_too_long). Either way the input
# is malformed.

def sue.tag(b: Bool, s: M.St, +n: Nat, +rest: String, eb: {LawsBase.wire_fits(7n+n) == b : Bool}) -> {F.step(F.Live{s}, Wr.put_nat(7n+n, rest)) == (F.Live{s}, Wr.err("selection: malformed event")) : F.St & String}:
  match b:
    case True{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(7n+n, rest)), Wr.Got{7n+n, rest}, Wire.wire_nat_round_trip(7n+n, rest, eb)) : {F.step.ev(s, F.get_ev.go(_)) == (F.Live{s}, Wr.err("selection: malformed event")) : F.St & String}
      {==}
    case False{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(7n+n, rest)), Wr.Bad{}, Wire.wire_nat_too_long(7n+n, rest, eb)) : {F.step.ev(s, F.get_ev.go(_)) == (F.Live{s}, Wr.err("selection: malformed event")) : F.St & String}
      {==}

def Selection.selection_ffi_unknown_event(s, n, rest):
  sue.tag(LawsBase.wire_fits(7n+n), s, n, rest, {==})
