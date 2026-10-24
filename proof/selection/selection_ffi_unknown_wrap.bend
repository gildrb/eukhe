# eukhe: the proof of LAW selection_ffi_unknown_wrap

import Base
import ../../bend/selection.bend as M
import ../../bend/ffi_selection.bend as F
import ../../bend/wire.bend as Wr
import ../../laws/selection.bend as Selection
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire
import ../wire/wire_nat_too_long.bend as PWireNatTooLong

# The release tag reads back; the row count either reads back or is too
# long (malformed at once); the first row's wrap tag either reads back as
# no wrap or is too long; a bad first row makes the row list bad, however
# many rows it promised.

def suw.wrap(b: Bool, +n: Nat, +rest: String, eb: {LawsBase.wire_fits(3n+n) == b : Bool}) -> {F.get_row(Wr.put_nat(3n+n, rest)) == Wr.Bad{} : Wr.Dec<M.Row>}:
  match b:
    case True{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(3n+n, rest)), Wr.Got{3n+n, rest}, Wire.wire_nat_round_trip(3n+n, rest, eb)) : {F.get_row.wrap(F.get_wrap.go(_)) == Wr.Bad{} : Wr.Dec<M.Row>}
      {==}
    case False{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(3n+n, rest)), Wr.Bad{}, Wire.wire_nat_too_long(3n+n, rest, eb)) : {F.get_row.wrap(F.get_wrap.go(_)) == Wr.Bad{} : Wr.Dec<M.Row>}
      {==}

def suw.go(k: Nat, +n: Nat, +rest: String) -> {Wr.get_list.go(~M.Row, ~F.get_row, k, F.get_row(Wr.put_nat(3n+n, rest))) == Wr.Bad{} : Wr.Dec<List<&2, M.Row>>}:
  match k:
    case 0n:
      %Equal.sym(Wr.Dec<M.Row>, F.get_row(Wr.put_nat(3n+n, rest)), Wr.Bad{}, suw.wrap(LawsBase.wire_fits(3n+n), n, rest, {==})) : {Wr.get_list.go(~M.Row, ~F.get_row, 0n, _) == Wr.Bad{} : Wr.Dec<List<&2, M.Row>>}
      {==}
    case 1n+m:
      %Equal.sym(Wr.Dec<M.Row>, F.get_row(Wr.put_nat(3n+n, rest)), Wr.Bad{}, suw.wrap(LawsBase.wire_fits(3n+n), n, rest, {==})) : {Wr.get_list.go(~M.Row, ~F.get_row, 1n+m, _) == Wr.Bad{} : Wr.Dec<List<&2, M.Row>>}
      {==}

def suw.count(b: Bool, s: M.St, +k: Nat, +n: Nat, +rest: String, eb: {LawsBase.wire_fits(1n+k) == b : Bool}) -> {F.step(F.Live{s}, Wr.put_nat(2n, Wr.put_nat(1n+k, Wr.put_nat(3n+n, rest)))) == (F.Live{s}, Wr.err("selection: malformed event")) : F.St & String}:
  match b:
    case True{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n, Wr.put_nat(1n+k, Wr.put_nat(3n+n, rest)))), Wr.Got{2n, Wr.put_nat(1n+k, Wr.put_nat(3n+n, rest))}, Wire.wire_nat_round_trip(2n, Wr.put_nat(1n+k, Wr.put_nat(3n+n, rest)), {==})) : {F.step.ev(s, F.get_ev.go(_)) == (F.Live{s}, Wr.err("selection: malformed event")) : F.St & String}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n+k, Wr.put_nat(3n+n, rest))), Wr.Got{1n+k, Wr.put_nat(3n+n, rest)}, Wire.wire_nat_round_trip(1n+k, Wr.put_nat(3n+n, rest), eb)) : {F.step.ev(s, F.get_ev.rows(Wr.get_list.start(~M.Row, ~F.get_row, _))) == (F.Live{s}, Wr.err("selection: malformed event")) : F.St & String}
      %Equal.sym(Wr.Dec<List<&2, M.Row>>, Wr.get_list.go(~M.Row, ~F.get_row, k, F.get_row(Wr.put_nat(3n+n, rest))), Wr.Bad{}, suw.go(k, n, rest)) : {F.step.ev(s, F.get_ev.rows(_)) == (F.Live{s}, Wr.err("selection: malformed event")) : F.St & String}
      {==}
    case False{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n, Wr.put_nat(1n+k, Wr.put_nat(3n+n, rest)))), Wr.Got{2n, Wr.put_nat(1n+k, Wr.put_nat(3n+n, rest))}, Wire.wire_nat_round_trip(2n, Wr.put_nat(1n+k, Wr.put_nat(3n+n, rest)), {==})) : {F.step.ev(s, F.get_ev.go(_)) == (F.Live{s}, Wr.err("selection: malformed event")) : F.St & String}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n+k, Wr.put_nat(3n+n, rest))), Wr.Bad{}, Wire.wire_nat_too_long(1n+k, Wr.put_nat(3n+n, rest), eb)) : {F.step.ev(s, F.get_ev.rows(Wr.get_list.start(~M.Row, ~F.get_row, _))) == (F.Live{s}, Wr.err("selection: malformed event")) : F.St & String}
      {==}

def Selection.selection_ffi_unknown_wrap(s, k, n, rest):
  suw.count(LawsBase.wire_fits(1n+k), s, k, n, rest, {==})
