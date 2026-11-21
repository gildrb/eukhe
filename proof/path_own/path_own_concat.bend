# eukhe: the proof of LAW path_own_concat
#
# PROOF: the first naming rule of xs then ys is the one of xs, else the
# one of ys counted past xs (LA.po.first_app); counting ys from the number
# of rules of xs moves each place that far (LA.po.first_shift); the
# answers then join as the spec joins them (LA.po.then_of).

import Base
import ../../bend/path_own.bend as Po
import ../../laws/path_own.bend as PathOwn
import ./base.bend as LA

def PathOwn.path_own_concat(xs, ys, at, c):
  +n = List.length(&2, Po.Rule, xs)
  +a = Po.first(xs, at, 0n)
  +b = Po.first(ys, at, 0n)
  %Equal.sym(Maybe<&2, Nat>, Po.first(List.append(&2, Po.Rule, xs, ys), at, 0n), LA.po.fthen(a, Po.first(ys, at, Nat.add(n, 0n))), LA.po.first_app(xs, ys, at, 0n)) : {Po.of(_, c) == PathOwn.po_then(Po.of(a, c), n, Po.of(b, c)) : Po.Wc}
  %Equal.sym(Maybe<&2, Nat>, Po.first(ys, at, Nat.add(n, 0n)), LA.po.mshift(n, b), LA.po.first_shift(ys, at, n, 0n)) : {Po.of(LA.po.fthen(a, _), c) == PathOwn.po_then(Po.of(a, c), n, Po.of(b, c)) : Po.Wc}
  LA.po.then_of(a, n, b, c)
