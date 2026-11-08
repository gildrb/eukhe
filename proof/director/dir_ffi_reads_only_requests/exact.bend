# eukhe: lemmas of LAW dir_ffi_reads_only_requests (and
# dir_ffi_malformed_unless_request): whatever the entry's decoder reads is
# the laws' spelling of what it read, then its rest, and fits the wire
#
# Each decoder of bend/ffi_director.bend answers Got{x, rest} only for the
# laws' spelling of x before rest, x within the wire (a predicate per
# decoder answer, carried stage by stage with wire_nat_exact and
# wire_nat_decoded_fits; an unknown tag is Bad). A list: its count, then
# as many spelled items (pdx.ls.loop, pdx.vs.loop, as dcw.strs.loop).

import Base
import ../../../bend/director.bend as Dr
import ../../../bend/ffi_director.bend as FDr
import ../../../bend/wire.bend as Wr
import ../../../laws/director.bend as Director
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/base/spell.bend as LAWireSpell

# s spelled up to a field a is s spelled up to its spelling b
def pdx.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# A layer
# -------

def pdx.LP(s: String, d: Wr.Dec<Dr.Layer>) -> Type:
  match d:
    case Wr.Got{l, r}:
      {s == Director.dir_spell_layer(l, r) : String} & {Director.dir_layer_fits(l) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def pdx.layer.b(-s: String, +k: Nat, +s1: String, pre: {s == Wr.put_nat(k, s1) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> pdx.LP(s, FDr.get_layer.b(k, d)):
  match d:
    case Wr.Got{+b, +r}:
      +e = ed
      (pdx.step(z => Wr.put_nat(k, z), s, s1, Wr.put_nat(b, r), pre, Wire.wire_nat_exact(s1, b, r, e)), LAWireSpell.ws_and_tt(LawsBase.wire_fits(k), LawsBase.wire_fits(b), fk, Wire.wire_nat_decoded_fits(s1, b, r, e)))
    case Wr.Bad{}:
      Unit{}

def pdx.layer.k(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> pdx.LP(s, FDr.get_layer.k(d)):
  match d:
    case Wr.Got{+k, +s1}:
      +e = ed
      pdx.layer.b(s, k, s1, Wire.wire_nat_exact(s, k, s1, e), Wire.wire_nat_decoded_fits(s, k, s1, e), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

# a layer decoded is spelled, and fits
def pdx.layer(+s: String) -> pdx.LP(s, FDr.get_layer(s)):
  pdx.layer.k(s, Wr.get_nat(s), {==})

# A stack
# -------

def pdx.ls.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Dr.Layer>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Director.dir_spell_layers.items(xs, r) : String} & ({List.length(&2, Dr.Layer, xs) == 1n+m : Nat} & {Director.dir_layers_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def pdx.ls.step(-s: String, +x: Dr.Layer, +s3: String, -k: Nat, ex: {s == Director.dir_spell_layer(x, s3) : String}, fx: {Director.dir_layer_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Dr.Layer>>, ih: pdx.ls.PL(s3, k, d)) -> pdx.ls.PL(s, 1n+k, Wr.get_list.cons(Dr.Layer, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (pdx.step(z => Director.dir_spell_layer(x, z), s, s3, Director.dir_spell_layers.items(ys, r), ex, e1), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Dr.Layer, ys), 1n+k, e2), LAWireSpell.ws_and_tt(Director.dir_layer_fits(x), Director.dir_layers_fit(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

def pdx.ls.loop(m: Nat, cur: Wr.Dec<Dr.Layer>, +s: String, pc: pdx.LP(s, cur)) -> pdx.ls.PL(s, m, Wr.get_list.go(~Dr.Layer, ~FDr.get_layer, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LAWireSpell.ws_and_tt(Director.dir_layer_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      pdx.ls.step(s, x, s3, k, e, f, Wr.get_list.go(~Dr.Layer, ~FDr.get_layer, k, FDr.get_layer(s3)), pdx.ls.loop(k, FDr.get_layer(s3), s3, pdx.layer(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def pdx.ls.LS(s: String, d: Wr.Dec<List<&2, Dr.Layer>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Director.dir_spell_layers(xs, r) : String} & ({LawsBase.wire_fits(List.length(&2, Dr.Layer, xs)) == True{} : Bool} & {Director.dir_layers_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def pdx.ls.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Dr.Layer>>, pl: pdx.ls.PL(s2, m, d)) -> pdx.ls.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      +e2s = Equal.sym(Nat, List.length(&2, Dr.Layer, xs), 1n+m, e2)
      +es = pdx.step(z => Wr.put_nat(1n+m, z), s, s2, Director.dir_spell_layers.items(xs, r), en, e1)
      %e2s : {s == Wr.put_nat(_, Director.dir_spell_layers.items(xs, r)) : String} & ({LawsBase.wire_fits(_) == True{} : Bool} & {Director.dir_layers_fit(xs) == True{} : Bool})
      (es, (fn, e3))
    case Wr.Bad{}:
      Unit{}

def pdx.ls.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> pdx.ls.LS(s, Wr.get_list.start(~Dr.Layer, ~FDr.get_layer, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, (fn, {==}))
    case 1n++m:
      pdx.ls.conv(s, s2, m, en, fn, Wr.get_list.go(~Dr.Layer, ~FDr.get_layer, m, FDr.get_layer(s2)), pdx.ls.loop(m, FDr.get_layer(s2), s2, pdx.layer(s2)))

def pdx.ls.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> pdx.ls.LS(s, Wr.get_list.start(~Dr.Layer, ~FDr.get_layer, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      pdx.ls.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a stack decoded is spelled, and its count and every layer fit
def pdx.ls.list(+s: String) -> pdx.ls.LS(s, Wr.get_list(~Dr.Layer, ~FDr.get_layer, s)):
  pdx.ls.top(s, Wr.get_nat(s), {==})

# A verdict
# ---------

def pdx.VP(s: String, d: Wr.Dec<Dr.Verdict>) -> Type:
  match d:
    case Wr.Got{v, r}:
      {s == Director.dir_spell_verdict(v, r) : String} & {Director.dir_verdict_fits(v) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def pdx.verdict.stack(-s: String, -s1: String, pre: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<Dr.Layer>, lp: pdx.LP(s1, d)) -> pdx.VP(s, FDr.get_verdict.stack(d)):
  match d:
    case Wr.Got{+l, +r}:
      (e, f) = lp
      (pdx.step(z => Wr.put_nat(3n, z), s, s1, Director.dir_spell_layer(l, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def pdx.verdict.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> pdx.VP(s, FDr.get_verdict.tag(t, s1)):
  match t:
    case 0n:
      (pre, {==})
    case 1n:
      (pre, {==})
    case 2n:
      (pre, {==})
    case 3n:
      pdx.verdict.stack(s, s1, pre, FDr.get_layer(s1), pdx.layer(s1))
    case 4n:
      (pre, {==})
    case 5n:
      (pre, {==})
    case 6n:
      (pre, {==})
    case 7n+x:
      Unit{}

def pdx.verdict.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> pdx.VP(s, FDr.get_verdict.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      pdx.verdict.tag(t, s1, s, Wire.wire_nat_exact(s, t, s1, ed))
    case Wr.Bad{}:
      Unit{}

# a verdict decoded is spelled, and fits
def pdx.verdict(+s: String) -> pdx.VP(s, FDr.get_verdict(s)):
  pdx.verdict.go(s, Wr.get_nat(s), {==})

# The verdicts
# ------------

def pdx.vs.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Dr.Verdict>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Director.dir_spell_verdicts.items(xs, r) : String} & ({List.length(&2, Dr.Verdict, xs) == 1n+m : Nat} & {Director.dir_verdicts_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def pdx.vs.step(-s: String, +x: Dr.Verdict, +s3: String, -k: Nat, ex: {s == Director.dir_spell_verdict(x, s3) : String}, fx: {Director.dir_verdict_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Dr.Verdict>>, ih: pdx.vs.PL(s3, k, d)) -> pdx.vs.PL(s, 1n+k, Wr.get_list.cons(Dr.Verdict, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (pdx.step(z => Director.dir_spell_verdict(x, z), s, s3, Director.dir_spell_verdicts.items(ys, r), ex, e1), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Dr.Verdict, ys), 1n+k, e2), LAWireSpell.ws_and_tt(Director.dir_verdict_fits(x), Director.dir_verdicts_fit(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

def pdx.vs.loop(m: Nat, cur: Wr.Dec<Dr.Verdict>, +s: String, pc: pdx.VP(s, cur)) -> pdx.vs.PL(s, m, Wr.get_list.go(~Dr.Verdict, ~FDr.get_verdict, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LAWireSpell.ws_and_tt(Director.dir_verdict_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      pdx.vs.step(s, x, s3, k, e, f, Wr.get_list.go(~Dr.Verdict, ~FDr.get_verdict, k, FDr.get_verdict(s3)), pdx.vs.loop(k, FDr.get_verdict(s3), s3, pdx.verdict(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def pdx.vs.LS(s: String, d: Wr.Dec<List<&2, Dr.Verdict>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Director.dir_spell_verdicts(xs, r) : String} & ({LawsBase.wire_fits(List.length(&2, Dr.Verdict, xs)) == True{} : Bool} & {Director.dir_verdicts_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def pdx.vs.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Dr.Verdict>>, pl: pdx.vs.PL(s2, m, d)) -> pdx.vs.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      +e2s = Equal.sym(Nat, List.length(&2, Dr.Verdict, xs), 1n+m, e2)
      +es = pdx.step(z => Wr.put_nat(1n+m, z), s, s2, Director.dir_spell_verdicts.items(xs, r), en, e1)
      %e2s : {s == Wr.put_nat(_, Director.dir_spell_verdicts.items(xs, r)) : String} & ({LawsBase.wire_fits(_) == True{} : Bool} & {Director.dir_verdicts_fit(xs) == True{} : Bool})
      (es, (fn, e3))
    case Wr.Bad{}:
      Unit{}

def pdx.vs.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> pdx.vs.LS(s, Wr.get_list.start(~Dr.Verdict, ~FDr.get_verdict, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, (fn, {==}))
    case 1n++m:
      pdx.vs.conv(s, s2, m, en, fn, Wr.get_list.go(~Dr.Verdict, ~FDr.get_verdict, m, FDr.get_verdict(s2)), pdx.vs.loop(m, FDr.get_verdict(s2), s2, pdx.verdict(s2)))

def pdx.vs.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> pdx.vs.LS(s, Wr.get_list.start(~Dr.Verdict, ~FDr.get_verdict, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      pdx.vs.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a list of verdicts decoded is spelled, and its count and every verdict
# fit
def pdx.vs.list(+s: String) -> pdx.vs.LS(s, Wr.get_list(~Dr.Verdict, ~FDr.get_verdict, s)):
  pdx.vs.top(s, Wr.get_nat(s), {==})

# The end of a loop
# -----------------

def pdx.EP(s: String, d: Wr.Dec<Maybe<&2, Dr.Out>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == Director.dir_spell_end(m, r) : String}
    case Wr.Bad{}:
      Unit

def pdx.end.out(t: Nat, +s2: String, -s: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(t, s2)) : String}) -> pdx.EP(s, FDr.get_end.out(t, s2)):
  match t:
    case 0n:
      pre
    case 1n:
      pre
    case 2n:
      pre
    case 3n+x:
      Unit{}

def pdx.end.some(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> pdx.EP(s, FDr.get_end.some(d)):
  match d:
    case Wr.Got{+t, +s2}:
      pdx.end.out(t, s2, s, pdx.step(z => Wr.put_nat(1n, z), s, s1, Wr.put_nat(t, s2), pre, Wire.wire_nat_exact(s1, t, s2, ed)))
    case Wr.Bad{}:
      Unit{}

def pdx.end.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> pdx.EP(s, FDr.get_end.tag(t, s1)):
  match t:
    case 0n:
      pre
    case 1n:
      pdx.end.some(s, s1, pre, Wr.get_nat(s1), {==})
    case 2n+x:
      Unit{}

def pdx.end.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> pdx.EP(s, FDr.get_end.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      pdx.end.tag(t, s1, s, Wire.wire_nat_exact(s, t, s1, ed))
    case Wr.Bad{}:
      Unit{}

# an end decoded is spelled
def pdx.end(+s: String) -> pdx.EP(s, FDr.get_end(s)):
  pdx.end.go(s, Wr.get_nat(s), {==})

# The loop
# --------

def pdx.LoopP(s: String, d: Wr.Dec<Dr.Loop>) -> Type:
  match d:
    case Wr.Got{l, r}:
      {s == Director.dir_spell_loop(l, r) : String} & {Director.dir_loop_fits(l) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def pdx.loop.end(-s: String, +n: Nat, +st: List<&2, Dr.Layer>, -s2: String, pre: {s == Wr.put_nat(n, Director.dir_spell_layers(st, s2)) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, fc: {LawsBase.wire_fits(List.length(&2, Dr.Layer, st)) == True{} : Bool}, fi: {Director.dir_layers_fit(st) == True{} : Bool}, d: Wr.Dec<Maybe<&2, Dr.Out>>, ep: pdx.EP(s2, d)) -> pdx.LoopP(s, FDr.get_loop.end(n, st, d)):
  match d:
    case Wr.Got{+e, +s3}:
      (pdx.step(z => Wr.put_nat(n, Director.dir_spell_layers(st, z)), s, s2, Director.dir_spell_end(e, s3), pre, ep), LAWireSpell.ws_and_tt(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(List.length(&2, Dr.Layer, st)), Director.dir_layers_fit(st)), fn, LAWireSpell.ws_and_tt(LawsBase.wire_fits(List.length(&2, Dr.Layer, st)), Director.dir_layers_fit(st), fc, fi)))
    case Wr.Bad{}:
      Unit{}

def pdx.loop.stack(-s: String, +n: Nat, -s1: String, pre: {s == Wr.put_nat(n, s1) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<List<&2, Dr.Layer>>, ls: pdx.ls.LS(s1, d)) -> pdx.LoopP(s, FDr.get_loop.stack(n, d)):
  match d:
    case Wr.Got{+st, +s2}:
      (e, g) = ls
      (fc, fi) = g
      pdx.loop.end(s, n, st, s2, pdx.step(z => Wr.put_nat(n, z), s, s1, Director.dir_spell_layers(st, s2), pre, e), fn, fc, fi, FDr.get_end(s2), pdx.end(s2))
    case Wr.Bad{}:
      Unit{}

def pdx.loop.left(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> pdx.LoopP(s, FDr.get_loop.left(d)):
  match d:
    case Wr.Got{+n, +s1}:
      +e = ed
      pdx.loop.stack(s, n, s1, Wire.wire_nat_exact(s, n, s1, e), Wire.wire_nat_decoded_fits(s, n, s1, e), Wr.get_list(~Dr.Layer, ~FDr.get_layer, s1), pdx.ls.list(s1))
    case Wr.Bad{}:
      Unit{}

# a loop decoded is spelled, and fits
def pdx.loop(+s: String) -> pdx.LoopP(s, FDr.get_loop(s)):
  pdx.loop.left(s, Wr.get_nat(s), {==})

# The request
# -----------

def pdx.RP(s: String, d: Wr.Dec<FDr.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == Director.dir_spell_req(q, r) : String} & {Director.dir_req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def pdx.req.vs(-s: String, +c: Nat, +l: Dr.Loop, -s2: String, pre: {s == Wr.put_nat(c, Director.dir_spell_loop(l, s2)) : String}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, fl: {Director.dir_loop_fits(l) == True{} : Bool}, d: Wr.Dec<List<&2, Dr.Verdict>>, ls: pdx.vs.LS(s2, d)) -> pdx.RP(s, FDr.get_req.vs(c, l, d)):
  match d:
    case Wr.Got{+vs, +s3}:
      (e, g) = ls
      (fn, fi) = g
      (pdx.step(z => Wr.put_nat(c, Director.dir_spell_loop(l, z)), s, s2, Director.dir_spell_verdicts(vs, s3), pre, e), LAWireSpell.ws_and_tt(LawsBase.wire_fits(c), Bool.and(Director.dir_loop_fits(l), Bool.and(LawsBase.wire_fits(List.length(&2, Dr.Verdict, vs)), Director.dir_verdicts_fit(vs))), fc, LAWireSpell.ws_and_tt(Director.dir_loop_fits(l), Bool.and(LawsBase.wire_fits(List.length(&2, Dr.Verdict, vs)), Director.dir_verdicts_fit(vs)), fl, LAWireSpell.ws_and_tt(LawsBase.wire_fits(List.length(&2, Dr.Verdict, vs)), Director.dir_verdicts_fit(vs), fn, fi))))
    case Wr.Bad{}:
      Unit{}

def pdx.req.loop(-s: String, +c: Nat, -s1: String, pre: {s == Wr.put_nat(c, s1) : String}, fc: {LawsBase.wire_fits(c) == True{} : Bool}, d: Wr.Dec<Dr.Loop>, lp: pdx.LoopP(s1, d)) -> pdx.RP(s, FDr.get_req.loop(c, d)):
  match d:
    case Wr.Got{+l, +s2}:
      (e, fl) = lp
      pdx.req.vs(s, c, l, s2, pdx.step(z => Wr.put_nat(c, z), s, s1, Director.dir_spell_loop(l, s2), pre, e), fc, fl, Wr.get_list(~Dr.Verdict, ~FDr.get_verdict, s2), pdx.vs.list(s2))
    case Wr.Bad{}:
      Unit{}

def pdx.req.cap(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> pdx.RP(s, FDr.get_req.cap(d)):
  match d:
    case Wr.Got{+c, +s1}:
      +e = ed
      pdx.req.loop(s, c, s1, Wire.wire_nat_exact(s, c, s1, e), Wire.wire_nat_decoded_fits(s, c, s1, e), FDr.get_loop(s1), pdx.loop(s1))
    case Wr.Bad{}:
      Unit{}

# whatever the entry's decoder reads is a spelled request that fits, then
# the rest
def pdx.req(+s: String) -> pdx.RP(s, FDr.get_req(s)):
  pdx.req.cap(s, Wr.get_nat(s), {==})
