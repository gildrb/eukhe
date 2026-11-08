# eukhe: the entry's decoders read only spelled values
#
# Whatever a decoder of bend/ffi_infer.bend reads is the laws' spelling
# (laws/infer.bend core_infer_spell_*) of what it read, then its rest, and
# every number fits: a Nat by wire_nat_exact and wire_nat_decoded_fits, the
# cap by its tag (an unknown tag is Bad), a tool field by field, a list by
# its count and item by item, the request stage by stage along the entry's
# seq, the equation of the input so far carried in a predicate per stage.

import Base
import ../../../bend/ffi_infer.bend as FIn
import ../../../bend/infer.bend as If
import ../../../bend/wire.bend as Wr
import ../../../laws/infer.bend as Infer
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/base/spell.bend as LAWireSpell

# s spelled up to a field a is s spelled up to its spelling b
def ix.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# and(and(a, b), c) holds: and(a, and(b, c)) holds
def ix.assoc(a: Bool, -b: Bool, -c: Bool, h: {Bool.and(Bool.and(a, b), c) == True{} : Bool}) -> {Bool.and(a, Bool.and(b, c)) == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      h

# A Nat, the cap
# --------------

def ix.Nat(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ix.nat.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> ix.Nat(s, d):
  match d:
    case Wr.Got{+n, +r}:
      +e = ed
      (Wire.wire_nat_exact(s, n, r, e), Wire.wire_nat_decoded_fits(s, n, r, e))
    case Wr.Bad{}:
      Unit{}

def ix.nat(+s: String) -> ix.Nat(s, Wr.get_nat(s)):
  ix.nat.go(s, Wr.get_nat(s), {==})

def ix.MNat(s: String, d: Wr.Dec<Maybe<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == Infer.core_infer_spell_mnat(m, r) : String} & {LawsBase.core_mfits(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ix.mnat.some(-s: String, -s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Nat>, inv: ix.Nat(s0, d)) -> ix.MNat(s, FIn.get_mnat.some(d)):
  match d:
    case Wr.Got{+n, +r}:
      (e1, fn) = inv
      (ix.step(z => Wr.put_nat(1n, z), s, s0, Wr.put_nat(n, r), pre, e1), fn)
    case Wr.Bad{}:
      Unit{}

def ix.mnat.tag(-s: String, t: Nat, +s0: String, en: {s == Wr.put_nat(t, s0) : String}) -> ix.MNat(s, FIn.get_mnat.tag(t, s0)):
  match t:
    case 0n:
      (en, {==})
    case 1n:
      ix.mnat.some(s, s0, en, Wr.get_nat(s0), ix.nat(s0))
    case 2n+k:
      Unit{}

def ix.mnat.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> ix.MNat(s, FIn.get_mnat.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      ix.mnat.tag(s, t, s0, Wire.wire_nat_exact(s, t, s0, ed))
    case Wr.Bad{}:
      Unit{}

def ix.mnat(+s: String) -> ix.MNat(s, FIn.get_mnat(s)):
  ix.mnat.go(s, Wr.get_nat(s), {==})

# A tool: its id, then its priority
# ---------------------------------

def ix.t2(q: FIn.P2<Nat, Nat>, r: String) -> String:
  match q:
    case FIn.P2{a, b}:
      Wr.put_nat(a, Wr.put_nat(b, r))

def ix.tg2(q: FIn.P2<Nat, Nat>) -> Bool:
  match q:
    case FIn.P2{a, b}:
      Bool.and(LawsBase.wire_fits(a), LawsBase.wire_fits(b))

def ix.T2(s: String, d: Wr.Dec<FIn.P2<Nat, Nat>>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ix.t2(q, r) : String} & {ix.tg2(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ix.tf2(-s: String, +a: Nat, -r: String, pre: {s == Wr.put_nat(a, r) : String}, fa: {LawsBase.wire_fits(a) == True{} : Bool}, e: Wr.Dec<Nat>, inv: ix.Nat(r, e)) -> ix.T2(s, FIn.seq.fin(~Nat, ~Nat, a, e)):
  match e:
    case Wr.Got{+b, +r2}:
      (e1, fb) = inv
      (ix.step(z => Wr.put_nat(a, z), s, r, Wr.put_nat(b, r2), pre, e1), LAWireSpell.ws_and_tt(LawsBase.wire_fits(a), LawsBase.wire_fits(b), fa, fb))
    case Wr.Bad{}:
      Unit{}

def ix.ts2(-s: String, d: Wr.Dec<Nat>, inv: ix.Nat(s, d)) -> ix.T2(s, FIn.seq(~Nat, ~Nat, ~Wr.get_nat, d)):
  match d:
    case Wr.Got{+a, +r}:
      (pre, fa) = inv
      ix.tf2(s, a, r, pre, fa, Wr.get_nat(r), ix.nat(r))
    case Wr.Bad{}:
      Unit{}

def ix.Tool(s: String, d: Wr.Dec<If.Tool>) -> Type:
  match d:
    case Wr.Got{t, r}:
      {s == Infer.core_infer_spell_tool(t, r) : String} & {Infer.core_tool_fits(t) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ix.tool.of(-s: String, d: Wr.Dec<FIn.P2<Nat, Nat>>, inv: ix.T2(s, d)) -> ix.Tool(s, FIn.get_tool.of(d)):
  match d:
    case Wr.Got{q, r}:
      match q:
        case FIn.P2{i, p}:
          inv
    case Wr.Bad{}:
      Unit{}

def ix.tool(+s: String) -> ix.Tool(s, FIn.get_tool(s)):
  +d1 = Wr.get_nat(s)
  ix.tool.of(s, FIn.seq(~Nat, ~Nat, ~Wr.get_nat, d1), ix.ts2(s, d1, ix.nat(s)))

# A list of tools: its count, then tool by tool
# ---------------------------------------------

# what the item loop's answer says about its input s (m + 1 tools)
def ix.Ttl(s: String, m: Nat, d: Wr.Dec<List<&2, If.Tool>>) -> Type:
  match d:
    case Wr.Got{t, r}:
      {s == Infer.core_infer_spell_tools.items(t, r) : String} & ({List.length(&2, If.Tool, t) == 1n+m : Nat} & {Infer.core_tools_fit(t) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def ix.ttl.at(+s: String, -d: Wr.Dec<If.Tool>, er: {FIn.get_tool(s) == d : Wr.Dec<If.Tool>}) -> ix.Tool(s, d):
  %er : ix.Tool(s, _)
  ix.tool(s)

def ix.ttl.one(-s: String, +x: If.Tool, -s3: String, ex: ix.Tool(s, Wr.Got{x, s3})) -> ix.Ttl(s, 0n, Wr.Got{[x], s3}):
  (ea, eb) = ex
  (ea, ({==}, LAWireSpell.ws_and_tt(Infer.core_tool_fits(x), True{}, eb, {==})))

def ix.ttl.step(-s: String, +x: If.Tool, +s3: String, -k: Nat, ea: {s == Infer.core_infer_spell_tool(x, s3) : String}, eb: {Infer.core_tool_fits(x) == True{} : Bool},
  d: Wr.Dec<List<&2, If.Tool>>, ih: ix.Ttl(s3, k, d)) -> ix.Ttl(s, 1n+k, Wr.get_list.cons(If.Tool, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, ee) = ih
      (e2, e3) = ee
      (ix.step(z => Infer.core_infer_spell_tool(x, z), s, s3, Infer.core_infer_spell_tools.items(ys, r), ea, e1),
        (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, If.Tool, ys), 1n+k, e2),
          LAWireSpell.ws_and_tt(Infer.core_tool_fits(x), Infer.core_tools_fit(ys), eb, e3)))
    case Wr.Bad{}:
      Unit{}

def ix.ttl.step2(-s: String, +x: If.Tool, +s3: String, -k: Nat, ex: ix.Tool(s, Wr.Got{x, s3}),
  d: Wr.Dec<List<&2, If.Tool>>, ih: ix.Ttl(s3, k, d)) -> ix.Ttl(s, 1n+k, Wr.get_list.cons(If.Tool, x, d)):
  (ea, eb) = ex
  ix.ttl.step(s, x, s3, k, ea, eb, d, ih)

# the item loop accepts only spelled tools that fit
def ix.ttl(m: Nat, cur: Wr.Dec<If.Tool>, +s: String, er: {FIn.get_tool(s) == cur : Wr.Dec<If.Tool>}) ->
  ix.Ttl(s, m, Wr.get_list.go(~If.Tool, ~FIn.get_tool, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      ix.ttl.one(s, x, s3, ix.ttl.at(s, Wr.Got{x, s3}, er))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      ix.ttl.step2(s, x, s3, k, ix.ttl.at(s, Wr.Got{x, s3}, er),
        Wr.get_list.go(~If.Tool, ~FIn.get_tool, k, FIn.get_tool(s3)), ix.ttl(k, FIn.get_tool(s3), s3, {==}))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a tool list decoder's answer says about its input s
def ix.Tools(s: String, d: Wr.Dec<List<&2, If.Tool>>) -> Type:
  match d:
    case Wr.Got{t, r}:
      {s == Infer.core_infer_spell_tools(t, r) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, If.Tool, t)), Infer.core_tools_fit(t)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ix.tools.eq(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, +t: List<&2, If.Tool>, -r: String,
  e1: {s2 == Infer.core_infer_spell_tools.items(t, r) : String}, e2: {List.length(&2, If.Tool, t) == 1n+m : Nat}) -> {s == Infer.core_infer_spell_tools(t, r) : String}:
  %Equal.sym(Nat, List.length(&2, If.Tool, t), 1n+m, e2) : {s == Wr.put_nat(_, Infer.core_infer_spell_tools.items(t, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def ix.tools.fit(-m: Nat, hn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, +t: List<&2, If.Tool>,
  e2: {List.length(&2, If.Tool, t) == 1n+m : Nat}, e3: {Infer.core_tools_fit(t) == True{} : Bool}) -> {Bool.and(LawsBase.wire_fits(List.length(&2, If.Tool, t)), Infer.core_tools_fit(t)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, If.Tool, t), 1n+m, e2) : {Bool.and(LawsBase.wire_fits(_), Infer.core_tools_fit(t)) == True{} : Bool}
  LAWireSpell.ws_and_tt(LawsBase.wire_fits(1n+m), Infer.core_tools_fit(t), hn, e3)

def ix.tools.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, hn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  d: Wr.Dec<List<&2, If.Tool>>, tl: ix.Ttl(s2, m, d)) -> ix.Tools(s, d):
  match d:
    case Wr.Got{+t, +r}:
      (e1, ee) = tl
      (e2, e3) = ee
      +e4 = e2
      (ix.tools.eq(s, s2, m, en, t, r, e1, e4), ix.tools.fit(m, hn, t, e4, e3))
    case Wr.Bad{}:
      Unit{}

def ix.tools.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, hn: {LawsBase.wire_fits(n) == True{} : Bool}) ->
  ix.Tools(s, Wr.get_list.start(~If.Tool, ~FIn.get_tool, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      ix.tools.conv(s, s2, m, en, hn, Wr.get_list.go(~If.Tool, ~FIn.get_tool, m, FIn.get_tool(s2)), ix.ttl(m, FIn.get_tool(s2), s2, {==}))

def ix.tools.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) ->
  ix.Tools(s, Wr.get_list.start(~If.Tool, ~FIn.get_tool, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e2 = ed
      ix.tools.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e2), Wire.wire_nat_decoded_fits(s, n, s2, e2))
    case Wr.Bad{}:
      Unit{}

# every list of tools the decoder reads is spelled, its numbers fit
def ix.tools(+s: String) -> ix.Tools(s, FIn.get_tools(s)):
  ix.tools.top(s, Wr.get_nat(s), {==})

# A list of ids: its count, then id by id
# ---------------------------------------

# what the item loop's answer says about its input s (m + 1 ids)
def ix.Ntl(s: String, m: Nat, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{t, r}:
      {s == LawsBase.wire_spell_nats.items(t, r) : String} & ({List.length(&2, Nat, t) == 1n+m : Nat} & {LawsBase.wire_nats_fit(t) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def ix.ntl.at(+s: String, -d: Wr.Dec<Nat>, er: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> ix.Nat(s, d):
  %er : ix.Nat(s, _)
  ix.nat(s)

def ix.ntl.one(-s: String, +x: Nat, -s3: String, ex: ix.Nat(s, Wr.Got{x, s3})) -> ix.Ntl(s, 0n, Wr.Got{[x], s3}):
  (ea, eb) = ex
  (ea, ({==}, LAWireSpell.ws_and_tt(LawsBase.wire_fits(x), True{}, eb, {==})))

def ix.ntl.step(-s: String, +x: Nat, +s3: String, -k: Nat, ea: {s == Wr.put_nat(x, s3) : String}, eb: {LawsBase.wire_fits(x) == True{} : Bool},
  d: Wr.Dec<List<&2, Nat>>, ih: ix.Ntl(s3, k, d)) -> ix.Ntl(s, 1n+k, Wr.get_list.cons(Nat, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, ee) = ih
      (e2, e3) = ee
      (ix.step(z => Wr.put_nat(x, z), s, s3, LawsBase.wire_spell_nats.items(ys, r), ea, e1),
        (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Nat, ys), 1n+k, e2),
          LAWireSpell.ws_and_tt(LawsBase.wire_fits(x), LawsBase.wire_nats_fit(ys), eb, e3)))
    case Wr.Bad{}:
      Unit{}

def ix.ntl.step2(-s: String, +x: Nat, +s3: String, -k: Nat, ex: ix.Nat(s, Wr.Got{x, s3}),
  d: Wr.Dec<List<&2, Nat>>, ih: ix.Ntl(s3, k, d)) -> ix.Ntl(s, 1n+k, Wr.get_list.cons(Nat, x, d)):
  (ea, eb) = ex
  ix.ntl.step(s, x, s3, k, ea, eb, d, ih)

# the item loop accepts only spelled ids that fit
def ix.ntl(m: Nat, cur: Wr.Dec<Nat>, +s: String, er: {Wr.get_nat(s) == cur : Wr.Dec<Nat>}) ->
  ix.Ntl(s, m, Wr.get_list.go(~Nat, ~Wr.get_nat, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      ix.ntl.one(s, x, s3, ix.ntl.at(s, Wr.Got{x, s3}, er))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      ix.ntl.step2(s, x, s3, k, ix.ntl.at(s, Wr.Got{x, s3}, er),
        Wr.get_list.go(~Nat, ~Wr.get_nat, k, Wr.get_nat(s3)), ix.ntl(k, Wr.get_nat(s3), s3, {==}))
    case 1n++k Wr.Bad{}:
      Unit{}

# what an id list decoder's answer says about its input s
def ix.Ids(s: String, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{t, r}:
      {s == LawsBase.wire_spell_nats(t, r) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, t)), LawsBase.wire_nats_fit(t)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ix.ids.eq(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, +t: List<&2, Nat>, -r: String,
  e1: {s2 == LawsBase.wire_spell_nats.items(t, r) : String}, e2: {List.length(&2, Nat, t) == 1n+m : Nat}) -> {s == LawsBase.wire_spell_nats(t, r) : String}:
  %Equal.sym(Nat, List.length(&2, Nat, t), 1n+m, e2) : {s == Wr.put_nat(_, LawsBase.wire_spell_nats.items(t, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def ix.ids.fit(-m: Nat, hn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, +t: List<&2, Nat>,
  e2: {List.length(&2, Nat, t) == 1n+m : Nat}, e3: {LawsBase.wire_nats_fit(t) == True{} : Bool}) -> {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, t)), LawsBase.wire_nats_fit(t)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Nat, t), 1n+m, e2) : {Bool.and(LawsBase.wire_fits(_), LawsBase.wire_nats_fit(t)) == True{} : Bool}
  LAWireSpell.ws_and_tt(LawsBase.wire_fits(1n+m), LawsBase.wire_nats_fit(t), hn, e3)

def ix.ids.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, hn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  d: Wr.Dec<List<&2, Nat>>, tl: ix.Ntl(s2, m, d)) -> ix.Ids(s, d):
  match d:
    case Wr.Got{+t, +r}:
      (e1, ee) = tl
      (e2, e3) = ee
      +e4 = e2
      (ix.ids.eq(s, s2, m, en, t, r, e1, e4), ix.ids.fit(m, hn, t, e4, e3))
    case Wr.Bad{}:
      Unit{}

def ix.ids.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, hn: {LawsBase.wire_fits(n) == True{} : Bool}) ->
  ix.Ids(s, Wr.get_list.start(~Nat, ~Wr.get_nat, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      ix.ids.conv(s, s2, m, en, hn, Wr.get_list.go(~Nat, ~Wr.get_nat, m, Wr.get_nat(s2)), ix.ntl(m, Wr.get_nat(s2), s2, {==}))

def ix.ids.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) ->
  ix.Ids(s, Wr.get_list.start(~Nat, ~Wr.get_nat, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e2 = ed
      ix.ids.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e2), Wire.wire_nat_decoded_fits(s, n, s2, e2))
    case Wr.Bad{}:
      Unit{}

# every list of ids the decoder reads is spelled, its numbers fit
def ix.ids(+s: String) -> ix.Ids(s, FIn.get_ids(s)):
  ix.ids.top(s, Wr.get_nat(s), {==})

# A request: the cap, the tools, the needed ids
# ---------------------------------------------

def ix.r2(q: FIn.P2<Maybe<&2, Nat>, List<&2, If.Tool>>, r: String) -> String:
  match q:
    case FIn.P2{a, b}:
      Infer.core_infer_spell_mnat(a, Infer.core_infer_spell_tools(b, r))

def ix.rg2(q: FIn.P2<Maybe<&2, Nat>, List<&2, If.Tool>>) -> Bool:
  match q:
    case FIn.P2{a, +b}:
      Bool.and(LawsBase.core_mfits(a), Bool.and(LawsBase.wire_fits(List.length(&2, If.Tool, b)), Infer.core_tools_fit(b)))

def ix.r3(q: FIn.P2<FIn.P2<Maybe<&2, Nat>, List<&2, If.Tool>>, List<&2, Nat>>, r: String) -> String:
  match q:
    case FIn.P2{a, b}:
      ix.r2(a, LawsBase.wire_spell_nats(b, r))

def ix.rg3(q: FIn.P2<FIn.P2<Maybe<&2, Nat>, List<&2, If.Tool>>, List<&2, Nat>>) -> Bool:
  match q:
    case FIn.P2{a, +b}:
      Bool.and(ix.rg2(a), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, b)), LawsBase.wire_nats_fit(b)))

def ix.R2(s: String, d: Wr.Dec<FIn.P2<Maybe<&2, Nat>, List<&2, If.Tool>>>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ix.r2(q, r) : String} & {ix.rg2(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ix.R3(s: String, d: Wr.Dec<FIn.P2<FIn.P2<Maybe<&2, Nat>, List<&2, If.Tool>>, List<&2, Nat>>>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ix.r3(q, r) : String} & {ix.rg3(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ix.rf2(-s: String, +a: Maybe<&2, Nat>, -r: String, pre: {s == Infer.core_infer_spell_mnat(a, r) : String}, fa: {LawsBase.core_mfits(a) == True{} : Bool}, e: Wr.Dec<List<&2, If.Tool>>, inv: ix.Tools(r, e)) -> ix.R2(s, FIn.seq.fin(~Maybe<&2, Nat>, ~List<&2, If.Tool>, a, e)):
  match e:
    case Wr.Got{+b, +r2}:
      (e1, fb) = inv
      (ix.step(z => Infer.core_infer_spell_mnat(a, z), s, r, Infer.core_infer_spell_tools(b, r2), pre, e1), LAWireSpell.ws_and_tt(LawsBase.core_mfits(a), Bool.and(LawsBase.wire_fits(List.length(&2, If.Tool, b)), Infer.core_tools_fit(b)), fa, fb))
    case Wr.Bad{}:
      Unit{}

def ix.rs2(-s: String, d: Wr.Dec<Maybe<&2, Nat>>, inv: ix.MNat(s, d)) -> ix.R2(s, FIn.seq(~Maybe<&2, Nat>, ~List<&2, If.Tool>, ~FIn.get_tools, d)):
  match d:
    case Wr.Got{+a, +r}:
      (pre, fa) = inv
      ix.rf2(s, a, r, pre, fa, FIn.get_tools(r), ix.tools(r))
    case Wr.Bad{}:
      Unit{}

def ix.rf3(-s: String, +a: FIn.P2<Maybe<&2, Nat>, List<&2, If.Tool>>, -r: String, pre: {s == ix.r2(a, r) : String}, ga: {ix.rg2(a) == True{} : Bool}, e: Wr.Dec<List<&2, Nat>>, inv: ix.Ids(r, e)) -> ix.R3(s, FIn.seq.fin(~FIn.P2<Maybe<&2, Nat>, List<&2, If.Tool>>, ~List<&2, Nat>, a, e)):
  match e:
    case Wr.Got{+b, +r2}:
      (e1, fb) = inv
      (ix.step(z => ix.r2(a, z), s, r, LawsBase.wire_spell_nats(b, r2), pre, e1), LAWireSpell.ws_and_tt(ix.rg2(a), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, b)), LawsBase.wire_nats_fit(b)), ga, fb))
    case Wr.Bad{}:
      Unit{}

def ix.rs3(-s: String, d: Wr.Dec<FIn.P2<Maybe<&2, Nat>, List<&2, If.Tool>>>, inv: ix.R2(s, d)) -> ix.R3(s, FIn.seq(~FIn.P2<Maybe<&2, Nat>, List<&2, If.Tool>>, ~List<&2, Nat>, ~FIn.get_ids, d)):
  match d:
    case Wr.Got{+a, +r}:
      (pre, ga) = inv
      ix.rf3(s, a, r, pre, ga, FIn.get_ids(r), ix.ids(r))
    case Wr.Bad{}:
      Unit{}

# what a request decoder's answer says about its input s
def ix.Req(s: String, d: Wr.Dec<FIn.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == Infer.core_infer_spell_req(q, r) : String} & {Infer.core_infer_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ix.req.of(-s: String, d: Wr.Dec<FIn.P2<FIn.P2<Maybe<&2, Nat>, List<&2, If.Tool>>, List<&2, Nat>>>, inv: ix.R3(s, d)) -> ix.Req(s, FIn.get_req.of(d)):
  match d:
    case Wr.Got{q, r}:
      match q:
        case FIn.P2{q2, +need}:
          match q2:
            case FIn.P2{+cap, +ts}:
              (e, f) = inv
              (e, ix.assoc(LawsBase.core_mfits(cap), Bool.and(LawsBase.wire_fits(List.length(&2, If.Tool, ts)), Infer.core_tools_fit(ts)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, need)), LawsBase.wire_nats_fit(need)), f))
    case Wr.Bad{}:
      Unit{}

# every request the decoder reads is spelled, and fits; the rest follows
def ix.req(+s: String) -> ix.Req(s, FIn.get_req(s)):
  +d1 = FIn.get_mnat(s)
  +d2 = FIn.seq(~Maybe<&2, Nat>, ~List<&2, If.Tool>, ~FIn.get_tools, d1)
  ix.req.of(s, FIn.seq(~FIn.P2<Maybe<&2, Nat>, List<&2, If.Tool>>, ~List<&2, Nat>, ~FIn.get_ids, d2), ix.rs3(s, d2, ix.rs2(s, d1, ix.mnat(s))))
