# eukhe: lemmas the proofs of area tool_surface share

import Base
import ../../bend/ffi_tool_surface.bend as FTs
import ../../bend/tools.bend as Tl
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tool_surface.bend as ToolSurface
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire

# Logic
# -----

def ts.NZ(n: Nat, G: Type) -> Type:
  match n:
    case 0n:
      G
    case 1n+k:
      Unit

# 1 + c is not 0
def ts.succ_zero(-c: Nat, -G: Type, h: {1n+c == 0n : Nat}) -> G:
  %h : ts.NZ(_, G)
  Unit{}

def ts.eq_refl(t: Nat) -> {Nat.is_eq(t, t) == True{} : Bool}:
  match t:
    case 0n:
      {==}
    case 1n+p:
      ts.eq_refl(p)

def ts.or_true(a: Bool, -b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

# a list with no copy of t after its head y (test b of y against t):
# the head's count and the rest's
def ts.zero_tail(-y: Nat, -t: Nat, -rest: List<&2, Nat>, -b: Bool, e: {Nat.is_eq(y, t) == b : Bool}, none: {Nat.add(ToolSurface.ts_one(Nat.is_eq(y, t)), ToolSurface.ts_count(rest, t)) == 0n : Nat}) -> {Nat.add(ToolSurface.ts_one(b), ToolSurface.ts_count(rest, t)) == 0n : Nat}:
  Equal.trans(Nat, Nat.add(ToolSurface.ts_one(b), ToolSurface.ts_count(rest, t)), Nat.add(ToolSurface.ts_one(Nat.is_eq(y, t)), ToolSurface.ts_count(rest, t)), 0n, Equal.sym(Nat, Nat.add(ToolSurface.ts_one(Nat.is_eq(y, t)), ToolSurface.ts_count(rest, t)), Nat.add(ToolSurface.ts_one(b), ToolSurface.ts_count(rest, t)), Equal.cong(Bool, Nat, z => Nat.add(ToolSurface.ts_one(z), ToolSurface.ts_count(rest, t)), Nat.is_eq(y, t), b, e)), none)

# Membership
# ----------

# t is an element of pre ++ t <> post
def ts.elem_at(pre: List<&2, Nat>, +t: Nat, -post: List<&2, Nat>) -> {Tl.elem(List.append(&2, Nat, pre, t <> post), t) == True{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(t, t), True{}, ts.eq_refl(t)) : {Bool.or(_, Tl.elem(post, t)) == True{} : Bool}
      {==}
    case +y <> pr:
      ts.or_true(Nat.is_eq(y, t), Tl.elem(List.append(&2, Nat, pr, t <> post), t), ts.elem_at(pr, t, post))

# The entry answers as the laws spell the model's decision
# --------------------------------------------------------

def ts.schema(x: Tl.Schema) -> {FTs.put_schema(x) == ToolSurface.spell_schema(x) : String}:
  match x:
    case Tl.Schema{ps, v}:
      {==}

def ts.reply(q: FTs.Req) -> {FTs.answer(q) == ToolSurface.spell_answer(q) : String}:
  match q:
    case FTs.QBuild{+ps, +v}:
      ts.schema(Tl.build(Tl.Schema{ps, v}))
    case FTs.QJoin{d, t}:
      {==}
    case FTs.QQuit{d, t}:
      {==}
    case FTs.QReach{d, t}:
      {==}

# The entry's decoder reads back what Rust writes
# -----------------------------------------------

def ts.rt_build(+ps: List<&2, Nat>, +v: Nat, +rest: String, +fits: {ToolSurface.req_fits(FTs.QBuild{ps, v}) == True{} : Bool}) -> {FTs.get_req(ToolSurface.spell_req(FTs.QBuild{ps, v}, rest)) == Wr.Got{FTs.QBuild{ps, v}, rest} : Wr.Dec<FTs.Req>}:
  +hl = LLogicBool.wr_and_l(ToolSurface.ns_fit(ps), LawsBase.wire_fits(v), fits)
  +hn = LLogicBool.wr_and_r(ToolSurface.ns_fit(ps), LawsBase.wire_fits(v), fits)
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, ToolSurface.spell_ns(ps, Wr.put_nat(v, rest))), Wr.Got{ps, Wr.put_nat(v, rest)}, Wire.wire_list_round_trip(ps, Wr.put_nat(v, rest), hl)) : {FTs.get_build(_) == Wr.Got{FTs.QBuild{ps, v}, rest} : Wr.Dec<FTs.Req>}
  %LWire.pw6.nat(v, rest, hn) : {FTs.get_build.version(ps, _) == Wr.Got{FTs.QBuild{ps, v}, rest} : Wr.Dec<FTs.Req>}
  {==}

def ts.rt_join(+d: List<&2, Nat>, +t: Nat, +rest: String, +fits: {ToolSurface.req_fits(FTs.QJoin{d, t}) == True{} : Bool}) -> {FTs.get_req(ToolSurface.spell_req(FTs.QJoin{d, t}, rest)) == Wr.Got{FTs.QJoin{d, t}, rest} : Wr.Dec<FTs.Req>}:
  +hl = LLogicBool.wr_and_l(ToolSurface.ns_fit(d), LawsBase.wire_fits(t), fits)
  +hn = LLogicBool.wr_and_r(ToolSurface.ns_fit(d), LawsBase.wire_fits(t), fits)
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, ToolSurface.spell_ns(d, Wr.put_nat(t, rest))), Wr.Got{d, Wr.put_nat(t, rest)}, Wire.wire_list_round_trip(d, Wr.put_nat(t, rest), hl)) : {FTs.get_join(_) == Wr.Got{FTs.QJoin{d, t}, rest} : Wr.Dec<FTs.Req>}
  %LWire.pw6.nat(t, rest, hn) : {FTs.get_join.t(d, _) == Wr.Got{FTs.QJoin{d, t}, rest} : Wr.Dec<FTs.Req>}
  {==}

def ts.rt_quit(+d: List<&2, Nat>, +t: Nat, +rest: String, +fits: {ToolSurface.req_fits(FTs.QQuit{d, t}) == True{} : Bool}) -> {FTs.get_req(ToolSurface.spell_req(FTs.QQuit{d, t}, rest)) == Wr.Got{FTs.QQuit{d, t}, rest} : Wr.Dec<FTs.Req>}:
  +hl = LLogicBool.wr_and_l(ToolSurface.ns_fit(d), LawsBase.wire_fits(t), fits)
  +hn = LLogicBool.wr_and_r(ToolSurface.ns_fit(d), LawsBase.wire_fits(t), fits)
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, ToolSurface.spell_ns(d, Wr.put_nat(t, rest))), Wr.Got{d, Wr.put_nat(t, rest)}, Wire.wire_list_round_trip(d, Wr.put_nat(t, rest), hl)) : {FTs.get_quit(_) == Wr.Got{FTs.QQuit{d, t}, rest} : Wr.Dec<FTs.Req>}
  %LWire.pw6.nat(t, rest, hn) : {FTs.get_quit.t(d, _) == Wr.Got{FTs.QQuit{d, t}, rest} : Wr.Dec<FTs.Req>}
  {==}

def ts.rt_reach(+d: List<&2, Nat>, +t: Nat, +rest: String, +fits: {ToolSurface.req_fits(FTs.QReach{d, t}) == True{} : Bool}) -> {FTs.get_req(ToolSurface.spell_req(FTs.QReach{d, t}, rest)) == Wr.Got{FTs.QReach{d, t}, rest} : Wr.Dec<FTs.Req>}:
  +hl = LLogicBool.wr_and_l(ToolSurface.ns_fit(d), LawsBase.wire_fits(t), fits)
  +hn = LLogicBool.wr_and_r(ToolSurface.ns_fit(d), LawsBase.wire_fits(t), fits)
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, ToolSurface.spell_ns(d, Wr.put_nat(t, rest))), Wr.Got{d, Wr.put_nat(t, rest)}, Wire.wire_list_round_trip(d, Wr.put_nat(t, rest), hl)) : {FTs.get_reach(_) == Wr.Got{FTs.QReach{d, t}, rest} : Wr.Dec<FTs.Req>}
  %LWire.pw6.nat(t, rest, hn) : {FTs.get_reach.t(d, _) == Wr.Got{FTs.QReach{d, t}, rest} : Wr.Dec<FTs.Req>}
  {==}

# a request Rust writes, every number within the wire, reads back with
# the input after it
def ts.rt(q: FTs.Req, +rest: String, fits: {ToolSurface.req_fits(q) == True{} : Bool}) -> {FTs.get_req(ToolSurface.spell_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FTs.Req>}:
  match q:
    case FTs.QBuild{ps, v}:
      ts.rt_build(ps, v, rest, fits)
    case FTs.QJoin{d, t}:
      ts.rt_join(d, t, rest, fits)
    case FTs.QQuit{d, t}:
      ts.rt_quit(d, t, rest, fits)
    case FTs.QReach{d, t}:
      ts.rt_reach(d, t, rest, fits)
