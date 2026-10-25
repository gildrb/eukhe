# eukhe: lemmas of the entry proofs of area codemode_describe: spelled
# requests read back
#
# Each decoder of bend/ffi_codemode_describe.bend reads the spec's
# spelling of a value whose numbers fit back and leaves the rest untouched
# (Nats, Bools: proof/context_order/base/read.bend; strings:
# wire_str_round_trip; lists of strings: wire_strs_round_trip).

import Base
import ../../../bend/codemode_describe.bend as Dsc
import ../../../bend/ffi_codemode_describe.bend as FDsc
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/codemode_describe.bend as CodemodeDescribe
import ../../context_order/base.bend as LACo
import ../../context_order/base/read.bend as LACoRead

def cdq.str(+a: String, +rest: String, h: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}) -> {Wr.Got{a, rest} == Wr.get_str(Wr.put_str(a, rest)) : Wr.Dec<String>}:
  Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, rest)), Wr.Got{a, rest}, Wire.wire_str_round_trip(a, rest, h))

def cdq.tool(t: Dsc.Tool, +rest: String, +h: {CodemodeDescribe.tool_fits(t) == True{} : Bool}) -> {FDsc.get_tool(CodemodeDescribe.spell_tool(t, rest)) == Wr.Got{t, rest} : Wr.Dec<Dsc.Tool>}:
  match t:
    case Dsc.Tool{+n, +z}:
      %cdq.str(n, Wr.put_nat(z, rest), LACo.co.and_l(LawsBase.wire_fits(String.length(n)), LawsBase.wire_fits(z), h)) : {FDsc.get_tool.name(_) == Wr.Got{Dsc.Tool{n, z}, rest} : Wr.Dec<Dsc.Tool>}
      %LACoRead.cot.nat(z, rest, LACo.co.and_r(LawsBase.wire_fits(String.length(n)), LawsBase.wire_fits(z), h)) : {FDsc.get_tool.size(n, _) == Wr.Got{Dsc.Tool{n, z}, rest} : Wr.Dec<Dsc.Tool>}
      {==}

def cdq.space(s: Dsc.Space, +rest: String, +h: {CodemodeDescribe.space_fits(s) == True{} : Bool}) -> {FDsc.get_space(CodemodeDescribe.spell_space(s, rest)) == Wr.Got{s, rest} : Wr.Dec<Dsc.Space>}:
  match s:
    case Dsc.Space{+n, +k, +p, +a}:
      +l = Bool.and(LawsBase.wire_fits(String.length(n)), LawsBase.wire_fits(String.length(k)))
      +r = Bool.and(LawsBase.wire_fits(String.length(p)), LawsBase.wire_fits(String.length(a)))
      +hl = LACo.co.and_l(l, r, h)
      +hr = LACo.co.and_r(l, r, h)
      %cdq.str(n, Wr.put_str(k, Wr.put_str(p, Wr.put_str(a, rest))), LACo.co.and_l(LawsBase.wire_fits(String.length(n)), LawsBase.wire_fits(String.length(k)), hl)) : {FDsc.get_space.name(_) == Wr.Got{Dsc.Space{n, k, p, a}, rest} : Wr.Dec<Dsc.Space>}
      %cdq.str(k, Wr.put_str(p, Wr.put_str(a, rest)), LACo.co.and_r(LawsBase.wire_fits(String.length(n)), LawsBase.wire_fits(String.length(k)), hl)) : {FDsc.get_space.key(n, _) == Wr.Got{Dsc.Space{n, k, p, a}, rest} : Wr.Dec<Dsc.Space>}
      %cdq.str(p, Wr.put_str(a, rest), LACo.co.and_l(LawsBase.wire_fits(String.length(p)), LawsBase.wire_fits(String.length(a)), hr)) : {FDsc.get_space.prefix(n, k, _) == Wr.Got{Dsc.Space{n, k, p, a}, rest} : Wr.Dec<Dsc.Space>}
      %cdq.str(a, rest, LACo.co.and_r(LawsBase.wire_fits(String.length(p)), LawsBase.wire_fits(String.length(a)), hr)) : {FDsc.get_space.about(n, k, p, _) == Wr.Got{Dsc.Space{n, k, p, a}, rest} : Wr.Dec<Dsc.Space>}
      {==}

# a spelled list of tools whose count and items fit reads back
def cdq.tl.go_rt(+t: List<&2, Dsc.Tool>, +x: Dsc.Tool, +rest: String, +h: {CodemodeDescribe.tools_all(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Dsc.Tool, ~FDsc.get_tool, List.length(&2, Dsc.Tool, t), FDsc.get_tool(CodemodeDescribe.spell_tool(x, CodemodeDescribe.spell_tools.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Dsc.Tool>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Dsc.Tool>, FDsc.get_tool(CodemodeDescribe.spell_tool(x, rest)), Wr.Got{x, rest}, cdq.tool(x, rest, LACo.co.and_l(CodemodeDescribe.tool_fits(x), CodemodeDescribe.tools_all([]), h))) : {Wr.get_list.go(~Dsc.Tool, ~FDsc.get_tool, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Dsc.Tool>>}
      {==}
    case Con{+y, +u}:
      +r2 = CodemodeDescribe.spell_tool(y, CodemodeDescribe.spell_tools.items(u, rest))
      %Equal.sym(Wr.Dec<Dsc.Tool>, FDsc.get_tool(CodemodeDescribe.spell_tool(x, r2)), Wr.Got{x, r2}, cdq.tool(x, r2, LACo.co.and_l(CodemodeDescribe.tool_fits(x), CodemodeDescribe.tools_all(y <> u), h))) : {Wr.get_list.go(~Dsc.Tool, ~FDsc.get_tool, 1n+List.length(&2, Dsc.Tool, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Dsc.Tool>>}
      %Equal.sym(Wr.Dec<List<&2, Dsc.Tool>>, Wr.get_list.go(~Dsc.Tool, ~FDsc.get_tool, List.length(&2, Dsc.Tool, u), FDsc.get_tool(r2)), Wr.Got{y <> u, rest}, cdq.tl.go_rt(u, y, rest, LACo.co.and_r(CodemodeDescribe.tool_fits(x), CodemodeDescribe.tools_all(y <> u), h))) : {Wr.get_list.cons(Dsc.Tool, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Dsc.Tool>>}
      {==}

def cdq.tl.rt(+xs: List<&2, Dsc.Tool>, +r: String, +h: {Bool.and(LawsBase.wire_fits(List.length(&2, Dsc.Tool, xs)), CodemodeDescribe.tools_all(xs)) == True{} : Bool}) -> {Wr.get_list(~Dsc.Tool, ~FDsc.get_tool, Wr.put_nat(List.length(&2, Dsc.Tool, xs), CodemodeDescribe.spell_tools.items(xs, r))) == Wr.Got{xs, r} : Wr.Dec<List<&2, Dsc.Tool>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, r)), Wr.Got{0n, r}, Wire.wire_nat_round_trip(0n, r, {==})) : {Wr.get_list.start(~Dsc.Tool, ~FDsc.get_tool, _) == Wr.Got{Nil{}, r} : Wr.Dec<List<&2, Dsc.Tool>>}
      {==}
    case Con{+x, +t}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Dsc.Tool, x <> t), CodemodeDescribe.spell_tools.items(x <> t, r))), Wr.Got{List.length(&2, Dsc.Tool, x <> t), CodemodeDescribe.spell_tools.items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, Dsc.Tool, x <> t), CodemodeDescribe.spell_tools.items(x <> t, r), LACo.co.and_l(LawsBase.wire_fits(List.length(&2, Dsc.Tool, x <> t)), CodemodeDescribe.tools_all(x <> t), h))) : {Wr.get_list.start(~Dsc.Tool, ~FDsc.get_tool, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Dsc.Tool>>}
      cdq.tl.go_rt(t, x, r, LACo.co.and_r(LawsBase.wire_fits(List.length(&2, Dsc.Tool, x <> t)), CodemodeDescribe.tools_all(x <> t), h))

# a spelled list of namespaces whose count and items fit reads back
def cdq.sl.go_rt(+t: List<&2, Dsc.Space>, +x: Dsc.Space, +rest: String, +h: {CodemodeDescribe.spaces_all(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Dsc.Space, ~FDsc.get_space, List.length(&2, Dsc.Space, t), FDsc.get_space(CodemodeDescribe.spell_space(x, CodemodeDescribe.spell_spaces.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Dsc.Space>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Dsc.Space>, FDsc.get_space(CodemodeDescribe.spell_space(x, rest)), Wr.Got{x, rest}, cdq.space(x, rest, LACo.co.and_l(CodemodeDescribe.space_fits(x), CodemodeDescribe.spaces_all([]), h))) : {Wr.get_list.go(~Dsc.Space, ~FDsc.get_space, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Dsc.Space>>}
      {==}
    case Con{+y, +u}:
      +r2 = CodemodeDescribe.spell_space(y, CodemodeDescribe.spell_spaces.items(u, rest))
      %Equal.sym(Wr.Dec<Dsc.Space>, FDsc.get_space(CodemodeDescribe.spell_space(x, r2)), Wr.Got{x, r2}, cdq.space(x, r2, LACo.co.and_l(CodemodeDescribe.space_fits(x), CodemodeDescribe.spaces_all(y <> u), h))) : {Wr.get_list.go(~Dsc.Space, ~FDsc.get_space, 1n+List.length(&2, Dsc.Space, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Dsc.Space>>}
      %Equal.sym(Wr.Dec<List<&2, Dsc.Space>>, Wr.get_list.go(~Dsc.Space, ~FDsc.get_space, List.length(&2, Dsc.Space, u), FDsc.get_space(r2)), Wr.Got{y <> u, rest}, cdq.sl.go_rt(u, y, rest, LACo.co.and_r(CodemodeDescribe.space_fits(x), CodemodeDescribe.spaces_all(y <> u), h))) : {Wr.get_list.cons(Dsc.Space, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Dsc.Space>>}
      {==}

def cdq.sl.rt(+xs: List<&2, Dsc.Space>, +r: String, +h: {Bool.and(LawsBase.wire_fits(List.length(&2, Dsc.Space, xs)), CodemodeDescribe.spaces_all(xs)) == True{} : Bool}) -> {Wr.get_list(~Dsc.Space, ~FDsc.get_space, Wr.put_nat(List.length(&2, Dsc.Space, xs), CodemodeDescribe.spell_spaces.items(xs, r))) == Wr.Got{xs, r} : Wr.Dec<List<&2, Dsc.Space>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, r)), Wr.Got{0n, r}, Wire.wire_nat_round_trip(0n, r, {==})) : {Wr.get_list.start(~Dsc.Space, ~FDsc.get_space, _) == Wr.Got{Nil{}, r} : Wr.Dec<List<&2, Dsc.Space>>}
      {==}
    case Con{+x, +t}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Dsc.Space, x <> t), CodemodeDescribe.spell_spaces.items(x <> t, r))), Wr.Got{List.length(&2, Dsc.Space, x <> t), CodemodeDescribe.spell_spaces.items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, Dsc.Space, x <> t), CodemodeDescribe.spell_spaces.items(x <> t, r), LACo.co.and_l(LawsBase.wire_fits(List.length(&2, Dsc.Space, x <> t)), CodemodeDescribe.spaces_all(x <> t), h))) : {Wr.get_list.start(~Dsc.Space, ~FDsc.get_space, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Dsc.Space>>}
      cdq.sl.go_rt(t, x, r, LACo.co.and_r(LawsBase.wire_fits(List.length(&2, Dsc.Space, x <> t)), CodemodeDescribe.spaces_all(x <> t), h))

# a spelled request whose numbers fit reads back
def cdq.req(q: FDsc.Req, +rest: String, +h: {CodemodeDescribe.req_fits(q) == True{} : Bool}) -> {FDsc.get_req(CodemodeDescribe.spell_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FDsc.Req>}:
  match q:
    case FDsc.QSpaces{+ns, +ps}:
      +r2 = LawsBase.wire_spell_strs(ps, rest)
      %LACoRead.cot.nat(0n, LawsBase.wire_spell_strs(ns, r2), {==}) : {FDsc.get_req.tag(_) == Wr.Got{FDsc.QSpaces{ns, ps}, rest} : Wr.Dec<FDsc.Req>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, LawsBase.wire_spell_strs(ns, r2)), Wr.Got{ns, r2}, Wire.wire_strs_round_trip(ns, r2, LACo.co.and_l(LawsBase.wire_strs_fit(ns), LawsBase.wire_strs_fit(ps), h))) : {FDsc.get_spaces(_) == Wr.Got{FDsc.QSpaces{ns, ps}, rest} : Wr.Dec<FDsc.Req>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, r2), Wr.Got{ps, rest}, Wire.wire_strs_round_trip(ps, rest, LACo.co.and_r(LawsBase.wire_strs_fit(ns), LawsBase.wire_strs_fit(ps), h))) : {FDsc.get_spaces.prefixes(ns, _) == Wr.Got{FDsc.QSpaces{ns, ps}, rest} : Wr.Dec<FDsc.Req>}
      {==}
    case FDsc.QSection{+ts, +ss, +b}:
      +r3 = Wr.put_nat(List.length(&2, Dsc.Space, ss), CodemodeDescribe.spell_spaces.items(ss, Wr.put_nat(b, rest)))
      +ft = Bool.and(LawsBase.wire_fits(List.length(&2, Dsc.Tool, ts)), CodemodeDescribe.tools_all(ts))
      +fr = Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Dsc.Space, ss)), CodemodeDescribe.spaces_all(ss)), LawsBase.wire_fits(b))
      +hr = LACo.co.and_r(ft, fr, h)
      %LACoRead.cot.nat(1n, Wr.put_nat(List.length(&2, Dsc.Tool, ts), CodemodeDescribe.spell_tools.items(ts, r3)), {==}) : {FDsc.get_req.tag(_) == Wr.Got{FDsc.QSection{ts, ss, b}, rest} : Wr.Dec<FDsc.Req>}
      %Equal.sym(Wr.Dec<List<&2, Dsc.Tool>>, Wr.get_list(~Dsc.Tool, ~FDsc.get_tool, Wr.put_nat(List.length(&2, Dsc.Tool, ts), CodemodeDescribe.spell_tools.items(ts, r3))), Wr.Got{ts, r3}, cdq.tl.rt(ts, r3, LACo.co.and_l(ft, fr, h))) : {FDsc.get_section(_) == Wr.Got{FDsc.QSection{ts, ss, b}, rest} : Wr.Dec<FDsc.Req>}
      %Equal.sym(Wr.Dec<List<&2, Dsc.Space>>, Wr.get_list(~Dsc.Space, ~FDsc.get_space, r3), Wr.Got{ss, Wr.put_nat(b, rest)}, cdq.sl.rt(ss, Wr.put_nat(b, rest), LACo.co.and_l(Bool.and(LawsBase.wire_fits(List.length(&2, Dsc.Space, ss)), CodemodeDescribe.spaces_all(ss)), LawsBase.wire_fits(b), hr))) : {FDsc.get_section.spaces(ts, _) == Wr.Got{FDsc.QSection{ts, ss, b}, rest} : Wr.Dec<FDsc.Req>}
      %LACoRead.cot.nat(b, rest, LACo.co.and_r(Bool.and(LawsBase.wire_fits(List.length(&2, Dsc.Space, ss)), CodemodeDescribe.spaces_all(ss)), LawsBase.wire_fits(b), hr)) : {FDsc.get_section.budget(ts, ss, _) == Wr.Got{FDsc.QSection{ts, ss, b}, rest} : Wr.Dec<FDsc.Req>}
      {==}
    case FDsc.QDescribe{+m, +c}:
      %LACoRead.cot.nat(2n, Wr.put_bool(m, Wr.put_bool(c, rest)), {==}) : {FDsc.get_req.tag(_) == Wr.Got{FDsc.QDescribe{m, c}, rest} : Wr.Dec<FDsc.Req>}
      %LACoRead.cot.bool(m, Wr.put_bool(c, rest)) : {FDsc.get_describe(_) == Wr.Got{FDsc.QDescribe{m, c}, rest} : Wr.Dec<FDsc.Req>}
      %LACoRead.cot.bool(c, rest) : {FDsc.get_describe.classify(m, _) == Wr.Got{FDsc.QDescribe{m, c}, rest} : Wr.Dec<FDsc.Req>}
      {==}
