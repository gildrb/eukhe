# eukhe: lemmas of the entry proofs of area codemode_describe: only spelled
# requests decode
#
# Each decoder of bend/ffi_codemode_describe.bend answers Got only for the
# spec's spelling of a value whose numbers fit (Nats and Bools:
# proof/context_order/base/exact.bend; strings: wire_str_exact,
# wire_str_decoded_fits; lists of strings: wire_strs_exact,
# wire_strs_decoded_fit).

import Base
import ../../../bend/codemode_describe.bend as Dsc
import ../../../bend/ffi_codemode_describe.bend as FDsc
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/codemode_describe.bend as CodemodeDescribe
import ../../context_order/base.bend as LACo
import ../../context_order/base/exact.bend as LACoExact

def cde.under(-s: String, -s1: String, -y: String, -f: String -> String, e: {s == f(s1) : String}, p: {s1 == y : String}) -> {s == f(y) : String}:
  %p : {s == f(_) : String}
  e

# ---- strings ----

def cde.PS(s: String, d: Wr.Dec<String>) -> Type:
  match d:
    case Wr.Got{+a, r}:
      {s == Wr.put_str(a, r) : String} & {LawsBase.wire_fits(String.length(a)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cde.ps_go(+s: String, d: Wr.Dec<String>, +ed: {Wr.get_str(s) == d : Wr.Dec<String>}) -> cde.PS(s, d):
  match d:
    case Wr.Got{+a, +r}:
      (Wire.wire_str_exact(s, a, r, ed), Wire.wire_str_decoded_fits(s, a, r, ed))
    case Wr.Bad{}:
      Unit{}

def cde.ps(+s: String) -> cde.PS(s, Wr.get_str(s)):
  cde.ps_go(s, Wr.get_str(s), {==})

def cde.PL(s: String, d: Wr.Dec<List<&2, String>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == LawsBase.wire_spell_strs(xs, r) : String} & {LawsBase.wire_strs_fit(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cde.pl_go(+s: String, d: Wr.Dec<List<&2, String>>, +ed: {Wr.get_list(~String, ~Wr.get_str, s) == d : Wr.Dec<List<&2, String>>}) -> cde.PL(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (Wire.wire_strs_exact(s, xs, r, ed), Wire.wire_strs_decoded_fit(s, xs, r, ed))
    case Wr.Bad{}:
      Unit{}

def cde.pl(+s: String) -> cde.PL(s, Wr.get_list(~String, ~Wr.get_str, s)):
  cde.pl_go(s, Wr.get_list(~String, ~Wr.get_str, s), {==})

# ---- tools ----

def cde.TO(s: String, d: Wr.Dec<Dsc.Tool>) -> Type:
  match d:
    case Wr.Got{+t, r}:
      {s == CodemodeDescribe.spell_tool(t, r) : String} & {CodemodeDescribe.tool_fits(t) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cde.to.size(-s: String, -s1: String, +n: String, e0: {s == Wr.put_str(n, s1) : String}, fn: {LawsBase.wire_fits(String.length(n)) == True{} : Bool}, d: Wr.Dec<Nat>, p: LACoExact.coe.PNF(s1, d)) -> cde.TO(s, FDsc.get_tool.size(n, d)):
  match d:
    case Wr.Got{+z, +r}:
      (e1, f1) = p
      (cde.under(s, s1, Wr.put_nat(z, r), y => Wr.put_str(n, y), e0, e1), LACo.co.and_tt(LawsBase.wire_fits(String.length(n)), LawsBase.wire_fits(z), fn, f1))
    case Wr.Bad{}:
      Unit{}

def cde.to.name(-s: String, d: Wr.Dec<String>, p: cde.PS(s, d)) -> cde.TO(s, FDsc.get_tool.name(d)):
  match d:
    case Wr.Got{+n, +s1}:
      (e0, f0) = p
      cde.to.size(s, s1, n, e0, f0, Wr.get_nat(s1), LACoExact.coe.pnf(s1))
    case Wr.Bad{}:
      Unit{}

def cde.tool(+s: String) -> cde.TO(s, FDsc.get_tool(s)):
  cde.to.name(s, Wr.get_str(s), cde.ps(s))

def cde.tl.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Dsc.Tool>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == CodemodeDescribe.spell_tools.items(xs, r) : String} & ({List.length(&2, Dsc.Tool, xs) == 1n+m : Nat} & {CodemodeDescribe.tools_all(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def cde.tl.step(-s: String, +x: Dsc.Tool, +s3: String, -k: Nat, ex: {s == CodemodeDescribe.spell_tool(x, s3) : String}, fx: {CodemodeDescribe.tool_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Dsc.Tool>>, ih: cde.tl.PL(s3, k, d)) -> cde.tl.PL(s, 1n+k, Wr.get_list.cons(Dsc.Tool, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, rest) = ih
      (e2, e3) = rest
      (cde.under(s, s3, CodemodeDescribe.spell_tools.items(ys, r), y => CodemodeDescribe.spell_tool(x, y), ex, e1), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Dsc.Tool, ys), 1n+k, e2), LACo.co.and_tt(CodemodeDescribe.tool_fits(x), CodemodeDescribe.tools_all(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

def cde.tl.loop(m: Nat, cur: Wr.Dec<Dsc.Tool>, +s: String, pc: cde.TO(s, cur)) -> cde.tl.PL(s, m, Wr.get_list.go(~Dsc.Tool, ~FDsc.get_tool, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LACo.co.and_tt(CodemodeDescribe.tool_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      cde.tl.step(s, x, s3, k, e, f, Wr.get_list.go(~Dsc.Tool, ~FDsc.get_tool, k, FDsc.get_tool(s3)), cde.tl.loop(k, FDsc.get_tool(s3), s3, cde.tool(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def cde.tl.LS(s: String, d: Wr.Dec<List<&2, Dsc.Tool>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_nat(List.length(&2, Dsc.Tool, xs), CodemodeDescribe.spell_tools.items(xs, r)) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, Dsc.Tool, xs)), CodemodeDescribe.tools_all(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cde.tl.conv(-s: String, -s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Dsc.Tool>>, pl: cde.tl.PL(s2, m, d)) -> cde.tl.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, rest) = pl
      (+e2, e3) = rest
      %Equal.sym(Nat, List.length(&2, Dsc.Tool, xs), 1n+m, e2) : {s == Wr.put_nat(_, CodemodeDescribe.spell_tools.items(xs, r)) : String} & {Bool.and(LawsBase.wire_fits(_), CodemodeDescribe.tools_all(xs)) == True{} : Bool}
      (cde.under(s, s2, CodemodeDescribe.spell_tools.items(xs, r), y => Wr.put_nat(1n+m, y), en, e1), LACo.co.and_tt(LawsBase.wire_fits(1n+m), CodemodeDescribe.tools_all(xs), fn, e3))
    case Wr.Bad{}:
      Unit{}

def cde.tl.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> cde.tl.LS(s, Wr.get_list.start(~Dsc.Tool, ~FDsc.get_tool, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      cde.tl.conv(s, s2, m, en, fn, Wr.get_list.go(~Dsc.Tool, ~FDsc.get_tool, m, FDsc.get_tool(s2)), cde.tl.loop(m, FDsc.get_tool(s2), s2, cde.tool(s2)))

def cde.tl.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cde.tl.LS(s, Wr.get_list.start(~Dsc.Tool, ~FDsc.get_tool, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      cde.tl.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

def cde.tl.list(+s: String) -> cde.tl.LS(s, Wr.get_list(~Dsc.Tool, ~FDsc.get_tool, s)):
  cde.tl.top(s, Wr.get_nat(s), {==})

# ---- namespaces ----

def cde.SP(s: String, d: Wr.Dec<Dsc.Space>) -> Type:
  match d:
    case Wr.Got{+x, r}:
      {s == CodemodeDescribe.spell_space(x, r) : String} & {CodemodeDescribe.space_fits(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cde.sp.about(-s: String, -s3: String, +n: String, +k: String, +p: String, e0: {s == Wr.put_str(n, Wr.put_str(k, Wr.put_str(p, s3))) : String}, fn: {LawsBase.wire_fits(String.length(n)) == True{} : Bool}, fk: {LawsBase.wire_fits(String.length(k)) == True{} : Bool}, fp: {LawsBase.wire_fits(String.length(p)) == True{} : Bool}, d: Wr.Dec<String>, ps: cde.PS(s3, d)) -> cde.SP(s, FDsc.get_space.about(n, k, p, d)):
  match d:
    case Wr.Got{+a, +r}:
      (e1, f1) = ps
      (cde.under(s, s3, Wr.put_str(a, r), y => Wr.put_str(n, Wr.put_str(k, Wr.put_str(p, y))), e0, e1), LACo.co.and_tt(Bool.and(LawsBase.wire_fits(String.length(n)), LawsBase.wire_fits(String.length(k))), Bool.and(LawsBase.wire_fits(String.length(p)), LawsBase.wire_fits(String.length(a))), LACo.co.and_tt(LawsBase.wire_fits(String.length(n)), LawsBase.wire_fits(String.length(k)), fn, fk), LACo.co.and_tt(LawsBase.wire_fits(String.length(p)), LawsBase.wire_fits(String.length(a)), fp, f1)))
    case Wr.Bad{}:
      Unit{}

def cde.sp.prefix(-s: String, -s2: String, +n: String, +k: String, e0: {s == Wr.put_str(n, Wr.put_str(k, s2)) : String}, fn: {LawsBase.wire_fits(String.length(n)) == True{} : Bool}, fk: {LawsBase.wire_fits(String.length(k)) == True{} : Bool}, d: Wr.Dec<String>, ps: cde.PS(s2, d)) -> cde.SP(s, FDsc.get_space.prefix(n, k, d)):
  match d:
    case Wr.Got{+p, +s3}:
      (e1, f1) = ps
      cde.sp.about(s, s3, n, k, p, cde.under(s, s2, Wr.put_str(p, s3), y => Wr.put_str(n, Wr.put_str(k, y)), e0, e1), fn, fk, f1, Wr.get_str(s3), cde.ps(s3))
    case Wr.Bad{}:
      Unit{}

def cde.sp.key(-s: String, -s1: String, +n: String, e0: {s == Wr.put_str(n, s1) : String}, fn: {LawsBase.wire_fits(String.length(n)) == True{} : Bool}, d: Wr.Dec<String>, ps: cde.PS(s1, d)) -> cde.SP(s, FDsc.get_space.key(n, d)):
  match d:
    case Wr.Got{+k, +s2}:
      (e1, f1) = ps
      cde.sp.prefix(s, s2, n, k, cde.under(s, s1, Wr.put_str(k, s2), y => Wr.put_str(n, y), e0, e1), fn, f1, Wr.get_str(s2), cde.ps(s2))
    case Wr.Bad{}:
      Unit{}

def cde.sp.name(-s: String, d: Wr.Dec<String>, ps: cde.PS(s, d)) -> cde.SP(s, FDsc.get_space.name(d)):
  match d:
    case Wr.Got{+n, +s1}:
      (e0, f0) = ps
      cde.sp.key(s, s1, n, e0, f0, Wr.get_str(s1), cde.ps(s1))
    case Wr.Bad{}:
      Unit{}

def cde.space(+s: String) -> cde.SP(s, FDsc.get_space(s)):
  cde.sp.name(s, Wr.get_str(s), cde.ps(s))

def cde.sl.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Dsc.Space>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == CodemodeDescribe.spell_spaces.items(xs, r) : String} & ({List.length(&2, Dsc.Space, xs) == 1n+m : Nat} & {CodemodeDescribe.spaces_all(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def cde.sl.step(-s: String, +x: Dsc.Space, +s3: String, -k: Nat, ex: {s == CodemodeDescribe.spell_space(x, s3) : String}, fx: {CodemodeDescribe.space_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Dsc.Space>>, ih: cde.sl.PL(s3, k, d)) -> cde.sl.PL(s, 1n+k, Wr.get_list.cons(Dsc.Space, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, rest) = ih
      (e2, e3) = rest
      (cde.under(s, s3, CodemodeDescribe.spell_spaces.items(ys, r), y => CodemodeDescribe.spell_space(x, y), ex, e1), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Dsc.Space, ys), 1n+k, e2), LACo.co.and_tt(CodemodeDescribe.space_fits(x), CodemodeDescribe.spaces_all(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

def cde.sl.loop(m: Nat, cur: Wr.Dec<Dsc.Space>, +s: String, pc: cde.SP(s, cur)) -> cde.sl.PL(s, m, Wr.get_list.go(~Dsc.Space, ~FDsc.get_space, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LACo.co.and_tt(CodemodeDescribe.space_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      cde.sl.step(s, x, s3, k, e, f, Wr.get_list.go(~Dsc.Space, ~FDsc.get_space, k, FDsc.get_space(s3)), cde.sl.loop(k, FDsc.get_space(s3), s3, cde.space(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def cde.sl.LS(s: String, d: Wr.Dec<List<&2, Dsc.Space>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_nat(List.length(&2, Dsc.Space, xs), CodemodeDescribe.spell_spaces.items(xs, r)) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, Dsc.Space, xs)), CodemodeDescribe.spaces_all(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cde.sl.conv(-s: String, -s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Dsc.Space>>, pl: cde.sl.PL(s2, m, d)) -> cde.sl.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, rest) = pl
      (+e2, e3) = rest
      %Equal.sym(Nat, List.length(&2, Dsc.Space, xs), 1n+m, e2) : {s == Wr.put_nat(_, CodemodeDescribe.spell_spaces.items(xs, r)) : String} & {Bool.and(LawsBase.wire_fits(_), CodemodeDescribe.spaces_all(xs)) == True{} : Bool}
      (cde.under(s, s2, CodemodeDescribe.spell_spaces.items(xs, r), y => Wr.put_nat(1n+m, y), en, e1), LACo.co.and_tt(LawsBase.wire_fits(1n+m), CodemodeDescribe.spaces_all(xs), fn, e3))
    case Wr.Bad{}:
      Unit{}

def cde.sl.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> cde.sl.LS(s, Wr.get_list.start(~Dsc.Space, ~FDsc.get_space, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      cde.sl.conv(s, s2, m, en, fn, Wr.get_list.go(~Dsc.Space, ~FDsc.get_space, m, FDsc.get_space(s2)), cde.sl.loop(m, FDsc.get_space(s2), s2, cde.space(s2)))

def cde.sl.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cde.sl.LS(s, Wr.get_list.start(~Dsc.Space, ~FDsc.get_space, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      cde.sl.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

def cde.sl.list(+s: String) -> cde.sl.LS(s, Wr.get_list(~Dsc.Space, ~FDsc.get_space, s)):
  cde.sl.top(s, Wr.get_nat(s), {==})

# ---- requests ----

def cde.RQ(s: String, d: Wr.Dec<FDsc.Req>) -> Type:
  match d:
    case Wr.Got{+q, r}:
      {s == CodemodeDescribe.spell_req(q, r) : String} & {CodemodeDescribe.req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cde.rq.ps(-s: String, -s2: String, +ns: List<&2, String>, e0: {s == Wr.put_nat(0n, LawsBase.wire_spell_strs(ns, s2)) : String}, fn: {LawsBase.wire_strs_fit(ns) == True{} : Bool}, d: Wr.Dec<List<&2, String>>, p: cde.PL(s2, d)) -> cde.RQ(s, FDsc.get_spaces.prefixes(ns, d)):
  match d:
    case Wr.Got{+ps, +r}:
      (e1, f1) = p
      (cde.under(s, s2, LawsBase.wire_spell_strs(ps, r), y => Wr.put_nat(0n, LawsBase.wire_spell_strs(ns, y)), e0, e1), LACo.co.and_tt(LawsBase.wire_strs_fit(ns), LawsBase.wire_strs_fit(ps), fn, f1))
    case Wr.Bad{}:
      Unit{}

def cde.rq.ns(-s: String, -s1: String, e0: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<List<&2, String>>, p: cde.PL(s1, d)) -> cde.RQ(s, FDsc.get_spaces(d)):
  match d:
    case Wr.Got{+ns, +s2}:
      (e1, f1) = p
      cde.rq.ps(s, s2, ns, cde.under(s, s1, LawsBase.wire_spell_strs(ns, s2), y => Wr.put_nat(0n, y), e0, e1), f1, Wr.get_list(~String, ~Wr.get_str, s2), cde.pl(s2))
    case Wr.Bad{}:
      Unit{}

def cde.rq.budget(-s: String, -s3: String, +ts: List<&2, Dsc.Tool>, +ss: List<&2, Dsc.Space>, e0: {s == Wr.put_nat(1n, Wr.put_nat(List.length(&2, Dsc.Tool, ts), CodemodeDescribe.spell_tools.items(ts, Wr.put_nat(List.length(&2, Dsc.Space, ss), CodemodeDescribe.spell_spaces.items(ss, s3))))) : String}, ft: {Bool.and(LawsBase.wire_fits(List.length(&2, Dsc.Tool, ts)), CodemodeDescribe.tools_all(ts)) == True{} : Bool}, fs: {Bool.and(LawsBase.wire_fits(List.length(&2, Dsc.Space, ss)), CodemodeDescribe.spaces_all(ss)) == True{} : Bool}, d: Wr.Dec<Nat>, p: LACoExact.coe.PNF(s3, d)) -> cde.RQ(s, FDsc.get_section.budget(ts, ss, d)):
  match d:
    case Wr.Got{+b, +r}:
      (e1, f1) = p
      (cde.under(s, s3, Wr.put_nat(b, r), y => Wr.put_nat(1n, Wr.put_nat(List.length(&2, Dsc.Tool, ts), CodemodeDescribe.spell_tools.items(ts, Wr.put_nat(List.length(&2, Dsc.Space, ss), CodemodeDescribe.spell_spaces.items(ss, y))))), e0, e1), LACo.co.and_tt(Bool.and(LawsBase.wire_fits(List.length(&2, Dsc.Tool, ts)), CodemodeDescribe.tools_all(ts)), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Dsc.Space, ss)), CodemodeDescribe.spaces_all(ss)), LawsBase.wire_fits(b)), ft, LACo.co.and_tt(Bool.and(LawsBase.wire_fits(List.length(&2, Dsc.Space, ss)), CodemodeDescribe.spaces_all(ss)), LawsBase.wire_fits(b), fs, f1)))
    case Wr.Bad{}:
      Unit{}

def cde.rq.spaces(-s: String, -s2: String, +ts: List<&2, Dsc.Tool>, e0: {s == Wr.put_nat(1n, Wr.put_nat(List.length(&2, Dsc.Tool, ts), CodemodeDescribe.spell_tools.items(ts, s2))) : String}, ft: {Bool.and(LawsBase.wire_fits(List.length(&2, Dsc.Tool, ts)), CodemodeDescribe.tools_all(ts)) == True{} : Bool}, d: Wr.Dec<List<&2, Dsc.Space>>, p: cde.sl.LS(s2, d)) -> cde.RQ(s, FDsc.get_section.spaces(ts, d)):
  match d:
    case Wr.Got{+ss, +s3}:
      (e1, f1) = p
      cde.rq.budget(s, s3, ts, ss, cde.under(s, s2, Wr.put_nat(List.length(&2, Dsc.Space, ss), CodemodeDescribe.spell_spaces.items(ss, s3)), y => Wr.put_nat(1n, Wr.put_nat(List.length(&2, Dsc.Tool, ts), CodemodeDescribe.spell_tools.items(ts, y))), e0, e1), ft, f1, Wr.get_nat(s3), LACoExact.coe.pnf(s3))
    case Wr.Bad{}:
      Unit{}

def cde.rq.tools(-s: String, -s1: String, e0: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<List<&2, Dsc.Tool>>, p: cde.tl.LS(s1, d)) -> cde.RQ(s, FDsc.get_section(d)):
  match d:
    case Wr.Got{+ts, +s2}:
      (e1, f1) = p
      cde.rq.spaces(s, s2, ts, cde.under(s, s1, Wr.put_nat(List.length(&2, Dsc.Tool, ts), CodemodeDescribe.spell_tools.items(ts, s2)), y => Wr.put_nat(1n, y), e0, e1), f1, Wr.get_list(~Dsc.Space, ~FDsc.get_space, s2), cde.sl.list(s2))
    case Wr.Bad{}:
      Unit{}

def cde.rq.classify(-s: String, -s2: String, +m: Bool, e0: {s == Wr.put_nat(2n, Wr.put_bool(m, s2)) : String}, d: Wr.Dec<Bool>, p: LACoExact.coe.PB(s2, d)) -> cde.RQ(s, FDsc.get_describe.classify(m, d)):
  match d:
    case Wr.Got{+c, +r}:
      (cde.under(s, s2, Wr.put_bool(c, r), y => Wr.put_nat(2n, Wr.put_bool(m, y)), e0, p), {==})
    case Wr.Bad{}:
      Unit{}

def cde.rq.models(-s: String, -s1: String, e0: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Bool>, p: LACoExact.coe.PB(s1, d)) -> cde.RQ(s, FDsc.get_describe(d)):
  match d:
    case Wr.Got{+m, +s2}:
      cde.rq.classify(s, s2, m, cde.under(s, s1, Wr.put_bool(m, s2), y => Wr.put_nat(2n, y), e0, p), Wr.get_bool(s2), LACoExact.coe.pb(s2))
    case Wr.Bad{}:
      Unit{}

def cde.rq.top(-s: String, d: Wr.Dec<Nat>, p: LACoExact.coe.PNF(s, d)) -> cde.RQ(s, FDsc.get_req.tag(d)):
  match d:
    case Wr.Got{t, +s1}:
      match t:
        case 0n:
          (e0, f0) = p
          cde.rq.ns(s, s1, e0, Wr.get_list(~String, ~Wr.get_str, s1), cde.pl(s1))
        case 1n:
          (e0, f0) = p
          cde.rq.tools(s, s1, e0, Wr.get_list(~Dsc.Tool, ~FDsc.get_tool, s1), cde.tl.list(s1))
        case 2n:
          (e0, f0) = p
          cde.rq.models(s, s1, e0, Wr.get_bool(s1), LACoExact.coe.pb(s1))
        case 3n+u:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a request decoded is spelled, and its numbers fit
def cde.req(+s: String) -> cde.RQ(s, FDsc.get_req(s)):
  cde.rq.top(s, Wr.get_nat(s), LACoExact.coe.pnf(s))
