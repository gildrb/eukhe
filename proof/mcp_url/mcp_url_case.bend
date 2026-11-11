# eukhe: the proof of LAW mcp_url_case
#
# PROOF: the hosts read alike (mc.k1): up to the changed char the `[` drop and, after it, the `]` drop and the lowercasing treat both texts the same, and the two chars lower alike (mc.k2).

import Base
import ../../bend/mcp_url.bend as Mu
import ../../laws/mcp_url.bend as McpUrl
import ./base/text.bend as LT

# the lowercased text after the trailing `]`s drop, of x then u b and x then l b
def mc.k2.at(g: Bool, r1: String, r2: String, +c: Char, e: {String.to_lower(r1) == String.to_lower(r2) : String}) -> {String.to_lower(Mu.drop_close.at(g, c, r1)) == String.to_lower(Mu.drop_close.at(g, c, r2)) : String}:
  match g:
    case False{}:
      Equal.cong(String, String, z => SCon{Char.to_lower(c), z}, String.to_lower(r1), String.to_lower(r2), e)
    case True{}:
      match r1:
        case SNil{}:
          match r2:
            case SNil{}:
              {==}
            case SCon{+x, +u}:
              LT.mt.nil_cons({String.to_lower(Mu.drop_close.at(True{}, c, SNil{})) == String.to_lower(Mu.drop_close.at(True{}, c, SCon{x, u})) : String}, Char.to_lower(x), String.to_lower(u), e)
        case SCon{+x, +u}:
          match r2:
            case SNil{}:
              LT.mt.nil_cons({String.to_lower(Mu.drop_close.at(True{}, c, SCon{x, u})) == String.to_lower(Mu.drop_close.at(True{}, c, SNil{})) : String}, Char.to_lower(x), String.to_lower(u), Equal.sym(String, SCon{Char.to_lower(x), String.to_lower(u)}, SNil{}, e))
            case SCon{+y, +v}:
              Equal.cong(String, String, z => SCon{Char.to_lower(c), z}, String.to_lower(SCon{x, u}), String.to_lower(SCon{y, v}), e)

def mc.k2(x: String, +u: Char, +l: Char, +b: String, same: {Char.to_lower(u) == Char.to_lower(l) : Char}, nuc: {Char.is_eq(u, ']') == False{} : Bool}, nlc: {Char.is_eq(l, ']') == False{} : Bool}) -> {String.to_lower(Mu.drop_close(String.append(x, SCon{u, b}))) == String.to_lower(Mu.drop_close(String.append(x, SCon{l, b}))) : String}:
  match x:
    case SNil{}:
      %Equal.sym(Bool, Char.is_eq(u, ']'), False{}, nuc) : {String.to_lower(Mu.drop_close.at(_, u, Mu.drop_close(b))) == String.to_lower(Mu.drop_close(SCon{l, b})) : String}
      %Equal.sym(Bool, Char.is_eq(l, ']'), False{}, nlc) : {String.to_lower(SCon{u, Mu.drop_close(b)}) == String.to_lower(Mu.drop_close.at(_, l, Mu.drop_close(b))) : String}
      Equal.cong(Char, String, z => SCon{z, String.to_lower(Mu.drop_close(b))}, Char.to_lower(u), Char.to_lower(l), same)
    case SCon{+c, +r}:
      mc.k2.at(Char.is_eq(c, ']'), Mu.drop_close(String.append(r, SCon{u, b})), Mu.drop_close(String.append(r, SCon{l, b})), c, mc.k2(r, u, l, b, same, nuc, nlc))

def mc.k1.at(g: Bool, +c: Char, +r: String, +u: Char, +l: Char, +b: String, same: {Char.to_lower(u) == Char.to_lower(l) : Char}, nuc: {Char.is_eq(u, ']') == False{} : Bool}, nlc: {Char.is_eq(l, ']') == False{} : Bool}, ih: {Mu.bare(String.append(r, SCon{u, b})) == Mu.bare(String.append(r, SCon{l, b})) : String}) -> {String.to_lower(Mu.drop_close(Mu.drop_open.at(g, c, String.append(r, SCon{u, b}), Mu.drop_open(String.append(r, SCon{u, b}))))) == String.to_lower(Mu.drop_close(Mu.drop_open.at(g, c, String.append(r, SCon{l, b}), Mu.drop_open(String.append(r, SCon{l, b}))))) : String}:
  match g:
    case True{}:
      ih
    case False{}:
      mc.k2(SCon{c, r}, u, l, b, same, nuc, nlc)

# the host as read, of a then u b and a then l b
def mc.k1(a: String, +u: Char, +l: Char, +b: String, +same: {Char.to_lower(u) == Char.to_lower(l) : Char}, nuo: {Char.is_eq(u, '[') == False{} : Bool}, nlo: {Char.is_eq(l, '[') == False{} : Bool}, +nuc: {Char.is_eq(u, ']') == False{} : Bool}, +nlc: {Char.is_eq(l, ']') == False{} : Bool}) -> {Mu.bare(String.append(a, SCon{u, b})) == Mu.bare(String.append(a, SCon{l, b})) : String}:
  match a:
    case SNil{}:
      %Equal.sym(Bool, Char.is_eq(u, '['), False{}, nuo) : {String.to_lower(Mu.drop_close(Mu.drop_open.at(_, u, b, Mu.drop_open(b)))) == String.to_lower(Mu.drop_close(Mu.drop_open(SCon{l, b}))) : String}
      %Equal.sym(Bool, Char.is_eq(l, '['), False{}, nlo) : {String.to_lower(Mu.drop_close(SCon{u, b})) == String.to_lower(Mu.drop_close(Mu.drop_open.at(_, l, b, Mu.drop_open(b)))) : String}
      mc.k2(SNil{}, u, l, b, same, nuc, nlc)
    case SCon{+c, +r}:
      mc.k1.at(Char.is_eq(c, '['), c, r, u, l, b, same, nuc, nlc, mc.k1(r, u, l, b, same, nuo, nlo, nuc, nlc))

def McpUrl.mcp_url_case(a, u, l, b, same, nu, nl):
  +nu0 = nu
  +nl0 = nl
  LT.mt.same(String.append(a, SCon{u, b}), String.append(a, SCon{l, b}), mc.k1(a, u, l, b, same, LT.mt.or_fl(Char.is_eq(u, '['), Char.is_eq(u, ']'), nu0), LT.mt.or_fl(Char.is_eq(l, '['), Char.is_eq(l, ']'), nl0), LT.mt.or_fr(Char.is_eq(u, '['), Char.is_eq(u, ']'), nu0), LT.mt.or_fr(Char.is_eq(l, '['), Char.is_eq(l, ']'), nl0)))
