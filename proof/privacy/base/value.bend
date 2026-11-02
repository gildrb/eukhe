# eukhe: lemmas shared by the proofs of area privacy, section ip: the
# value the IPv6 grammar computes for an address is the spec's, and so is
# the test for a value that reaches no one

import Base
import ../../../bend/privacy/ip.bend as Ip
import ../../../spec/harness/privacy.bend as S
import ./none.bend as LNn

def pvl.hexs(gs: List<&2, String>) -> {Ip.hexs(gs) == S.hexs(gs) : String}:
  match gs:
    case Nil{}:
      {==}
    case +g <> rest:
      %pvl.hexs(rest) : {String.append(Ip.pad(g), Ip.hexs(rest)) == String.append(S.pad(g), _) : String}
      {==}

def pvl.dval(s: String, acc: U32) -> {Ip.dval(s, acc) == S.dval(s, acc) : U32}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      match c:
        case Chr{x}:
          pvl.dval(t, U32.add(U32.mul(acc, 10), U32.sub(x, 48)))

def pvl.hexq(q: Ip.Quad) -> {Ip.hexq(q) == S.hexq(q) : String}:
  match q:
    case Ip.Quad{+a, +b, +c, +d}:
      %pvl.dval(a, 0) : {Ip.hexq(Ip.Quad{a, b, c, d}) == S.byte(_, S.byte(S.dval(b, 0), S.byte(S.dval(c, 0), S.byte(S.dval(d, 0), SNil{})))) : String}
      %pvl.dval(b, 0) : {Ip.hexq(Ip.Quad{a, b, c, d}) == S.byte(Ip.dval(a, 0), S.byte(_, S.byte(S.dval(c, 0), S.byte(S.dval(d, 0), SNil{})))) : String}
      %pvl.dval(c, 0) : {Ip.hexq(Ip.Quad{a, b, c, d}) == S.byte(Ip.dval(a, 0), S.byte(Ip.dval(b, 0), S.byte(_, S.byte(S.dval(d, 0), SNil{})))) : String}
      %pvl.dval(d, 0) : {Ip.hexq(Ip.Quad{a, b, c, d}) == S.byte(Ip.dval(a, 0), S.byte(Ip.dval(b, 0), S.byte(Ip.dval(c, 0), S.byte(_, SNil{})))) : String}
      {==}

def pvl.mhexq(q: Maybe<&2, Ip.Quad>) -> {Ip.mhexq(q) == S.mhexq(q) : String}:
  match q:
    case None{}:
      {==}
    case Some{x}:
      pvl.hexq(x)

# what an IPv4 adds to the count: two
def pvl.qn(q: Maybe<&2, Ip.Quad>) -> {Ip.Quad.n(q) == List.length(&2, String, List.append(&2, String, S.quad_items(q), S.quad_items(q))) : Nat}:
  match q:
    case None{}:
      {==}
    case Some{x}:
      {==}

def pvl.value6(a: Ip.Addr) -> {Ip.value6(a) == S.value6(a) : String}:
  match a:
    case Ip.Full{+gs, +q}:
      %pvl.hexs(gs) : {String.append(Ip.hexs(gs), Ip.mhexq(q)) == String.append(_, S.mhexq(q)) : String}
      %pvl.mhexq(q) : {String.append(Ip.hexs(gs), Ip.mhexq(q)) == String.append(Ip.hexs(gs), _) : String}
      {==}
    case Ip.Gap{+l, +r, +q}:
      +k = Nat.add(List.length(&2, String, l), List.length(&2, String, r))
      %pvl.qn(q) : {Ip.value6(Ip.Gap{l, r, q}) == String.append(S.hexs(List.append(&2, String, l, List.append(&2, String, List.replicate(String, Nat.sub(8n, Nat.add(k, _)), "0"), r))), S.mhexq(q)) : String}
      %pvl.hexs(List.append(&2, String, l, List.append(&2, String, List.replicate(String, Nat.sub(8n, Nat.add(k, Ip.Quad.n(q))), "0"), r))) : {Ip.value6(Ip.Gap{l, r, q}) == String.append(_, S.mhexq(q)) : String}
      %pvl.mhexq(q) : {Ip.value6(Ip.Gap{l, r, q}) == String.append(Ip.hexs(List.append(&2, String, l, List.append(&2, String, List.replicate(String, Nat.sub(8n, Nat.add(k, Ip.Quad.n(q))), "0"), r))), _) : String}
      {==}

def pvl.special6(+v: String) -> {Ip.special6(v) == S.special6(v) : Bool}:
  {==}

# an empty text is no other: anything follows
def pvl.SIf(s: String, G: Type) -> Type:
  match s:
    case SNil{}:
      Unit
    case SCon{c, u}:
      G

# a value that starts with nine zero digits is no IPv4's eight: the
# address is no IPv4 alone
def pvl.isq(a: Ip.Addr, -w: String, e: {S.value6(a) == String.append("000000000", w) : String}) -> {LNn.pnn.isq(a) == False{} : Bool}:
  match a:
    case Ip.Full{gs, q}:
      match gs:
        case Nil{}:
          match q:
            case None{}:
              {==}
            case Some{x}:
              match x:
                case Ip.Quad{qa, qb, qc, qd}:
                  +X = {Ip.Full{Nil{}, Some{Ip.Quad{qa, qb, qc, qd}}} : Ip.Addr}
                  %Equal.cong(String, String, s => String.drop(s, 8n), S.value6(X), String.append("000000000", w), e) : pvl.SIf(_, {LNn.pnn.isq(X) == False{} : Bool})
                  Unit{}
        case g <> rest:
          {==}
    case Ip.Gap{l, r, q}:
      {==}
