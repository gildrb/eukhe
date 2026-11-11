# eukhe: the proof of LAW mcp_url_name_passes
#
# PROOF: a lowercase host without brackets reads as itself (mn.open, mn.close); not a localhost name, of other than four parts it is no IPv4 quad (mn.parts), and without `:` no IPv6 address (mn.colon).

import Base
import ../../bend/mcp_url.bend as Mu
import ../../laws/mcp_url.bend as McpUrl
import ./base/text.bend as LT

def mn.open(x: String, h: {McpUrl.mu_lacks(x, '[') == True{} : Bool}) -> {Mu.drop_open(x) == x : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Char.is_eq(c, '['), False{}, LT.mt.not_t(Char.is_eq(c, '['), LT.mt.and_l(Bool.not(Char.is_eq(c, '[')), McpUrl.mu_lacks(t, '['), h))) : {Mu.drop_open.at(_, c, t, Mu.drop_open(t)) == SCon{c, t} : String}
      {==}

def mn.close(x: String, +h: {McpUrl.mu_lacks(x, ']') == True{} : Bool}) -> {Mu.drop_close(x) == x : String}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Char.is_eq(c, ']'), False{}, LT.mt.not_t(Char.is_eq(c, ']'), LT.mt.and_l(Bool.not(Char.is_eq(c, ']')), McpUrl.mu_lacks(t, ']'), h))) : {Mu.drop_close.at(_, c, Mu.drop_close(t)) == SCon{c, t} : String}
      Equal.cong(String, String, z => SCon{c, z}, Mu.drop_close(t), t, mn.close(t, LT.mt.and_r(Bool.not(Char.is_eq(c, ']')), McpUrl.mu_lacks(t, ']'), h)))

def mn.colon(x: String, +h: {McpUrl.mu_lacks(x, ':') == True{} : Bool}) -> {String.contains(x, ":") == False{} : Bool}:
  match x:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Char.is_eq(c, ':'), False{}, LT.mt.not_t(Char.is_eq(c, ':'), LT.mt.and_l(Bool.not(Char.is_eq(c, ':')), McpUrl.mu_lacks(t, ':'), h))) : {String.contains.if(t, ":", String.starts_with.go.if(SNil{}, t, _)) == False{} : Bool}
      mn.colon(t, LT.mt.and_r(Bool.not(Char.is_eq(c, ':')), McpUrl.mu_lacks(t, ':'), h))

def mn.parts(ps: List<&2, String>, h: {Nat.is_eq(List.length(&2, String, ps), 4n) == False{} : Bool}) -> {Mu.v4.parts(ps) == Mu.V4No{} : Mu.V4}:
  match ps:
    case Nil{}:
      {==}
    case p <> t1:
      match t1:
        case Nil{}:
          {==}
        case q <> t2:
          match t2:
            case Nil{}:
              {==}
            case r <> t3:
              match t3:
                case Nil{}:
                  {==}
                case s <> t4:
                  match t4:
                    case Nil{}:
                      LT.mt.absurd({Mu.v4.parts([p, q, r, s]) == Mu.V4No{} : Mu.V4}, h)
                    case x <> t5:
                      {==}

def McpUrl.mcp_url_name_passes(x, plain, lower, named, parts):
  +p0 = plain
  +p1 = LT.mt.and_r(McpUrl.mu_lacks(x, '['), Bool.and(McpUrl.mu_lacks(x, ']'), McpUrl.mu_lacks(x, ':')), p0)
  +EB = Equal.trans(String, Mu.bare(x), String.to_lower(x), x, Equal.cong(String, String, z => String.to_lower(z), Mu.drop_close(Mu.drop_open(x)), x, Equal.trans(String, Mu.drop_close(Mu.drop_open(x)), Mu.drop_close(x), x, Equal.cong(String, String, z => Mu.drop_close(z), Mu.drop_open(x), x, mn.open(x, LT.mt.and_l(McpUrl.mu_lacks(x, '['), Bool.and(McpUrl.mu_lacks(x, ']'), McpUrl.mu_lacks(x, ':')), p0))), mn.close(x, LT.mt.and_l(McpUrl.mu_lacks(x, ']'), McpUrl.mu_lacks(x, ':'), p1)))), lower)
  %Equal.sym(String, Mu.bare(x), x, EB) : {Mu.refused.at(Bool.or(String.eq(_, "localhost"), String.ends_with(_, ".localhost")), _) == False{} : Bool}
  %Equal.sym(Bool, Bool.or(String.eq(x, "localhost"), String.ends_with(x, ".localhost")), False{}, named) : {Mu.refused.at(_, x) == False{} : Bool}
  %Equal.sym(Mu.V4, Mu.v4.parts(String.split(x, '.')), Mu.V4No{}, mn.parts(String.split(x, '.'), parts)) : {Mu.after_v4(_, x) == False{} : Bool}
  %Equal.sym(Bool, String.contains(x, ":"), False{}, mn.colon(x, LT.mt.and_r(McpUrl.mu_lacks(x, ']'), McpUrl.mu_lacks(x, ':'), p1))) : {Mu.v6(_, x) == False{} : Bool}
  {==}
