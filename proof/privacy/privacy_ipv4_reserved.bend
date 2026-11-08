# eukhe: the proof of LAW privacy_ipv4_reserved
#
# PROOF: the first octet is read whole (its digits, then the dot), so the
# IPv6 reader turns to an IPv4 from the start: two groups, never counted
# (prs.v6_none); the IPv4 grammar reads the first octet 0, 127 or 255 and
# refuses whatever the other three octets are (prs.v4b).

import Base
import ../../bend/privacy/ip.bend as Ip
import ../../bend/privacy/context.bend as Cx
import ../../laws/privacy/ip.bend as PrivacyIp

# with an IPv4 at the start, the IPv6 reader answers none
def prs.v6_none(-n: Nat, m: Maybe<&2, Ip.QCut>) -> {Ip.v6.got(n, Ip.quad_end(Ip.Acc{False{}, Nil{}, Nil{}}, m)) == None{} : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{r}:
      match r:
        case Ip.QCut{q, rest}:
          {==}

def prs.v4d(-n: Nat, +a: String, -b: String, -c: String, +fa: {Bool.not(Bool.or(String.eq(a, "0"), Bool.or(String.eq(a, "127"), String.eq(a, "255")))) == False{} : Bool}, m: Maybe<&2, Ip.Cut>) -> {Ip.v4.got(n, Ip.quad.d(a, b, c, m)) == None{} : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{r}:
      match r:
        case Ip.Cut{d, +rest}:
          %Equal.sym(Bool, Bool.not(Bool.or(String.eq(a, "0"), Bool.or(String.eq(a, "127"), String.eq(a, "255")))), False{}, fa) : {Ip.ans(Bool.and(_, Ip.after4(rest)), Nat.sub(n, List.length(&2, Ip.Sym, rest))) == None{} : Maybe<&2, Nat>}
          {==}

def prs.v4c(-n: Nat, +a: String, -b: String, +fa: {Bool.not(Bool.or(String.eq(a, "0"), Bool.or(String.eq(a, "127"), String.eq(a, "255")))) == False{} : Bool}, m: Maybe<&2, Ip.Cut>) -> {Ip.v4.got(n, Ip.quad.c(a, b, m)) == None{} : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{r}:
      match r:
        case Ip.Cut{c, rest}:
          prs.v4d(n, a, b, c, fa, Ip.dot_oct(rest))

def prs.v4b(-n: Nat, +a: String, +fa: {Bool.not(Bool.or(String.eq(a, "0"), Bool.or(String.eq(a, "127"), String.eq(a, "255")))) == False{} : Bool}, m: Maybe<&2, Ip.Cut>) -> {Ip.v4.got(n, Ip.quad.b(a, m)) == None{} : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{r}:
      match r:
        case Ip.Cut{b, rest}:
          prs.v4c(n, a, b, fa, Ip.dot_oct(rest))

def prs.v6_0(ok: Bool, +X: String) -> {Ip.v6.go(ok, SCon{'0', SCon{'.', X}}) == None{} : Maybe<&2, Nat>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      prs.v6_none(List.length(&2, Ip.Sym, Ip.Sym.list(SCon{'0', SCon{'.', X}})), Ip.quad(Ip.Sym.list(SCon{'0', SCon{'.', X}})))

def prs.v4_0(ok: Bool, +X: String) -> {Ip.v4.go(ok, SCon{'0', SCon{'.', X}}) == None{} : Maybe<&2, Nat>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      prs.v4b(List.length(&2, Ip.Sym, Ip.Sym.list(SCon{'0', SCon{'.', X}})), "0", {==}, Ip.oct(Ip.Sym.list(X)))

def prs.ip_0(+before: String, +X: String) -> {Ip.ip(before, String.append("0", SCon{'.', X})) == None{} : Maybe<&2, Nat>}:
  %Equal.sym(Maybe<&2, Nat>, Ip.v6.go(Ip.edge6(Ip.last(before)), SCon{'0', SCon{'.', X}}), None{}, prs.v6_0(Ip.edge6(Ip.last(before)), X)) : {Maybe.or(&2, Nat, _, Ip.v4(before, SCon{'0', SCon{'.', X}})) == None{} : Maybe<&2, Nat>}
  %Equal.sym(Maybe<&2, Nat>, Ip.v4.go(Bool.and(Ip.edge4(Ip.last2(before, None{}, None{})), Bool.not(Cx.vctx(before))), SCon{'0', SCon{'.', X}}), None{}, prs.v4_0(Bool.and(Ip.edge4(Ip.last2(before, None{}, None{})), Bool.not(Cx.vctx(before))), X)) : {Maybe.or(&2, Nat, None{}, _) == None{} : Maybe<&2, Nat>}
  {==}

def prs.v6_127(ok: Bool, +X: String) -> {Ip.v6.go(ok, SCon{'1', SCon{'2', SCon{'7', SCon{'.', X}}}}) == None{} : Maybe<&2, Nat>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      prs.v6_none(List.length(&2, Ip.Sym, Ip.Sym.list(SCon{'1', SCon{'2', SCon{'7', SCon{'.', X}}}})), Ip.quad(Ip.Sym.list(SCon{'1', SCon{'2', SCon{'7', SCon{'.', X}}}})))

def prs.v4_127(ok: Bool, +X: String) -> {Ip.v4.go(ok, SCon{'1', SCon{'2', SCon{'7', SCon{'.', X}}}}) == None{} : Maybe<&2, Nat>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      prs.v4b(List.length(&2, Ip.Sym, Ip.Sym.list(SCon{'1', SCon{'2', SCon{'7', SCon{'.', X}}}})), "127", {==}, Ip.oct(Ip.Sym.list(X)))

def prs.ip_127(+before: String, +X: String) -> {Ip.ip(before, String.append("127", SCon{'.', X})) == None{} : Maybe<&2, Nat>}:
  %Equal.sym(Maybe<&2, Nat>, Ip.v6.go(Ip.edge6(Ip.last(before)), SCon{'1', SCon{'2', SCon{'7', SCon{'.', X}}}}), None{}, prs.v6_127(Ip.edge6(Ip.last(before)), X)) : {Maybe.or(&2, Nat, _, Ip.v4(before, SCon{'1', SCon{'2', SCon{'7', SCon{'.', X}}}})) == None{} : Maybe<&2, Nat>}
  %Equal.sym(Maybe<&2, Nat>, Ip.v4.go(Bool.and(Ip.edge4(Ip.last2(before, None{}, None{})), Bool.not(Cx.vctx(before))), SCon{'1', SCon{'2', SCon{'7', SCon{'.', X}}}}), None{}, prs.v4_127(Bool.and(Ip.edge4(Ip.last2(before, None{}, None{})), Bool.not(Cx.vctx(before))), X)) : {Maybe.or(&2, Nat, None{}, _) == None{} : Maybe<&2, Nat>}
  {==}

def prs.v6_255(ok: Bool, +X: String) -> {Ip.v6.go(ok, SCon{'2', SCon{'5', SCon{'5', SCon{'.', X}}}}) == None{} : Maybe<&2, Nat>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      prs.v6_none(List.length(&2, Ip.Sym, Ip.Sym.list(SCon{'2', SCon{'5', SCon{'5', SCon{'.', X}}}})), Ip.quad(Ip.Sym.list(SCon{'2', SCon{'5', SCon{'5', SCon{'.', X}}}})))

def prs.v4_255(ok: Bool, +X: String) -> {Ip.v4.go(ok, SCon{'2', SCon{'5', SCon{'5', SCon{'.', X}}}}) == None{} : Maybe<&2, Nat>}:
  match ok:
    case False{}:
      {==}
    case True{}:
      prs.v4b(List.length(&2, Ip.Sym, Ip.Sym.list(SCon{'2', SCon{'5', SCon{'5', SCon{'.', X}}}})), "255", {==}, Ip.oct(Ip.Sym.list(X)))

def prs.ip_255(+before: String, +X: String) -> {Ip.ip(before, String.append("255", SCon{'.', X})) == None{} : Maybe<&2, Nat>}:
  %Equal.sym(Maybe<&2, Nat>, Ip.v6.go(Ip.edge6(Ip.last(before)), SCon{'2', SCon{'5', SCon{'5', SCon{'.', X}}}}), None{}, prs.v6_255(Ip.edge6(Ip.last(before)), X)) : {Maybe.or(&2, Nat, _, Ip.v4(before, SCon{'2', SCon{'5', SCon{'5', SCon{'.', X}}}})) == None{} : Maybe<&2, Nat>}
  %Equal.sym(Maybe<&2, Nat>, Ip.v4.go(Bool.and(Ip.edge4(Ip.last2(before, None{}, None{})), Bool.not(Cx.vctx(before))), SCon{'2', SCon{'5', SCon{'5', SCon{'.', X}}}}), None{}, prs.v4_255(Bool.and(Ip.edge4(Ip.last2(before, None{}, None{})), Bool.not(Cx.vctx(before))), X)) : {Maybe.or(&2, Nat, None{}, _) == None{} : Maybe<&2, Nat>}
  {==}

def PrivacyIp.privacy_ipv4_reserved(b, c, d, before, t):
  (prs.ip_0(before, String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})), (prs.ip_127(before, String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})})), prs.ip_255(before, String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t)})}))))
