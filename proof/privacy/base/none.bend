# eukhe: lemmas shared by the proofs of area privacy, section ip: texts
# the IPv4 grammar reads no quad from (a hex group, then no `.`; three
# octets, then no `.`)

import Base
import ../../../bend/privacy/ip.bend as Ip
import ../../../bend/privacy/context.bend as Cx
import ../../../spec/harness/privacy.bend as S
import ./chars.bend as LIp
import ./read.bend as LRd
import ./quad.bend as LQd

# no `.` first
def pnn.nodot(ys: List<&2, Ip.Sym>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case y <> rest:
      match y:
        case Ip.Dot{}:
          False{}
        case Ip.Dig{c}:
          True{}
        case Ip.Hx{c}:
          True{}
        case Ip.Col{}:
          True{}
        case Ip.Let{}:
          True{}
        case Ip.Und{}:
          True{}
        case Ip.Dash{}:
          True{}
        case Ip.Oth{}:
          True{}

def pnn.dot(rest: List<&2, Ip.Sym>, h: {pnn.nodot(rest) == True{} : Bool}) -> {Ip.dot_oct(rest) == None{} : Maybe<&2, Ip.Cut>}:
  match rest:
    case Nil{}:
      {==}
    case y <> t:
      match y:
        case Ip.Dot{}:
          LIp.pip.absurd_ft({Ip.dot_oct(Ip.Dot{} <> t) == None{} : Maybe<&2, Ip.Cut>}, h)
        case Ip.Dig{c}:
          {==}
        case Ip.Hx{c}:
          {==}
        case Ip.Col{}:
          {==}
        case Ip.Let{}:
          {==}
        case Ip.Und{}:
          {==}
        case Ip.Dash{}:
          {==}
        case Ip.Oth{}:
          {==}

def pnn.ok(b: Bool, +ds: String, +rest: List<&2, Ip.Sym>, +h: {pnn.nodot(rest) == True{} : Bool}) -> {Ip.quad.a(Ip.oct.ok(b, ds, rest)) == None{} : Maybe<&2, Ip.QCut>}:
  match b:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(Maybe<&2, Ip.Cut>, Ip.dot_oct(rest), None{}, pnn.dot(rest, h)) : {Ip.quad.b(ds, _) == None{} : Maybe<&2, Ip.QCut>}
      {==}

def pnn.qa(r: Ip.Cut, +h: {pnn.nodot(LRd.prd.cut_rest(r)) == True{} : Bool}) -> {Ip.quad.a(Ip.oct.of(r)) == None{} : Maybe<&2, Ip.QCut>}:
  match r:
    case Ip.Cut{+ds, +rest}:
      pnn.ok(Ip.oct_ok(ds), ds, rest, h)

def pnn.cons_rest(-c: Char, r: Ip.Cut) -> {LRd.prd.cut_rest(Ip.run.cons(c, r)) == LRd.prd.cut_rest(r) : List<&2, Ip.Sym>}:
  match r:
    case Ip.Cut{s, rest}:
      {==}

def pnn.drun_c(+c: Char, e: Either<&1, &1, {Ip.Sym.of(c) == Ip.Dig{c} : Ip.Sym}, {Ip.Sym.of(c) == Ip.Hx{c} : Ip.Sym}>, +ys: List<&2, Ip.Sym>, +ih: {pnn.nodot(LRd.prd.cut_rest(Ip.drun(ys))) == True{} : Bool}) -> {pnn.nodot(LRd.prd.cut_rest(Ip.drun(Ip.Sym.of(c) <> ys))) == True{} : Bool}:
  match e:
    case Inl{+d}:
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Dig{c}, d) : {pnn.nodot(LRd.prd.cut_rest(Ip.drun(_ <> ys))) == True{} : Bool}
      %Equal.sym(List<&2, Ip.Sym>, LRd.prd.cut_rest(Ip.run.cons(c, Ip.drun(ys))), LRd.prd.cut_rest(Ip.drun(ys)), pnn.cons_rest(c, Ip.drun(ys))) : {pnn.nodot(_) == True{} : Bool}
      ih
    case Inr{+x}:
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Hx{c}, x) : {pnn.nodot(LRd.prd.cut_rest(Ip.drun(_ <> ys))) == True{} : Bool}
      {==}

# the digit run over a hex text, then Y (no digit, no `.` first), stops
# before no `.`
def pnn.drun(g: String, +Y: String, +hg: {S.all_hex(g) == True{} : Bool}, +h4: {S.stops4(Y) == True{} : Bool}, +hd: {pnn.nodot(Ip.Sym.list(Y)) == True{} : Bool}) -> {pnn.nodot(LRd.prd.cut_rest(Ip.drun(Ip.Sym.list(String.append(g, Y))))) == True{} : Bool}:
  match g:
    case SNil{}:
      %Equal.sym(Ip.Cut, Ip.drun(Ip.Sym.list(Y)), Ip.Cut{SNil{}, Ip.Sym.list(Y)}, LRd.prd.drun_end4(Y, h4)) : {pnn.nodot(LRd.prd.cut_rest(_)) == True{} : Bool}
      hd
    case SCon{+c, +g2}:
      +hc = LIp.pip.and_l(S.hex(c), S.all_hex(g2), hg)
      +hr = LIp.pip.and_r(S.hex(c), S.all_hex(g2), hg)
      pnn.drun_c(c, LRd.prd.hex_sym(c, hc), Ip.Sym.list(String.append(g2, Y)), pnn.drun(g2, Y, hr, h4, hd))

# a hex text, then Y: no quad
def pnn.hex_quad(+g: String, +Y: String, +hg: {S.all_hex(g) == True{} : Bool}, +h4: {S.stops4(Y) == True{} : Bool}, +hd: {pnn.nodot(Ip.Sym.list(Y)) == True{} : Bool}) -> {Ip.quad(Ip.Sym.list(String.append(g, Y))) == None{} : Maybe<&2, Ip.QCut>}:
  pnn.qa(Ip.drun(Ip.Sym.list(String.append(g, Y))), pnn.drun(g, Y, hg, h4, hd))

# no quad: no IPv4
def pnn.v4(b: Bool, +X: String, +h: {Ip.quad(Ip.Sym.list(X)) == None{} : Maybe<&2, Ip.QCut>}) -> {Ip.v4.go(b, X) == None{} : Maybe<&2, Nat>}:
  match b:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(Maybe<&2, Ip.QCut>, Ip.quad(Ip.Sym.list(X)), None{}, h) : {Ip.v4.got(List.length(&2, Ip.Sym, Ip.Sym.list(X)), _) == None{} : Maybe<&2, Nat>}
      {==}

# no quad: no IPv4, whatever comes before
def pnn.v4_at(+before: String, +X: String, +h: {Ip.quad(Ip.Sym.list(X)) == None{} : Maybe<&2, Ip.QCut>}) -> {Ip.v4(before, X) == None{} : Maybe<&2, Nat>}:
  pnn.v4(Bool.and(Ip.edge4(Ip.last2(before, None{}, None{})), Bool.not(Cx.vctx(before))), X, h)

# What follows an address
# -----------------------

def pnn.nodot_y(y: Ip.Sym, -ys: List<&2, Ip.Sym>, +h: {S.k_stop6(LIp.pip.kind(y)) == True{} : Bool}) -> {pnn.nodot(y <> ys) == True{} : Bool}:
  match y:
    case Ip.Dot{}:
      LIp.pip.absurd_ft({pnn.nodot(Ip.Dot{} <> ys) == True{} : Bool}, h)
    case Ip.Dig{c}:
      {==}
    case Ip.Hx{c}:
      {==}
    case Ip.Col{}:
      {==}
    case Ip.Let{}:
      {==}
    case Ip.Und{}:
      {==}
    case Ip.Dash{}:
      {==}
    case Ip.Oth{}:
      {==}

def pnn.stop_nodot(t: String, +h: {S.stops6(t) == True{} : Bool}) -> {pnn.nodot(Ip.Sym.list(t)) == True{} : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, u}:
      pnn.nodot_y(Ip.Sym.of(c), Ip.Sym.list(u), LRd.prd.stop_kind(c, h))

# no word char, `:` or `.` does not go on with an IPv6
def pnn.free_stop_k(k: S.CKind, +h: {S.k_free(k) == True{} : Bool}) -> {S.k_stop6(k) == True{} : Bool}:
  match k:
    case S.KDash{}:
      {==}
    case S.KOth{}:
      {==}
    case S.KDec{}:
      LIp.pip.absurd_ft({S.k_stop6(S.KDec{}) == True{} : Bool}, h)
    case S.KHex{}:
      LIp.pip.absurd_ft({S.k_stop6(S.KHex{}) == True{} : Bool}, h)
    case S.KLet{}:
      {==}
    case S.KUnd{}:
      {==}
    case S.KCol{}:
      LIp.pip.absurd_ft({S.k_stop6(S.KCol{}) == True{} : Bool}, h)
    case S.KDot{}:
      LIp.pip.absurd_ft({S.k_stop6(S.KDot{}) == True{} : Bool}, h)

def pnn.free_stop(t: String, +h: {S.free(S.first(t)) == True{} : Bool}) -> {S.stops6(t) == True{} : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, u}:
      pnn.free_stop_k(S.kind(c), h)

# The text an address writes
# --------------------------

# an IPv4 alone first
def pnn.isq(a: Ip.Addr) -> Bool:
  match a:
    case Ip.Full{gs, q}:
      match gs:
        case Nil{}:
          Maybe.is_some(&2, Ip.Quad, q)
        case g <> rest:
          False{}
    case Ip.Gap{l, r, q}:
      False{}

# items joined after a hex group, then Y: no quad
def pnn.join_quad(+g: String, rest: List<&2, String>, +Y: String, +hg: {S.all_hex(g) == True{} : Bool}, +h4: {S.stops4(Y) == True{} : Bool}, +hd: {pnn.nodot(Ip.Sym.list(Y)) == True{} : Bool}) -> {Ip.quad(Ip.Sym.list(S.join(g <> rest, Y))) == None{} : Maybe<&2, Ip.QCut>}:
  match rest:
    case Nil{}:
      pnn.hex_quad(g, Y, hg, h4, hd)
    case +y <> +ys:
      pnn.hex_quad(g, SCon{':', S.join(y <> ys, Y)}, hg, {==}, {==})

def pnn.grp_hex(+g: String, -rest: List<&2, String>, +h: {S.groups(g <> rest) == True{} : Bool}) -> {S.all_hex(g) == True{} : Bool}:
  LIp.pip.and_l(S.all_hex(g), Bool.and(Nat.is_le(1n, String.length(g)), Nat.is_le(String.length(g), 4n)), LIp.pip.and_l(S.group(g), S.groups(rest), h))

# the text a shaped address writes that is not an IPv4 alone: no quad
def pnn.text6(a: Ip.Addr, +t: String, +sh: {S.shaped(a) == True{} : Bool}, +st: {S.stops6(t) == True{} : Bool}, +hn: {pnn.isq(a) == False{} : Bool}) -> {Ip.quad(Ip.Sym.list(S.text6(a, t))) == None{} : Maybe<&2, Ip.QCut>}:
  match a:
    case Ip.Full{gs, +q}:
      match gs:
        case Nil{}:
          match q:
            case None{}:
              pnn.hex_quad(SNil{}, t, {==}, LRd.prd.stops6_4(t, st), pnn.stop_nodot(t, st))
            case Some{x}:
              LIp.pip.absurd_ft({Ip.quad(Ip.Sym.list(S.text6(Ip.Full{Nil{}, Some{x}}, t))) == None{} : Maybe<&2, Ip.QCut>}, Equal.sym(Bool, True{}, False{}, hn))
        case +g <> +rest:
          +hg = pnn.grp_hex(g, rest, LIp.pip.and_l(S.groups(g <> rest), S.mquad_ok(q), sh))
          pnn.join_quad(g, List.append(&2, String, rest, S.quad_items(q)), t, hg, LRd.prd.stops6_4(t, st), pnn.stop_nodot(t, st))
    case Ip.Gap{l, +r, +q}:
      match l:
        case Nil{}:
          pnn.hex_quad(SNil{}, S.text6(Ip.Gap{Nil{}, r, q}, t), {==}, {==}, {==})
        case +g <> +rest:
          +hg = pnn.grp_hex(g, rest, LIp.pip.and_l(S.groups(g <> rest), S.groups(r), LIp.pip.and_l(Bool.and(S.groups(g <> rest), S.groups(r)), S.mquad_ok(q), sh)))
          pnn.join_quad(g, rest, SCon{':', SCon{':', S.join(List.append(&2, String, r, S.quad_items(q)), t)}}, hg, {==}, {==})
