# eukhe: lemmas shared by the proofs of area privacy, section ip: what the
# IPv4 grammar reads is what the spec writes (a digit run, an octet, a dot
# and an octet, four octets), followed by the rest of the text

import Base
import ../../../bend/privacy/ip.bend as Ip
import ../../../bend/privacy/context.bend as Cx
import ../../../spec/harness/privacy.bend as S
import ./chars.bend as LIp
import ./read.bend as LRd
import ./quad.bend as LQd
import ./none.bend as LNn
import ./cls.bend as LCl

# Digit runs
# ----------

# a run r of s: s is its digits, then t, the rest of r
def pqi.DP(s: String, r: Ip.Cut) -> Type:
  match r:
    case Ip.Cut{d, rest}:
      Sigma<&1, &1, String, t => {s == String.append(d, t) : String} & ({rest == Ip.Sym.list(t) : List<&2, Ip.Sym>} & ({S.all_dec(d) == True{} : Bool} & {S.stops4(t) == True{} : Bool}))>

def pqi.cons(+c: Char, -u: String, r: Ip.Cut, ih: pqi.DP(u, r), +hd: {S.dec(c) == True{} : Bool}) -> pqi.DP(SCon{c, u}, Ip.run.cons(c, r)):
  match r:
    case Ip.Cut{+d, rest}:
      (+t, pr) = ih
      (e1, more) = pr
      (e2, ee) = more
      (e3, e4) = ee
      (t, (Equal.cong(String, String, z => SCon{c, z}, u, String.append(d, t), e1), (e2, (LQd.pqd.and_i(S.dec(c), S.all_dec(d), hd, e3), e4))))

def pqi.kd(+c: Char, -y: Ip.Sym, ey: {Ip.Sym.of(c) == y : Ip.Sym}, hk: {S.k_dec(LIp.pip.kind(y)) == False{} : Bool}) -> {S.k_dec(LIp.pip.kind(Ip.Sym.of(c))) == False{} : Bool}:
  %Equal.sym(Ip.Sym, Ip.Sym.of(c), y, ey) : {S.k_dec(LIp.pip.kind(_)) == False{} : Bool}
  hk

def pqi.st4(+c: Char, -u: String, hk: {S.k_dec(LIp.pip.kind(Ip.Sym.of(c))) == False{} : Bool}) -> {S.stops4(SCon{c, u}) == True{} : Bool}:
  %LIp.pip.kind_of(c) : {Bool.not(S.k_dec(_)) == True{} : Bool}
  %Equal.sym(Bool, S.k_dec(LIp.pip.kind(Ip.Sym.of(c))), False{}, hk) : {Bool.not(_) == True{} : Bool}
  {==}

# a char that is no decimal digit ends the run
def pqi.stop4(+c: Char, +u: String, +hk: {S.k_dec(LIp.pip.kind(Ip.Sym.of(c))) == False{} : Bool}) -> pqi.DP(SCon{c, u}, Ip.drun(Ip.Sym.of(c) <> Ip.Sym.list(u))):
  %Equal.sym(Ip.Cut, Ip.drun(Ip.Sym.of(c) <> Ip.Sym.list(u)), Ip.Cut{SNil{}, Ip.Sym.of(c) <> Ip.Sym.list(u)}, LRd.prd.drun_stop(Ip.Sym.of(c), Ip.Sym.list(u), hk)) : pqi.DP(SCon{c, u}, _)
  (SCon{c, u}, ({==}, ({==}, ({==}, pqi.st4(c, u, hk)))))

def pqi.drun_c(+c: Char, +u: String, k: LCl.pcl.C(c, Ip.Sym.of(c)), ih: pqi.DP(u, Ip.drun(Ip.Sym.list(u)))) -> pqi.DP(SCon{c, u}, Ip.drun(Ip.Sym.of(c) <> Ip.Sym.list(u))):
  match k:
    case Inl{p}:
      (ey, hd) = p
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Dig{c}, ey) : pqi.DP(SCon{c, u}, Ip.drun(_ <> Ip.Sym.list(u)))
      pqi.cons(c, u, Ip.drun(Ip.Sym.list(u)), ih, hd)
    case Inr{k2}:
      match k2:
        case Inl{p}:
          (ey, hh) = p
          pqi.stop4(c, u, pqi.kd(c, Ip.Hx{c}, ey, {==}))
        case Inr{k3}:
          match k3:
            case Inl{p}:
              (ey, ec) = p
              pqi.stop4(c, u, pqi.kd(c, Ip.Col{}, ey, {==}))
            case Inr{k4}:
              match k4:
                case Inl{p}:
                  (ey, ec) = p
                  pqi.stop4(c, u, pqi.kd(c, Ip.Dot{}, ey, {==}))
                case Inr{hs}:
                  pqi.stop4(c, u, LRd.prd.stop6_dec(LIp.pip.kind(Ip.Sym.of(c)), hs))

# the digit run of every text
def pqi.drun(s: String) -> pqi.DP(s, Ip.drun(Ip.Sym.list(s))):
  match s:
    case SNil{}:
      (SNil{}, ({==}, ({==}, ({==}, {==}))))
    case SCon{+c, +u}:
      pqi.drun_c(c, u, LCl.pcl.of(c), pqi.drun(u))

# Octets
# ------

# an octet read, then t
def pqi.OP(s: String, m: Maybe<&2, Ip.Cut>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{r}:
      match r:
        case Ip.Cut{o, rest}:
          Sigma<&1, &1, String, t => {s == String.append(o, t) : String} & ({rest == Ip.Sym.list(t) : List<&2, Ip.Sym>} & ({S.octet(o) == True{} : Bool} & {S.stops4(t) == True{} : Bool}))>

def pqi.octet3(a: Char, b: Char, c: Char, +h1: {Ip.oct_ok(SCon{a, SCon{b, SCon{c, SNil{}}}}) == True{} : Bool}, +h2: {S.all_dec(SCon{a, SCon{b, SCon{c, SNil{}}}}) == True{} : Bool}) -> {S.octet(SCon{a, SCon{b, SCon{c, SNil{}}}}) == True{} : Bool}:
  match a b c:
    case Chr{+x} Chr{+y} Chr{+z}:
      +ha = LIp.pip.and_l(S.dec(Chr{x}), Bool.and(S.dec(Chr{y}), Bool.and(S.dec(Chr{z}), True{})), h2)
      +h2b = LIp.pip.and_r(S.dec(Chr{x}), Bool.and(S.dec(Chr{y}), Bool.and(S.dec(Chr{z}), True{})), h2)
      +hb = LIp.pip.and_l(S.dec(Chr{y}), Bool.and(S.dec(Chr{z}), True{}), h2b)
      +hc = LIp.pip.and_l(S.dec(Chr{z}), True{}, LIp.pip.and_r(S.dec(Chr{y}), Bool.and(S.dec(Chr{z}), True{}), h2b))
      +h0 = LIp.pip.and_l(Bool.not(Char.is_eq(Chr{x}, '0')), Ip.le255(Chr{x}, Chr{y}, Chr{z}), h1)
      +hl = LIp.pip.and_r(Bool.not(Char.is_eq(Chr{x}, '0')), Ip.le255(Chr{x}, Chr{y}, Chr{z}), h1)
      LQd.pqd.and_i(Bool.and(Bool.and(S.dec(Chr{x}), S.dec(Chr{y})), Bool.and(S.dec(Chr{z}), Bool.not(Char.is_eq(Chr{x}, '0')))), Ip.le255(Chr{x}, Chr{y}, Chr{z}), LQd.pqd.and_i(Bool.and(S.dec(Chr{x}), S.dec(Chr{y})), Bool.and(S.dec(Chr{z}), Bool.not(Char.is_eq(Chr{x}, '0'))), LQd.pqd.and_i(S.dec(Chr{x}), S.dec(Chr{y}), ha, hb), LQd.pqd.and_i(S.dec(Chr{z}), Bool.not(Char.is_eq(Chr{x}, '0')), hc, h0)), hl)

# the grammar's octet, all decimal digits, is the spec's
def pqi.octet(d: String, +h1: {Ip.oct_ok(d) == True{} : Bool}, +h2: {S.all_dec(d) == True{} : Bool}) -> {S.octet(d) == True{} : Bool}:
  match d:
    case SNil{}:
      LIp.pip.absurd_ft({S.octet(SNil{}) == True{} : Bool}, h1)
    case SCon{+a, t1}:
      match t1:
        case SNil{}:
          LIp.pip.and_l(S.dec(a), True{}, h2)
        case SCon{+b, t2}:
          match t2:
            case SNil{}:
              +ha = LIp.pip.and_l(S.dec(a), Bool.and(S.dec(b), True{}), h2)
              +hb = LIp.pip.and_l(S.dec(b), True{}, LIp.pip.and_r(S.dec(a), Bool.and(S.dec(b), True{}), h2))
              LQd.pqd.and_i(Bool.and(S.dec(a), S.dec(b)), Bool.not(Char.is_eq(a, '0')), LQd.pqd.and_i(S.dec(a), S.dec(b), ha, hb), h1)
            case SCon{+c, t3}:
              match t3:
                case SNil{}:
                  pqi.octet3(a, b, c, h1, h2)
                case SCon{e, t4}:
                  LIp.pip.absurd_ft({S.octet(SCon{a, SCon{b, SCon{c, SCon{e, t4}}}}) == True{} : Bool}, h1)

def pqi.oct_ok(-s: String, +d: String, +rest: List<&2, Ip.Sym>, b: Bool, +eb: {Ip.oct_ok(d) == b : Bool}, dp: pqi.DP(s, Ip.Cut{d, rest})) -> pqi.OP(s, Ip.oct.ok(b, d, rest)):
  match b:
    case False{}:
      Unit{}
    case True{}:
      (+t, pr) = dp
      (e1, more) = pr
      (e2, ee) = more
      (e3, e4) = ee
      (t, (e1, (e2, (pqi.octet(d, eb, e3), e4))))

def pqi.oct_of(-s: String, r: Ip.Cut, dp: pqi.DP(s, r)) -> pqi.OP(s, Ip.oct.of(r)):
  match r:
    case Ip.Cut{+d, +rest}:
      pqi.oct_ok(s, d, rest, Ip.oct_ok(d), {==}, dp)

# the octet of every text
def pqi.oct(+s: String) -> pqi.OP(s, Ip.oct(Ip.Sym.list(s))):
  pqi.oct_of(s, Ip.drun(Ip.Sym.list(s)), pqi.drun(s))

# A dot, then an octet
# --------------------

def pqi.DOP(s: String, m: Maybe<&2, Ip.Cut>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{r}:
      match r:
        case Ip.Cut{o, rest}:
          Sigma<&1, &1, String, t => {s == SCon{'.', String.append(o, t)} : String} & ({rest == Ip.Sym.list(t) : List<&2, Ip.Sym>} & ({S.octet(o) == True{} : Bool} & {S.stops4(t) == True{} : Bool}))>

def pqi.op_dop(-u: String, -c: Char, +ec: {c == '.' : Char}, m: Maybe<&2, Ip.Cut>, op: pqi.OP(u, m)) -> pqi.DOP(SCon{c, u}, m):
  match m:
    case None{}:
      Unit{}
    case Some{r}:
      match r:
        case Ip.Cut{+o, rest}:
          (+t, pr) = op
          (e1, more) = pr
          (t, (Equal.trans(String, SCon{c, u}, SCon{'.', u}, SCon{'.', String.append(o, t)}, Equal.cong(Char, String, z => SCon{z, u}, c, '.', ec), Equal.cong(String, String, z => SCon{'.', z}, u, String.append(o, t), e1)), more))

def pqi.none_dop(-s: String, m: Maybe<&2, Ip.Cut>, +e: {m == None{} : Maybe<&2, Ip.Cut>}) -> pqi.DOP(s, m):
  %Equal.sym(Maybe<&2, Ip.Cut>, m, None{}, e) : pqi.DOP(s, _)
  Unit{}

def pqi.dot_c(+c: Char, +u: String, k: LCl.pcl.C(c, Ip.Sym.of(c))) -> pqi.DOP(SCon{c, u}, Ip.dot_oct(Ip.Sym.of(c) <> Ip.Sym.list(u))):
  match k:
    case Inl{p}:
      (ey, hd) = p
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Dig{c}, ey) : pqi.DOP(SCon{c, u}, Ip.dot_oct(_ <> Ip.Sym.list(u)))
      Unit{}
    case Inr{k2}:
      match k2:
        case Inl{p}:
          (ey, hh) = p
          %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Hx{c}, ey) : pqi.DOP(SCon{c, u}, Ip.dot_oct(_ <> Ip.Sym.list(u)))
          Unit{}
        case Inr{k3}:
          match k3:
            case Inl{p}:
              (ey, ec) = p
              %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Col{}, ey) : pqi.DOP(SCon{c, u}, Ip.dot_oct(_ <> Ip.Sym.list(u)))
              Unit{}
            case Inr{k4}:
              match k4:
                case Inl{p}:
                  (ey, ec) = p
                  %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Dot{}, ey) : pqi.DOP(SCon{c, u}, Ip.dot_oct(_ <> Ip.Sym.list(u)))
                  pqi.op_dop(u, c, ec, Ip.oct(Ip.Sym.list(u)), pqi.oct(u))
                case Inr{hs}:
                  pqi.none_dop(SCon{c, u}, Ip.dot_oct(Ip.Sym.of(c) <> Ip.Sym.list(u)), LNn.pnn.dot(Ip.Sym.of(c) <> Ip.Sym.list(u), LNn.pnn.nodot_y(Ip.Sym.of(c), Ip.Sym.list(u), hs)))

# a dot and an octet of every text
def pqi.dot(s: String) -> pqi.DOP(s, Ip.dot_oct(Ip.Sym.list(s))):
  match s:
    case SNil{}:
      Unit{}
    case SCon{+c, +u}:
      pqi.dot_c(c, u, LCl.pcl.of(c))

# Quads
# -----

# a quad read, then t
def pqi.QP(s: String, m: Maybe<&2, Ip.QCut>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{r}:
      match r:
        case Ip.QCut{q, rest}:
          Sigma<&1, &1, String, t => {s == S.quad_text(q, t) : String} & ({rest == Ip.Sym.list(t) : List<&2, Ip.Sym>} & ({S.quad_ok(q) == True{} : Bool} & {S.stops4(t) == True{} : Bool}))>

def pqi.qd(-s: String, +a: String, +b: String, +c: String, -t3: String, +e: {s == String.append(a, SCon{'.', String.append(b, SCon{'.', String.append(c, t3)})}) : String}, +ea: {S.octet(a) == True{} : Bool}, +eb: {S.octet(b) == True{} : Bool}, +ec: {S.octet(c) == True{} : Bool}, m: Maybe<&2, Ip.Cut>, dp: pqi.DOP(t3, m)) -> pqi.QP(s, Ip.quad.d(a, b, c, m)):
  match m:
    case None{}:
      Unit{}
    case Some{r}:
      match r:
        case Ip.Cut{+d, rest}:
          (+t4, pr) = dp
          (f1, more) = pr
          (f2, ff) = more
          (f3, f4) = ff
          +E = Equal.trans(String, s, String.append(a, SCon{'.', String.append(b, SCon{'.', String.append(c, t3)})}), String.append(a, SCon{'.', String.append(b, SCon{'.', String.append(c, SCon{'.', String.append(d, t4)})})}), e, Equal.cong(String, String, z => String.append(a, SCon{'.', String.append(b, SCon{'.', String.append(c, z)})}), t3, SCon{'.', String.append(d, t4)}, f1))
          (t4, (E, (f2, (LQd.pqd.and_i(Bool.and(S.octet(a), S.octet(b)), Bool.and(S.octet(c), S.octet(d)), LQd.pqd.and_i(S.octet(a), S.octet(b), ea, eb), LQd.pqd.and_i(S.octet(c), S.octet(d), ec, f3)), f4))))

def pqi.qc(-s: String, +a: String, +b: String, -t2: String, +e: {s == String.append(a, SCon{'.', String.append(b, t2)}) : String}, +ea: {S.octet(a) == True{} : Bool}, +eb: {S.octet(b) == True{} : Bool}, m: Maybe<&2, Ip.Cut>, dp: pqi.DOP(t2, m)) -> pqi.QP(s, Ip.quad.c(a, b, m)):
  match m:
    case None{}:
      Unit{}
    case Some{r}:
      match r:
        case Ip.Cut{+c, +rest}:
          (+t3, pr) = dp
          (f1, more) = pr
          (f2, ff) = more
          (f3, f4) = ff
          +E = Equal.trans(String, s, String.append(a, SCon{'.', String.append(b, t2)}), String.append(a, SCon{'.', String.append(b, SCon{'.', String.append(c, t3)})}), e, Equal.cong(String, String, z => String.append(a, SCon{'.', String.append(b, z)}), t2, SCon{'.', String.append(c, t3)}, f1))
          %Equal.sym(List<&2, Ip.Sym>, rest, Ip.Sym.list(t3), f2) : pqi.QP(s, Ip.quad.d(a, b, c, Ip.dot_oct(_)))
          pqi.qd(s, a, b, c, t3, E, ea, eb, f3, Ip.dot_oct(Ip.Sym.list(t3)), pqi.dot(t3))

def pqi.qb(-s: String, +a: String, -t1: String, +e: {s == String.append(a, t1) : String}, +ea: {S.octet(a) == True{} : Bool}, m: Maybe<&2, Ip.Cut>, dp: pqi.DOP(t1, m)) -> pqi.QP(s, Ip.quad.b(a, m)):
  match m:
    case None{}:
      Unit{}
    case Some{r}:
      match r:
        case Ip.Cut{+b, +rest}:
          (+t2, pr) = dp
          (f1, more) = pr
          (f2, ff) = more
          (f3, f4) = ff
          +E = Equal.trans(String, s, String.append(a, t1), String.append(a, SCon{'.', String.append(b, t2)}), e, Equal.cong(String, String, z => String.append(a, z), t1, SCon{'.', String.append(b, t2)}, f1))
          %Equal.sym(List<&2, Ip.Sym>, rest, Ip.Sym.list(t2), f2) : pqi.QP(s, Ip.quad.c(a, b, Ip.dot_oct(_)))
          pqi.qc(s, a, b, t2, E, ea, f3, Ip.dot_oct(Ip.Sym.list(t2)), pqi.dot(t2))

def pqi.qa(-s: String, m: Maybe<&2, Ip.Cut>, op: pqi.OP(s, m)) -> pqi.QP(s, Ip.quad.a(m)):
  match m:
    case None{}:
      Unit{}
    case Some{r}:
      match r:
        case Ip.Cut{+a, +rest}:
          (+t1, pr) = op
          (e1, more) = pr
          (e2, ee) = more
          (e3, e4) = ee
          %Equal.sym(List<&2, Ip.Sym>, rest, Ip.Sym.list(t1), e2) : pqi.QP(s, Ip.quad.b(a, Ip.dot_oct(_)))
          pqi.qb(s, a, t1, e1, e3, Ip.dot_oct(Ip.Sym.list(t1)), pqi.dot(t1))

# the quad of every text
def pqi.quad(+s: String) -> pqi.QP(s, Ip.quad(Ip.Sym.list(s))):
  pqi.qa(s, Ip.oct(Ip.Sym.list(s)), pqi.oct(s))
