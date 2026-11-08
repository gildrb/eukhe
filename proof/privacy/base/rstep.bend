# eukhe: lemmas shared by the proofs of area privacy, section ip: every
# answer the IPv6 reader gives is an address the spec writes, followed by
# the rest of the text (pri.rd, by induction on the text left, one step of
# the reader per char: LCl.pcl.of says what each char is)

import Base
import ../../../bend/privacy/ip.bend as Ip
import ../../../bend/privacy/context.bend as Cx
import ../../../spec/harness/privacy.bend as S
import ./chars.bend as LIp
import ./read.bend as LRd
import ./quad.bend as LQd
import ./cls.bend as LCl
import ./qinv.bend as LQi
import ./rinv.bend as LRi

# Steps of the reader
# -------------------

def pri.grp0_hex(+c: Char, e: Either<&1, &1, {Ip.Sym.of(c) == Ip.Dig{c} : Ip.Sym}, {Ip.Sym.of(c) == Ip.Hx{c} : Ip.Sym}>, +ys: List<&2, Ip.Sym>, +s: List<&2, Ip.Sym>, +acc: Ip.Acc) -> {Ip.read(Ip.Sym.of(c) <> ys, Ip.Grp{s, 0n}, acc) == Ip.read(ys, Ip.Long{s}, acc) : Ip.Read}:
  match e:
    case Inl{+d}:
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Dig{c}, d) : {Ip.read(_ <> ys, Ip.Grp{s, 0n}, acc) == Ip.read(ys, Ip.Long{s}, acc) : Ip.Read}
      {==}
    case Inr{+x}:
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Hx{c}, x) : {Ip.read(_ <> ys, Ip.Grp{s, 0n}, acc) == Ip.read(ys, Ip.Long{s}, acc) : Ip.Read}
      {==}

def pri.long_hex(+c: Char, e: Either<&1, &1, {Ip.Sym.of(c) == Ip.Dig{c} : Ip.Sym}, {Ip.Sym.of(c) == Ip.Hx{c} : Ip.Sym}>, +ys: List<&2, Ip.Sym>, +s: List<&2, Ip.Sym>, +acc: Ip.Acc) -> {Ip.read(Ip.Sym.of(c) <> ys, Ip.Long{s}, acc) == Ip.read(ys, Ip.Long{s}, acc) : Ip.Read}:
  match e:
    case Inl{+d}:
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Dig{c}, d) : {Ip.read(_ <> ys, Ip.Long{s}, acc) == Ip.read(ys, Ip.Long{s}, acc) : Ip.Read}
      {==}
    case Inr{+x}:
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Hx{c}, x) : {Ip.read(_ <> ys, Ip.Long{s}, acc) == Ip.read(ys, Ip.Long{s}, acc) : Ip.Read}
      {==}

def pri.long_stop(y: Ip.Sym, -ys: List<&2, Ip.Sym>, -s: List<&2, Ip.Sym>, -acc: Ip.Acc, +h: {S.k_stop6(LIp.pip.kind(y)) == True{} : Bool}) -> {Ip.read(y <> ys, Ip.Long{s}, acc) == Ip.Bad{} : Ip.Read}:
  match y:
    case Ip.Dig{c}:
      LIp.pip.absurd_ft({Ip.read(Ip.Dig{c} <> ys, Ip.Long{s}, acc) == Ip.Bad{} : Ip.Read}, h)
    case Ip.Hx{c}:
      LIp.pip.absurd_ft({Ip.read(Ip.Hx{c} <> ys, Ip.Long{s}, acc) == Ip.Bad{} : Ip.Read}, h)
    case Ip.Col{}:
      LIp.pip.absurd_ft({Ip.read(Ip.Col{} <> ys, Ip.Long{s}, acc) == Ip.Bad{} : Ip.Read}, h)
    case Ip.Dot{}:
      LIp.pip.absurd_ft({Ip.read(Ip.Dot{} <> ys, Ip.Long{s}, acc) == Ip.Bad{} : Ip.Read}, h)
    case Ip.Let{}:
      {==}
    case Ip.Und{}:
      {==}
    case Ip.Dash{}:
      {==}
    case Ip.Oth{}:
      {==}

# a `:` inside a run of more than four hex digits
def pri.long_col(ys: List<&2, Ip.Sym>, -s: List<&2, Ip.Sym>, -acc: Ip.Acc) -> {Ip.read(Ip.Col{} <> ys, Ip.Long{s}, acc) == Ip.Bad{} : Ip.Read}:
  match ys:
    case Nil{}:
      {==}
    case y <> t:
      match y:
        case Ip.Dig{c}:
          {==}
        case Ip.Hx{c}:
          {==}
        case Ip.Col{}:
          {==}
        case Ip.Dot{}:
          {==}
        case Ip.Let{}:
          {==}
        case Ip.Und{}:
          {==}
        case Ip.Dash{}:
          {==}
        case Ip.Oth{}:
          {==}

# a `:` after a `::`: the reading ends before it
def pri.open_col(ys: List<&2, Ip.Sym>, -acc: Ip.Acc) -> {Ip.read(Ip.Col{} <> ys, Ip.Open{}, acc) == Ip.finish(acc, None{}, Ip.Col{} <> ys) : Ip.Read}:
  match ys:
    case Nil{}:
      {==}
    case y <> t:
      match y:
        case Ip.Dig{c}:
          {==}
        case Ip.Hx{c}:
          {==}
        case Ip.Col{}:
          {==}
        case Ip.Dot{}:
          {==}
        case Ip.Let{}:
          {==}
        case Ip.Und{}:
          {==}
        case Ip.Dash{}:
          {==}
        case Ip.Oth{}:
          {==}

# a `:` that a char that does not go on with an address follows
def pri.col_stop(y: Ip.Sym, -ys: List<&2, Ip.Sym>, -m: Ip.Mode, -acc: Ip.Acc, +h: {S.k_stop6(LIp.pip.kind(y)) == True{} : Bool}) -> {Ip.read(Ip.Col{} <> (y <> ys), m, acc) == Ip.read.colon(m, acc, Ip.Col{} <> (y <> ys)) : Ip.Read}:
  match y:
    case Ip.Dig{c}:
      LIp.pip.absurd_ft({Ip.read(Ip.Col{} <> (Ip.Dig{c} <> ys), m, acc) == Ip.read.colon(m, acc, Ip.Col{} <> (Ip.Dig{c} <> ys)) : Ip.Read}, h)
    case Ip.Hx{c}:
      LIp.pip.absurd_ft({Ip.read(Ip.Col{} <> (Ip.Hx{c} <> ys), m, acc) == Ip.read.colon(m, acc, Ip.Col{} <> (Ip.Hx{c} <> ys)) : Ip.Read}, h)
    case Ip.Col{}:
      LIp.pip.absurd_ft({Ip.read(Ip.Col{} <> (Ip.Col{} <> ys), m, acc) == Ip.read.colon(m, acc, Ip.Col{} <> (Ip.Col{} <> ys)) : Ip.Read}, h)
    case Ip.Dot{}:
      LIp.pip.absurd_ft({Ip.read(Ip.Col{} <> (Ip.Dot{} <> ys), m, acc) == Ip.read.colon(m, acc, Ip.Col{} <> (Ip.Dot{} <> ys)) : Ip.Read}, h)
    case Ip.Let{}:
      {==}
    case Ip.Und{}:
      {==}
    case Ip.Dash{}:
      {==}
    case Ip.Oth{}:
      {==}

def pri.chars2(+c: Char, +c2: Char, +u2: String, +ec: {c == ':' : Char}, +ec2: {c2 == ':' : Char}) -> {SCon{c, SCon{c2, u2}} == SCon{':', SCon{':', u2}} : String}:
  Equal.trans(String, SCon{c, SCon{c2, u2}}, SCon{':', SCon{c2, u2}}, SCon{':', SCon{':', u2}}, Equal.cong(Char, String, z => SCon{z, SCon{c2, u2}}, c, ':', ec), Equal.cong(Char, String, z => SCon{':', SCon{z, u2}}, c2, ':', ec2))

# A hex digit
# -----------

def pri.hexstep(+c: Char, +u: String, m: Ip.Mode, +acc: Ip.Acc, +F: String, inv: LRi.pri.Inv(F, SCon{c, u}, m, acc), e: Either<&1, &1, {Ip.Sym.of(c) == Ip.Dig{c} : Ip.Sym}, {Ip.Sym.of(c) == Ip.Hx{c} : Ip.Sym}>, +hc: {S.hex(c) == True{} : Bool}, ih: LRi.pri.IH(u)) -> LRi.pri.RP(F, Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(u), m, acc)):
  match m:
    case Ip.Begin{}:
      (ea, ef) = inv
      %Equal.sym(Ip.Acc, acc, Ip.Acc{False{}, Nil{}, Nil{}}, ea) : LRi.pri.RP(F, Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(u), Ip.Begin{}, _))
      %Equal.sym(Ip.Read, Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(u), Ip.Begin{}, Ip.Acc{False{}, Nil{}, Nil{}}), Ip.read(Ip.Sym.list(u), Ip.Grp{Ip.Sym.of(c) <> Ip.Sym.list(u), 3n}, Ip.Acc{False{}, Nil{}, Nil{}}), LRd.prd.begin_hex(c, e, Ip.Sym.list(u), Ip.Acc{False{}, Nil{}, Nil{}})) : LRi.pri.RP(F, _)
      ih(Ip.Grp{Ip.Sym.of(c) <> Ip.Sym.list(u), 3n}, Ip.Acc{False{}, Nil{}, Nil{}}, F, (SCon{c, SNil{}}, ({==}, (LQd.pqd.and_i(S.hex(c), True{}, hc, {==}), ({==}, ({==}, (ef, ({==}, ({==}, {==})))))))))
    case Ip.Grp{+start, +room}:
      match room:
        case 0n:
          (+G, pr) = inv
          (es, p1) = pr
          (eh, p2) = p1
          (e1, p3) = p2
          (er, p4) = p3
          (ef, ok) = p4
          %Equal.sym(Ip.Read, Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(u), Ip.Grp{start, 0n}, acc), Ip.read(Ip.Sym.list(u), Ip.Long{start}, acc), pri.grp0_hex(c, e, Ip.Sym.list(u), start, acc)) : LRi.pri.RP(F, _)
          ih(Ip.Long{start}, acc, F, (String.append(G, SCon{c, SNil{}}), (LRi.pri.snoc_es(G, c, u, start, es), (LRi.pri.snoc_ef(acc, G, c, u, F, ef), ok))))
        case 1n+p:
          (+G, pr) = inv
          (es, p1) = pr
          (eh, p2) = p1
          (e1, p3) = p2
          (er, p4) = p3
          (ef, ok) = p4
          %Equal.sym(Ip.Read, Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(u), Ip.Grp{start, 1n+p}, acc), Ip.read(Ip.Sym.list(u), Ip.Grp{start, p}, acc), LRd.prd.grp_hex(c, e, Ip.Sym.list(u), start, p, acc)) : LRi.pri.RP(F, _)
          ih(Ip.Grp{start, p}, acc, F, (String.append(G, SCon{c, SNil{}}), (LRi.pri.snoc_es(G, c, u, start, es), (LRi.pri.hsnoc(G, c, eh, hc), (LRi.pri.grp_le1(G, c), (LRi.pri.grp_add(G, c, p, er), (LRi.pri.snoc_ef(acc, G, c, u, F, ef), ok)))))))
    case Ip.Long{+start}:
      (+G, pr) = inv
      (es, p1) = pr
      (ef, ok) = p1
      %Equal.sym(Ip.Read, Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(u), Ip.Long{start}, acc), Ip.read(Ip.Sym.list(u), Ip.Long{start}, acc), pri.long_hex(c, e, Ip.Sym.list(u), start, acc)) : LRi.pri.RP(F, _)
      ih(Ip.Long{start}, acc, F, (String.append(G, SCon{c, SNil{}}), (LRi.pri.snoc_es(G, c, u, start, es), (LRi.pri.snoc_ef(acc, G, c, u, F, ef), ok))))
    case Ip.Open{}:
      (+l, pr) = inv
      (ea, p1) = pr
      (ef, hg) = p1
      +AO = {Ip.Acc{True{}, l, Nil{}} : Ip.Acc}
      %Equal.sym(Ip.Acc, acc, AO, ea) : LRi.pri.RP(F, Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(u), Ip.Open{}, _))
      %Equal.sym(Ip.Read, Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(u), Ip.Open{}, AO), Ip.read(Ip.Sym.list(u), Ip.Grp{Ip.Sym.of(c) <> Ip.Sym.list(u), 3n}, AO), LRd.prd.open_hex(c, e, Ip.Sym.list(u), AO)) : LRi.pri.RP(F, _)
      ih(Ip.Grp{Ip.Sym.of(c) <> Ip.Sym.list(u), 3n}, AO, F, (SCon{c, SNil{}}, ({==}, (LQd.pqd.and_i(S.hex(c), True{}, hc, {==}), ({==}, ({==}, (ef, (hg, ({==}, Unit{})))))))))

# A `.`
# -----

def pri.dotstep(+c: Char, +u: String, m: Ip.Mode, +acc: Ip.Acc, +F: String, inv: LRi.pri.Inv(F, SCon{c, u}, m, acc), +ey: {Ip.Sym.of(c) == Ip.Dot{} : Ip.Sym}) -> LRi.pri.RP(F, Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(u), m, acc)):
  match m:
    case Ip.Begin{}:
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Dot{}, ey) : LRi.pri.RP(F, Ip.read(_ <> Ip.Sym.list(u), Ip.Begin{}, acc))
      Unit{}
    case Ip.Grp{+start, +room}:
      (+G, pr) = inv
      (es, p1) = pr
      (eh, p2) = p1
      (e1, p3) = p2
      (er, p4) = p3
      (ef, ok) = p4
      +X = String.append(G, SCon{c, u})
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Dot{}, ey) : LRi.pri.RP(F, Ip.read(_ <> Ip.Sym.list(u), Ip.Grp{start, room}, acc))
      %Equal.sym(List<&2, Ip.Sym>, start, Ip.Sym.list(X), es) : LRi.pri.RP(F, Ip.quad_end(acc, Ip.quad(_)))
      LRi.pri.qend(acc, X, F, ef, ok, Ip.quad(Ip.Sym.list(X)), LQi.pqi.quad(X))
    case Ip.Long{+start}:
      (+G, pr) = inv
      (es, p1) = pr
      (ef, ok) = p1
      +X = String.append(G, SCon{c, u})
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Dot{}, ey) : LRi.pri.RP(F, Ip.read(_ <> Ip.Sym.list(u), Ip.Long{start}, acc))
      %Equal.sym(List<&2, Ip.Sym>, start, Ip.Sym.list(X), es) : LRi.pri.RP(F, Ip.quad_end(acc, Ip.quad(_)))
      LRi.pri.qend(acc, X, F, ef, ok, Ip.quad(Ip.Sym.list(X)), LQi.pqi.quad(X))
    case Ip.Open{}:
      (+l, pr) = inv
      (ea, p1) = pr
      (ef, hg) = p1
      +AO = {Ip.Acc{True{}, l, Nil{}} : Ip.Acc}
      %Equal.sym(Ip.Acc, acc, AO, ea) : LRi.pri.RP(F, Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(u), Ip.Open{}, _))
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Dot{}, ey) : LRi.pri.RP(F, Ip.read(_ <> Ip.Sym.list(u), Ip.Open{}, AO))
      LRi.pri.fin_open(l, SCon{c, u}, Ip.Dot{} <> Ip.Sym.list(u), Equal.cong(Ip.Sym, List<&2, Ip.Sym>, y => y <> Ip.Sym.list(u), Ip.Dot{}, Ip.Sym.of(c), Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Dot{}, ey)), F, ef, hg)

# A char that does not go on with an address
# ------------------------------------------

def pri.stopstep(+c: Char, +u: String, m: Ip.Mode, +acc: Ip.Acc, +F: String, inv: LRi.pri.Inv(F, SCon{c, u}, m, acc), +hs: {S.k_stop6(LIp.pip.kind(Ip.Sym.of(c))) == True{} : Bool}) -> LRi.pri.RP(F, Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(u), m, acc)):
  match m:
    case Ip.Begin{}:
      %Equal.sym(Ip.Read, Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(u), Ip.Begin{}, acc), Ip.Bad{}, LRd.prd.begin_stop(Ip.Sym.of(c), Ip.Sym.list(u), acc, hs)) : LRi.pri.RP(F, _)
      Unit{}
    case Ip.Grp{+start, +room}:
      (+G, pr) = inv
      (es, p1) = pr
      (+eh, p2) = p1
      (e1, p3) = p2
      (er, p4) = p3
      (ef, ok) = p4
      +hG = LRi.pri.grp(G, room, eh, e1, er)
      +gst = LRi.pri.gis(G, SCon{c, u}, start, es, eh, LRi.pri.run_nh(Ip.Sym.of(c), Ip.Sym.list(u), LRi.pri.nh_stop(Ip.Sym.of(c), hs)))
      %Equal.sym(Ip.Read, Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(u), Ip.Grp{start, room}, acc), Ip.finish(Ip.Acc.push(acc, Ip.group(start)), None{}, Ip.Sym.of(c) <> Ip.Sym.list(u)), LRd.prd.grp_stop(Ip.Sym.of(c), Ip.Sym.list(u), start, room, acc, hs)) : LRi.pri.RP(F, _)
      %Equal.sym(String, Ip.group(start), G, gst) : LRi.pri.RP(F, Ip.finish(Ip.Acc.push(acc, _), None{}, Ip.Sym.of(c) <> Ip.Sym.list(u)))
      LRi.pri.fin_grp(acc, G, SCon{c, u}, Ip.Sym.of(c) <> Ip.Sym.list(u), {==}, F, ef, ok, hG)
    case Ip.Long{+start}:
      %Equal.sym(Ip.Read, Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(u), Ip.Long{start}, acc), Ip.Bad{}, pri.long_stop(Ip.Sym.of(c), Ip.Sym.list(u), start, acc, hs)) : LRi.pri.RP(F, _)
      Unit{}
    case Ip.Open{}:
      (+l, pr) = inv
      (ea, p1) = pr
      (ef, hg) = p1
      +AO = {Ip.Acc{True{}, l, Nil{}} : Ip.Acc}
      %Equal.sym(Ip.Acc, acc, AO, ea) : LRi.pri.RP(F, Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(u), Ip.Open{}, _))
      %Equal.sym(Ip.Read, Ip.read(Ip.Sym.of(c) <> Ip.Sym.list(u), Ip.Open{}, AO), Ip.finish(AO, None{}, Ip.Sym.of(c) <> Ip.Sym.list(u)), LRd.prd.open_stop(Ip.Sym.of(c), Ip.Sym.list(u), AO, hs)) : LRi.pri.RP(F, _)
      LRi.pri.fin_open(l, SCon{c, u}, Ip.Sym.of(c) <> Ip.Sym.list(u), {==}, F, ef, hg)

# A `:`
# -----

# a `:` last
def pri.col_nil(+c: Char, m: Ip.Mode, +acc: Ip.Acc, +F: String, inv: LRi.pri.Inv(F, SCon{c, SNil{}}, m, acc), +ey: {Ip.Sym.of(c) == Ip.Col{} : Ip.Sym}) -> LRi.pri.RP(F, Ip.read(Ip.Sym.of(c) <> Nil{}, m, acc)):
  match m:
    case Ip.Begin{}:
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Col{}, ey) : LRi.pri.RP(F, Ip.read(_ <> Nil{}, Ip.Begin{}, acc))
      Unit{}
    case Ip.Grp{start, room}:
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Col{}, ey) : LRi.pri.RP(F, Ip.read(_ <> Nil{}, Ip.Grp{start, room}, acc))
      Unit{}
    case Ip.Long{start}:
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Col{}, ey) : LRi.pri.RP(F, Ip.read(_ <> Nil{}, Ip.Long{start}, acc))
      Unit{}
    case Ip.Open{}:
      (+l, pr) = inv
      (ea, p1) = pr
      (ef, hg) = p1
      +AO = {Ip.Acc{True{}, l, Nil{}} : Ip.Acc}
      %Equal.sym(Ip.Acc, acc, AO, ea) : LRi.pri.RP(F, Ip.read(Ip.Sym.of(c) <> Nil{}, Ip.Open{}, _))
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Col{}, ey) : LRi.pri.RP(F, Ip.read(_ <> Nil{}, Ip.Open{}, AO))
      LRi.pri.fin_open(l, SCon{c, SNil{}}, Ip.Col{} <> Nil{}, Equal.cong(Ip.Sym, List<&2, Ip.Sym>, y => y <> Nil{}, Ip.Col{}, Ip.Sym.of(c), Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Col{}, ey)), F, ef, hg)

# `::` at the start of the text
def pri.bcol(+c: Char, +c2: Char, +u2: String, k2: LCl.pcl.C(c2, Ip.Sym.of(c2)), ih2: LRi.pri.IH(u2), +F: String, +ef: {F == SCon{c, SCon{c2, u2}} : String}, +ec: {c == ':' : Char}) -> LRi.pri.RP(F, Ip.read(Ip.Col{} <> (Ip.Sym.of(c2) <> Ip.Sym.list(u2)), Ip.Begin{}, Ip.Acc{False{}, Nil{}, Nil{}})):
  match k2:
    case Inl{p}:
      (ey2, hd2) = p
      %Equal.sym(Ip.Sym, Ip.Sym.of(c2), Ip.Dig{c2}, ey2) : LRi.pri.RP(F, Ip.read(Ip.Col{} <> (_ <> Ip.Sym.list(u2)), Ip.Begin{}, Ip.Acc{False{}, Nil{}, Nil{}}))
      Unit{}
    case Inr{k3}:
      match k3:
        case Inl{p}:
          (ey2, hh2) = p
          %Equal.sym(Ip.Sym, Ip.Sym.of(c2), Ip.Hx{c2}, ey2) : LRi.pri.RP(F, Ip.read(Ip.Col{} <> (_ <> Ip.Sym.list(u2)), Ip.Begin{}, Ip.Acc{False{}, Nil{}, Nil{}}))
          Unit{}
        case Inr{k4}:
          match k4:
            case Inl{p}:
              (ey2, ec2) = p
              %Equal.sym(Ip.Sym, Ip.Sym.of(c2), Ip.Col{}, ey2) : LRi.pri.RP(F, Ip.read(Ip.Col{} <> (_ <> Ip.Sym.list(u2)), Ip.Begin{}, Ip.Acc{False{}, Nil{}, Nil{}}))
              ih2(Ip.Open{}, Ip.Acc{True{}, Nil{}, Nil{}}, F, (Nil{}, ({==}, (Equal.trans(String, F, SCon{c, SCon{c2, u2}}, SCon{':', SCon{':', u2}}, ef, pri.chars2(c, c2, u2, ec, ec2)), {==}))))
            case Inr{k5}:
              match k5:
                case Inl{p}:
                  (ey2, ed2) = p
                  %Equal.sym(Ip.Sym, Ip.Sym.of(c2), Ip.Dot{}, ey2) : LRi.pri.RP(F, Ip.read(Ip.Col{} <> (_ <> Ip.Sym.list(u2)), Ip.Begin{}, Ip.Acc{False{}, Nil{}, Nil{}}))
                  Unit{}
                case Inr{hs2}:
                  %Equal.sym(Ip.Read, Ip.read(Ip.Col{} <> (Ip.Sym.of(c2) <> Ip.Sym.list(u2)), Ip.Begin{}, Ip.Acc{False{}, Nil{}, Nil{}}), Ip.read.colon(Ip.Begin{}, Ip.Acc{False{}, Nil{}, Nil{}}, Ip.Col{} <> (Ip.Sym.of(c2) <> Ip.Sym.list(u2))), pri.col_stop(Ip.Sym.of(c2), Ip.Sym.list(u2), Ip.Begin{}, Ip.Acc{False{}, Nil{}, Nil{}}, hs2)) : LRi.pri.RP(F, _)
                  Unit{}

# `::` after a group G: the `::` of the address
def pri.gcol_gap(acc: Ip.Acc, +c: Char, +c2: Char, +u2: String, ih2: LRi.pri.IH(u2), +start: List<&2, Ip.Sym>, +room: Nat, +G: String, +F: String, +ef: {F == LRi.pri.pre(acc, String.append(G, SCon{c, SCon{c2, u2}})) : String}, ok: LRi.pri.AccOK(acc), +hG: {S.group(G) == True{} : Bool}, +gst: {Ip.group(start) == G : String}, +ec: {c == ':' : Char}, +ec2: {c2 == ':' : Char}) -> LRi.pri.RP(F, Ip.read(Ip.Col{} <> (Ip.Col{} <> Ip.Sym.list(u2)), Ip.Grp{start, room}, acc)):
  match acc:
    case Ip.Acc{gap, +l, +r}:
      match gap:
        case False{}:
          (hl, rr) = ok
          (hr, er0) = rr
          +Y = {SCon{':', SCon{':', u2}} : String}
          +E = Equal.trans(String, F, LRi.pri.sep(l, String.append(G, SCon{c, SCon{c2, u2}})), S.join(List.append(&2, String, l, [G]), Y), ef, Equal.trans(String, LRi.pri.sep(l, String.append(G, SCon{c, SCon{c2, u2}})), LRi.pri.sep(l, String.append(G, Y)), S.join(List.append(&2, String, l, [G]), Y), Equal.cong(String, String, z => LRi.pri.sep(l, String.append(G, z)), SCon{c, SCon{c2, u2}}, Y, pri.chars2(c, c2, u2, ec, ec2)), LRi.pri.j1(l, G, Y)))
          %Equal.sym(String, Ip.group(start), G, gst) : LRi.pri.RP(F, Ip.read(Ip.Sym.list(u2), Ip.Open{}, Ip.Acc{True{}, List.append(&2, String, l, [_]), r}))
          %Equal.sym(List<&2, String>, r, Nil{}, er0) : LRi.pri.RP(F, Ip.read(Ip.Sym.list(u2), Ip.Open{}, Ip.Acc{True{}, List.append(&2, String, l, [G]), _}))
          ih2(Ip.Open{}, Ip.Acc{True{}, List.append(&2, String, l, [G]), Nil{}}, F, (List.append(&2, String, l, [G]), ({==}, (E, LRi.pri.gsnoc(l, G, hl, hG)))))
        case True{}:
          Unit{}

# a group G, `:`, then a hex digit c2: the next group
def pri.gcol_hex(+c: Char, +c2: Char, +u2: String, e2a: Either<&1, &1, {Ip.Sym.of(c2) == Ip.Dig{c2} : Ip.Sym}, {Ip.Sym.of(c2) == Ip.Hx{c2} : Ip.Sym}>, e2b: Either<&1, &1, {Ip.Sym.of(c2) == Ip.Dig{c2} : Ip.Sym}, {Ip.Sym.of(c2) == Ip.Hx{c2} : Ip.Sym}>, +hc2: {S.hex(c2) == True{} : Bool}, ih2: LRi.pri.IH(u2), +start: List<&2, Ip.Sym>, +room: Nat, +G: String, +acc: Ip.Acc, +F: String, +ef: {F == LRi.pri.pre(acc, String.append(G, SCon{c, SCon{c2, u2}})) : String}, ok: LRi.pri.AccOK(acc), +hG: {S.group(G) == True{} : Bool}, +gst: {Ip.group(start) == G : String}, +ec: {c == ':' : Char}) -> LRi.pri.RP(F, Ip.read(Ip.Col{} <> (Ip.Sym.of(c2) <> Ip.Sym.list(u2)), Ip.Grp{start, room}, acc)):
  +L2 = Ip.Sym.list(u2)
  +AP = Ip.Acc.push(acc, Ip.group(start))
  +X = {SCon{c2, u2} : String}
  +E = Equal.trans(String, F, LRi.pri.pre(acc, String.append(G, SCon{c, X})), LRi.pri.pre(Ip.Acc.push(acc, G), X), ef, Equal.trans(String, LRi.pri.pre(acc, String.append(G, SCon{c, X})), LRi.pri.pre(acc, String.append(G, SCon{':', X})), LRi.pri.pre(Ip.Acc.push(acc, G), X), Equal.cong(Char, String, z => LRi.pri.pre(acc, String.append(G, SCon{z, X})), c, ':', ec), LRi.pri.pre_push(acc, G, X)))
  %Equal.sym(Ip.Read, Ip.read(Ip.Col{} <> (Ip.Sym.of(c2) <> L2), Ip.Grp{start, room}, acc), Ip.read(Ip.Sym.of(c2) <> L2, Ip.Open{}, AP), LRd.prd.grp_sep(c2, e2a, L2, start, room, acc)) : LRi.pri.RP(F, _)
  %Equal.sym(Ip.Read, Ip.read(Ip.Sym.of(c2) <> L2, Ip.Open{}, AP), Ip.read(L2, Ip.Grp{Ip.Sym.of(c2) <> L2, 3n}, AP), LRd.prd.open_hex(c2, e2b, L2, AP)) : LRi.pri.RP(F, _)
  %Equal.sym(String, Ip.group(start), G, gst) : LRi.pri.RP(F, Ip.read(L2, Ip.Grp{Ip.Sym.of(c2) <> L2, 3n}, Ip.Acc.push(acc, _)))
  ih2(Ip.Grp{Ip.Sym.of(c2) <> L2, 3n}, Ip.Acc.push(acc, G), F, (SCon{c2, SNil{}}, ({==}, (LQd.pqd.and_i(S.hex(c2), True{}, hc2, {==}), ({==}, ({==}, (E, LRi.pri.ok_push(acc, G, ok, hG))))))))

# a group G, then `:`
def pri.gcol(+c: Char, +c2: Char, +u2: String, k2: LCl.pcl.C(c2, Ip.Sym.of(c2)), ih2: LRi.pri.IH(u2), +start: List<&2, Ip.Sym>, +room: Nat, +G: String, +acc: Ip.Acc, +F: String, +ef: {F == LRi.pri.pre(acc, String.append(G, SCon{c, SCon{c2, u2}})) : String}, ok: LRi.pri.AccOK(acc), +hG: {S.group(G) == True{} : Bool}, +gst: {Ip.group(start) == G : String}, +ec: {c == ':' : Char}) -> LRi.pri.RP(F, Ip.read(Ip.Col{} <> (Ip.Sym.of(c2) <> Ip.Sym.list(u2)), Ip.Grp{start, room}, acc)):
  match k2:
    case Inl{p}:
      (+ey2, hd2) = p
      pri.gcol_hex(c, c2, u2, Inl{ey2}, Inl{ey2}, LQd.pqd.dec_hex(c2, hd2), ih2, start, room, G, acc, F, ef, ok, hG, gst, ec)
    case Inr{k3}:
      match k3:
        case Inl{p}:
          (+ey2, hh2) = p
          pri.gcol_hex(c, c2, u2, Inr{ey2}, Inr{ey2}, hh2, ih2, start, room, G, acc, F, ef, ok, hG, gst, ec)
        case Inr{k4}:
          match k4:
            case Inl{p}:
              (ey2, ec2) = p
              %Equal.sym(Ip.Sym, Ip.Sym.of(c2), Ip.Col{}, ey2) : LRi.pri.RP(F, Ip.read(Ip.Col{} <> (_ <> Ip.Sym.list(u2)), Ip.Grp{start, room}, acc))
              pri.gcol_gap(acc, c, c2, u2, ih2, start, room, G, F, ef, ok, hG, gst, ec, ec2)
            case Inr{k5}:
              match k5:
                case Inl{p}:
                  (ey2, ed2) = p
                  %Equal.sym(Ip.Sym, Ip.Sym.of(c2), Ip.Dot{}, ey2) : LRi.pri.RP(F, Ip.read(Ip.Col{} <> (_ <> Ip.Sym.list(u2)), Ip.Grp{start, room}, acc))
                  Unit{}
                case Inr{hs2}:
                  %Equal.sym(Ip.Read, Ip.read(Ip.Col{} <> (Ip.Sym.of(c2) <> Ip.Sym.list(u2)), Ip.Grp{start, room}, acc), Ip.read.colon(Ip.Grp{start, room}, acc, Ip.Col{} <> (Ip.Sym.of(c2) <> Ip.Sym.list(u2))), pri.col_stop(Ip.Sym.of(c2), Ip.Sym.list(u2), Ip.Grp{start, room}, acc, hs2)) : LRi.pri.RP(F, _)
                  Unit{}

# a `:`, then c2
def pri.col2(+c: Char, +c2: Char, +u2: String, m: Ip.Mode, +acc: Ip.Acc, +F: String, inv: LRi.pri.Inv(F, SCon{c, SCon{c2, u2}}, m, acc), +ey: {Ip.Sym.of(c) == Ip.Col{} : Ip.Sym}, +ec: {c == ':' : Char}, k2: LCl.pcl.C(c2, Ip.Sym.of(c2)), ih2: LRi.pri.IH(u2)) -> LRi.pri.RP(F, Ip.read(Ip.Sym.of(c) <> (Ip.Sym.of(c2) <> Ip.Sym.list(u2)), m, acc)):
  match m:
    case Ip.Begin{}:
      (ea, ef) = inv
      %Equal.sym(Ip.Acc, acc, Ip.Acc{False{}, Nil{}, Nil{}}, ea) : LRi.pri.RP(F, Ip.read(Ip.Sym.of(c) <> (Ip.Sym.of(c2) <> Ip.Sym.list(u2)), Ip.Begin{}, _))
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Col{}, ey) : LRi.pri.RP(F, Ip.read(_ <> (Ip.Sym.of(c2) <> Ip.Sym.list(u2)), Ip.Begin{}, Ip.Acc{False{}, Nil{}, Nil{}}))
      pri.bcol(c, c2, u2, k2, ih2, F, ef, ec)
    case Ip.Grp{+start, +room}:
      (+G, pr) = inv
      (es, p1) = pr
      (+eh, p2) = p1
      (e1, p3) = p2
      (er, p4) = p3
      (ef, ok) = p4
      +hG = LRi.pri.grp(G, room, eh, e1, er)
      +gst = LRi.pri.gis(G, SCon{c, SCon{c2, u2}}, start, es, eh, LRi.pri.run_nh(Ip.Sym.of(c), (Ip.Sym.of(c2) <> Ip.Sym.list(u2)), LRi.pri.nh_eq(c, Ip.Col{}, ey, {==})))
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Col{}, ey) : LRi.pri.RP(F, Ip.read(_ <> (Ip.Sym.of(c2) <> Ip.Sym.list(u2)), Ip.Grp{start, room}, acc))
      pri.gcol(c, c2, u2, k2, ih2, start, room, G, acc, F, ef, ok, hG, gst, ec)
    case Ip.Long{+start}:
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Col{}, ey) : LRi.pri.RP(F, Ip.read(_ <> (Ip.Sym.of(c2) <> Ip.Sym.list(u2)), Ip.Long{start}, acc))
      %Equal.sym(Ip.Read, Ip.read(Ip.Col{} <> (Ip.Sym.of(c2) <> Ip.Sym.list(u2)), Ip.Long{start}, acc), Ip.Bad{}, pri.long_col((Ip.Sym.of(c2) <> Ip.Sym.list(u2)), start, acc)) : LRi.pri.RP(F, _)
      Unit{}
    case Ip.Open{}:
      (+l, pr) = inv
      (ea, p1) = pr
      (ef, hg) = p1
      +AO = {Ip.Acc{True{}, l, Nil{}} : Ip.Acc}
      %Equal.sym(Ip.Acc, acc, AO, ea) : LRi.pri.RP(F, Ip.read(Ip.Sym.of(c) <> (Ip.Sym.of(c2) <> Ip.Sym.list(u2)), Ip.Open{}, _))
      %Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Col{}, ey) : LRi.pri.RP(F, Ip.read(_ <> (Ip.Sym.of(c2) <> Ip.Sym.list(u2)), Ip.Open{}, AO))
      %Equal.sym(Ip.Read, Ip.read(Ip.Col{} <> (Ip.Sym.of(c2) <> Ip.Sym.list(u2)), Ip.Open{}, AO), Ip.finish(AO, None{}, Ip.Col{} <> (Ip.Sym.of(c2) <> Ip.Sym.list(u2))), pri.open_col((Ip.Sym.of(c2) <> Ip.Sym.list(u2)), AO)) : LRi.pri.RP(F, _)
      LRi.pri.fin_open(l, SCon{c, SCon{c2, u2}}, Ip.Col{} <> (Ip.Sym.of(c2) <> Ip.Sym.list(u2)), Equal.cong(Ip.Sym, List<&2, Ip.Sym>, y => y <> (Ip.Sym.of(c2) <> Ip.Sym.list(u2)), Ip.Col{}, Ip.Sym.of(c), Equal.sym(Ip.Sym, Ip.Sym.of(c), Ip.Col{}, ey)), F, ef, hg)

# The text ends
# -------------

def pri.nil(m: Ip.Mode, +acc: Ip.Acc, +F: String, inv: LRi.pri.Inv(F, SNil{}, m, acc)) -> LRi.pri.RP(F, Ip.read(Nil{}, m, acc)):
  match m:
    case Ip.Begin{}:
      Unit{}
    case Ip.Grp{+start, +room}:
      (+G, pr) = inv
      (es, p1) = pr
      (+eh, p2) = p1
      (e1, p3) = p2
      (er, p4) = p3
      (ef, ok) = p4
      +hG = LRi.pri.grp(G, room, eh, e1, er)
      +gst = LRi.pri.gis(G, SNil{}, start, es, eh, {==})
      %Equal.sym(String, Ip.group(start), G, gst) : LRi.pri.RP(F, Ip.finish(Ip.Acc.push(acc, _), None{}, Nil{}))
      LRi.pri.fin_grp(acc, G, SNil{}, Nil{}, {==}, F, ef, ok, hG)
    case Ip.Long{start}:
      Unit{}
    case Ip.Open{}:
      (+l, pr) = inv
      (ea, p1) = pr
      (ef, hg) = p1
      %Equal.sym(Ip.Acc, acc, Ip.Acc{True{}, l, Nil{}}, ea) : LRi.pri.RP(F, Ip.read(Nil{}, Ip.Open{}, _))
      LRi.pri.fin_open(l, SNil{}, Nil{}, {==}, F, ef, hg)

# The reading
# -----------

def pri.cons1(+c: Char, m: Ip.Mode, +acc: Ip.Acc, +F: String, inv: LRi.pri.Inv(F, SCon{c, SNil{}}, m, acc), k: LCl.pcl.C(c, Ip.Sym.of(c)), ih: LRi.pri.IH(SNil{})) -> LRi.pri.RP(F, Ip.read(Ip.Sym.of(c) <> Nil{}, m, acc)):
  match k:
    case Inl{p}:
      (ey, hd) = p
      pri.hexstep(c, SNil{}, m, acc, F, inv, Inl{ey}, LQd.pqd.dec_hex(c, hd), ih)
    case Inr{k2}:
      match k2:
        case Inl{p}:
          (ey, hh) = p
          pri.hexstep(c, SNil{}, m, acc, F, inv, Inr{ey}, hh, ih)
        case Inr{k3}:
          match k3:
            case Inl{p}:
              (ey, ec) = p
              pri.col_nil(c, m, acc, F, inv, ey)
            case Inr{k4}:
              match k4:
                case Inl{p}:
                  (ey, ed) = p
                  pri.dotstep(c, SNil{}, m, acc, F, inv, ey)
                case Inr{hs}:
                  pri.stopstep(c, SNil{}, m, acc, F, inv, hs)

def pri.cons2(+c: Char, +c2: Char, +u2: String, m: Ip.Mode, +acc: Ip.Acc, +F: String, inv: LRi.pri.Inv(F, SCon{c, SCon{c2, u2}}, m, acc), k: LCl.pcl.C(c, Ip.Sym.of(c)), ih1: LRi.pri.IH(SCon{c2, u2}), ih2: LRi.pri.IH(u2)) -> LRi.pri.RP(F, Ip.read(Ip.Sym.of(c) <> (Ip.Sym.of(c2) <> Ip.Sym.list(u2)), m, acc)):
  match k:
    case Inl{p}:
      (ey, hd) = p
      pri.hexstep(c, SCon{c2, u2}, m, acc, F, inv, Inl{ey}, LQd.pqd.dec_hex(c, hd), ih1)
    case Inr{k2}:
      match k2:
        case Inl{p}:
          (ey, hh) = p
          pri.hexstep(c, SCon{c2, u2}, m, acc, F, inv, Inr{ey}, hh, ih1)
        case Inr{k3}:
          match k3:
            case Inl{p}:
              (ey, ec) = p
              pri.col2(c, c2, u2, m, acc, F, inv, ey, ec, LCl.pcl.of(c2), ih2)
            case Inr{k4}:
              match k4:
                case Inl{p}:
                  (ey, ed) = p
                  pri.dotstep(c, SCon{c2, u2}, m, acc, F, inv, ey)
                case Inr{hs}:
                  pri.stopstep(c, SCon{c2, u2}, m, acc, F, inv, hs)

# every answer of the reader, from every place it can be, is an address
# the spec writes, then the rest of the text
def pri.rd(s: String, m: Ip.Mode, +acc: Ip.Acc, +F: String, inv: LRi.pri.Inv(F, s, m, acc)) -> LRi.pri.RP(F, Ip.read(Ip.Sym.list(s), m, acc)):
  match s:
    case SNil{}:
      pri.nil(m, acc, F, inv)
    case SCon{+c, +u}:
      match u:
        case SNil{}:
          pri.cons1(c, m, acc, F, inv, LCl.pcl.of(c), m2 => a2 => F2 => i2 => pri.rd(u, m2, a2, F2, i2))
        case SCon{+c2, +u2}:
          pri.cons2(c, c2, u2, m, acc, F, inv, LCl.pcl.of(c), m2 => a2 => F2 => i2 => pri.rd(u, m2, a2, F2, i2), m2 => a2 => F2 => i2 => pri.rd(u2, m2, a2, F2, i2))
