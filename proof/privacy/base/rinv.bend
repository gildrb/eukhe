# eukhe: lemmas shared by the proofs of area privacy, section ip: what the
# IPv6 reader has read at each step, as the text the spec writes (the
# groups read so far, joined by `:`, a `::` after the groups before it),
# and the address it answers when it stops

import Base
import ../../../bend/privacy/ip.bend as Ip
import ../../../bend/privacy/context.bend as Cx
import ../../../spec/harness/privacy.bend as S
import ./chars.bend as LIp
import ./read.bend as LRd
import ./quad.bend as LQd
import ./items.bend as LIt
import ./qinv.bend as LQi

# Texts
# -----

# the items xs, then `:` and X (X alone when there is none)
def pri.sep(xs: List<&2, String>, X: String) -> String:
  match xs:
    case Nil{}:
      X
    case y <> ys:
      S.join(y <> ys, SCon{':', X})

# the text read before X, from the groups read so far
def pri.pre(acc: Ip.Acc, X: String) -> String:
  match acc:
    case Ip.Acc{gap, l, r}:
      match gap:
        case False{}:
          pri.sep(l, X)
        case True{}:
          S.join(l, SCon{':', SCon{':', pri.sep(r, X)}})

def pri.GapR(gap: Bool, r: List<&2, String>) -> Type:
  match gap:
    case False{}:
      {r == Nil{} : List<&2, String>}
    case True{}:
      Unit

# the groups read so far are groups, and none follows a `::` not read
def pri.AccOK(acc: Ip.Acc) -> Type:
  match acc:
    case Ip.Acc{gap, l, r}:
      {S.groups(l) == True{} : Bool} & ({S.groups(r) == True{} : Bool} & pri.GapR(gap, r))

# what the reader answers: an address the spec writes, then t
def pri.RP(F: String, r: Ip.Read) -> Type:
  match r:
    case Ip.Bad{}:
      Unit
    case Ip.Got{a, rest}:
      Sigma<&1, &1, String, t => {F == S.text6(a, t) : String} & ({rest == Ip.Sym.list(t) : List<&2, Ip.Sym>} & {S.shaped(a) == True{} : Bool})>

# where the reader is in F, with s left
def pri.Inv(F: String, s: String, m: Ip.Mode, acc: Ip.Acc) -> Type:
  match m:
    case Ip.Begin{}:
      {acc == Ip.Acc{False{}, Nil{}, Nil{}} : Ip.Acc} & {F == s : String}
    case Ip.Grp{start, room}:
      Sigma<&1, &1, String, G => {start == Ip.Sym.list(String.append(G, s)) : List<&2, Ip.Sym>} & ({S.all_hex(G) == True{} : Bool} & ({Nat.is_le(1n, String.length(G)) == True{} : Bool} & ({Nat.add(String.length(G), room) == 4n : Nat} & ({F == pri.pre(acc, String.append(G, s)) : String} & pri.AccOK(acc)))))>
    case Ip.Long{start}:
      Sigma<&1, &1, String, G => {start == Ip.Sym.list(String.append(G, s)) : List<&2, Ip.Sym>} & ({F == pri.pre(acc, String.append(G, s)) : String} & pri.AccOK(acc))>
    case Ip.Open{}:
      Sigma<&1, &1, List<&2, String>, l => {acc == Ip.Acc{True{}, l, Nil{}} : Ip.Acc} & ({F == S.join(l, SCon{':', SCon{':', s}}) : String} & {S.groups(l) == True{} : Bool})>

# the reading of what is left after s, from every place
def pri.IH(u: String) -> Type:
  @m2: Ip.Mode -> @acc2: Ip.Acc -> @F2: String -> pri.Inv(F2, u, m2, acc2) -> pri.RP(F2, Ip.read(Ip.Sym.list(u), m2, acc2))

# Groups
# ------

def pri.lsnoc(G: String, -c: Char) -> {String.length(String.append(G, SCon{c, SNil{}})) == 1n+String.length(G) : Nat}:
  match G:
    case SNil{}:
      {==}
    case SCon{x, g}:
      %pri.lsnoc(g, c) : {1n+String.length(String.append(g, SCon{c, SNil{}})) == 1n+_ : Nat}
      {==}

def pri.hsnoc(G: String, +c: Char, +hg: {S.all_hex(G) == True{} : Bool}, +hc: {S.hex(c) == True{} : Bool}) -> {S.all_hex(String.append(G, SCon{c, SNil{}})) == True{} : Bool}:
  match G:
    case SNil{}:
      LQd.pqd.and_i(S.hex(c), True{}, hc, {==})
    case SCon{+x, +g}:
      LQd.pqd.and_i(S.hex(x), S.all_hex(String.append(g, SCon{c, SNil{}})), LIp.pip.and_l(S.hex(x), S.all_hex(g), hg), pri.hsnoc(g, c, LIp.pip.and_r(S.hex(x), S.all_hex(g), hg), hc))

def pri.gsnoc(l: List<&2, String>, +G: String, +hl: {S.groups(l) == True{} : Bool}, +hG: {S.group(G) == True{} : Bool}) -> {S.groups(List.append(&2, String, l, [G])) == True{} : Bool}:
  match l:
    case Nil{}:
      LQd.pqd.and_i(S.group(G), True{}, hG, {==})
    case +x <> +xs:
      LQd.pqd.and_i(S.group(x), S.groups(List.append(&2, String, xs, [G])), LIp.pip.and_l(S.group(x), S.groups(xs), hl), pri.gsnoc(xs, G, LIp.pip.and_r(S.group(x), S.groups(xs), hl), hG))

def pri.zero_le(m: Nat) -> {Nat.is_le(0n, m) == True{} : Bool}:
  match m:
    case 0n:
      {==}
    case 1n+k:
      {==}

def pri.le_add(n: Nat, +m: Nat) -> {Nat.is_le(n, Nat.add(n, m)) == True{} : Bool}:
  match n:
    case 0n:
      pri.zero_le(m)
    case 1n+k:
      pri.le_add(k, m)

def pri.le4(+G: String, +room: Nat, +er: {Nat.add(String.length(G), room) == 4n : Nat}) -> {Nat.is_le(String.length(G), 4n) == True{} : Bool}:
  %er : {Nat.is_le(String.length(G), _) == True{} : Bool}
  pri.le_add(String.length(G), room)

# a group read with room left is a group
def pri.grp(+G: String, +room: Nat, +eh: {S.all_hex(G) == True{} : Bool}, +e1: {Nat.is_le(1n, String.length(G)) == True{} : Bool}, +er: {Nat.add(String.length(G), room) == 4n : Nat}) -> {S.group(G) == True{} : Bool}:
  LQd.pqd.and_i(S.all_hex(G), Bool.and(Nat.is_le(1n, String.length(G)), Nat.is_le(String.length(G), 4n)), eh, LQd.pqd.and_i(Nat.is_le(1n, String.length(G)), Nat.is_le(String.length(G), 4n), e1, pri.le4(G, room, er)))

def pri.grp_le1(+G: String, +c: Char) -> {Nat.is_le(1n, String.length(String.append(G, SCon{c, SNil{}}))) == True{} : Bool}:
  %Equal.sym(Nat, String.length(String.append(G, SCon{c, SNil{}})), 1n+String.length(G), pri.lsnoc(G, c)) : {Nat.is_le(1n, _) == True{} : Bool}
  pri.zero_le(String.length(G))

def pri.grp_add(+G: String, +c: Char, +p: Nat, +er: {Nat.add(String.length(G), 1n+p) == 4n : Nat}) -> {Nat.add(String.length(String.append(G, SCon{c, SNil{}})), p) == 4n : Nat}:
  %Equal.sym(Nat, String.length(String.append(G, SCon{c, SNil{}})), 1n+String.length(G), pri.lsnoc(G, c)) : {Nat.add(_, p) == 4n : Nat}
  Equal.trans(Nat, 1n+Nat.add(String.length(G), p), Nat.add(String.length(G), 1n+p), 4n, Equal.sym(Nat, Nat.add(String.length(G), 1n+p), 1n+Nat.add(String.length(G), p), LRd.prd.add_succ(String.length(G), p)), er)

# Joins
# -----

def pri.j1c(xs: List<&2, String>, +x: String, +G: String, +Y: String) -> {pri.sep(x <> xs, String.append(G, Y)) == S.join(x <> List.append(&2, String, xs, [G]), Y) : String}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +ys:
      Equal.cong(String, String, z => String.append(x, SCon{':', z}), pri.sep(y <> ys, String.append(G, Y)), S.join(y <> List.append(&2, String, ys, [G]), Y), pri.j1c(ys, y, G, Y))

# a group G read after the items l, then Y
def pri.j1(l: List<&2, String>, +G: String, +Y: String) -> {pri.sep(l, String.append(G, Y)) == S.join(List.append(&2, String, l, [G]), Y) : String}:
  match l:
    case Nil{}:
      {==}
    case +x <> +xs:
      pri.j1c(xs, x, G, Y)

def pri.j2(l: List<&2, String>, -G: String, -X: String) -> {pri.sep(List.append(&2, String, l, [G]), X) == S.join(List.append(&2, String, l, [G]), SCon{':', X}) : String}:
  match l:
    case Nil{}:
      {==}
    case x <> xs:
      {==}

def pri.app_nil_join(+xs: List<&2, String>, +t: String) -> {S.join(xs, t) == S.join(List.append(&2, String, xs, Nil{}), t) : String}:
  Equal.cong(List<&2, String>, String, z => S.join(z, t), xs, List.append(&2, String, xs, Nil{}), Equal.sym(List<&2, String>, List.append(&2, String, xs, Nil{}), xs, LIt.pit.app_nil(xs)))

# a group G read, then `:` and X: the text read before X after it
def pri.pre_push(acc: Ip.Acc, +G: String, +X: String) -> {pri.pre(acc, String.append(G, SCon{':', X})) == pri.pre(Ip.Acc.push(acc, G), X) : String}:
  match acc:
    case Ip.Acc{gap, +l, +r}:
      match gap:
        case False{}:
          Equal.trans(String, pri.sep(l, String.append(G, SCon{':', X})), S.join(List.append(&2, String, l, [G]), SCon{':', X}), pri.sep(List.append(&2, String, l, [G]), X), pri.j1(l, G, SCon{':', X}), Equal.sym(String, pri.sep(List.append(&2, String, l, [G]), X), S.join(List.append(&2, String, l, [G]), SCon{':', X}), pri.j2(l, G, X)))
        case True{}:
          Equal.cong(String, String, z => S.join(l, SCon{':', SCon{':', z}}), pri.sep(r, String.append(G, SCon{':', X})), pri.sep(List.append(&2, String, r, [G]), X), Equal.trans(String, pri.sep(r, String.append(G, SCon{':', X})), S.join(List.append(&2, String, r, [G]), SCon{':', X}), pri.sep(List.append(&2, String, r, [G]), X), pri.j1(r, G, SCon{':', X}), Equal.sym(String, pri.sep(List.append(&2, String, r, [G]), X), S.join(List.append(&2, String, r, [G]), SCon{':', X}), pri.j2(r, G, X))))

def pri.ok_push(acc: Ip.Acc, +G: String, ok: pri.AccOK(acc), +hG: {S.group(G) == True{} : Bool}) -> pri.AccOK(Ip.Acc.push(acc, G)):
  match acc:
    case Ip.Acc{gap, +l, +r}:
      match gap:
        case False{}:
          (hl, rr) = ok
          (hr, er) = rr
          (pri.gsnoc(l, G, hl, hG), (hr, er))
        case True{}:
          (hl, rr) = ok
          (hr, u0) = rr
          (hl, (pri.gsnoc(r, G, hr, hG), u0))

# Group starts
# ------------

# no hex digit
def pri.nh(y: Ip.Sym) -> Bool:
  match y:
    case Ip.Dig{c}:
      False{}
    case Ip.Hx{c}:
      False{}
    case Ip.Col{}:
      True{}
    case Ip.Dot{}:
      True{}
    case Ip.Let{}:
      True{}
    case Ip.Und{}:
      True{}
    case Ip.Dash{}:
      True{}
    case Ip.Oth{}:
      True{}

def pri.run_nh(y: Ip.Sym, -ys: List<&2, Ip.Sym>, +h: {pri.nh(y) == True{} : Bool}) -> {Ip.run(y <> ys) == Ip.Cut{SNil{}, y <> ys} : Ip.Cut}:
  match y:
    case Ip.Dig{c}:
      LIp.pip.absurd_ft({Ip.run(Ip.Dig{c} <> ys) == Ip.Cut{SNil{}, Ip.Dig{c} <> ys} : Ip.Cut}, h)
    case Ip.Hx{c}:
      LIp.pip.absurd_ft({Ip.run(Ip.Hx{c} <> ys) == Ip.Cut{SNil{}, Ip.Hx{c} <> ys} : Ip.Cut}, h)
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

def pri.nh_eq(+c: Char, -y: Ip.Sym, +ey: {Ip.Sym.of(c) == y : Ip.Sym}, +hy: {pri.nh(y) == True{} : Bool}) -> {pri.nh(Ip.Sym.of(c)) == True{} : Bool}:
  %Equal.sym(Ip.Sym, Ip.Sym.of(c), y, ey) : {pri.nh(_) == True{} : Bool}
  hy

def pri.nh_stop(y: Ip.Sym, +h: {S.k_stop6(LIp.pip.kind(y)) == True{} : Bool}) -> {pri.nh(y) == True{} : Bool}:
  match y:
    case Ip.Dig{c}:
      LIp.pip.absurd_ft({pri.nh(Ip.Dig{c}) == True{} : Bool}, h)
    case Ip.Hx{c}:
      LIp.pip.absurd_ft({pri.nh(Ip.Hx{c}) == True{} : Bool}, h)
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

# the group that started at start, G then s, is G
def pri.gis(+G: String, +s: String, -start: List<&2, Ip.Sym>, +es: {start == Ip.Sym.list(String.append(G, s)) : List<&2, Ip.Sym>}, +eh: {S.all_hex(G) == True{} : Bool}, +hr: {Ip.run(Ip.Sym.list(s)) == Ip.Cut{SNil{}, Ip.Sym.list(s)} : Ip.Cut}) -> {Ip.group(start) == G : String}:
  %Equal.sym(List<&2, Ip.Sym>, start, Ip.Sym.list(String.append(G, s)), es) : {Ip.group(_) == G : String}
  %Equal.sym(List<&2, Ip.Sym>, Ip.Sym.list(String.append(G, s)), List.append(&2, Ip.Sym, Ip.Sym.list(G), Ip.Sym.list(s)), LRd.prd.sym_app(G, s)) : {Ip.group(_) == G : String}
  LRd.prd.group_is(G, Ip.Sym.list(s), eh, hr)

# a group G read, s left: the same reading with G then c, u left
def pri.snoc_es(+G: String, +c: Char, +u: String, -start: List<&2, Ip.Sym>, +es: {start == Ip.Sym.list(String.append(G, SCon{c, u})) : List<&2, Ip.Sym>}) -> {start == Ip.Sym.list(String.append(String.append(G, SCon{c, SNil{}}), u)) : List<&2, Ip.Sym>}:
  Equal.trans(List<&2, Ip.Sym>, start, Ip.Sym.list(String.append(G, SCon{c, u})), Ip.Sym.list(String.append(String.append(G, SCon{c, SNil{}}), u)), es, Equal.cong(String, List<&2, Ip.Sym>, z => Ip.Sym.list(z), String.append(G, SCon{c, u}), String.append(String.append(G, SCon{c, SNil{}}), u), Equal.sym(String, String.append(String.append(G, SCon{c, SNil{}}), u), String.append(G, SCon{c, u}), LRd.prd.app_assoc(G, SCon{c, SNil{}}, u))))

def pri.snoc_ef(+acc: Ip.Acc, +G: String, +c: Char, +u: String, -F: String, +ef: {F == pri.pre(acc, String.append(G, SCon{c, u})) : String}) -> {F == pri.pre(acc, String.append(String.append(G, SCon{c, SNil{}}), u)) : String}:
  Equal.trans(String, F, pri.pre(acc, String.append(G, SCon{c, u})), pri.pre(acc, String.append(String.append(G, SCon{c, SNil{}}), u)), ef, Equal.cong(String, String, z => pri.pre(acc, z), String.append(G, SCon{c, u}), String.append(String.append(G, SCon{c, SNil{}}), u), Equal.sym(String, String.append(String.append(G, SCon{c, SNil{}}), u), String.append(G, SCon{c, u}), LRd.prd.app_assoc(G, SCon{c, SNil{}}, u))))

# Answers
# -------

# the reading ends after a `::`, s left
def pri.fin_open(+l: List<&2, String>, +s: String, -rest: List<&2, Ip.Sym>, +er: {rest == Ip.Sym.list(s) : List<&2, Ip.Sym>}, -F: String, +ef: {F == S.join(l, SCon{':', SCon{':', s}}) : String}, +hg: {S.groups(l) == True{} : Bool}) -> pri.RP(F, Ip.Got{Ip.Gap{l, Nil{}, None{}}, rest}):
  (s, (ef, (er, LQd.pqd.and_i(Bool.and(S.groups(l), True{}), True{}, LQd.pqd.and_i(S.groups(l), True{}, hg, {==}), {==}))))

# the reading ends after a group G, s left
def pri.fin_grp(acc: Ip.Acc, +G: String, +s: String, -rest: List<&2, Ip.Sym>, +er: {rest == Ip.Sym.list(s) : List<&2, Ip.Sym>}, -F: String, +ef: {F == pri.pre(acc, String.append(G, s)) : String}, ok: pri.AccOK(acc), +hG: {S.group(G) == True{} : Bool}) -> pri.RP(F, Ip.finish(Ip.Acc.push(acc, G), None{}, rest)):
  match acc:
    case Ip.Acc{gap, +l, +r}:
      match gap:
        case False{}:
          (hl, rr) = ok
          +L = List.append(&2, String, l, [G])
          +E = Equal.trans(String, F, pri.sep(l, String.append(G, s)), S.join(List.append(&2, String, L, Nil{}), s), ef, Equal.trans(String, pri.sep(l, String.append(G, s)), S.join(L, s), S.join(List.append(&2, String, L, Nil{}), s), pri.j1(l, G, s), pri.app_nil_join(L, s)))
          (s, (E, (er, LQd.pqd.and_i(S.groups(L), True{}, pri.gsnoc(l, G, hl, hG), {==}))))
        case True{}:
          (hl, rr) = ok
          (hr, u0) = rr
          +R = List.append(&2, String, r, [G])
          +E = Equal.trans(String, F, S.join(l, SCon{':', SCon{':', pri.sep(r, String.append(G, s))}}), S.join(l, SCon{':', SCon{':', S.join(List.append(&2, String, R, Nil{}), s)}}), ef, Equal.cong(String, String, z => S.join(l, SCon{':', SCon{':', z}}), pri.sep(r, String.append(G, s)), S.join(List.append(&2, String, R, Nil{}), s), Equal.trans(String, pri.sep(r, String.append(G, s)), S.join(R, s), S.join(List.append(&2, String, R, Nil{}), s), pri.j1(r, G, s), pri.app_nil_join(R, s))))
          (s, (E, (er, LQd.pqd.and_i(Bool.and(S.groups(l), S.groups(R)), True{}, LQd.pqd.and_i(S.groups(l), S.groups(R), hl, pri.gsnoc(r, G, hr, hG)), {==}))))

# the reading ends after an IPv4 q, t left
def pri.fin_q(acc: Ip.Acc, +q: Ip.Quad, +t: String, -rest: List<&2, Ip.Sym>, +er: {rest == Ip.Sym.list(t) : List<&2, Ip.Sym>}, -F: String, +ef: {F == pri.pre(acc, S.quad_text(q, t)) : String}, ok: pri.AccOK(acc), +hq: {S.quad_ok(q) == True{} : Bool}) -> pri.RP(F, Ip.Got{Ip.Acc.addr(acc, Some{q}), rest}):
  match acc:
    case Ip.Acc{gap, +l, +r}:
      match gap:
        case False{}:
          (hl, rr) = ok
          +q0 = S.quad_text(q, "")
          +qa = Equal.sym(String, String.append(q0, t), S.quad_text(q, t), LQd.pqd.qt_app(q, t))
          +E = Equal.trans(String, F, pri.sep(l, S.quad_text(q, t)), S.join(List.append(&2, String, l, [q0]), t), ef, Equal.trans(String, pri.sep(l, S.quad_text(q, t)), pri.sep(l, String.append(q0, t)), S.join(List.append(&2, String, l, [q0]), t), Equal.cong(String, String, z => pri.sep(l, z), S.quad_text(q, t), String.append(q0, t), qa), pri.j1(l, q0, t)))
          (t, (E, (er, LQd.pqd.and_i(S.groups(l), S.quad_ok(q), hl, hq))))
        case True{}:
          (hl, rr) = ok
          (hr, u0) = rr
          +q0 = S.quad_text(q, "")
          +qa = Equal.sym(String, String.append(q0, t), S.quad_text(q, t), LQd.pqd.qt_app(q, t))
          +E = Equal.trans(String, F, S.join(l, SCon{':', SCon{':', pri.sep(r, S.quad_text(q, t))}}), S.join(l, SCon{':', SCon{':', S.join(List.append(&2, String, r, [q0]), t)}}), ef, Equal.cong(String, String, z => S.join(l, SCon{':', SCon{':', z}}), pri.sep(r, S.quad_text(q, t)), S.join(List.append(&2, String, r, [q0]), t), Equal.trans(String, pri.sep(r, S.quad_text(q, t)), pri.sep(r, String.append(q0, t)), S.join(List.append(&2, String, r, [q0]), t), Equal.cong(String, String, z => pri.sep(r, z), S.quad_text(q, t), String.append(q0, t), qa), pri.j1(r, q0, t))))
          (t, (E, (er, LQd.pqd.and_i(Bool.and(S.groups(l), S.groups(r)), S.quad_ok(q), LQd.pqd.and_i(S.groups(l), S.groups(r), hl, hr), hq))))

# the IPv4 read from where a group started, X there
def pri.qend(+acc: Ip.Acc, +X: String, -F: String, +ef: {F == pri.pre(acc, X) : String}, ok: pri.AccOK(acc), m: Maybe<&2, Ip.QCut>, qp: LQi.pqi.QP(X, m)) -> pri.RP(F, Ip.quad_end(acc, m)):
  match m:
    case None{}:
      Unit{}
    case Some{r}:
      match r:
        case Ip.QCut{+q, rest}:
          (+t, pr) = qp
          (e1, more) = pr
          (e2, ee) = more
          (e3, e4) = ee
          pri.fin_q(acc, q, t, rest, e2, F, Equal.trans(String, F, pri.pre(acc, X), pri.pre(acc, S.quad_text(q, t)), ef, Equal.cong(String, String, z => pri.pre(acc, z), X, S.quad_text(q, t), e1)), ok, e3)
