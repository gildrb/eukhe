# eukhe: lemmas of LAW tree_replay_spec: on a valid tree the model's delete
# of a key x > 0 (Tr.prune) is the spec's (TS.del.keep: the nodes that are
# not x or below it, walking up their parents).
#
# PROOF: write R for the model's result. The delete laws give: R lacks x
# (tree_delete_removes), keeps its nodes unchanged (tree_delete_within),
# and drops a node only when it is x or its parent is dropped
# (tree_delete_only_below); R is valid (pt.del_sound). So a node below x is
# dropped (tp.l1, up its parents: a kept node would hang under a dropped
# parent), and a dropped node is below x (tp.l2, down to x). R and the
# spec's result then agree at every key (tp.p, tp.f), and two sorted
# lists that agree at every key are equal (pt.ext).

import Base
import ../../../bend/tree.bend as Tr
import ../../../laws/tree.bend as Tree
import ../../../spec/durable/tree.bend as TS
import ../../base/logic/bool.bend as LLogicBool
import ../base/logic.bend as LALogic
import ../base/nat.bend as LANat
import ../base/tree/above.bend as LATreeAbove
import ../base/tree/get.bend as LATreeGet
import ../base/tree/sound.bend as LATreeSound
import ../tree_delete_removes.bend as PTreeDeleteRemoves
import ../tree_delete_within.bend as PTreeDeleteWithin
import ../tree_delete_only_below.bend as PTreeDeleteOnlyBelow
import ./basic.bend as LB
import ./member.bend as LM
import ./set.bend as LS

# Small facts
# -----------

# a lookup that is_some says is not there is none
def tp.none_at(m: Maybe<&2, Tr.Ent>, h: {Maybe.is_some(&2, Tr.Ent, m) == False{} : Bool}) -> {m == None{} : Maybe<&2, Tr.Ent>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      LM.tm.tf({Some{x} == None{} : Maybe<&2, Tr.Ent>}, h)

def tp.or3(a: Bool, b: Bool, -z: Bool, o: {Bool.or(a, Bool.or(b, z)) == True{} : Bool}, na: {a == False{} : Bool}, nb: {b == False{} : Bool}) -> {z == True{} : Bool}:
  match a b:
    case True{} _:
      LM.tm.tf({z == True{} : Bool}, na)
    case False{} True{}:
      LM.tm.tf({z == True{} : Bool}, nb)
    case False{} False{}:
      o

def tp.not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      LM.tm.ft({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# nothing is below 0
def tp.lt0(-A: Type, x: Nat, h: {Nat.is_lt(x, 0n) == True{} : Bool}) -> A:
  match x:
    case 0n:
      LM.tm.ft(A, h)
    case 1n+p:
      LM.tm.ft(A, h)

# a < b <= 1 + c gives a <= c
def tp.lt_le(a: Nat, b: Nat, c: Nat, h1: {Nat.is_lt(a, b) == True{} : Bool}, h2: {Nat.is_le(b, 1n+c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b:
    case 0n b:
      match c:
        case 0n:
          {==}
        case 1n+cp:
          {==}
    case 1n+ap 0n:
      LM.tm.ft({Nat.is_le(1n+ap, c) == True{} : Bool}, h1)
    case 1n+ap 1n+bp:
      match bp:
        case 0n:
          tp.lt0({Nat.is_le(1n+ap, c) == True{} : Bool}, ap, h1)
        case 1n+bq:
          match c:
            case 0n:
              LM.tm.ft({Nat.is_le(1n+ap, 0n) == True{} : Bool}, h2)
            case 1n+cp:
              tp.lt_le(ap, 1n+bq, cp, h1, h2)

# a < b <= 0 is impossible
def tp.lt_le0(-A: Type, a: Nat, b: Nat, h1: {Nat.is_lt(a, b) == True{} : Bool}, h2: {Nat.is_le(b, 0n) == True{} : Bool}) -> A:
  match a b:
    case 0n 0n:
      LM.tm.ft(A, h1)
    case 1n+ap 0n:
      LM.tm.ft(A, h1)
    case _ 1n+bp:
      LM.tm.ft(A, h2)

def tp.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      tp.le_refl(p)

# a lookup of the model is the spec's, turned
def tp.get_ts(+l: List<&2, Tr.Ent>, +y: Nat, -m: Maybe<&2, Tr.Ent>, h: {TS.get(l, y) == m : Maybe<&2, Tr.Ent>}) -> {Tr.get(l, y) == m : Maybe<&2, Tr.Ent>}:
  Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(l, y), TS.get(l, y), m, LB.ts.get(l, y), h)

# The spec's result at a key
# --------------------------

def tp.kp(c: Bool, e: Tr.Ent) -> Maybe<&2, Tr.Ent>:
  match c:
    case True{}:
      Some{e}
    case False{}:
      None{}

# the node a delete of x from t keeps at a key where t has m
def tp.filt(m: Maybe<&2, Tr.Ent>, +t: List<&2, Tr.Ent>, +x: Nat) -> Maybe<&2, Tr.Ent>:
  match m:
    case None{}:
      None{}
    case Some{+e}:
      tp.kp(Bool.not(TS.gone(t, x, TS.key(e))), e)

def tp.f.at(b: Bool, c: Bool, +kh: Nat, +ph: Nat, +vh: Nat, +r: List<&2, Tr.Ent>, +t: List<&2, Tr.Ent>, +x: Nat, +y: Nat, +eb: {Nat.is_eq(kh, y) == b : Bool}, +ec: {Bool.not(TS.gone(t, x, kh)) == c : Bool}, +st: {Tr.sorted(Tr.Ent{kh, ph, vh} <> r) == True{} : Bool}, ih: {TS.get(TS.del.keep(r, t, x), y) == tp.filt(TS.get(r, y), t, x) : Maybe<&2, Tr.Ent>}) -> {TS.get(TS.keep.if(c, Tr.Ent{kh, ph, vh}, TS.del.keep(r, t, x)), y) == tp.filt(TS.get.pick(b, Tr.Ent{kh, ph, vh}, TS.get(r, y)), t, x) : Maybe<&2, Tr.Ent>}:
  match b c:
    case True{} True{}:
      %Equal.sym(Bool, Nat.is_eq(kh, y), True{}, eb) : {TS.get.pick(_, Tr.Ent{kh, ph, vh}, TS.get(TS.del.keep(r, t, x), y)) == tp.kp(Bool.not(TS.gone(t, x, kh)), Tr.Ent{kh, ph, vh}) : Maybe<&2, Tr.Ent>}
      %Equal.sym(Bool, Bool.not(TS.gone(t, x, kh)), True{}, ec) : {Some{Tr.Ent{kh, ph, vh}} == tp.kp(_, Tr.Ent{kh, ph, vh}) : Maybe<&2, Tr.Ent>}
      {==}
    case True{} False{}:
      +ky = LALogic.pt.eq_true(kh, y, eb)
      +ar = LLogicBool.tree.pt.and_l(Tr.above(kh, r), Tr.sorted(r), st)
      +sr = LLogicBool.tree.pt.and_r(Tr.above(kh, r), Tr.sorted(r), st)
      +ay = LS.ts.above_rw(y, kh, r, Equal.sym(Nat, kh, y, ky), ar)
      +gn = Equal.trans(Maybe<&2, Tr.Ent>, TS.get(r, y), Tr.get(r, y), None{}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(r, y), TS.get(r, y), LB.ts.get(r, y)), LATreeGet.pt.get_below(r, y, ay, sr))
      %Equal.sym(Maybe<&2, Tr.Ent>, TS.get(TS.del.keep(r, t, x), y), tp.filt(TS.get(r, y), t, x), ih) : {_ == tp.kp(Bool.not(TS.gone(t, x, kh)), Tr.Ent{kh, ph, vh}) : Maybe<&2, Tr.Ent>}
      %Equal.sym(Maybe<&2, Tr.Ent>, TS.get(r, y), None{}, gn) : {tp.filt(_, t, x) == tp.kp(Bool.not(TS.gone(t, x, kh)), Tr.Ent{kh, ph, vh}) : Maybe<&2, Tr.Ent>}
      %Equal.sym(Bool, Bool.not(TS.gone(t, x, kh)), False{}, ec) : {None{} == tp.kp(_, Tr.Ent{kh, ph, vh}) : Maybe<&2, Tr.Ent>}
      {==}
    case False{} True{}:
      %Equal.sym(Bool, Nat.is_eq(kh, y), False{}, eb) : {TS.get.pick(_, Tr.Ent{kh, ph, vh}, TS.get(TS.del.keep(r, t, x), y)) == tp.filt(TS.get(r, y), t, x) : Maybe<&2, Tr.Ent>}
      ih
    case False{} False{}:
      ih

# the spec's result at a key, on a sorted list s
def tp.f(s: List<&2, Tr.Ent>, +t: List<&2, Tr.Ent>, +x: Nat, +y: Nat, +st: {Tr.sorted(s) == True{} : Bool}) -> {TS.get(TS.del.keep(s, t, x), y) == tp.filt(TS.get(s, y), t, x) : Maybe<&2, Tr.Ent>}:
  match s:
    case Nil{}:
      {==}
    case +h <> +r:
      match h:
        case Tr.Ent{+kh, +ph, +vh}:
          +sr = LLogicBool.tree.pt.and_r(Tr.above(kh, r), Tr.sorted(r), st)
          tp.f.at(Nat.is_eq(kh, y), Bool.not(TS.gone(t, x, kh)), kh, ph, vh, r, t, x, y, {==}, {==}, st, tp.f(r, t, x, y, sr))

def tp.above_at(c: Bool, +k: Nat, +h: Tr.Ent, +d: List<&2, Tr.Ent>, ah: {Tr.above(k, h <> d) == True{} : Bool}, ad: {Tr.above(k, d) == True{} : Bool}) -> {Tr.above(k, TS.keep.if(c, h, d)) == True{} : Bool}:
  match c:
    case True{}:
      ah
    case False{}:
      ad

# a delete keeps a sorted list's lower bound
def tp.above_keep(s: List<&2, Tr.Ent>, +t: List<&2, Tr.Ent>, +x: Nat, +k: Nat, +al: {Tr.above(k, s) == True{} : Bool}, +st: {Tr.sorted(s) == True{} : Bool}) -> {Tr.above(k, TS.del.keep(s, t, x)) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +h <> +r:
      +sr = LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st)
      tp.above_at(Bool.not(TS.gone(t, x, TS.key(h))), k, h, TS.del.keep(r, t, x), al, tp.above_keep(r, t, x, k, LATreeAbove.pt.above_tail(k, h, r, al, st), sr))

def tp.sorted_at(c: Bool, +h: Tr.Ent, +d: List<&2, Tr.Ent>, +ah: {Tr.above(Tr.Ent.k(h), d) == True{} : Bool}, +sd: {Tr.sorted(d) == True{} : Bool}) -> {Tr.sorted(TS.keep.if(c, h, d)) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, Tr.above(Tr.Ent.k(h), d), True{}, ah) : {Bool.and(_, Tr.sorted(d)) == True{} : Bool}
      sd
    case False{}:
      sd

# a delete keeps a list sorted
def tp.sorted_keep(s: List<&2, Tr.Ent>, +t: List<&2, Tr.Ent>, +x: Nat, +st: {Tr.sorted(s) == True{} : Bool}) -> {Tr.sorted(TS.del.keep(s, t, x)) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +h <> +r:
      +al = LLogicBool.tree.pt.and_l(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st)
      +sr = LLogicBool.tree.pt.and_r(Tr.above(Tr.Ent.k(h), r), Tr.sorted(r), st)
      tp.sorted_at(Bool.not(TS.gone(t, x, TS.key(h))), h, TS.del.keep(r, t, x), tp.above_keep(r, t, x, Tr.Ent.k(h), al, sr), tp.sorted_keep(r, t, x, sr))

# Dropped below x (tp.l1)
# -----------------------

# the node x is dropped
def tp.at_x(+t: List<&2, Tr.Ent>, +q: Nat, +y: Nat, +rm: {Tr.has(Tr.prune(t, 1n+q), 1n+q) == False{} : Bool}, eh: {Nat.is_eq(y, 1n+q) == True{} : Bool}) -> {Tr.get(Tr.prune(t, 1n+q), y) == None{} : Maybe<&2, Tr.Ent>}:
  %Equal.sym(Nat, y, 1n+q, LALogic.pt.eq_true(y, 1n+q, eh)) : {Tr.get(Tr.prune(t, 1n+q), _) == None{} : Maybe<&2, Tr.Ent>}
  tp.none_at(Tr.get(Tr.prune(t, 1n+q), 1n+q), rm)

# a node whose parent is dropped is dropped: R would hold it under a
# parent R lacks
def tp.l1c(+t: List<&2, Tr.Ent>, +q: Nat, +y: Nat, +k: Nat, +pp: Nat, +v: Nat, +wi: {Tr.within(Tr.prune(t, 1n+q), t) == True{} : Bool}, +rR: {Tr.rooted.go(Tr.prune(t, 1n+q), Tr.prune(t, 1n+q)) == True{} : Bool}, +em: {TS.get(t, y) == Some{Tr.Ent{k, 1n+pp, v}} : Maybe<&2, Tr.Ent>}, ih: {Tr.get(Tr.prune(t, 1n+q), 1n+pp) == None{} : Maybe<&2, Tr.Ent>}, m2: Maybe<&2, Tr.Ent>, +e2m: {Tr.get(Tr.prune(t, 1n+q), y) == m2 : Maybe<&2, Tr.Ent>}) -> {m2 == None{} : Maybe<&2, Tr.Ent>}:
  match m2:
    case None{}:
      {==}
    case Some{+e2}:
      +E = {Tr.Ent{k, 1n+pp, v} : Tr.Ent}
      +gt = LM.tm.wm(Tr.prune(t, 1n+q), t, y, e2, wi, e2m)
      +gt2 = tp.get_ts(t, y, Some{E}, em)
      +eq = LALogic.tree.pt.some_inj(e2, E, Equal.trans(Maybe<&2, Tr.Ent>, Some{e2}, Tr.get(t, y), Some{E}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(t, y), Some{e2}, gt), gt2))
      +ok = LM.tm.ent_rw(z => {Tr.ok(Tr.prune(t, 1n+q), Tr.Ent.k(z), Tr.Ent.p(z)) == True{} : Bool}, e2, E, eq, LM.tm.rm(Tr.prune(t, 1n+q), Tr.prune(t, 1n+q), y, e2, rR, e2m))
      +hr = LLogicBool.tree.pt.and_r(Nat.is_lt(1n+pp, k), Tr.has(Tr.prune(t, 1n+q), 1n+pp), ok)
      +hn = Equal.cong(Maybe<&2, Tr.Ent>, Bool, z => Maybe.is_some(&2, Tr.Ent, z), Tr.get(Tr.prune(t, 1n+q), 1n+pp), None{}, ih)
      LM.tm.tf({Some{e2} == None{} : Maybe<&2, Tr.Ent>}, Equal.trans(Bool, True{}, Tr.has(Tr.prune(t, 1n+q), 1n+pp), False{}, Equal.sym(Bool, Tr.has(Tr.prune(t, 1n+q), 1n+pp), True{}, hr), hn))

# a node the spec finds below x is dropped
def tp.l1(f: Nat, +t: List<&2, Tr.Ent>, +q: Nat, +y: Nat, hit: Bool, m: Maybe<&2, Tr.Ent>, +rm: {Tr.has(Tr.prune(t, 1n+q), 1n+q) == False{} : Bool}, +wi: {Tr.within(Tr.prune(t, 1n+q), t) == True{} : Bool}, +rR: {Tr.rooted.go(Tr.prune(t, 1n+q), Tr.prune(t, 1n+q)) == True{} : Bool}, +eh: {Nat.is_eq(y, 1n+q) == hit : Bool}, +em: {TS.get(t, y) == m : Maybe<&2, Tr.Ent>}, hb: {TS.below(f, t, 1n+q, hit, m) == True{} : Bool}) -> {Tr.get(Tr.prune(t, 1n+q), y) == None{} : Maybe<&2, Tr.Ent>}:
  match f:
    case 0n:
      tp.at_x(t, q, y, rm, Equal.trans(Bool, Nat.is_eq(y, 1n+q), hit, True{}, eh, hb))
    case 1n+g:
      match hit:
        case True{}:
          tp.at_x(t, q, y, rm, eh)
        case False{}:
          match m:
            case None{}:
              LM.tm.ft({Tr.get(Tr.prune(t, 1n+q), y) == None{} : Maybe<&2, Tr.Ent>}, hb)
            case Some{e}:
              match e:
                case Tr.Ent{+k, p, +v}:
                  match p:
                    case 0n:
                      LM.tm.ft({Tr.get(Tr.prune(t, 1n+q), y) == None{} : Maybe<&2, Tr.Ent>}, hb)
                    case 1n++pp:
                      +ih = tp.l1(g, t, q, 1n+pp, Nat.is_eq(1n+pp, 1n+q), TS.get(t, 1n+pp), rm, wi, rR, {==}, {==}, hb)
                      tp.l1c(t, q, y, k, pp, v, wi, rR, em, ih, Tr.get(Tr.prune(t, 1n+q), y), {==})

# Below x when dropped (tp.l2)
# ----------------------------

# a dropped node that is not x: its parent is not 0 and is dropped
def tp.l2_ob(+t: List<&2, Tr.Ent>, +q: Nat, +y: Nat, +k: Nat, +p: Nat, +v: Nat, +ob: {Tr.only_below(t, 1n+q, Tr.prune(t, 1n+q)) == True{} : Bool}, eh: {Nat.is_eq(y, 1n+q) == False{} : Bool}, +gt: {Tr.get(t, y) == Some{Tr.Ent{k, p, v}} : Maybe<&2, Tr.Ent>}, gr: {Tr.get(Tr.prune(t, 1n+q), y) == None{} : Maybe<&2, Tr.Ent>}) -> {Bool.and(Bool.not(Nat.is_eq(p, 0n)), Bool.not(Tr.has(Tr.prune(t, 1n+q), p))) == True{} : Bool}:
  +E = {Tr.Ent{k, p, v} : Tr.Ent}
  +o = LM.tm.om(t, 1n+q, Tr.prune(t, 1n+q), y, E, ob, gt)
  +ky = LALogic.pt.eq_true(k, y, LM.tm.gk(t, y, E, gt))
  +na = Equal.trans(Bool, Tr.has(Tr.prune(t, 1n+q), k), Tr.has(Tr.prune(t, 1n+q), y), False{}, Equal.cong(Nat, Bool, z => Tr.has(Tr.prune(t, 1n+q), z), k, y, ky), Equal.cong(Maybe<&2, Tr.Ent>, Bool, z => Maybe.is_some(&2, Tr.Ent, z), Tr.get(Tr.prune(t, 1n+q), y), None{}, gr))
  +nb = Equal.trans(Bool, Nat.is_eq(k, 1n+q), Nat.is_eq(y, 1n+q), False{}, Equal.cong(Nat, Bool, z => Nat.is_eq(z, 1n+q), k, y, ky), eh)
  tp.or3(Tr.has(Tr.prune(t, 1n+q), k), Nat.is_eq(k, 1n+q), Bool.and(Bool.not(Nat.is_eq(p, 0n)), Bool.not(Tr.has(Tr.prune(t, 1n+q), p))), o, na, nb)

# a dropped node of t is below x, for the spec, with fuel f >= y
def tp.l2(f: Nat, +t: List<&2, Tr.Ent>, +q: Nat, +y: Nat, hit: Bool, m: Maybe<&2, Tr.Ent>, +ob: {Tr.only_below(t, 1n+q, Tr.prune(t, 1n+q)) == True{} : Bool}, +rt: {Tr.rooted.go(t, t) == True{} : Bool}, +eh: {Nat.is_eq(y, 1n+q) == hit : Bool}, +em: {TS.get(t, y) == m : Maybe<&2, Tr.Ent>}, hm: {Maybe.is_some(&2, Tr.Ent, m) == True{} : Bool}, +gr: {Tr.get(Tr.prune(t, 1n+q), y) == None{} : Maybe<&2, Tr.Ent>}, +yf: {Nat.is_le(y, f) == True{} : Bool}) -> {TS.below(f, t, 1n+q, hit, m) == True{} : Bool}:
  match f:
    case 0n:
      match hit:
        case True{}:
          {==}
        case False{}:
          match m:
            case None{}:
              LM.tm.ft({TS.below(0n, t, 1n+q, False{}, None{}) == True{} : Bool}, hm)
            case Some{e}:
              match e:
                case Tr.Ent{+k, p, +v}:
                  match p:
                    case 0n:
                      +gt = tp.get_ts(t, y, Some{Tr.Ent{k, 0n, v}}, em)
                      LM.tm.ft({TS.below(0n, t, 1n+q, False{}, Some{Tr.Ent{k, 0n, v}}) == True{} : Bool}, tp.l2_ob(t, q, y, k, 0n, v, ob, eh, gt, gr))
                    case 1n++pp:
                      +E = {Tr.Ent{k, 1n+pp, v} : Tr.Ent}
                      +gt = tp.get_ts(t, y, Some{E}, em)
                      +ok = LM.tm.rm(t, t, y, E, rt, gt)
                      +lt = LLogicBool.tree.pt.and_l(Nat.is_lt(1n+pp, k), Tr.has(t, 1n+pp), ok)
                      +ky = LALogic.pt.eq_true(k, y, LM.tm.gk(t, y, E, gt))
                      +lty = Equal.trans(Bool, Nat.is_lt(1n+pp, y), Nat.is_lt(1n+pp, k), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(1n+pp, z), y, k, Equal.sym(Nat, k, y, ky)), lt)
                      tp.lt_le0({TS.below(0n, t, 1n+q, False{}, Some{E}) == True{} : Bool}, 1n+pp, y, lty, yf)
    case 1n++g:
      match hit:
        case True{}:
          {==}
        case False{}:
          match m:
            case None{}:
              LM.tm.ft({TS.below(1n+g, t, 1n+q, False{}, None{}) == True{} : Bool}, hm)
            case Some{e}:
              match e:
                case Tr.Ent{+k, p, +v}:
                  match p:
                    case 0n:
                      +gt = tp.get_ts(t, y, Some{Tr.Ent{k, 0n, v}}, em)
                      LM.tm.ft({TS.below(1n+g, t, 1n+q, False{}, Some{Tr.Ent{k, 0n, v}}) == True{} : Bool}, tp.l2_ob(t, q, y, k, 0n, v, ob, eh, gt, gr))
                    case 1n++pp:
                      +E = {Tr.Ent{k, 1n+pp, v} : Tr.Ent}
                      +gt = tp.get_ts(t, y, Some{E}, em)
                      +ok = LM.tm.rm(t, t, y, E, rt, gt)
                      +lt = LLogicBool.tree.pt.and_l(Nat.is_lt(1n+pp, k), Tr.has(t, 1n+pp), ok)
                      +ht = LLogicBool.tree.pt.and_r(Nat.is_lt(1n+pp, k), Tr.has(t, 1n+pp), ok)
                      +ky = LALogic.pt.eq_true(k, y, LM.tm.gk(t, y, E, gt))
                      +lty = Equal.trans(Bool, Nat.is_lt(1n+pp, y), Nat.is_lt(1n+pp, k), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(1n+pp, z), y, k, Equal.sym(Nat, k, y, ky)), lt)
                      +hr = tp.not_t(Tr.has(Tr.prune(t, 1n+q), 1n+pp), tp.l2_ob(t, q, y, k, 1n+pp, v, ob, eh, gt, gr))
                      +hm2 = Equal.trans(Bool, TS.has(t, 1n+pp), Tr.has(t, 1n+pp), True{}, Equal.sym(Bool, Tr.has(t, 1n+pp), TS.has(t, 1n+pp), LB.ts.has(t, 1n+pp)), ht)
                      tp.l2(g, t, q, 1n+pp, Nat.is_eq(1n+pp, 1n+q), TS.get(t, 1n+pp), ob, rt, {==}, {==}, hm2, tp.none_at(Tr.get(Tr.prune(t, 1n+q), 1n+pp), hr), tp.lt_le(1n+pp, y, g, lty, yf))

# The model's result at every key
# -------------------------------

# no node of t at y: none of R either
def tp.p_none(+t: List<&2, Tr.Ent>, +q: Nat, +y: Nat, +wi: {Tr.within(Tr.prune(t, 1n+q), t) == True{} : Bool}, em: {TS.get(t, y) == None{} : Maybe<&2, Tr.Ent>}, m2: Maybe<&2, Tr.Ent>, +e2m: {Tr.get(Tr.prune(t, 1n+q), y) == m2 : Maybe<&2, Tr.Ent>}) -> {m2 == None{} : Maybe<&2, Tr.Ent>}:
  match m2:
    case None{}:
      {==}
    case Some{+e2}:
      +gt = LM.tm.wm(Tr.prune(t, 1n+q), t, y, e2, wi, e2m)
      +gn = tp.get_ts(t, y, None{}, em)
      LALogic.tree.pt.none_some({Some{e2} == None{} : Maybe<&2, Tr.Ent>}, e2, Equal.trans(Maybe<&2, Tr.Ent>, None{}, Tr.get(t, y), Some{e2}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(t, y), None{}, gn), gt))

# a node of t at y the spec keeps: R holds it
def tp.p_kept(+t: List<&2, Tr.Ent>, +q: Nat, +y: Nat, +E: Tr.Ent, +ob: {Tr.only_below(t, 1n+q, Tr.prune(t, 1n+q)) == True{} : Bool}, +rt: {Tr.rooted.go(t, t) == True{} : Bool}, +wi: {Tr.within(Tr.prune(t, 1n+q), t) == True{} : Bool}, +em: {TS.get(t, y) == Some{E} : Maybe<&2, Tr.Ent>}, eg: {TS.gone(t, 1n+q, y) == False{} : Bool}, m2: Maybe<&2, Tr.Ent>, +e2m: {Tr.get(Tr.prune(t, 1n+q), y) == m2 : Maybe<&2, Tr.Ent>}) -> {m2 == Some{E} : Maybe<&2, Tr.Ent>}:
  match m2:
    case None{}:
      +hm = Equal.cong(Maybe<&2, Tr.Ent>, Bool, z => Maybe.is_some(&2, Tr.Ent, z), TS.get(t, y), Some{E}, em)
      +gy = tp.l2(y, t, q, y, Nat.is_eq(y, 1n+q), TS.get(t, y), ob, rt, {==}, {==}, hm, e2m, tp.le_refl(y))
      LM.tm.tf({None{} == Some{E} : Maybe<&2, Tr.Ent>}, Equal.trans(Bool, True{}, TS.gone(t, 1n+q, y), False{}, Equal.sym(Bool, TS.gone(t, 1n+q, y), True{}, gy), eg))
    case Some{+e2}:
      +gt = LM.tm.wm(Tr.prune(t, 1n+q), t, y, e2, wi, e2m)
      Equal.trans(Maybe<&2, Tr.Ent>, Some{e2}, Tr.get(t, y), Some{E}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(t, y), Some{e2}, gt), tp.get_ts(t, y, Some{E}, em))

def tp.p_some(g: Bool, +t: List<&2, Tr.Ent>, +q: Nat, +y: Nat, +E: Tr.Ent, +rm: {Tr.has(Tr.prune(t, 1n+q), 1n+q) == False{} : Bool}, +ob: {Tr.only_below(t, 1n+q, Tr.prune(t, 1n+q)) == True{} : Bool}, +rt: {Tr.rooted.go(t, t) == True{} : Bool}, +wi: {Tr.within(Tr.prune(t, 1n+q), t) == True{} : Bool}, +rR: {Tr.rooted.go(Tr.prune(t, 1n+q), Tr.prune(t, 1n+q)) == True{} : Bool}, +em: {TS.get(t, y) == Some{E} : Maybe<&2, Tr.Ent>}, +eg: {TS.gone(t, 1n+q, y) == g : Bool}) -> {Tr.get(Tr.prune(t, 1n+q), y) == tp.kp(Bool.not(g), E) : Maybe<&2, Tr.Ent>}:
  match g:
    case True{}:
      tp.l1(y, t, q, y, Nat.is_eq(y, 1n+q), TS.get(t, y), rm, wi, rR, {==}, {==}, eg)
    case False{}:
      tp.p_kept(t, q, y, E, ob, rt, wi, em, eg, Tr.get(Tr.prune(t, 1n+q), y), {==})

# R at y is the spec's result at y
def tp.p(+t: List<&2, Tr.Ent>, +q: Nat, +y: Nat, m: Maybe<&2, Tr.Ent>, +rm: {Tr.has(Tr.prune(t, 1n+q), 1n+q) == False{} : Bool}, +ob: {Tr.only_below(t, 1n+q, Tr.prune(t, 1n+q)) == True{} : Bool}, +rt: {Tr.rooted.go(t, t) == True{} : Bool}, +wi: {Tr.within(Tr.prune(t, 1n+q), t) == True{} : Bool}, +rR: {Tr.rooted.go(Tr.prune(t, 1n+q), Tr.prune(t, 1n+q)) == True{} : Bool}, +em: {TS.get(t, y) == m : Maybe<&2, Tr.Ent>}) -> {Tr.get(Tr.prune(t, 1n+q), y) == tp.filt(m, t, 1n+q) : Maybe<&2, Tr.Ent>}:
  match m:
    case None{}:
      tp.p_none(t, q, y, wi, em, Tr.get(Tr.prune(t, 1n+q), y), {==})
    case Some{e}:
      match e:
        case Tr.Ent{+k, +p, +v}:
          +E = {Tr.Ent{k, p, v} : Tr.Ent}
          +ky = LALogic.pt.eq_true(k, y, LM.tm.gk(t, y, E, tp.get_ts(t, y, Some{E}, em)))
          %Equal.sym(Bool, TS.gone(t, 1n+q, k), TS.gone(t, 1n+q, y), Equal.cong(Nat, Bool, z => TS.gone(t, 1n+q, z), k, y, ky)) : {Tr.get(Tr.prune(t, 1n+q), y) == tp.kp(Bool.not(_), E) : Maybe<&2, Tr.Ent>}
          tp.p_some(TS.gone(t, 1n+q, y), t, q, y, E, rm, ob, rt, wi, rR, em, {==})

# R and the spec's result agree at every key
def tp.eq(+t: List<&2, Tr.Ent>, +q: Nat, +y: Nat, +st: {Tr.sorted(t) == True{} : Bool}, +rm: {Tr.has(Tr.prune(t, 1n+q), 1n+q) == False{} : Bool}, +ob: {Tr.only_below(t, 1n+q, Tr.prune(t, 1n+q)) == True{} : Bool}, +rt: {Tr.rooted.go(t, t) == True{} : Bool}, +wi: {Tr.within(Tr.prune(t, 1n+q), t) == True{} : Bool}, +rR: {Tr.rooted.go(Tr.prune(t, 1n+q), Tr.prune(t, 1n+q)) == True{} : Bool}) -> {Tr.get(Tr.prune(t, 1n+q), y) == Tr.get(TS.del.keep(t, t, 1n+q), y) : Maybe<&2, Tr.Ent>}:
  +D = TS.del.keep(t, t, 1n+q)
  +a = tp.p(t, q, y, TS.get(t, y), rm, ob, rt, wi, rR, {==})
  +b = Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(D, y), TS.get(D, y), tp.filt(TS.get(t, y), t, 1n+q), LB.ts.get(D, y), tp.f(t, t, 1n+q, y, st))
  Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(Tr.prune(t, 1n+q), y), tp.filt(TS.get(t, y), t, 1n+q), Tr.get(D, y), a, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(D, y), tp.filt(TS.get(t, y), t, 1n+q), b))

def tp.ag(es: List<&2, Tr.Ent>, +t: List<&2, Tr.Ent>, +q: Nat, +st: {Tr.sorted(t) == True{} : Bool}, +rm: {Tr.has(Tr.prune(t, 1n+q), 1n+q) == False{} : Bool}, +ob: {Tr.only_below(t, 1n+q, Tr.prune(t, 1n+q)) == True{} : Bool}, +rt: {Tr.rooted.go(t, t) == True{} : Bool}, +wi: {Tr.within(Tr.prune(t, 1n+q), t) == True{} : Bool}, +rR: {Tr.rooted.go(Tr.prune(t, 1n+q), Tr.prune(t, 1n+q)) == True{} : Bool}) -> LALogic.pt.Agree(es, Tr.prune(t, 1n+q), TS.del.keep(t, t, 1n+q)):
  match es:
    case Nil{}:
      Unit{}
    case +e <> rest:
      (tp.eq(t, q, Tr.Ent.k(e), st, rm, ob, rt, wi, rR), tp.ag(rest, t, q, st, rm, ob, rt, wi, rR))

# on a valid tree the model's delete of a key x > 0 is the spec's
def tp.prune(+t: List<&2, Tr.Ent>, +q: Nat, +good: {Tr.sound(t) == True{} : Bool}) -> {Tr.prune(t, 1n+q) == TS.del.keep(t, t, 1n+q) : List<&2, Tr.Ent>}:
  +st = LLogicBool.tree.pt.and_l(Tr.sorted(t), Tr.rooted(t), good)
  +rt = LLogicBool.tree.pt.and_r(Tr.sorted(t), Tr.rooted(t), good)
  +sR = LATreeSound.pt.del_sound(t, 1n+q, good)
  +stR = LLogicBool.tree.pt.and_l(Tr.sorted(Tr.prune(t, 1n+q)), Tr.rooted(Tr.prune(t, 1n+q)), sR)
  +rR = LLogicBool.tree.pt.and_r(Tr.sorted(Tr.prune(t, 1n+q)), Tr.rooted(Tr.prune(t, 1n+q)), sR)
  +rm = Tree.tree_delete_removes(t, good, 1n+q)
  +wi = Tree.tree_delete_within(t, good, 1n+q)
  +ob = Tree.tree_delete_only_below(t, good, 1n+q)
  +D = TS.del.keep(t, t, 1n+q)
  LATreeGet.pt.ext(Tr.prune(t, 1n+q), D, stR, tp.sorted_keep(t, t, 1n+q, st), tp.ag(Tr.prune(t, 1n+q), t, q, st, rm, ob, rt, wi, rR), tp.ag(D, t, q, st, rm, ob, rt, wi, rR))
