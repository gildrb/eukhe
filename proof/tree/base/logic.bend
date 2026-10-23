# eukhe: lemmas the proofs of area tree share: logic

import Base
import ../../../bend/ffi_tree.bend as Ft
import ../../../bend/tree.bend as Tr
import ../../../laws/tree.bend as Tree
import ../../base/bool.bend as LBool
import ../../base/logic/bool.bend as LLogicBool
import ../../base/logic/logic.bend as LLogicLogic
import ../../base/nat.bend as LNat

def pt.CD(c: Cmp, l: Type, e: Type, g: Type) -> Type:
  match c:
    case LT{}:
      l
    case EQ{}:
      e
    case GT{}:
      g

# Membership
# ----------

def pt.void(-A: Type, e: Empty) -> A:
  match e:

def pt.or_l(a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      LLogicLogic.pt.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def pt.or_r(a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      LLogicLogic.pt.absurd({b == False{} : Bool}, h)
    case False{}:
      h

def pt.flip(-a: Bool, h: {a == True{} : Bool}, g: {a == False{} : Bool}) -> Empty:
  LLogicLogic.pt.absurd(Empty, Equal.trans(Bool, True{}, a, False{}, Equal.sym(Bool, a, True{}, h), g))

# an or whose right side is false holds by its left side
def pt.or_l_true(a: Bool, +b: Bool, +h: {Bool.or(a, b) == True{} : Bool}, nb: {b == False{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pt.void({False{} == True{} : Bool}, pt.flip(b, h, nb))

# every node of pre is kept in b, or its key is gone
def pt.cov(pre: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>, +gone: List<&2, Nat>) -> Bool:
  match pre:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(Bool.or(Tr.has(b, Tr.Ent.k(e)), Tr.elem(gone, Tr.Ent.k(e))), pt.cov(rest, b, gone))

# every node of s hangs under the root, a node of pre, or a node before it
def pt.upl(s: List<&2, Tr.Ent>, +pre: List<&2, Tr.Ent>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(Tr.ok(pre, Tr.Ent.k(e), Tr.Ent.p(e)), pt.upl(rest, List.append(&2, Tr.Ent, pre, [e])))

# Rewind: still, minimal
# ----------------------

# b has the key of every node of s
def pt.allhas(s: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(Tr.has(b, Tr.Ent.k(e)), pt.allhas(rest, b))

# Delete

# every key of gone is x or more
def tc.nall(gone: List<&2, Nat>, +x: Nat) -> Bool:
  match gone:
    case Nil{}:
      True{}
    case +g <> rest:
      Bool.and(Bool.not(Nat.is_lt(g, x)), tc.nall(rest, x))

# every node of s is above its parent
def tc.desc(s: List<&2, Tr.Ent>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(Nat.is_lt(Tr.Ent.p(e), Tr.Ent.k(e)), tc.desc(rest))

# every fork's largest parent key is at least each side's
def tc.mpok(m: Tr.KMap) -> Bool:
  match m:
    case Tr.KNil{}:
      True{}
    case Tr.KOne{e}:
      True{}
    case Tr.KFork{+mid, +mp, +l, +r}:
      Bool.and(tc.mpok(l), Bool.and(tc.mpok(r), Bool.and(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r)))))

# every parent key of t is at most b
def tc.ple(t: List<&2, Tr.Ent>, +b: Nat) -> Bool:
  match t:
    case Nil{}:
      True{}
    case +e <> r:
      Bool.and(Nat.is_ge(b, Tr.Ent.p(e)), tc.ple(r, b))

# no key of t is x
def tc.nokey(t: List<&2, Tr.Ent>, +x: Nat) -> Bool:
  match t:
    case Nil{}:
      True{}
    case +e <> r:
      Bool.and(Bool.not(Nat.is_eq(Tr.Ent.k(e), x)), tc.nokey(r, x))

def tc.not_ff(b: Bool, h: {Bool.not(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      LLogicLogic.pt.absurd({False{} == True{} : Bool}, h)

def tc.or_fl(a: Bool, +b: Bool, +h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  pt.or_l(a, b, h)

# every key of gone is x, or below every key of s
def tc.gb(gone: List<&2, Nat>, +x: Nat, +s: List<&2, Tr.Ent>) -> Bool:
  match gone:
    case Nil{}:
      True{}
    case +z <> rest:
      Bool.and(Bool.or(Nat.is_eq(z, x), Tr.above(z, s)), tc.gb(rest, x, s))

# every key of ks is above k
def tc.gtall(ks: List<&2, Nat>, +k: Nat) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case +z <> rest:
      Bool.and(Nat.is_lt(k, z), tc.gtall(rest, k))

# The stack in the tree: order
# ----------------------------

# every key of t is less than m
def pd.lt_all(t: List<&2, Tr.Ent>, +m: Nat) -> Bool:
  match t:
    case Nil{}:
      True{}
    case e <> rest:
      Bool.and(Nat.is_lt(Tr.Ent.k(e), m), pd.lt_all(rest, m))

# the ops of a rewind
# ------------------

def tf.fit_l(+o: Tr.Op, -ops: List<&2, Tr.Op>, h: {Tree.tree.ops_fit(o <> ops) == True{} : Bool}) -> {Tree.tree.op_fits(o) == True{} : Bool}:
  LLogicBool.wr_and_l(Tree.tree.op_fits(o), Tree.tree.ops_fit(ops), h)

def tf.fit_r(+o: Tr.Op, -ops: List<&2, Tr.Op>, h: {Tree.tree.ops_fit(o <> ops) == True{} : Bool}) -> {Tree.tree.ops_fit(ops) == True{} : Bool}:
  LLogicBool.wr_and_r(Tree.tree.op_fits(o), Tree.tree.ops_fit(ops), h)

def pt.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LLogicLogic.tree.pt.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LLogicLogic.tree.pt.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pt.eq_true(p, q, h))

def pt.cmp_eq(a: Nat, b: Nat, h: {Nat.cmp(a, b) == EQ{} : Cmp}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      %h : pt.CD(_, Unit, {0n == 1n+q : Nat}, Unit)
      Unit{}
    case 1n+p 0n:
      %h : pt.CD(_, Unit, {1n+p == 0n : Nat}, Unit)
      Unit{}
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pt.cmp_eq(p, q, h))

# Keys that differ
# ----------------

def pt.ne_go(+a: Nat, +x: Nat, c: Bool, ec: {Nat.is_eq(a, x) == c : Bool}, -f: Nat -> Bool, na: {f(a) == False{} : Bool}, hx: {f(x) == True{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      +fe = Equal.cong(Nat, Bool, f, a, x, pt.eq_true(a, x, ec))
      pt.void({True{} == False{} : Bool}, pt.flip(f(x), hx, Equal.trans(Bool, f(x), f(a), False{}, Equal.sym(Bool, f(a), f(x), fe), na)))
    case False{}:
      {==}

def tc.nall_cons(+k: Nat, +gone: List<&2, Nat>, +x: Nat, +kx: {Nat.is_lt(k, x) == False{} : Bool}, +ng: {tc.nall(gone, x) == True{} : Bool}) -> {tc.nall(k <> gone, x) == True{} : Bool}:
  LBool.tree.pt.and_t(Bool.not(Nat.is_lt(k, x)), tc.nall(gone, x), LBool.pt.not_t(Nat.is_lt(k, x), kx), ng)

def tc.nokey_ge(t: List<&2, Tr.Ent>, +b: Nat, +x: Nat, +gb: {LLogicBool.tc.ge(t, b) == True{} : Bool}, +xb: {Nat.is_lt(x, b) == True{} : Bool}) -> {tc.nokey(t, x) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +e <> +r:
      LBool.tree.pt.and_t(Bool.not(Nat.is_eq(Tr.Ent.k(e), x)), tc.nokey(r, x), LBool.pt.not_t(Nat.is_eq(Tr.Ent.k(e), x), LNat.tc.ge_miss(e, b, x, LNat.tc.ge_head(e, r, b, gb), xb)), tc.nokey_ge(r, b, x, LLogicBool.tc.ge_tail(e, r, b, gb), xb))

def tc.nokey_lt(t: List<&2, Tr.Ent>, +b: Nat, +x: Nat, +lb: {LLogicBool.tc.lt(t, b) == True{} : Bool}, +xb: {Nat.is_lt(x, b) == False{} : Bool}) -> {tc.nokey(t, x) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case +e <> +r:
      LBool.tree.pt.and_t(Bool.not(Nat.is_eq(Tr.Ent.k(e), x)), tc.nokey(r, x), LBool.pt.not_t(Nat.is_eq(Tr.Ent.k(e), x), LNat.tc.lt_miss(e, b, x, LNat.tc.lt_head(e, r, b, lb), xb)), tc.nokey_lt(r, b, x, LLogicBool.tc.lt_tail(e, r, b, lb), xb))

# l1 and l2 hold the same node at the key of each node of es
def pt.Agree(es: List<&2, Tr.Ent>, +l1: List<&2, Tr.Ent>, +l2: List<&2, Tr.Ent>) -> Type:
  match es:
    case Nil{}:
      Unit
    case +e <> rest:
      ({Tr.get(l1, Tr.Ent.k(e)) == Tr.get(l2, Tr.Ent.k(e)) : Maybe<&2, Tr.Ent>} & pt.Agree(rest, l1, l2))

# The compiled core
# -----------------
# The key map refines the sorted list: a fork's left keys are below its
# split and its right keys at or above it (`tc.bst`), so its nodes in
# order are sorted (`tc.sorted_read`), a lookup down the map is the list
# lookup (`tc.get`), and a put, an unset and a drop are the list's set,
# unset and unset of each key (`tc.put_read`, `tc.unset_read`). A record
# on the map is apply on the list (`tc.rec_read`), with the model's answer
# (`tc.rec_ans`); a delete walks only the nodes from its key on, and the
# nodes before them never go (`tc.drops_ge`). The plan merges two sorted
# lists; the merge is diff (`tc.diff_m`).

# the keys of the nodes that prune.go removes from s, in order: the walk
# of a delete with its gone keys as a list (the core keeps them in a key
# map, `Tr.drops.s`; `tc.drops` shows the two walks drop the same keys)
def tc.dgo(s: List<&2, Tr.Ent>, +gone: List<&2, Nat>, hit: Bool) -> List<&2, Nat>:
  match s:
    case Nil{}:
      Nil{}
    case +e <> +rest:
      match hit:
        case True{}:
          Tr.Ent.k(e) <> tc.dgo(rest, Tr.Ent.k(e) <> gone, Tr.gone.at(rest, Tr.Ent.k(e) <> gone))
        case False{}:
          tc.dgo(rest, gone, Tr.gone.at(rest, gone))

# t less the nodes of keys ks, one by one
def tc.unsets(ks: List<&2, Nat>, t: List<&2, Tr.Ent>) -> List<&2, Tr.Ent>:
  match ks:
    case Nil{}:
      t
    case k <> rest:
      tc.unsets(rest, Tr.unset(t, k))

# The nodes a delete of x may remove: its node, and the nodes with a
# parent of x or more

def tc.fx.at(c: Bool, +e: Tr.Ent, rest: List<&2, Tr.Ent>) -> List<&2, Tr.Ent>:
  match c:
    case True{}:
      e <> rest
    case False{}:
      rest

def tc.fx(t: List<&2, Tr.Ent>, +x: Nat) -> List<&2, Tr.Ent>:
  match t:
    case Nil{}:
      Nil{}
    case +e <> r:
      tc.fx.at(Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.not(Nat.is_lt(Tr.Ent.p(e), x))), e, tc.fx(r, x))

def tc.fx_drop(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +x: Nat, +ne: {Nat.is_eq(Tr.Ent.k(e), x) == False{} : Bool}, +px: {Nat.is_lt(Tr.Ent.p(e), x) == True{} : Bool}) -> {tc.fx(e <> r, x) == tc.fx(r, x) : List<&2, Tr.Ent>}:
  %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), x), False{}, ne) : {tc.fx.at(Bool.or(_, Bool.not(Nat.is_lt(Tr.Ent.p(e), x))), e, tc.fx(r, x)) == tc.fx(r, x) : List<&2, Tr.Ent>}
  %Equal.sym(Bool, Nat.is_lt(Tr.Ent.p(e), x), True{}, px) : {tc.fx.at(Bool.or(False{}, Bool.not(_)), e, tc.fx(r, x)) == tc.fx(r, x) : List<&2, Tr.Ent>}
  {==}

# The gone map
# the gone keys of a list, as the gone map holds them
def tc.bld(gone: List<&2, Nat>) -> List<&2, Tr.Ent>:
  match gone:
    case Nil{}:
      Nil{}
    case k <> rest:
      Tr.set(tc.bld(rest), Tr.Ent{k, 0n, 0n})

def pt.MD(m: Maybe<&2, Tr.Ent>, n: Type, s: Type) -> Type:
  match m:
    case None{}:
      n
    case Some{x}:
      s

# Rewind: reaches
# ---------------
# A lookup after a patch follows the ops on its key (`pt.look`); the dels
# drop exactly the keys b lacks, the puts set exactly the nodes a lacks or
# holds differently. So the patched tree and b agree on every key, and two
# sorted trees that agree on their keys are equal (`pt.ext`).

def tree.pt.pick(c: Bool, n: Maybe<&2, Tr.Ent>, m: Maybe<&2, Tr.Ent>) -> Maybe<&2, Tr.Ent>:
  match c:
    case True{}:
      n
    case False{}:
      m

# the node at key x after one op, from m
def pt.upd(o: Tr.Op, m: Maybe<&2, Tr.Ent>, +x: Nat) -> Maybe<&2, Tr.Ent>:
  match o:
    case Tr.Put{+k, p, v}:
      tree.pt.pick(Nat.is_eq(k, x), Some{Tr.Ent{k, p, v}}, m)
    case Tr.Del{k}:
      tree.pt.pick(Nat.is_eq(k, x), None{}, m)

# the node at key x after the ops, from m
def pt.look(ops: List<&2, Tr.Op>, m: Maybe<&2, Tr.Ent>, +x: Nat) -> Maybe<&2, Tr.Ent>:
  match ops:
    case Nil{}:
      m
    case o <> rest:
      pt.look(rest, pt.upd(o, m, x), x)

def pt.pick_same(c: Bool, +m: Maybe<&2, Tr.Ent>) -> {tree.pt.pick(c, m, m) == m : Maybe<&2, Tr.Ent>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def tc.dg_ge(hit: Bool, +e: Tr.Ent, +r: List<&2, Tr.Ent>, +X: List<&2, Tr.Ent>, +gone: List<&2, Nat>, +ih1: {tc.dgo(r, gone, Tr.gone.at(r, gone)) == tc.dgo(X, gone, Tr.gone.at(X, gone)) : List<&2, Nat>}, ih2: {tc.dgo(r, Tr.Ent.k(e) <> gone, Tr.gone.at(r, Tr.Ent.k(e) <> gone)) == tc.dgo(X, Tr.Ent.k(e) <> gone, Tr.gone.at(X, Tr.Ent.k(e) <> gone)) : List<&2, Nat>}) -> {tc.dgo(e <> r, gone, hit) == tc.dgo(e <> X, gone, hit) : List<&2, Nat>}:
  match hit:
    case True{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, ys => Tr.Ent.k(e) <> ys, tc.dgo(r, Tr.Ent.k(e) <> gone, Tr.gone.at(r, Tr.Ent.k(e) <> gone)), tc.dgo(X, Tr.Ent.k(e) <> gone, Tr.gone.at(X, Tr.Ent.k(e) <> gone)), ih2)
    case False{}:
      ih1

def tc.mpok_l(+mid: Nat, +mp: Nat, +l: Tr.KMap, +r: Tr.KMap, +h: {tc.mpok(Tr.KFork{mid, mp, l, r}) == True{} : Bool}) -> {tc.mpok(l) == True{} : Bool}:
  LLogicBool.tree.pt.and_l(tc.mpok(l), Bool.and(tc.mpok(r), Bool.and(Nat.is_ge(mp, Tr.KMap.mp(l)), Nat.is_ge(mp, Tr.KMap.mp(r)))), h)

def tree.pt.none_some(-A: Type, -x: Tr.Ent, e: {None{} == Some{x} : Maybe<&2, Tr.Ent>}) -> A:
  %e : pt.MD(_, Unit, A)
  Unit{}

def pt.some_none(-A: Type, -x: Tr.Ent, e: {Some{x} == None{} : Maybe<&2, Tr.Ent>}) -> A:
  %e : pt.MD(_, A, Unit)
  Unit{}

def pt.ent_true(a: Tr.Ent, b: Tr.Ent, +h: {Tr.Ent.eq(a, b) == True{} : Bool}) -> {a == b : Tr.Ent}:
  match a b:
    case Tr.Ent{+ak, +ap, +av} Tr.Ent{+bk, +bp, +bv}:
      +hk = pt.eq_true(ak, bk, LLogicBool.tree.pt.and_l(Nat.is_eq(ak, bk), Bool.and(Nat.is_eq(ap, bp), Nat.is_eq(av, bv)), h))
      +h2 = LLogicBool.tree.pt.and_r(Nat.is_eq(ak, bk), Bool.and(Nat.is_eq(ap, bp), Nat.is_eq(av, bv)), h)
      +hp = pt.eq_true(ap, bp, LLogicBool.tree.pt.and_l(Nat.is_eq(ap, bp), Nat.is_eq(av, bv), h2))
      +hv = pt.eq_true(av, bv, LLogicBool.tree.pt.and_r(Nat.is_eq(ap, bp), Nat.is_eq(av, bv), h2))
      %hk : {Tr.Ent{ak, ap, av} == Tr.Ent{_, bp, bv} : Tr.Ent}
      %hp : {Tr.Ent{ak, ap, av} == Tr.Ent{ak, _, bv} : Tr.Ent}
      %hv : {Tr.Ent{ak, ap, av} == Tr.Ent{ak, ap, _} : Tr.Ent}
      {==}

# a lookup that is the same as Some{e} is Some{e}
def pt.same_some(m: Maybe<&2, Tr.Ent>, +e: Tr.Ent, h: {Tr.same(m, Some{e}) == True{} : Bool}) -> {m == Some{e} : Maybe<&2, Tr.Ent>}:
  match m:
    case None{}:
      LLogicLogic.tree.pt.absurdF({None{} == Some{e} : Maybe<&2, Tr.Ent>}, h)
    case Some{x}:
      Equal.cong(Tr.Ent, Maybe<&2, Tr.Ent>, y => Some{y}, x, e, pt.ent_true(x, e, h))

def pt.val(m: Maybe<&2, Tr.Ent>, d: Tr.Ent) -> Tr.Ent:
  match m:
    case None{}:
      d
    case Some{x}:
      x

def tree.pt.some_inj(+x: Tr.Ent, +y: Tr.Ent, h: {Some{x} == Some{y} : Maybe<&2, Tr.Ent>}) -> {x == y : Tr.Ent}:
  Equal.cong(Maybe<&2, Tr.Ent>, Tr.Ent, m => pt.val(m, x), Some{x}, Some{y}, h)

# an unset of a key above the head keeps the head
def tc.unsets_cons(ks: List<&2, Nat>, +e: Tr.Ent, +r: List<&2, Tr.Ent>, +gt: {tc.gtall(ks, Tr.Ent.k(e)) == True{} : Bool}) -> {tc.unsets(ks, e <> r) == e <> tc.unsets(ks, r) : List<&2, Tr.Ent>}:
  match ks:
    case Nil{}:
      {==}
    case +z <> +rest:
      +lt = LLogicBool.tree.pt.and_l(Nat.is_lt(Tr.Ent.k(e), z), tc.gtall(rest, Tr.Ent.k(e)), gt)
      +ne = LNat.pt.lt_ne(Tr.Ent.k(e), z, lt)
      %Equal.sym(Bool, Nat.is_eq(Tr.Ent.k(e), z), False{}, ne) : {tc.unsets(rest, Tr.unset.go(e <> r, z, _)) == e <> tc.unsets(rest, Tr.unset(r, z)) : List<&2, Tr.Ent>}
      tc.unsets_cons(rest, e, Tr.unset(r, z), LLogicBool.tree.pt.and_r(Nat.is_lt(Tr.Ent.k(e), z), tc.gtall(rest, Tr.Ent.k(e)), gt))

def tc.desc_of(s: List<&2, Tr.Ent>, +all: List<&2, Tr.Ent>, +rs: {Tr.rooted.go(s, all) == True{} : Bool}) -> {tc.desc(s) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case +e <> +rest:
      +o = LLogicBool.tree.pt.and_l(Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(rest, all), rs)
      +lt = LLogicBool.tree.pt.and_l(Nat.is_lt(Tr.Ent.p(e), Tr.Ent.k(e)), Bool.or(Nat.is_eq(Tr.Ent.p(e), 0n), Tr.has(all, Tr.Ent.p(e))), o)
      LBool.tree.pt.and_t(Nat.is_lt(Tr.Ent.p(e), Tr.Ent.k(e)), tc.desc(rest), lt, tc.desc_of(rest, all, LLogicBool.tree.pt.and_r(Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)), Tr.rooted.go(rest, all), rs)))

# the items of a list of ops, then rest
def tf.items(ops: List<&2, Tr.Op>, rest: String) -> String:
  match ops:
    case Nil{}:
      rest
    case o <> r:
      Ft.put_op(o, tf.items(r, rest))
