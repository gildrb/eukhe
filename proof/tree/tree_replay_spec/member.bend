# eukhe: lemmas of LAW tree_replay_spec: what a scan of a list says of its
# node at a key: the node found has that key; a rooted, within or
# only_below scan holds of it.

import Base
import ../../../bend/tree.bend as Tr
import ../../base/logic/bool.bend as LLogicBool
import ../base/logic.bend as LALogic
import ../base/tree/get.bend as LATreeGet

def tm.B(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

# True is not False
def tm.tf(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : tm.B(_, Unit, A)
  Unit{}

def tm.ft(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : tm.B(_, A, Unit)
  Unit{}

# the first node of a list, found at key y: it is the node e
def tm.hit(+hh: Tr.Ent, +r: List<&2, Tr.Ent>, +y: Nat, +e: Tr.Ent, eb: {Nat.is_eq(Tr.Ent.k(hh), y) == True{} : Bool}, h: {Tr.get(hh <> r, y) == Some{e} : Maybe<&2, Tr.Ent>}) -> {hh == e : Tr.Ent}:
  LALogic.tree.pt.some_inj(hh, e, Equal.trans(Maybe<&2, Tr.Ent>, Some{hh}, Tr.get(hh <> r, y), Some{e}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(hh <> r, y), Some{hh}, LATreeGet.pt.get_hit(hh, r, y, eb)), h))

# a later node, found at key y
def tm.miss(+hh: Tr.Ent, +r: List<&2, Tr.Ent>, +y: Nat, -e: Tr.Ent, eb: {Nat.is_eq(Tr.Ent.k(hh), y) == False{} : Bool}, h: {Tr.get(hh <> r, y) == Some{e} : Maybe<&2, Tr.Ent>}) -> {Tr.get(r, y) == Some{e} : Maybe<&2, Tr.Ent>}:
  Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(r, y), Tr.get(hh <> r, y), Some{e}, Equal.sym(Maybe<&2, Tr.Ent>, Tr.get(hh <> r, y), Tr.get(r, y), LATreeGet.pt.get_miss(hh, r, y, eb)), h)

def tm.ent_rw(-A: Tr.Ent -> Type, -a: Tr.Ent, -b: Tr.Ent, e: {a == b : Tr.Ent}, h: A(a)) -> A(b):
  %e : A(_)
  h

# Keys
# ----

def tm.gk.at(b: Bool, +hh: Tr.Ent, +r: List<&2, Tr.Ent>, +y: Nat, +e: Tr.Ent, +eb: {Nat.is_eq(Tr.Ent.k(hh), y) == b : Bool}, h: {Tr.get(hh <> r, y) == Some{e} : Maybe<&2, Tr.Ent>}, ih: {Tr.get(r, y) == Some{e} : Maybe<&2, Tr.Ent>} -> {Nat.is_eq(Tr.Ent.k(e), y) == True{} : Bool}) -> {Nat.is_eq(Tr.Ent.k(e), y) == True{} : Bool}:
  match b:
    case True{}:
      tm.ent_rw(z => {Nat.is_eq(Tr.Ent.k(z), y) == True{} : Bool}, hh, e, tm.hit(hh, r, y, e, eb, h), eb)
    case False{}:
      ih(tm.miss(hh, r, y, e, eb, h))

# the node found at key y has key y
def tm.gk(l: List<&2, Tr.Ent>, +y: Nat, +e: Tr.Ent, h: {Tr.get(l, y) == Some{e} : Maybe<&2, Tr.Ent>}) -> {Nat.is_eq(Tr.Ent.k(e), y) == True{} : Bool}:
  match l:
    case Nil{}:
      LALogic.tree.pt.none_some({Nat.is_eq(Tr.Ent.k(e), y) == True{} : Bool}, e, h)
    case +hh <> +r:
      tm.gk.at(Nat.is_eq(Tr.Ent.k(hh), y), hh, r, y, e, {==}, h, z => tm.gk(r, y, e, z))

# Rooted
# ------

def tm.rm.at(b: Bool, +hh: Tr.Ent, +r: List<&2, Tr.Ent>, +all: List<&2, Tr.Ent>, +y: Nat, +e: Tr.Ent, +eb: {Nat.is_eq(Tr.Ent.k(hh), y) == b : Bool}, +rs: {Tr.rooted.go(hh <> r, all) == True{} : Bool}, h: {Tr.get(hh <> r, y) == Some{e} : Maybe<&2, Tr.Ent>}, ih: {Tr.rooted.go(r, all) == True{} : Bool} -> {Tr.get(r, y) == Some{e} : Maybe<&2, Tr.Ent>} -> {Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)) == True{} : Bool}) -> {Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)) == True{} : Bool}:
  match b:
    case True{}:
      tm.ent_rw(z => {Tr.ok(all, Tr.Ent.k(z), Tr.Ent.p(z)) == True{} : Bool}, hh, e, tm.hit(hh, r, y, e, eb, h), LLogicBool.tree.pt.and_l(Tr.ok(all, Tr.Ent.k(hh), Tr.Ent.p(hh)), Tr.rooted.go(r, all), rs))
    case False{}:
      ih(LLogicBool.tree.pt.and_r(Tr.ok(all, Tr.Ent.k(hh), Tr.Ent.p(hh)), Tr.rooted.go(r, all), rs), tm.miss(hh, r, y, e, eb, h))

# a node of a rooted scan hangs in all
def tm.rm(s: List<&2, Tr.Ent>, +all: List<&2, Tr.Ent>, +y: Nat, +e: Tr.Ent, +rs: {Tr.rooted.go(s, all) == True{} : Bool}, h: {Tr.get(s, y) == Some{e} : Maybe<&2, Tr.Ent>}) -> {Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)) == True{} : Bool}:
  match s:
    case Nil{}:
      LALogic.tree.pt.none_some({Tr.ok(all, Tr.Ent.k(e), Tr.Ent.p(e)) == True{} : Bool}, e, h)
    case +hh <> +r:
      tm.rm.at(Nat.is_eq(Tr.Ent.k(hh), y), hh, r, all, y, e, {==}, rs, h, z1 => z2 => tm.rm(r, all, y, e, z1, z2))

# Within
# ------

def tm.wm.at(b: Bool, +hh: Tr.Ent, +r: List<&2, Tr.Ent>, +t: List<&2, Tr.Ent>, +y: Nat, +e: Tr.Ent, +eb: {Nat.is_eq(Tr.Ent.k(hh), y) == b : Bool}, +w: {Tr.within(hh <> r, t) == True{} : Bool}, h: {Tr.get(hh <> r, y) == Some{e} : Maybe<&2, Tr.Ent>}, ih: {Tr.within(r, t) == True{} : Bool} -> {Tr.get(r, y) == Some{e} : Maybe<&2, Tr.Ent>} -> {Tr.get(t, y) == Some{e} : Maybe<&2, Tr.Ent>}) -> {Tr.get(t, y) == Some{e} : Maybe<&2, Tr.Ent>}:
  match b:
    case True{}:
      +sm = LALogic.pt.same_some(Tr.get(t, Tr.Ent.k(hh)), hh, LLogicBool.tree.pt.and_l(Tr.same(Tr.get(t, Tr.Ent.k(hh)), Some{hh}), Tr.within(r, t), w))
      +ky = LALogic.pt.eq_true(Tr.Ent.k(hh), y, eb)
      +g1 = Equal.trans(Maybe<&2, Tr.Ent>, Tr.get(t, y), Tr.get(t, Tr.Ent.k(hh)), Some{hh}, Equal.cong(Nat, Maybe<&2, Tr.Ent>, z => Tr.get(t, z), y, Tr.Ent.k(hh), Equal.sym(Nat, Tr.Ent.k(hh), y, ky)), sm)
      tm.ent_rw(z => {Tr.get(t, y) == Some{z} : Maybe<&2, Tr.Ent>}, hh, e, tm.hit(hh, r, y, e, eb, h), g1)
    case False{}:
      ih(LLogicBool.tree.pt.and_r(Tr.same(Tr.get(t, Tr.Ent.k(hh)), Some{hh}), Tr.within(r, t), w), tm.miss(hh, r, y, e, eb, h))

# a node of a scan within t is t's node at its key
def tm.wm(r: List<&2, Tr.Ent>, +t: List<&2, Tr.Ent>, +y: Nat, +e: Tr.Ent, +w: {Tr.within(r, t) == True{} : Bool}, h: {Tr.get(r, y) == Some{e} : Maybe<&2, Tr.Ent>}) -> {Tr.get(t, y) == Some{e} : Maybe<&2, Tr.Ent>}:
  match r:
    case Nil{}:
      LALogic.tree.pt.none_some({Tr.get(t, y) == Some{e} : Maybe<&2, Tr.Ent>}, e, h)
    case +hh <> +rr:
      tm.wm.at(Nat.is_eq(Tr.Ent.k(hh), y), hh, rr, t, y, e, {==}, w, h, z1 => z2 => tm.wm(rr, t, y, e, z1, z2))

# Only below
# ----------

# a node a delete of x may drop from the result r: it stays, it is x, or
# its parent is a node r does not hold
def tm.OB(+e: Tr.Ent, +x: Nat, +r: List<&2, Tr.Ent>) -> Bool:
  Bool.or(Tr.has(r, Tr.Ent.k(e)), Bool.or(Nat.is_eq(Tr.Ent.k(e), x), Bool.and(Bool.not(Nat.is_eq(Tr.Ent.p(e), 0n)), Bool.not(Tr.has(r, Tr.Ent.p(e))))))

def tm.om.at(b: Bool, +hh: Tr.Ent, +s: List<&2, Tr.Ent>, +x: Nat, +r: List<&2, Tr.Ent>, +y: Nat, +e: Tr.Ent, +eb: {Nat.is_eq(Tr.Ent.k(hh), y) == b : Bool}, +o: {Tr.only_below(hh <> s, x, r) == True{} : Bool}, h: {Tr.get(hh <> s, y) == Some{e} : Maybe<&2, Tr.Ent>}, ih: {Tr.only_below(s, x, r) == True{} : Bool} -> {Tr.get(s, y) == Some{e} : Maybe<&2, Tr.Ent>} -> {tm.OB(e, x, r) == True{} : Bool}) -> {tm.OB(e, x, r) == True{} : Bool}:
  match b:
    case True{}:
      tm.ent_rw(z => {tm.OB(z, x, r) == True{} : Bool}, hh, e, tm.hit(hh, s, y, e, eb, h), LLogicBool.tree.pt.and_l(tm.OB(hh, x, r), Tr.only_below(s, x, r), o))
    case False{}:
      ih(LLogicBool.tree.pt.and_r(tm.OB(hh, x, r), Tr.only_below(s, x, r), o), tm.miss(hh, s, y, e, eb, h))

# a node of t that a delete of x drops from r: it is x, or its parent is
# dropped too
def tm.om(s: List<&2, Tr.Ent>, +x: Nat, +r: List<&2, Tr.Ent>, +y: Nat, +e: Tr.Ent, +o: {Tr.only_below(s, x, r) == True{} : Bool}, h: {Tr.get(s, y) == Some{e} : Maybe<&2, Tr.Ent>}) -> {tm.OB(e, x, r) == True{} : Bool}:
  match s:
    case Nil{}:
      LALogic.tree.pt.none_some({tm.OB(e, x, r) == True{} : Bool}, e, h)
    case +hh <> +rest:
      tm.om.at(Nat.is_eq(Tr.Ent.k(hh), y), hh, rest, x, r, y, e, {==}, o, h, z1 => z2 => tm.om(rest, x, r, y, e, z1, z2))
