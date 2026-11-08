# eukhe: lemmas the proofs of area tree share: whatever the entry's
# decoders read is the laws' spelling of what they read (tree.spell_*),
# then the rest, and every number of it fits the wire. Field by field with
# the wire's exactness laws (wire_nat_exact, wire_nat_decoded_fits); an
# unknown tag reads Bad. Each stage carries the input spelled up to its
# field (`e`).

import Base
import ../../../bend/ffi_tree.bend as Ft
import ../../../bend/tree.bend as Tr
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/tree.bend as Tree
import ../../../laws/wire.bend as Wire
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits

# both halves of an and hold
def te.and2(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  %Equal.sym(Bool, b, True{}, eb) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

# s is the tag t then s1, and s1 is x: s is the tag t then x
def te.after(-s: String, +t: Nat, -s1: String, -x: String, pre: {s == Wr.put_nat(t, s1) : String}, e: {s1 == x : String}) -> {s == Wr.put_nat(t, x) : String}:
  Equal.trans(String, s, Wr.put_nat(t, s1), Wr.put_nat(t, x), pre, Equal.cong(String, String, z => Wr.put_nat(t, z), s1, x, e))

# A Nat
# -----

def te.N(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def te.nat.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> te.N(s, d):
  match d:
    case Wr.Got{+n, +r}:
      +e = ed
      (Wire.wire_nat_exact(s, n, r, e), Wire.wire_nat_decoded_fits(s, n, r, e))
    case Wr.Bad{}:
      Unit{}

# a Nat decoded is spelled, and fits
def te.nat(+s: String) -> te.N(s, Wr.get_nat(s)):
  te.nat.at(s, Wr.get_nat(s), {==})

# An op
# -----

def te.O(s: String, d: Wr.Dec<Tr.Op>) -> Type:
  match d:
    case Wr.Got{o, r}:
      {s == Tree.tree.spell_op(o, r) : String} & {Tree.tree.op_fits(o) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def te.op.v(-s: String, +k: Nat, +p: Nat, -s3: String, e: {s == Wr.put_nat(0n, Wr.put_nat(k, Wr.put_nat(p, s3))) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, fp: {LawsBase.wire_fits(p) == True{} : Bool}, d: Wr.Dec<Nat>, nd: te.N(s3, d)) -> te.O(s, Ft.get_op.v(k, p, d)):
  match d:
    case Wr.Got{+v, +s4}:
      (e3, fv) = nd
      (Equal.trans(String, s, Wr.put_nat(0n, Wr.put_nat(k, Wr.put_nat(p, s3))), Wr.put_nat(0n, Wr.put_nat(k, Wr.put_nat(p, Wr.put_nat(v, s4)))), e, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(k, Wr.put_nat(p, z))), s3, Wr.put_nat(v, s4), e3)),
        te.and2(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(p), LawsBase.wire_fits(v)), fk, te.and2(LawsBase.wire_fits(p), LawsBase.wire_fits(v), fp, fv)))
    case Wr.Bad{}:
      Unit{}

def te.op.p(-s: String, +k: Nat, -s2: String, e: {s == Wr.put_nat(0n, Wr.put_nat(k, s2)) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<Nat>, nd: te.N(s2, d)) -> te.O(s, Ft.get_op.p(k, d)):
  match d:
    case Wr.Got{+p, +s3}:
      (e2, fp) = nd
      te.op.v(s, k, p, s3, Equal.trans(String, s, Wr.put_nat(0n, Wr.put_nat(k, s2)), Wr.put_nat(0n, Wr.put_nat(k, Wr.put_nat(p, s3))), e, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(k, z)), s2, Wr.put_nat(p, s3), e2)), fk, fp, Wr.get_nat(s3), te.nat(s3))
    case Wr.Bad{}:
      Unit{}

def te.op.k(-s: String, -s1: String, e: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Nat>, nd: te.N(s1, d)) -> te.O(s, Ft.get_op.put(d)):
  match d:
    case Wr.Got{+k, +s2}:
      (e1, fk) = nd
      te.op.p(s, k, s2, te.after(s, 0n, s1, Wr.put_nat(k, s2), e, e1), fk, Wr.get_nat(s2), te.nat(s2))
    case Wr.Bad{}:
      Unit{}

def te.op.del(-s: String, -s1: String, e: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, nd: te.N(s1, d)) -> te.O(s, Ft.get_op.del(d)):
  match d:
    case Wr.Got{+k, +s2}:
      (e1, fk) = nd
      (te.after(s, 1n, s1, Wr.put_nat(k, s2), e, e1), fk)
    case Wr.Bad{}:
      Unit{}

def te.op.tag(-s: String, n: Nat, +s1: String, e: {s == Wr.put_nat(n, s1) : String}) -> te.O(s, Ft.get_op.tag(n, s1)):
  match n:
    case 0n:
      te.op.k(s, s1, e, Wr.get_nat(s1), te.nat(s1))
    case 1n+a:
      match a:
        case 0n:
          te.op.del(s, s1, e, Wr.get_nat(s1), te.nat(s1))
        case 1n+b:
          Unit{}

def te.op.go(-s: String, d: Wr.Dec<Nat>, nd: te.N(s, d)) -> te.O(s, Ft.get_op.go(d)):
  match d:
    case Wr.Got{+n, +s1}:
      (e, f) = nd
      te.op.tag(s, n, s1, e)
    case Wr.Bad{}:
      Unit{}

# an op decoded is spelled, and fits
def te.op(+s: String) -> te.O(s, Ft.get_op(s)):
  te.op.go(s, Wr.get_nat(s), te.nat(s))

# The ops of a rewind
# -------------------

# what the item loop's answer says about its input s (m + 1 ops)
def te.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Tr.Op>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Tree.tree.spell_ops(xs, r) : String} & ({List.length(&2, Tr.Op, xs) == 1n+m : Nat} & {Tree.tree.ops_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def te.ops.step(-s: String, +x: Tr.Op, +s3: String, -k: Nat, ex: {s == Tree.tree.spell_op(x, s3) : String}, fx: {Tree.tree.op_fits(x) == True{} : Bool},
  d: Wr.Dec<List<&2, Tr.Op>>, ih: te.PL(s3, k, d)) -> te.PL(s, 1n+k, Wr.get_list.cons(Tr.Op, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (Equal.trans(String, s, Tree.tree.spell_op(x, s3), Tree.tree.spell_op(x, Tree.tree.spell_ops(ys, r)), ex,
          Equal.cong(String, String, z => Tree.tree.spell_op(x, z), s3, Tree.tree.spell_ops(ys, r), e1)),
        (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Tr.Op, ys), 1n+k, e2), te.and2(Tree.tree.op_fits(x), Tree.tree.ops_fit(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only spelled ops that fit
def te.ops.loop(m: Nat, cur: Wr.Dec<Tr.Op>, +s: String, pc: te.O(s, cur)) ->
  te.PL(s, m, Wr.get_list.go(~Tr.Op, ~Ft.get_op, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, te.and2(Tree.tree.op_fits(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      te.ops.step(s, x, s3, k, e, f, Wr.get_list.go(~Tr.Op, ~Ft.get_op, k, Ft.get_op(s3)),
        te.ops.loop(k, Ft.get_op(s3), s3, te.op(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder's answer says about its input s
def te.LS(s: String, d: Wr.Dec<List<&2, Tr.Op>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_nat(List.length(&2, Tr.Op, xs), Tree.tree.spell_ops(xs, r)) : String} & ({LawsBase.wire_fits(List.length(&2, Tr.Op, xs)) == True{} : Bool} & {Tree.tree.ops_fit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def te.ops.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Tr.Op>, -r: String,
  en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == Tree.tree.spell_ops(xs, r) : String},
  e2: {List.length(&2, Tr.Op, xs) == 1n+m : Nat}) -> {s == Wr.put_nat(List.length(&2, Tr.Op, xs), Tree.tree.spell_ops(xs, r)) : String}:
  %Equal.sym(Nat, List.length(&2, Tr.Op, xs), 1n+m, e2) : {s == Wr.put_nat(_, Tree.tree.spell_ops(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def te.ops.conv_f(-m: Nat, -xs: List<&2, Tr.Op>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  e2: {List.length(&2, Tr.Op, xs) == 1n+m : Nat}) -> {LawsBase.wire_fits(List.length(&2, Tr.Op, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Tr.Op, xs), 1n+m, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
  fn

def te.ops.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String},
  fn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  d: Wr.Dec<List<&2, Tr.Op>>, pl: te.PL(s2, m, d)) -> te.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      (te.ops.conv_s(s, s2, m, xs, r, en, e1, e2), (te.ops.conv_f(m, xs, fn, e2), e3))
    case Wr.Bad{}:
      Unit{}

def te.ops.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String},
  fn: {LawsBase.wire_fits(n) == True{} : Bool}) ->
  te.LS(s, Wr.get_list.start(~Tr.Op, ~Ft.get_op, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, (fn, {==}))
    case 1n++m:
      te.ops.conv(s, s2, m, en, fn, Wr.get_list.go(~Tr.Op, ~Ft.get_op, m, Ft.get_op(s2)),
        te.ops.loop(m, Ft.get_op(s2), s2, te.op(s2)))

def te.ops.top(-s: String, d: Wr.Dec<Nat>, nd: te.N(s, d)) ->
  te.LS(s, Wr.get_list.start(~Tr.Op, ~Ft.get_op, d)):
  match d:
    case Wr.Got{+n, +s2}:
      (en, fn) = nd
      te.ops.nat(s, n, s2, en, fn)
    case Wr.Bad{}:
      Unit{}

# a list of ops decoded is its count then the ops spelled, all fitting
def te.ops(+s: String) -> te.LS(s, Wr.get_list(~Tr.Op, ~Ft.get_op, s)):
  te.ops.top(s, Wr.get_nat(s), te.nat(s))

# An ask
# ------

def te.A(s: String, d: Wr.Dec<Tr.Ask>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == Tree.tree.spell_ask(q, r) : String} & {Tree.tree.ask_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def te.rec.do(-s: String, -s2: String, e: {s == Wr.put_nat(0n, Wr.put_nat(0n, s2)) : String}, d: Wr.Dec<Tr.Op>, od: te.O(s2, d)) -> te.A(s, Ft.get_ask.note(Ft.get_rec.do(d))):
  match d:
    case Wr.Got{+o, +s3}:
      (e1, f) = od
      (Equal.trans(String, s, Wr.put_nat(0n, Wr.put_nat(0n, s2)), Wr.put_nat(0n, Wr.put_nat(0n, Tree.tree.spell_op(o, s3))), e, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(0n, z)), s2, Tree.tree.spell_op(o, s3), e1)), f)
    case Wr.Bad{}:
      Unit{}

def te.rec.rewind(-s: String, -s2: String, e: {s == Wr.put_nat(0n, Wr.put_nat(1n, s2)) : String}, d: Wr.Dec<List<&2, Tr.Op>>, ld: te.LS(s2, d)) -> te.A(s, Ft.get_ask.note(Ft.get_rec.rewind(d))):
  match d:
    case Wr.Got{+ops, +s3}:
      (e1, f12) = ld
      (f1, f2) = f12
      (Equal.trans(String, s, Wr.put_nat(0n, Wr.put_nat(1n, s2)), Wr.put_nat(0n, Wr.put_nat(1n, Wr.put_nat(List.length(&2, Tr.Op, ops), Tree.tree.spell_ops(ops, s3)))), e, Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(1n, z)), s2, Wr.put_nat(List.length(&2, Tr.Op, ops), Tree.tree.spell_ops(ops, s3)), e1)),
        te.and2(LawsBase.wire_fits(List.length(&2, Tr.Op, ops)), Tree.tree.ops_fit(ops), f1, f2))
    case Wr.Bad{}:
      Unit{}

def te.rec.tag(-s: String, n: Nat, +s2: String, e: {s == Wr.put_nat(0n, Wr.put_nat(n, s2)) : String}) -> te.A(s, Ft.get_ask.note(Ft.get_rec.tag(n, s2))):
  match n:
    case 0n:
      te.rec.do(s, s2, e, Ft.get_op(s2), te.op(s2))
    case 1n+a:
      match a:
        case 0n:
          te.rec.rewind(s, s2, e, Wr.get_list(~Tr.Op, ~Ft.get_op, s2), te.ops(s2))
        case 1n+b:
          Unit{}

def te.rec.go(-s: String, -s1: String, e: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Nat>, nd: te.N(s1, d)) -> te.A(s, Ft.get_ask.note(Ft.get_rec.go(d))):
  match d:
    case Wr.Got{+n, +s2}:
      (e1, f1) = nd
      te.rec.tag(s, n, s2, te.after(s, 0n, s1, Wr.put_nat(n, s2), e, e1))
    case Wr.Bad{}:
      Unit{}

def te.plan(-s: String, -s1: String, e: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, nd: te.N(s1, d)) -> te.A(s, Ft.get_ask.plan(d)):
  match d:
    case Wr.Got{+n, +s2}:
      (e1, f) = nd
      (te.after(s, 1n, s1, Wr.put_nat(n, s2), e, e1), f)
    case Wr.Bad{}:
      Unit{}

def te.snap(-s: String, -s1: String, e: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Nat>, nd: te.N(s1, d)) -> te.A(s, Ft.get_ask.snap(d)):
  match d:
    case Wr.Got{+n, +s2}:
      (e1, f) = nd
      (te.after(s, 2n, s1, Wr.put_nat(n, s2), e, e1), f)
    case Wr.Bad{}:
      Unit{}

def te.ask.tag(-s: String, n: Nat, +s1: String, e: {s == Wr.put_nat(n, s1) : String}) -> te.A(s, Ft.get_ask.tag(n, s1)):
  match n:
    case 0n:
      te.rec.go(s, s1, e, Wr.get_nat(s1), te.nat(s1))
    case 1n+a:
      match a:
        case 0n:
          te.plan(s, s1, e, Wr.get_nat(s1), te.nat(s1))
        case 1n+b:
          match b:
            case 0n:
              te.snap(s, s1, e, Wr.get_nat(s1), te.nat(s1))
            case 1n+c:
              Unit{}

def te.ask.go(-s: String, d: Wr.Dec<Nat>, nd: te.N(s, d)) -> te.A(s, Ft.get_ask.go(d)):
  match d:
    case Wr.Got{+n, +s1}:
      (e, f) = nd
      te.ask.tag(s, n, s1, e)
    case Wr.Bad{}:
      Unit{}

# an ask decoded is spelled, then the rest, and every number of it fits
def te.ask(+s: String) -> te.A(s, Ft.get_ask(s)):
  te.ask.go(s, Wr.get_nat(s), te.nat(s))
