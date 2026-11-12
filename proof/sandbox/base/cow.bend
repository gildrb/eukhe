# eukhe: lemmas the proofs of the hand-back entry share (laws/sandbox.bend,
# section the hand-back entry: spelled requests)

import Base
import ../../../bend/ffi_sandbox.bend as FSb
import ../../../bend/sandbox.bend as Sb
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/sandbox.bend as Sandbox
import ../../../laws/wire.bend as Wire
import ../../base/logic/bool.bend as LLogicBool
import ../../base/wire.bend as LWire
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits

# The rule
# --------

def cw.same(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> {Sb.m.eq(a, b) == Sandbox.cow_same_spec(a, b) : Bool}:
  match a b:
    case None{} None{}:
      {==}
    case None{} Some{y}:
      {==}
    case Some{x} None{}:
      {==}
    case Some{x} Some{y}:
      {==}

def cw.at(x: Bool, y: Bool, z: Bool, c: Maybe<&2, Nat>) -> {Sb.plan.at(x, y, z, c) == Sandbox.CowPlan.go(x, y, z, c) : Sb.Plan}:
  match x:
    case True{}:
      {==}
    case False{}:
      match y:
        case True{}:
          match c:
            case None{}:
              {==}
            case Some{v}:
              {==}
        case False{}:
          match z:
            case True{}:
              {==}
            case False{}:
              {==}

def cw.plan(+p: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, +c: Maybe<&2, Nat>) -> {Sb.plan(p, b, c) == Sandbox.cow_plan_spec(p, b, c) : Sb.Plan}:
  %cw.same(c, b) : {Sb.plan.at(Sb.m.eq(c, b), Sb.m.eq(p, b), Sb.m.eq(p, c), c) == Sandbox.CowPlan.go(_, Sandbox.cow_same_spec(p, b), Sandbox.cow_same_spec(p, c), c) : Sb.Plan}
  %cw.same(p, b) : {Sb.plan.at(Sb.m.eq(c, b), Sb.m.eq(p, b), Sb.m.eq(p, c), c) == Sandbox.CowPlan.go(Sb.m.eq(c, b), _, Sandbox.cow_same_spec(p, c), c) : Sb.Plan}
  %cw.same(p, c) : {Sb.plan.at(Sb.m.eq(c, b), Sb.m.eq(p, b), Sb.m.eq(p, c), c) == Sandbox.CowPlan.go(Sb.m.eq(c, b), Sb.m.eq(p, b), _, c) : Sb.Plan}
  cw.at(Sb.m.eq(c, b), Sb.m.eq(p, b), Sb.m.eq(p, c), c)

def cw.put_plan(x: Sb.Plan) -> {FSb.put_plan(x, "") == Sandbox.cow_spell_plan(x) : String}:
  match x:
    case Sb.Keep{t}:
      {==}
    case Sb.Clash{}:
      {==}
    case Sb.Take{}:
      {==}
    case Sb.Drop{}:
      {==}

# The entry reads every input as the laws' reader does
# -----------------------------------------------------

def cw.some(r: Wr.Dec<Nat>) -> {Sandbox.cow_read_doc.some(r) == FSb.get_doc.some(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cw.doc_tag(t: Nat, s: String) -> {Sandbox.cow_read_doc.tag(t, s) == FSb.get_doc.tag(t, s) : Wr.Dec<Maybe<&2, Nat>>}:
  match t:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          cw.some(Wr.get_nat(s))
        case 1n+q:
          {==}

def cw.doc(r: Wr.Dec<Nat>) -> {Sandbox.cow_read_doc(r) == FSb.get_doc.go(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{t, s}:
      cw.doc_tag(t, s)
    case Wr.Bad{}:
      {==}

# The reader reads back what Rust writes
# --------------------------------------

def cw.rt_doc(m: Maybe<&2, Nat>, +rest: String, +h: {LawsBase.wire_mfits(m) == True{} : Bool}) -> {Wr.Got{m, rest} == Sandbox.cow_read_doc(Wr.get_nat(Sandbox.cow_spell_doc(m, rest))) : Wr.Dec<Maybe<&2, Nat>>}:
  match m:
    case None{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{None{}, rest} == Sandbox.cow_read_doc(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}
    case Some{+x}:
      %LWire.pw6.nat(1n, Wr.put_nat(x, rest), {==}) : {Wr.Got{Some{x}, rest} == Sandbox.cow_read_doc(_) : Wr.Dec<Maybe<&2, Nat>>}
      %LWire.pw6.nat(x, rest, h) : {Wr.Got{Some{x}, rest} == Sandbox.cow_read_doc.some(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}

# a content: the laws' reader is the entry's
def cse.docs(s: String) -> {Sandbox.cow_read_doc(Wr.get_nat(s)) == FSb.get_doc(s) : Wr.Dec<Maybe<&2, Nat>>}:
  cw.doc(Wr.get_nat(s))

# a content that fits, as the entry reads it: itself, with what follows it
def cse.rt_get(+m: Maybe<&2, Nat>, +rest: String, +h: {LawsBase.wire_mfits(m) == True{} : Bool}) -> {Wr.Got{m, rest} == FSb.get_doc(Sandbox.cow_spell_doc(m, rest)) : Wr.Dec<Maybe<&2, Nat>>}:
  Equal.trans(Wr.Dec<Maybe<&2, Nat>>, Wr.Got{m, rest}, Sandbox.cow_read_doc(Wr.get_nat(Sandbox.cow_spell_doc(m, rest))), FSb.get_doc(Sandbox.cow_spell_doc(m, rest)), cw.rt_doc(m, rest, h), cse.docs(Sandbox.cow_spell_doc(m, rest)))

# What the entry reads is spelled
# -------------------------------

# what a content decoder answer says about its input s: s spells it, and
# it fits
def cmu(s: String, d: Wr.Dec<Maybe<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{+m, rest}:
      {s == Sandbox.cow_spell_doc(m, rest) : String} & {LawsBase.wire_mfits(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a content tag 1: its id
def cmu.some(-s0: String, +s1: String, pre: {s0 == Wr.put_nat(1n, s1) : String}, r: Wr.Dec<Nat>, er: {Wr.get_nat(s1) == r : Wr.Dec<Nat>}) -> cmu(s0, FSb.get_doc.some(r)):
  match r:
    case Wr.Got{+x, +s2}:
      +e2 = er
      (Equal.trans(String, s0, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_nat(x, s2)), pre,
          Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_nat(x, s2), Wire.wire_nat_exact(s1, x, s2, e2))),
        Wire.wire_nat_decoded_fits(s1, x, s2, e2))
    case Wr.Bad{}:
      Unit{}

def cmu.tag(+s0: String, t: Nat, +s1: String, ex: {s0 == Wr.put_nat(t, s1) : String}) -> cmu(s0, FSb.get_doc.tag(t, s1)):
  match t:
    case 0n:
      (ex, {==})
    case 1n:
      cmu.some(s0, s1, ex, Wr.get_nat(s1), {==})
    case 2n+y:
      Unit{}

def cmu.top(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> cmu(s, FSb.get_doc.go(r)):
  match r:
    case Wr.Got{+t, +s1}:
      cmu.tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, er))
    case Wr.Bad{}:
      Unit{}

# every content the entry reads is spelled, and fits
def cmu.all(+s: String) -> cmu(s, FSb.get_doc(s)):
  cmu.top(s, Wr.get_nat(s), {==})
