# eukhe: lemmas the proofs of the hand-back entry share (laws/sandbox.bend,
# section "The hand-back entry, spelled")

import Base
import ../../../bend/ffi_sandbox.bend as FSb
import ../../../bend/sandbox.bend as Sb
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/sandbox.bend as Sandbox
import ../../base/wire.bend as LWire

# The entry reads every input as the laws' reader does
# -----------------------------------------------------

def cse.some(r: Wr.Dec<Nat>) -> {Sandbox.cow_read_some(r) == FSb.get_doc.some(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cse.tag(t: Nat, s: String) -> {Sandbox.cow_read_doc.tag(t, s) == FSb.get_doc.tag(t, s) : Wr.Dec<Maybe<&2, Nat>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      cse.some(Wr.get_nat(s))
    case 2n+u:
      {==}

def cse.doc(r: Wr.Dec<Nat>) -> {Sandbox.cow_read_doc(r) == FSb.get_doc.go(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{t, s}:
      cse.tag(t, s)
    case Wr.Bad{}:
      {==}

# a content: the laws' reader is the entry's
def cse.docs(s: String) -> {Sandbox.cow_read_doc(Wr.get_nat(s)) == FSb.get_doc(s) : Wr.Dec<Maybe<&2, Nat>>}:
  cse.doc(Wr.get_nat(s))

# The entry spells the plan as the laws do
# ----------------------------------------

def cse.plan(x: Sb.Plan) -> {FSb.put_plan(x, "") == Sandbox.cow_spell_plan(x) : String}:
  match x:
    case Sb.Keep{t}:
      {==}
    case Sb.Clash{}:
      {==}
    case Sb.Take{}:
      {==}
    case Sb.Drop{}:
      {==}

# The reader reads back what Rust writes
# --------------------------------------

# a content that fits reads back, with what follows it
def cse.rt_doc(m: Maybe<&2, Nat>, +rest: String, +h: {LawsBase.wire_mfits(m) == True{} : Bool}) -> {Wr.Got{m, rest} == Sandbox.cow_read_doc(Wr.get_nat(Sandbox.cow_spell_doc(m, rest))) : Wr.Dec<Maybe<&2, Nat>>}:
  match m:
    case None{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{None{}, rest} == Sandbox.cow_read_doc(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}
    case Some{+x}:
      %LWire.pw6.nat(1n, Wr.put_nat(x, rest), {==}) : {Wr.Got{Some{x}, rest} == Sandbox.cow_read_doc(_) : Wr.Dec<Maybe<&2, Nat>>}
      %LWire.pw6.nat(x, rest, h) : {Wr.Got{Some{x}, rest} == Sandbox.cow_read_some(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}

# a content that fits, as the entry reads it: itself, with what follows it
def cse.rt_get(+m: Maybe<&2, Nat>, +rest: String, +h: {LawsBase.wire_mfits(m) == True{} : Bool}) -> {Wr.Got{m, rest} == FSb.get_doc(Sandbox.cow_spell_doc(m, rest)) : Wr.Dec<Maybe<&2, Nat>>}:
  Equal.trans(Wr.Dec<Maybe<&2, Nat>>, Wr.Got{m, rest}, Sandbox.cow_read_doc(Wr.get_nat(Sandbox.cow_spell_doc(m, rest))), FSb.get_doc(Sandbox.cow_spell_doc(m, rest)), cse.rt_doc(m, rest, h), cse.docs(Sandbox.cow_spell_doc(m, rest)))
