# eukhe: lemmas the proofs of the runners entry share (laws/runners.bend,
# section runners entry): the entry spells the model's decision as the
# laws do, and its reader reads back every request Rust writes

import Base
import ../../../bend/ffi_runners.bend as FRu
import ../../../bend/runners.bend as Ru
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/runners.bend as Runners
import ../../../laws/wire.bend as Wire
import ../../base/logic/bool.bend as LLogicBool
import ../../base/wire.bend as LWire

# The entry answers as the laws spell the model's decision
# --------------------------------------------------------

def rn.reply(q: FRu.Req) -> {FRu.answer(q) == Runners.spell_answer(q) : String}:
  match q:
    case FRu.QRegistry{}:
      {==}
    case FRu.QMain{h}:
      match h:
        case True{}:
          {==}
        case False{}:
          {==}

# The entry's reader reads back what Rust writes
# ----------------------------------------------

def rn.rt_main(h: Bool, rest: String) -> {FRu.get_req(Runners.spell_req(FRu.QMain{h}, rest)) == Wr.Got{FRu.QMain{h}, rest} : Wr.Dec<FRu.Req>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

def rn.rt(q: FRu.Req, +rest: String) -> {FRu.get_req(Runners.spell_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FRu.Req>}:
  match q:
    case FRu.QRegistry{}:
      {==}
    case FRu.QMain{h}:
      rn.rt_main(h, rest)

def rn.main(r: Wr.Dec<Bool>) -> {Runners.read_main(r) == FRu.get_main(r) : Wr.Dec<FRu.Req>}:
  match r:
    case Wr.Got{h, s}:
      {==}
    case Wr.Bad{}:
      {==}

def rn.tag(t: Nat, s: String) -> {Runners.read_req.tag(t, s) == FRu.get_req.tag(t, s) : Wr.Dec<FRu.Req>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      rn.main(Wr.get_bool(s))
    case 4n+u:
      {==}

def rn.go(r: Wr.Dec<Nat>) -> {Runners.read_req.go(r) == FRu.get_req.go(r) : Wr.Dec<FRu.Req>}:
  match r:
    case Wr.Got{t, s}:
      rn.tag(t, s)
    case Wr.Bad{}:
      {==}

def rn.req(s: String) -> {Runners.read_req(s) == FRu.get_req(s) : Wr.Dec<FRu.Req>}:
  rn.go(Wr.get_nat(s))

def rn.end(b: Bool, q: FRu.Req) -> {FRu.run.end(b, q) == Runners.spec.end(b, q) : String}:
  match b:
    case True{}:
      rn.reply(q)
    case False{}:
      {==}

def rn.run(r: Wr.Dec<FRu.Req>) -> {FRu.run(r) == Runners.spec.run(r) : String}:
  match r:
    case Wr.Got{q, s}:
      rn.end(Wr.end(s), q)
    case Wr.Bad{}:
      {==}

def rn.exact(+s: String) -> {FRu.ffi(s) == Runners.spec(s) : String}:
  %rn.req(s) : {FRu.run(_) == Runners.spec(s) : String}
  rn.run(Runners.read_req(s))
