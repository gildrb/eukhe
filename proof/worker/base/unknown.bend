# eukhe: lemmas of the unknown-tag proofs of area worker: a tag past the
# last one reads as itself when it fits and as Bad when too long
# (LAWireSpell.ws_nat_read); both ways each tag dispatch answers Bad.

import Base
import ../../../bend/worker.bend as Wk
import ../../../bend/ffi_worker.bend as FWk
import ../../../bend/wire.bend as Wr
import ../../wire/base/spell.bend as LAWireSpell

def wu_req(b: Bool, -n: Nat, -rest: String) -> {FWk.get_req.go(LAWireSpell.ws_nat_answer(b, 2n+n, rest)) == Wr.Bad{} : Wr.Dec<FWk.Req>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def wu_mode(b: Bool, -n: Nat, -rest: String) -> {FWk.get_mode.go(LAWireSpell.ws_nat_answer(b, 2n+n, rest)) == Wr.Bad{} : Wr.Dec<Wk.Mode>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def wu_parked(b: Bool, -n: Nat, -rest: String) -> {FWk.get_parked.go(LAWireSpell.ws_nat_answer(b, 2n+n, rest)) == Wr.Bad{} : Wr.Dec<Maybe<&2, Nat>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def wu_ev(b: Bool, -n: Nat, -rest: String) -> {FWk.get_ev.go(LAWireSpell.ws_nat_answer(b, 6n+n, rest)) == Wr.Bad{} : Wr.Dec<Wk.Ev>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def wu_note(b: Bool, -n: Nat, -rest: String) -> {FWk.get_note.go(LAWireSpell.ws_nat_answer(b, 2n+n, rest)) == Wr.Bad{} : Wr.Dec<Maybe<&2, String>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def wu_verdict(b: Bool, -n: Nat, -rest: String) -> {FWk.get_verdict.go(LAWireSpell.ws_nat_answer(b, 6n+n, rest)) == Wr.Bad{} : Wr.Dec<Wk.Verdict>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}
