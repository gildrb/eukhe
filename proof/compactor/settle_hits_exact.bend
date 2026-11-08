# eukhe: the proof of LAW settle_hits_exact
#
# PROOF: the pending check and the count of one outcome are the spec's
# (case by case); a hit is hit_spec (settle_run_exact's srx.hit); then
# induction on the outcomes.

import Base
import ../../bend/compactor.bend as C
import ../../bend/optchat/bits.bend as OBits
import ../../laws/compactor.bend as Compactor
import ./settle_run_exact.bend as PSettleRunExact

def shx.pp(p: C.Pend) -> {C.Pend.pending(p) == Compactor.pending_spec(p) : Bool}:
  match p:
    case C.Made{}:
      {==}
    case C.Owed{n}:
      {==}

def shx.pa(ps: List<&2, C.Pend>, k: Nat) -> {C.pending_at(ps, k) == Compactor.pending_at_spec(ps, k) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case p <> rest:
      match k:
        case 0n:
          shx.pp(p)
        case 1n+j:
          shx.pa(rest, j)

def shx.cnt(d: Bool, o: C.Outcome) -> {OBits.bit(Bool.and(d, C.Outcome.lands(o)), 0n) == Compactor.counts_spec(d, o) : Nat}:
  match d:
    case False{}:
      {==}
    case True{}:
      match o:
        case C.Built{}:
          {==}
        case C.Failed{}:
          {==}
        case C.Disk{}:
          {==}
        case C.Stopped{}:
          {==}

def shx.one(+ps: List<&2, C.Pend>, +k: Nat, +o: C.Outcome) -> {OBits.bit(Bool.and(C.pending_at(ps, k), C.Outcome.lands(o)), 0n) == Compactor.counts_spec(Compactor.pending_at_spec(ps, k), o) : Nat}:
  %shx.pa(ps, k) : {OBits.bit(Bool.and(C.pending_at(ps, k), C.Outcome.lands(o)), 0n) == Compactor.counts_spec(_, o) : Nat}
  shx.cnt(C.pending_at(ps, k), o)

def shx.tail(-rest: List<&2, C.End>, +ps: List<&2, C.Pend>, +k: Nat, +o: C.Outcome, ih: {C.hits(rest, C.hit(ps, k, o)) == Compactor.hits_spec(rest, C.hit(ps, k, o)) : Nat}) -> {C.hits(rest, C.hit(ps, k, o)) == Compactor.hits_spec(rest, Compactor.hit_spec(ps, k, o)) : Nat}:
  %PSettleRunExact.srx.hit(ps, k, o) : {C.hits(rest, C.hit(ps, k, o)) == Compactor.hits_spec(rest, _) : Nat}
  ih

def shx.add(-a: Nat, -b: Nat, ea: {a == b : Nat}, -c: Nat, -d: Nat, ec: {c == d : Nat}) -> {Nat.add(a, c) == Nat.add(b, d) : Nat}:
  %ea : {Nat.add(a, c) == Nat.add(_, d) : Nat}
  %ec : {Nat.add(a, c) == Nat.add(a, _) : Nat}
  {==}

def shx.go(es: List<&2, C.End>, +ps: List<&2, C.Pend>) -> {C.hits(es, ps) == Compactor.hits_spec(es, ps) : Nat}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case C.End{+k, +o}:
          +ih = shx.go(rest, C.hit(ps, k, o))
          shx.add(OBits.bit(Bool.and(C.pending_at(ps, k), C.Outcome.lands(o)), 0n), Compactor.counts_spec(Compactor.pending_at_spec(ps, k), o), shx.one(ps, k, o), C.hits(rest, C.hit(ps, k, o)), Compactor.hits_spec(rest, Compactor.hit_spec(ps, k, o)), shx.tail(rest, ps, k, o, ih))

def Compactor.settle_hits_exact(es, ps):
  shx.go(es, ps)
