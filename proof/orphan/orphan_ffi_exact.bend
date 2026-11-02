# eukhe: the proof of LAW orphan_ffi_exact
#
# PROOF: the entry's decoder takes, stage by stage, the same branches on
# the same wire primitives as the spec's reader (ox.tag .. ox.work), so it
# reads every input as the spec does; on a request with nothing after it
# the entry's reply is the spec's (the work's exit due:
# orphan_work_exit_due), and the two error texts are the spec's.

import Base
import ../../bend/ffi_orphan.bend as FO
import ../../bend/orphan.bend as Or
import ../../bend/wire.bend as Wr
import ../../laws/orphan.bend as Orphan
import ./orphan_work_exit_due.bend as POrphanWorkExitDue

def ox.work(+m: Maybe<&2, Nat>, +a: Nat, d: Wr.Dec<Nat>) -> {FO.get_req.work(m, a, FO.get_work.of(d)) == Orphan.or_read.work(m, a, d) : Wr.Dec<FO.Req>}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n+p:
          {==}
    case Wr.Bad{}:
      {==}

def ox.absent(+m: Maybe<&2, Nat>, d: Wr.Dec<Nat>) -> {FO.get_req.absent(m, d) == Orphan.or_read.absent(m, d) : Wr.Dec<FO.Req>}:
  match d:
    case Wr.Got{+a, +s}:
      ox.work(m, a, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def ox.window(d: Wr.Dec<Nat>) -> {FO.get_req.window(FO.get_window.some(d)) == Orphan.or_read.window(d) : Wr.Dec<FO.Req>}:
  match d:
    case Wr.Got{+w, +s}:
      ox.absent(Some{w}, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

# the entry's decoder reads as the spec's reader
def ox.tag(d: Wr.Dec<Nat>) -> {FO.get_req.window(FO.get_window.of(d)) == Orphan.or_read.tag(d) : Wr.Dec<FO.Req>}:
  match d:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          ox.absent(None{}, Wr.get_nat(s))
        case 1n:
          ox.window(Wr.get_nat(s))
        case 2n+p:
          {==}
    case Wr.Bad{}:
      {==}

# the entry's reply to a whole request is the spec's
def ox.reply(q: FO.Req) -> {FO.put_reply(FO.decide(q), "") == Orphan.or_reply(q) : String}:
  match q:
    case FO.Req{m, +a, k}:
      match m:
        case None{}:
          match k:
            case Or.Idle{}:
              {==}
            case Or.Ongoing{}:
              {==}
        case Some{+w}:
          match k:
            case Or.Idle{}:
              {==}
            case Or.Ongoing{}:
              %Equal.sym(Bool, Or.exit_due.at(Some{w}, a, Or.Ongoing{}), Nat.is_le(Nat.add(w, w), a), Orphan.orphan_work_exit_due(w, a)) : {Wr.put_bool(_, Wr.put_nat(1n, "")) == Wr.put_bool(Nat.is_le(Nat.add(w, w), a), Wr.put_nat(1n, "")) : String}
              {==}

def ox.end(q: FO.Req, r: String) -> {FO.ffi.fin(Wr.end(r), q) == Orphan.or_entry.of(Wr.Got{q, r}) : String}:
  match r:
    case SNil{}:
      ox.reply(q)
    case SCon{c, t}:
      {==}

def ox.go(d: Wr.Dec<FO.Req>) -> {FO.ffi.go(d) == Orphan.or_entry.of(d) : String}:
  match d:
    case Wr.Got{q, r}:
      ox.end(q, r)
    case Wr.Bad{}:
      {==}

def Orphan.orphan_ffi_exact(s):
  %ox.tag(Wr.get_nat(s)) : {FO.ffi(s) == Orphan.or_entry.of(_) : String}
  ox.go(FO.get_req(s))
