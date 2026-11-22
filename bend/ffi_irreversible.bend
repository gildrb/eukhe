# ffi_irreversible: the irreversible effects (bend/irreversible.bend) as
# an entry of the compiled Bend core (crates/eukhe-bend/src/rules/
# irreversible.rs). Rust gathers the facts: an effect's class codes, the
# ledger (each entry's key, interned by Rust: equal keys, equal numbers,
# and its run), a key, a run; the model decides. A request names its
# question (crates/eukhe-bend/WIRE.md is the grammar):
#
#   tag 0  classes   the class codes (List<Nat>)
#                    -> T when the effect is irreversible (`irreversible`)
#   tag 1  record    the ledger (List<Nat>: key, run of each entry, in
#                    order), the key (Nat)
#                    -> 0, n (a new entry, id n) | 1, n (the key's entry,
#                       id n): `record`
#   tag 2  report    the ledger, the run (Nat)
#                    -> the ids of the run's entries, in order (List<Nat>):
#                       `report`
#
# Every input that is not exactly one request (an unknown tag, a ledger
# list of odd length, a number past the wire, input left over) answers the
# error form "irreversible: malformed request", never a default.
# laws/irreversible.bend states this file's laws; PROOF.bend proves them.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./irreversible.bend as Ir

# A request of the entry
type Req is Data:
  QClasses{cs: List<&2, Nat>}
  QRecord{es: List<&2, Ir.Entry>, key: Nat}
  QReport{es: List<&2, Ir.Entry>, run: Nat}

# The ledger
# ----------

def entries.cons(k: Nat, r: Nat, m: Maybe<&2, List<&2, Ir.Entry>>) -> Maybe<&2, List<&2, Ir.Entry>>:
  match m:
    case None{}:
      None{}
    case Some{es}:
      Some{Ir.Entry{k, r} <> es}

# the ledger a list of key, run pairs spells; None for an odd length
def entries.of(xs: List<&2, Nat>) -> Maybe<&2, List<&2, Ir.Entry>>:
  match xs:
    case Nil{}:
      Some{Nil{}}
    case k <> rest:
      match rest:
        case Nil{}:
          None{}
        case r <> more:
          entries.cons(k, r, entries.of(more))

# the list of key, run pairs of a ledger
def entries.flat(es: List<&2, Ir.Entry>) -> List<&2, Nat>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Ir.Entry{k, r}:
          k <> r <> entries.flat(rest)

# Requests
# --------

def get_ns(s: String) -> W.Dec<List<&2, Nat>>:
  W.get_list(~Nat, ~W.get_nat, s)

def get_classes(r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{cs, s}:
      W.Got{QClasses{cs}, s}
    case W.Bad{}:
      W.Bad{}

def get_record.key(es: List<&2, Ir.Entry>, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{k, s}:
      W.Got{QRecord{es, k}, s}
    case W.Bad{}:
      W.Bad{}

def get_report.run(es: List<&2, Ir.Entry>, r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{n, s}:
      W.Got{QReport{es, n}, s}
    case W.Bad{}:
      W.Bad{}

# the request with ledger m: tag 1 a record, tag 2 a report
def get_ledger.then(rec: Bool, m: Maybe<&2, List<&2, Ir.Entry>>, s: String) -> W.Dec<Req>:
  match rec:
    case True{}:
      match m:
        case None{}:
          W.Bad{}
        case Some{es}:
          get_record.key(es, W.get_nat(s))
    case False{}:
      match m:
        case None{}:
          W.Bad{}
        case Some{es}:
          get_report.run(es, W.get_nat(s))

def get_ledger(rec: Bool, r: W.Dec<List<&2, Nat>>) -> W.Dec<Req>:
  match r:
    case W.Got{xs, s}:
      get_ledger.then(rec, entries.of(xs), s)
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_classes(get_ns(s))
    case 1n:
      get_ledger(True{}, get_ns(s))
    case 2n:
      get_ledger(False{}, get_ns(s))
    case 3n+u:
      W.Bad{}

def get_req.go(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_req(s: String) -> W.Dec<Req>:
  get_req.go(W.get_nat(s))

# Replies
# -------

def put_recorded(r: Ir.Recorded, rest: String) -> String:
  match r:
    case Ir.New{n}:
      W.put_nat(0n, W.put_nat(n, rest))
    case Ir.Known{n}:
      W.put_nat(1n, W.put_nat(n, rest))

# the model's decision on a request, encoded
def answer(q: Req) -> String:
  match q:
    case QClasses{cs}:
      W.put_bool(Ir.irreversible(cs), "")
    case QRecord{es, k}:
      put_recorded(Ir.record(es, k), "")
    case QReport{es, n}:
      W.put_list(~Nat, ~W.put_nat, Ir.report(es, n), "")

def malformed() -> String:
  W.err("irreversible: malformed request")

def run.end(whole: Bool, q: Req) -> String:
  match whole:
    case True{}:
      answer(q)
    case False{}:
      malformed()

def run(r: W.Dec<Req>) -> String:
  match r:
    case W.Got{q, s}:
      run.end(W.end(s), q)
    case W.Bad{}:
      malformed()

# the entry: decode the request, answer the model's decision
def ffi(input: String) -> String:
  run(get_req(input))