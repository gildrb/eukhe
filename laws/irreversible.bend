# eukhe: the laws of area irreversible

import Base
import ../bend/irreversible.bend as Ir
import ../bend/ffi_irreversible.bend as FIr
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (I1, I4, I6, I13) Irreversible effects and their ledger
# --------------------------------------------------------
# spec/README.md I1, I4, I6, I13. bend/irreversible.bend: an effect is
# its class codes (0 read, 1 write, 2 exec inside the workspace; 3 net, 4
# outside, 5 protected, 6 secret, 7 unknown; any code past 7 is unknown
# too). Every effect runs (I2); one that is irreversible is recorded once
# in the root session's ledger, and the end of a run lists the ones that
# ran in it. It runs as the compiled core by bend/ffi_irreversible.bend
# (eukhe-bend rules/irreversible.rs), asked when an effect ran and by the
# session's `eukhe.effects` ledger (eukhe-durable harness/effects.rs).
# Every input is free: any codes, any ledger, any key, any run.
#
# R1 (I1): an effect is irreversible exactly when one of its codes is none
#     of read, write and exec (an unknown code included); nothing else
#     moves an effect across.
# R2 (I4): recording a key the ledger lacks answers New with the next id
#     (one past the entries) and appends exactly one entry, that key in
#     that run, last; every earlier entry stays as it was.
# R3 (I4): recording a key the ledger holds answers Known with the id of
#     its entry (its place, from 1) and changes nothing.
# R4 (I4): over any history of records, every earlier entry stays as it
#     was, each key recorded appears, each key once, each new entry holds
#     the key and the run of the record that added it (any run), and the
#     ids answered New are 1, 2, ... in order, one per entry.
# R5 (I6): the end-of-run list of run r is the ids of the entries
#     recorded in r, in ledger order; empty when none.
# R6 (I13): the entry answers each request Rust writes (every number
#     within the wire) with the model's answer, reads exactly the request
#     and nothing after it, and answers any other input with the exact
#     error form `E irreversible: malformed request`.
#
# Not pinned here: that Rust records every irreversible effect that ran
# under its key and run (eukhe-core and eukhe-durable tests), and the text
# of the end-of-run message (eukhe-types effects tests).
#
# Not pinned on their own: the request decoder's steps (`get_req.go`,
# `get_req.tag`, bend/ffi_irreversible.bend) are pinned through `get_req`
# (irreversible_entry_req_exact, irreversible_entry_req_example), the
# decoder the entry runs on every input; they have no law of their own.

# Spec helpers
# ------------

# R1: the code is read (0), write (1) or exec (2)
def ir_rwx(c: Nat) -> Bool:
  match c:
    case 0n:
      True{}
    case 1n+a:
      match a:
        case 0n:
          True{}
        case 1n+b:
          match b:
            case 0n:
              True{}
            case 1n+d:
              False{}

# R2-R4: some entry of es has key k
def ir_has(es: List<&2, Ir.Entry>, +k: Nat) -> Bool:
  match es:
    case Nil{}:
      False{}
    case e <> rest:
      match e:
        case Ir.Entry{j, r}:
          Bool.or(Nat.is_eq(j, k), ir_has(rest, k))

# R4: no two entries of es share a key
def ir_once(es: List<&2, Ir.Entry>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> +rest:
      match e:
        case Ir.Entry{k, r}:
          Bool.and(Bool.not(ir_has(rest, k)), ir_once(rest))

# R4: what each record of ops answers, in order, from the ledger es
def ir_answers(ops: List<&2, Ir.Entry>, +es: List<&2, Ir.Entry>) -> List<&2, Ir.Recorded>:
  match ops:
    case Nil{}:
      Nil{}
    case op <> rest:
      match op:
        case Ir.Entry{+k, +r}:
          Ir.record(es, k) <> ir_answers(rest, Ir.keep(es, k, r))

# R4: the ids of the New answers, in order
def ir_news(as: List<&2, Ir.Recorded>) -> List<&2, Nat>:
  match as:
    case Nil{}:
      Nil{}
    case a <> rest:
      match a:
        case Ir.New{n}:
          n <> ir_news(rest)
        case Ir.Known{n}:
          ir_news(rest)

# R4: the ids 1 to n, in order
def ir_upto(n: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n++m:
      List.append(&2, Nat, ir_upto(m), [1n+m])

# R5: the id n when the entry ran in the run asked (hit), else nothing
def ir_in_run(hit: Bool, n: Nat) -> List<&2, Nat>:
  match hit:
    case True{}:
      [n]
    case False{}:
      Nil{}

# R4: what the record of key k in run r adds to a ledger: nothing when the
# ledger holds k (held), else the one entry k in run r
def ir_added(held: Bool, k: Nat, r: Nat) -> List<&2, Ir.Entry>:
  match held:
    case True{}:
      Nil{}
    case False{}:
      [Ir.Entry{k, r}]

# R6: a list of Nats, spelled, then rest
def sp_ir_ns(xs: List<&2, Nat>, rest: String) -> String:
  Wr.put_list(~Nat, ~Wr.put_nat, xs, rest)

# R6: a ledger as Rust writes it: each entry's key, then its run
def sp_ir_ledger(es: List<&2, Ir.Entry>) -> List<&2, Nat>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      match e:
        case Ir.Entry{k, r}:
          k <> r <> sp_ir_ledger(rest)

# R6: the request q as Rust writes it, then rest
def sp_ir_req(q: FIr.Req, rest: String) -> String:
  match q:
    case FIr.QClasses{cs}:
      Wr.put_nat(0n, sp_ir_ns(cs, rest))
    case FIr.QRecord{es, k}:
      Wr.put_nat(1n, sp_ir_ns(sp_ir_ledger(es), Wr.put_nat(k, rest)))
    case FIr.QReport{es, r}:
      Wr.put_nat(2n, sp_ir_ns(sp_ir_ledger(es), Wr.put_nat(r, rest)))

# R6: a list of Nats fits the wire: its length and each item
def ir_ns_fit(+xs: List<&2, Nat>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))

# R6: every number of a request fits the wire
def ir_req_fits(q: FIr.Req) -> Bool:
  match q:
    case FIr.QClasses{cs}:
      ir_ns_fit(cs)
    case FIr.QRecord{es, k}:
      Bool.and(ir_ns_fit(sp_ir_ledger(es)), LawsBase.wire_fits(k))
    case FIr.QReport{es, r}:
      Bool.and(ir_ns_fit(sp_ir_ledger(es)), LawsBase.wire_fits(r))

# R6: a record's answer, spelled: 0 then the new id, or 1 then the known id
def sp_ir_recorded(a: Ir.Recorded) -> String:
  match a:
    case Ir.New{n}:
      Wr.put_nat(0n, Wr.put_nat(n, ""))
    case Ir.Known{n}:
      Wr.put_nat(1n, Wr.put_nat(n, ""))

# R6: the model's answer to q, spelled: T when irreversible; the record's
# answer; the ids of the run
def sp_ir_reply(q: FIr.Req) -> String:
  match q:
    case FIr.QClasses{cs}:
      Wr.put_bool(Ir.irreversible(cs), "")
    case FIr.QRecord{es, k}:
      sp_ir_recorded(Ir.record(es, k))
    case FIr.QReport{es, r}:
      sp_ir_ns(Ir.report(es, r), "")

# Laws: the classes (R1)
# ----------------------

# LAW irreversible_none (R1): an effect with no class code is reversible
# EXCLUDES: an empty effect recorded as irreversible
law irreversible_none:
  {Ir.irreversible(Nil{}) == False{} : Bool}

# LAW irreversible_one (R1): an effect of one code c is irreversible
# exactly when c is none of read (0), write (1) and exec (2)
# EXCLUDES: a net, outside, protected, secret or unknown code (or any code
#   past 7) taken as reversible; a read, write or exec taken as
#   irreversible; codes renumbered
law irreversible_one:
  for +c: Nat
  {Ir.irreversible([c]) == Bool.not(ir_rwx(c)) : Bool}

# LAW irreversible_concat (R1): the codes xs then ys are irreversible
# exactly when xs is or ys is
# EXCLUDES: only the first or the last code read, an irreversible code
#   hidden by a reversible one beside it
law irreversible_concat:
  for +xs: List<&2, Nat>
  for +ys: List<&2, Nat>
  {Ir.irreversible(List.append(&2, Nat, xs, ys)) == Bool.or(Ir.irreversible(xs), Ir.irreversible(ys)) : Bool}

# LAW irreversible_example (R1): anchor: read, write, exec and the three
# together are reversible; net, outside, protected, secret, unknown, a
# code past unknown, and exec with net are irreversible
# EXCLUDES: another numbering of the classes
law irreversible_example:
  {[Ir.irreversible([0n]), Ir.irreversible([1n]), Ir.irreversible([2n]), Ir.irreversible([0n, 1n, 2n]), Ir.irreversible([3n]), Ir.irreversible([4n]), Ir.irreversible([5n]), Ir.irreversible([6n]), Ir.irreversible([7n]), Ir.irreversible([9n]), Ir.irreversible([2n, 3n])] == [False{}, False{}, False{}, False{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}] : List<&2, Bool>}

# Laws: recording (R2, R3)
# ------------------------

# LAW irreversible_record_new (R2): recording a key k the ledger es lacks
# answers New with id 1 + the number of entries, and the ledger after it
# is es with exactly one entry appended last: k in run r; every earlier
# entry stays as it was
# EXCLUDES: an id reused or skipped, a new entry put first or not at all,
#   two entries appended, an earlier entry changed or dropped, the run
#   lost
law irreversible_record_new:
  for +es: List<&2, Ir.Entry>
  for +k: Nat
  for +r: Nat
  for fresh: {ir_has(es, k) == False{} : Bool}
  {Ir.record(es, k) == Ir.New{1n+List.length(&2, Ir.Entry, es)} : Ir.Recorded} & {Ir.keep(es, k, r) == List.append(&2, Ir.Entry, es, [Ir.Entry{k, r}]) : List<&2, Ir.Entry>}

# LAW irreversible_record_known (R3): recording a key k whose first entry
# comes after the entries pre answers Known with that entry's id, 1 + the
# number of entries of pre, and changes nothing, in any run r
# EXCLUDES: a replay after a crash recorded twice, a later run moving the
#   entry, the id of another entry, a known key's entry changed
law irreversible_record_known:
  for +pre: List<&2, Ir.Entry>
  for +k: Nat
  for +q: Nat
  for +post: List<&2, Ir.Entry>
  for +r: Nat
  for first: {ir_has(pre, k) == False{} : Bool}
  {Ir.record(List.append(&2, Ir.Entry, pre, Ir.Entry{k, q} <> post), k) == Ir.Known{1n+List.length(&2, Ir.Entry, pre)} : Ir.Recorded} & {Ir.keep(List.append(&2, Ir.Entry, pre, Ir.Entry{k, q} <> post), k, r) == List.append(&2, Ir.Entry, pre, Ir.Entry{k, q} <> post) : List<&2, Ir.Entry>}

# Laws: a history of records (R4)
# -------------------------------

# LAW irreversible_history_keeps (R4): after any records, the ledger is
# the ledger before them with entries appended: every earlier entry stays
# as it was, in its place
# EXCLUDES: a record that rewrites, reorders or drops an earlier entry
law irreversible_history_keeps:
  for ops: List<&2, Ir.Entry>
  for +es: List<&2, Ir.Entry>
  exs t: List<&2, Ir.Entry>
  {Ir.history(ops, es) == List.append(&2, Ir.Entry, es, t) : List<&2, Ir.Entry>}

# LAW irreversible_history_holds (R4): after any records, the ledger holds
# a key exactly when it held it before or a record named it
# EXCLUDES: a record lost, a key invented
law irreversible_history_holds:
  for ops: List<&2, Ir.Entry>
  for +es: List<&2, Ir.Entry>
  for +k: Nat
  {ir_has(Ir.history(ops, es), k) == Bool.or(ir_has(es, k), ir_has(ops, k)) : Bool}

# LAW irreversible_history_once (R4): after any records on a ledger where
# each key appears once, each key still appears once
# EXCLUDES: a replayed record appended again, a key recorded twice in one
#   history
law irreversible_history_once:
  for ops: List<&2, Ir.Entry>
  for +es: List<&2, Ir.Entry>
  for once: {ir_once(es) == True{} : Bool}
  {ir_once(Ir.history(ops, es)) == True{} : Bool}

# LAW irreversible_history_ids (R4): after any records on a ledger of n
# entries, the ids 1 to n then the ids answered New, in order, are exactly
# 1 to the number of entries: from an empty ledger the new ids are 1, 2,
# ... in order, one per entry, none reused
# EXCLUDES: an id reused, skipped or answered out of order; a New answer
#   for a known key; an entry with no New answer
law irreversible_history_ids:
  for ops: List<&2, Ir.Entry>
  for +es: List<&2, Ir.Entry>
  {List.append(&2, Nat, ir_upto(List.length(&2, Ir.Entry, es)), ir_news(ir_answers(ops, es))) == ir_upto(List.length(&2, Ir.Entry, Ir.history(ops, es))) : List<&2, Nat>}

# LAW irreversible_history_example (R2-R4): anchor: records of keys 5, 8,
# 5 (a replay in a later run) and 2 answer e1, e2, e1 again and e3; the
# ledger keeps the first run of key 5
# EXCLUDES: a replay recorded anew or moved to its later run
law irreversible_history_example:
  {ir_answers([Ir.Entry{5n, 1n}, Ir.Entry{8n, 1n}, Ir.Entry{5n, 2n}, Ir.Entry{2n, 2n}], Nil{}) == [Ir.New{1n}, Ir.New{2n}, Ir.Known{1n}, Ir.New{3n}] : List<&2, Ir.Recorded>} & {Ir.history([Ir.Entry{5n, 1n}, Ir.Entry{8n, 1n}, Ir.Entry{5n, 2n}, Ir.Entry{2n, 2n}], Nil{}) == [Ir.Entry{5n, 1n}, Ir.Entry{8n, 1n}, Ir.Entry{2n, 2n}] : List<&2, Ir.Entry>}

# LAW irreversible_history_last (R2, R4): after any records ops, one more
# record, key k in run r, adds to the ledger ops left exactly the entry k
# in run r when that ledger lacks k, and nothing when it holds k: every
# new entry of a history keeps the key and the run it was recorded with,
# whatever the run and wherever the record falls in the history
# EXCLUDES: a new entry filed under another run (run 0 as run 1, a run
#   taken modulo some number, the run of an earlier record), a record of a
#   later run moving an entry, the last record dropped, appended twice or
#   under another key
law irreversible_history_last:
  for ops: List<&2, Ir.Entry>
  for +es: List<&2, Ir.Entry>
  for +k: Nat
  for +r: Nat
  {Ir.history(List.append(&2, Ir.Entry, ops, [Ir.Entry{k, r}]), es) == List.append(&2, Ir.Entry, Ir.history(ops, es), ir_added(ir_has(Ir.history(ops, es), k), k, r)) : List<&2, Ir.Entry>}

# LAW irreversible_history_runs_example (R2, R4, R5): anchor: records of
# key 5 in run 0, key 3 in run 0, key 5 in run 7 (a replay) and key 8 in
# run 7 leave the ledger 5 in run 0, 3 in run 0, 8 in run 7; run 0 lists
# e1 and e2, run 7 lists e3
# EXCLUDES: run 0 filed as another run, a run past 2 changed, the replay
#   moved to run 7
law irreversible_history_runs_example:
  {Ir.history([Ir.Entry{5n, 0n}, Ir.Entry{3n, 0n}, Ir.Entry{5n, 7n}, Ir.Entry{8n, 7n}], Nil{}) == [Ir.Entry{5n, 0n}, Ir.Entry{3n, 0n}, Ir.Entry{8n, 7n}] : List<&2, Ir.Entry>} & {[Ir.report(Ir.history([Ir.Entry{5n, 0n}, Ir.Entry{3n, 0n}, Ir.Entry{5n, 7n}, Ir.Entry{8n, 7n}], Nil{}), 0n), Ir.report(Ir.history([Ir.Entry{5n, 0n}, Ir.Entry{3n, 0n}, Ir.Entry{5n, 7n}, Ir.Entry{8n, 7n}], Nil{}), 7n)] == [[1n, 2n], [3n]] : List<&2, List<&2, Nat>>}

# Laws: the end of a run (R5)
# ---------------------------

# LAW irreversible_report_none (R5): the end-of-run list of an empty
# ledger is empty
# EXCLUDES: an end message invented for a run with no irreversible effect
law irreversible_report_none:
  for +r: Nat
  {Ir.report(Nil{}, r) == Nil{} : List<&2, Nat>}

# LAW irreversible_report_last (R5): the end-of-run list of run r after an
# entry appended last (key k, run q) is the list before it, then that
# entry's id (1 + the entries before it) when q is r
# EXCLUDES: an entry of another run listed, an entry of the run left out,
#   ids out of order or off by one, a list of every run
law irreversible_report_last:
  for +es: List<&2, Ir.Entry>
  for +k: Nat
  for +q: Nat
  for +r: Nat
  {Ir.report(List.append(&2, Ir.Entry, es, [Ir.Entry{k, q}]), r) == List.append(&2, Nat, Ir.report(es, r), ir_in_run(Nat.is_eq(q, r), 1n+List.length(&2, Ir.Entry, es))) : List<&2, Nat>}

# LAW irreversible_report_example (R5): anchor: entries of runs 1, 2, 1:
# run 1 lists e1 and e3, run 2 lists e2, run 3 nothing
# EXCLUDES: a list of the whole ledger, ids counted from 0
law irreversible_report_example:
  {[Ir.report([Ir.Entry{4n, 1n}, Ir.Entry{6n, 2n}, Ir.Entry{7n, 1n}], 1n), Ir.report([Ir.Entry{4n, 1n}, Ir.Entry{6n, 2n}, Ir.Entry{7n, 1n}], 2n), Ir.report([Ir.Entry{4n, 1n}, Ir.Entry{6n, 2n}, Ir.Entry{7n, 1n}], 3n)] == [[1n, 3n], [2n], Nil{}] : List<&2, List<&2, Nat>>}

# Laws: the entry (R6)
# --------------------

# LAW irreversible_entry_answers (R6): the entry answers every request
# Rust writes, every number within the wire, with the model's answer,
# spelled
# EXCLUDES: a request misread (a ledger's key and run swapped, a key
#   misread), a default, another reply spelling
law irreversible_entry_answers:
  for +q: FIr.Req
  for fits: {ir_req_fits(q) == True{} : Bool}
  {FIr.ffi(sp_ir_req(q, "")) == sp_ir_reply(q) : String}

# LAW irreversible_entry_reads (R6): the entry's decoder reads a spelled
# request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law irreversible_entry_reads:
  for +q: FIr.Req
  for +rest: String
  for fits: {ir_req_fits(q) == True{} : Bool}
  {FIr.get_req(sp_ir_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FIr.Req>}

# LAW irreversible_entry_exact (R6): every input the entry does not answer
# with the error form is a spelled request that fits the wire
# EXCLUDES: an answer for input that is no request: an unknown tag (3 or
#   more), a ledger of odd length, a number past the wire, input left over
law irreversible_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FIr.ffi(s)) == False{} : Bool}
  exs q: FIr.Req
  {s == sp_ir_req(q, "") : String} & {ir_req_fits(q) == True{} : Bool}

# LAW irreversible_entry_req_exact (R6): the entry's decoder reads a
# request only from a spelled one: whatever it decodes is a request whose
# every number fits the wire, spelled, then the input after it
# EXCLUDES: a decoder that invents a request (a default request for an
#   unknown tag, empty or short input), reads a number with a leading zero
#   or past the wire, or reads a ledger of odd length
law irreversible_entry_req_exact:
  for +s: String
  for +q: FIr.Req
  for +rest: String
  for +h: {FIr.get_req(s) == Wr.Got{q, rest} : Wr.Dec<FIr.Req>}
  {s == sp_ir_req(q, rest) : String} & {ir_req_fits(q) == True{} : Bool}

# LAW irreversible_entry_req_example (R6): anchor: an unknown tag, a tag
# with a leading zero and empty input are no request
# EXCLUDES: a default request for an unknown tag or empty input
law irreversible_entry_req_example:
  {[FIr.get_req("3,"), FIr.get_req("01,"), FIr.get_req("")] == [Wr.Bad{}, Wr.Bad{}, Wr.Bad{}] : List<&2, Wr.Dec<FIr.Req>>}

# LAW irreversible_entry_refuses (R6): every error the entry answers is
# exactly `E irreversible: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law irreversible_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FIr.ffi(s)) == True{} : Bool}
  {FIr.ffi(s) == Wr.err("irreversible: malformed request") : String}

# LAW irreversible_entry_example (R6): anchor: the wire strings Rust sends
# and the replies it reads: exec with net is irreversible; key 4 is new on
# an empty ledger (e1) and known on the ledger [4 in run 1]; run 1 of the
# ledger [4 in run 1, 6 in run 2] lists e1; an odd ledger, an unknown tag
# and input left over are refused
# EXCLUDES: another request or reply spelling
law irreversible_entry_example:
  {[FIr.ffi("0,2,2,3,"), FIr.ffi("1,0,4,"), FIr.ffi("1,2,4,1,4,"), FIr.ffi("2,4,4,1,6,2,1,"), FIr.ffi("1,1,4,4,"), FIr.ffi("3,"), FIr.ffi("0,0,0,")] == ["T", "0,1,", "1,1,", "1,1,", Wr.err("irreversible: malformed request"), Wr.err("irreversible: malformed request"), Wr.err("irreversible: malformed request")] : List<&2, String>}
