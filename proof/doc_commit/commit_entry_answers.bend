# eukhe: the proof of LAW commit_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left
# (commit_entry_reads), so the entry answers the code's choice, which is
# the spec's reply by definition (the choices are pinned by
# laws/doc_commit/choices.bend); each reply encoder is the spec's
# spelling (dcw.put_*).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../bend/ffi_doc_commit.bend as FCm
import ../../bend/wire.bend as Wr
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ./base.bend as LA
import ../base/wire_dec.bend as LE
import ./commit_entry_reads.bend as PCommitEntryReads

def dcw.put_check(c: Cm.Check) -> {FCm.put_check(c) == DocCommit.sp_w_check(c) : String}:
  match c:
    case Cm.Go{}:
      {==}
    case Cm.Stop{at, why}:
      match why:
        case Cm.Changed{}:
          {==}
        case Cm.Taken{}:
          {==}

def dcw.put_outcome(o: Cm.Outcome) -> {FCm.put_outcome(o) == DocCommit.sp_w_outcome(o, "") : String}:
  match o:
    case Cm.Lands{w}:
      match w:
        case Cm.NoWarn{}:
          {==}
        case Cm.SyncWarn{}:
          {==}
        case Cm.RemoveWarn{}:
          {==}
    case Cm.Fails{}:
      {==}

def dcw.put_gate(g: Cm.Gate) -> {Wr.put_nat(FCm.gate.tag(g), "") == DocCommit.sp_w_gate(g) : String}:
  match g:
    case Cm.Proceed{}:
      {==}
    case Cm.Unseen{}:
      {==}
    case Cm.Stale{}:
      {==}

# the spec's items of a list of notes, then rest
def dcw.nitems(xs: List<&2, Cm.Note>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      DocCommit.sp_w_note(x, dcw.nitems(t, rest))

# one step of the entry's note encoder is the spec's
def dcw.nput_step(x: Cm.Note, -n: Nat, -r: String) -> {Wr.put_list.step(~Cm.Note, ~FCm.put_note, x, (n, r)) == (1n+n, DocCommit.sp_w_note(x, r)) : Nat & String}:
  match x:
    case Cm.Untouched{}:
      {==}
    case Cm.Written{}:
      {==}
    case Cm.Unwritten{}:
      {==}
    case Cm.Skipped{k}:
      {==}

def dcw.nput_go(xs: List<&2, Cm.Note>, -rest: String) ->
  {Wr.put_list.go(~Cm.Note, ~FCm.put_note, xs, rest) == (List.length(&2, Cm.Note, xs), dcw.nitems(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Cm.Note, ~FCm.put_note, t, rest), (List.length(&2, Cm.Note, t), dcw.nitems(t, rest)), dcw.nput_go(t, rest)) : {Wr.put_list.step(~Cm.Note, ~FCm.put_note, x, _) == (1n+List.length(&2, Cm.Note, t), DocCommit.sp_w_note(x, dcw.nitems(t, rest))) : Nat & String}
      dcw.nput_step(x, List.length(&2, Cm.Note, t), dcw.nitems(t, rest))

def dcw.sput_go(xs: List<&2, Cm.Note>, -rest: String) ->
  {Wr.put_list.go(~Cm.Note, ~DocCommit.sp_w_note, xs, rest) == (List.length(&2, Cm.Note, xs), dcw.nitems(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Cm.Note, ~DocCommit.sp_w_note, t, rest), (List.length(&2, Cm.Note, t), dcw.nitems(t, rest)), dcw.sput_go(t, rest)) : {Wr.put_list.step(~Cm.Note, ~DocCommit.sp_w_note, x, _) == (1n+List.length(&2, Cm.Note, t), DocCommit.sp_w_note(x, dcw.nitems(t, rest))) : Nat & String}
      {==}

# the entry's note list encoder is the spec's
def dcw.notes(+xs: List<&2, Cm.Note>, -rest: String) ->
  {Wr.put_list(~Cm.Note, ~FCm.put_note, xs, rest) == Wr.put_list(~Cm.Note, ~DocCommit.sp_w_note, xs, rest) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Cm.Note, ~FCm.put_note, xs, rest), (List.length(&2, Cm.Note, xs), dcw.nitems(xs, rest)), dcw.nput_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_list(~Cm.Note, ~DocCommit.sp_w_note, xs, rest) : String}
  %Equal.sym(Nat & String, Wr.put_list.go(~Cm.Note, ~DocCommit.sp_w_note, xs, rest), (List.length(&2, Cm.Note, xs), dcw.nitems(xs, rest)), dcw.sput_go(xs, rest)) : {Wr.put_list.fin((List.length(&2, Cm.Note, xs), dcw.nitems(xs, rest))) == Wr.put_list.fin(_) : String}
  {==}

def dcw.put_verdict(v: Cm.Verdict) -> {FCm.put_verdict(v) == DocCommit.sp_w_verdict(v) : String}:
  match v:
    case Cm.Failure{}:
      {==}
    case Cm.Summary{+ns, +p}:
      Equal.cong(String, String, z => Wr.put_nat(1n, z), Wr.put_list(~Cm.Note, ~FCm.put_note, ns, Wr.put_bool(p, "")), Wr.put_list(~Cm.Note, ~DocCommit.sp_w_note, ns, Wr.put_bool(p, "")), dcw.notes(ns, Wr.put_bool(p, "")))

def dcw.reply(q: FCm.Req) -> {FCm.answer(q) == DocCommit.sp_w_reply(q) : String}:
  match q:
    case FCm.QCheck{+ms}:
      dcw.put_check(Cm.check(ms))
    case FCm.QPublish{+p}:
      dcw.put_outcome(Cm.outcome(p))
    case FCm.QAnswer{+fs}:
      dcw.put_verdict(Cm.answer(fs))
    case FCm.QGate{+b, +d}:
      dcw.put_gate(Cm.gate(b, d))
    case FCm.QSeen{+d, +xs}:
      {==}
    case FCm.QPrefix{+h}:
      {==}
    case FCm.QSweep{+h, +es}:
      {==}

def DocCommit.commit_entry_answers(q, h):
  %Equal.sym(Wr.Dec<FCm.Req>, FCm.get_req(DocCommit.sp_w_req(q, "")), Wr.Got{q, ""}, DocCommit.commit_entry_reads(q, "", h)) : {FCm.ffi.got(_) == DocCommit.sp_w_reply(q) : String}
  dcw.reply(q)
