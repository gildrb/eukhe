# eukhe: the laws of area cron_serve: the stepper's entry, byte by byte

import Base
import ../../bend/cron.bend as Cr
import ../../bend/cron_store.bend as CS
import ../../bend/cron_serve.bend as Sv
import ../../bend/ffi_cron_serve.bend as FC
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase
import ../cron.bend as Cron
import ./serve.bend as CronServe

# (D2.3) The stepper the Rust store runs, as compiled Bend
# ---------------------------------------------------------
# The Rust store (crates/eukhe-core/src/cron/store/serve.rs, owner.rs) opens
# one stepper (bend/ffi_cron_serve.bend, entry 410 cron_serve) per process,
# sends it each update of a jobs file under the file's lock and the end of
# each run it guards, and does what each reply says; it asks the stepper's
# call whether a job is due. These laws pin every reply of the open, of
# every step from every state and of the call, for every input: the spec
# below spells events, questions and replies with the wire primitives and
# the spellers of laws/cron.bend, never with the entry's codec, and states
# each answer with the spec of laws/cron_serve/serve.bend. The grammar,
# restated from the entry's header:
#
#   open    the empty input                                   reply: empty
#   call    now (Nat), Fact                                   reply: Bool
#   Ev      0 an update: me (Nat), Disk, Op | 1 the end of a run: d (String)
#   Disk    0 missing | 1 unreadable | 2 read: List JRec, List CRec
#   JRec    0 known: id (Nat), Fact | 1 not read
#   CRec    0 known: dispatch (String), job (Nat), owner (Nat) | 1 not read
#   Fact    Cron.spell_fact: status, plan, next run, failures in a row
#   Op      0 claim: due, now (Nat), fresh (List String) | 1 recover: dead
#           (List Nat) | 2 finish: d (String), ran, failed (Bool), now (Nat)
#           | 3 cancel: job (Nat) | 4 resume: job, now (Nat) | 5 create: job
#           (Nat), Fact
#   reply   to 0: aside, write (Bool), List JOut, List COut; to 1: empty
#   JOut    0 kept | 1 Cron.spell_took | 2 Cron.spell_back | 3
#           Cron.spell_fin | 4 Cron.spell_cut | 5 Cron.spell_again | 6 new
#   COut    0 kept | 1 dropped | 2 new: position (Nat), dispatch (String)
#   errors  "cron_serve: malformed event" (the runs kept), "cron_serve:
#           malformed open", "cron_serve: the open was refused",
#           "cron_serve: malformed question"

# Spelling the input
# ------------------

def ce_spell_jrec(r: Sv.JRec, rest: String) -> String:
  match r:
    case Sv.JKnown{i, f}:
      Wr.put_nat(0n, Wr.put_nat(i, Cron.spell_fact(f, rest)))
    case Sv.JRaw{}:
      Wr.put_nat(1n, rest)

def ce_spell_jrecs(xs: List<&2, Sv.JRec>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      ce_spell_jrec(x, ce_spell_jrecs(t, rest))

def ce_spell_crec(c: Sv.CRec, rest: String) -> String:
  match c:
    case Sv.CKnown{d, j, o}:
      Wr.put_nat(0n, Wr.put_str(d, Wr.put_nat(j, Wr.put_nat(o, rest))))
    case Sv.CRaw{}:
      Wr.put_nat(1n, rest)

def ce_spell_crecs(xs: List<&2, Sv.CRec>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      ce_spell_crec(x, ce_spell_crecs(t, rest))

def ce_spell_disk(k: Sv.Disk, rest: String) -> String:
  match k:
    case Sv.Missing{}:
      Wr.put_nat(0n, rest)
    case Sv.Torn{}:
      Wr.put_nat(1n, rest)
    case Sv.Parsed{+js, +cs}:
      Wr.put_nat(2n, Wr.put_nat(List.length(&2, Sv.JRec, js), ce_spell_jrecs(js, Wr.put_nat(List.length(&2, Sv.CRec, cs), ce_spell_crecs(cs, rest)))))

def ce_spell_op(op: Sv.Op, rest: String) -> String:
  match op:
    case Sv.OClaim{due, now, fresh}:
      Wr.put_nat(0n, Wr.put_nat(due, Wr.put_nat(now, LawsBase.wire_spell_strs(fresh, rest))))
    case Sv.ORecover{dead}:
      Wr.put_nat(1n, LawsBase.wire_spell_nats(dead, rest))
    case Sv.OFinish{d, ran, failed, now}:
      Wr.put_nat(2n, Wr.put_str(d, Wr.put_bool(ran, Wr.put_bool(failed, Wr.put_nat(now, rest)))))
    case Sv.OCancel{n}:
      Wr.put_nat(3n, Wr.put_nat(n, rest))
    case Sv.OResume{n, now}:
      Wr.put_nat(4n, Wr.put_nat(n, Wr.put_nat(now, rest)))
    case Sv.OCreate{n, f}:
      Wr.put_nat(5n, Wr.put_nat(n, Cron.spell_fact(f, rest)))

# the event Rust writes
def ce_spell_ev(e: FC.Ev) -> String:
  match e:
    case FC.EServe{me, k, op}:
      Wr.put_nat(0n, Wr.put_nat(me, ce_spell_disk(k, ce_spell_op(op, ""))))
    case FC.EEnd{d}:
      Wr.put_nat(1n, Wr.put_str(d, ""))

# the question Rust writes
def ce_spell_ask(+now: Nat, f: CS.Fact) -> String:
  Wr.put_nat(now, Cron.spell_fact(f, ""))

# Fitting the wire
# ----------------

def ce_str_fits(+d: String) -> Bool:
  LawsBase.wire_fits(String.length(d))

def ce_jrec_fits(r: Sv.JRec) -> Bool:
  match r:
    case Sv.JKnown{i, f}:
      Bool.and(LawsBase.wire_fits(i), Cron.fact_fits(f))
    case Sv.JRaw{}:
      True{}

def ce_jrecs_fit(xs: List<&2, Sv.JRec>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(ce_jrec_fits(x), ce_jrecs_fit(t))

def ce_crec_fits(c: Sv.CRec) -> Bool:
  match c:
    case Sv.CKnown{d, j, o}:
      Bool.and(ce_str_fits(d), Bool.and(LawsBase.wire_fits(j), LawsBase.wire_fits(o)))
    case Sv.CRaw{}:
      True{}

def ce_crecs_fit(xs: List<&2, Sv.CRec>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      Bool.and(ce_crec_fits(x), ce_crecs_fit(t))

def ce_disk_fits(k: Sv.Disk) -> Bool:
  match k:
    case Sv.Missing{}:
      True{}
    case Sv.Torn{}:
      True{}
    case Sv.Parsed{+js, +cs}:
      Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Sv.JRec, js)), ce_jrecs_fit(js)), Bool.and(LawsBase.wire_fits(List.length(&2, Sv.CRec, cs)), ce_crecs_fit(cs)))

def ce_op_fits(op: Sv.Op) -> Bool:
  match op:
    case Sv.OClaim{due, now, fresh}:
      Bool.and(Bool.and(LawsBase.wire_fits(due), LawsBase.wire_fits(now)), LawsBase.wire_strs_fit(fresh))
    case Sv.ORecover{+dead}:
      Bool.and(LawsBase.wire_fits(List.length(&2, Nat, dead)), LawsBase.wire_nats_fit(dead))
    case Sv.OFinish{d, ran, failed, now}:
      Bool.and(ce_str_fits(d), LawsBase.wire_fits(now))
    case Sv.OCancel{n}:
      LawsBase.wire_fits(n)
    case Sv.OResume{n, now}:
      Bool.and(LawsBase.wire_fits(n), LawsBase.wire_fits(now))
    case Sv.OCreate{n, f}:
      Bool.and(LawsBase.wire_fits(n), Cron.fact_fits(f))

# every count, length and number of e fits the wire
def ce_ev_fits(e: FC.Ev) -> Bool:
  match e:
    case FC.EServe{me, k, op}:
      Bool.and(LawsBase.wire_fits(me), Bool.and(ce_disk_fits(k), ce_op_fits(op)))
    case FC.EEnd{d}:
      ce_str_fits(d)

# Spelling the reply
# ------------------

def ce_spell_jout(o: Sv.JOut, rest: String) -> String:
  match o:
    case Sv.JSame{}:
      Wr.put_nat(0n, rest)
    case Sv.JTook{t}:
      Wr.put_nat(1n, Cron.spell_took(t, rest))
    case Sv.JBack{b}:
      Wr.put_nat(2n, Cron.spell_back(b, rest))
    case Sv.JFin{x}:
      Wr.put_nat(3n, Cron.spell_fin(x, rest))
    case Sv.JCut{x}:
      Wr.put_nat(4n, Cron.spell_cut(x, rest))
    case Sv.JAgain{x}:
      Wr.put_nat(5n, Cron.spell_again(x, rest))
    case Sv.JNew{}:
      Wr.put_nat(6n, rest)

def ce_spell_jouts(xs: List<&2, Sv.JOut>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      ce_spell_jout(x, ce_spell_jouts(t, rest))

def ce_spell_cout(o: Sv.COut, rest: String) -> String:
  match o:
    case Sv.CKeep{}:
      Wr.put_nat(0n, rest)
    case Sv.CDrop{}:
      Wr.put_nat(1n, rest)
    case Sv.CNew{k, d}:
      Wr.put_nat(2n, Wr.put_nat(k, Wr.put_str(d, rest)))

def ce_spell_couts(xs: List<&2, Sv.COut>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      ce_spell_cout(x, ce_spell_couts(t, rest))

# the reply Rust reads to an update
def ce_spell_out(o: Sv.Out) -> String:
  match o:
    case Sv.Out{a, w, +js, +cs}:
      Wr.put_bool(a, Wr.put_bool(w, Wr.put_nat(List.length(&2, Sv.JOut, js), ce_spell_jouts(js, Wr.put_nat(List.length(&2, Sv.COut, cs), ce_spell_couts(cs, ""))))))

# Reading the input
# -----------------

def ce_read_jrec.fact(i: Nat, r: Wr.Dec<CS.Fact>) -> Wr.Dec<Sv.JRec>:
  match r:
    case Wr.Got{f, s}:
      Wr.Got{Sv.JKnown{i, f}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_jrec.known(r: Wr.Dec<Nat>) -> Wr.Dec<Sv.JRec>:
  match r:
    case Wr.Got{i, s}:
      ce_read_jrec.fact(i, Cron.read_fact(s))
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_jrec.tag(t: Nat, s: String) -> Wr.Dec<Sv.JRec>:
  match t:
    case 0n:
      ce_read_jrec.known(Wr.get_nat(s))
    case 1n:
      Wr.Got{Sv.JRaw{}, s}
    case 2n+p:
      Wr.Bad{}

def ce_read_jrec.go(r: Wr.Dec<Nat>) -> Wr.Dec<Sv.JRec>:
  match r:
    case Wr.Got{t, s}:
      ce_read_jrec.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_jrec(s: String) -> Wr.Dec<Sv.JRec>:
  ce_read_jrec.go(Wr.get_nat(s))

def ce_read_crec.owner(d: String, j: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Sv.CRec>:
  match r:
    case Wr.Got{o, s}:
      Wr.Got{Sv.CKnown{d, j, o}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_crec.job(d: String, r: Wr.Dec<Nat>) -> Wr.Dec<Sv.CRec>:
  match r:
    case Wr.Got{j, s}:
      ce_read_crec.owner(d, j, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_crec.known(r: Wr.Dec<String>) -> Wr.Dec<Sv.CRec>:
  match r:
    case Wr.Got{d, s}:
      ce_read_crec.job(d, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_crec.tag(t: Nat, s: String) -> Wr.Dec<Sv.CRec>:
  match t:
    case 0n:
      ce_read_crec.known(Wr.get_str(s))
    case 1n:
      Wr.Got{Sv.CRaw{}, s}
    case 2n+p:
      Wr.Bad{}

def ce_read_crec.go(r: Wr.Dec<Nat>) -> Wr.Dec<Sv.CRec>:
  match r:
    case Wr.Got{t, s}:
      ce_read_crec.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_crec(s: String) -> Wr.Dec<Sv.CRec>:
  ce_read_crec.go(Wr.get_nat(s))

def ce_read_disk.claims(js: List<&2, Sv.JRec>, r: Wr.Dec<List<&2, Sv.CRec>>) -> Wr.Dec<Sv.Disk>:
  match r:
    case Wr.Got{cs, s}:
      Wr.Got{Sv.Parsed{js, cs}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_disk.jobs(r: Wr.Dec<List<&2, Sv.JRec>>) -> Wr.Dec<Sv.Disk>:
  match r:
    case Wr.Got{js, s}:
      ce_read_disk.claims(js, Wr.get_list(~Sv.CRec, ~ce_read_crec, s))
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_disk.tag(t: Nat, s: String) -> Wr.Dec<Sv.Disk>:
  match t:
    case 0n:
      Wr.Got{Sv.Missing{}, s}
    case 1n:
      Wr.Got{Sv.Torn{}, s}
    case 2n:
      ce_read_disk.jobs(Wr.get_list(~Sv.JRec, ~ce_read_jrec, s))
    case 3n+p:
      Wr.Bad{}

def ce_read_disk(r: Wr.Dec<Nat>) -> Wr.Dec<Sv.Disk>:
  match r:
    case Wr.Got{t, s}:
      ce_read_disk.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_op.fresh(d: Nat, n: Nat, r: Wr.Dec<List<&2, String>>) -> Wr.Dec<Sv.Op>:
  match r:
    case Wr.Got{xs, s}:
      Wr.Got{Sv.OClaim{d, n, xs}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_op.now(d: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Sv.Op>:
  match r:
    case Wr.Got{n, s}:
      ce_read_op.fresh(d, n, Wr.get_list(~String, ~Wr.get_str, s))
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_op.claim(r: Wr.Dec<Nat>) -> Wr.Dec<Sv.Op>:
  match r:
    case Wr.Got{d, s}:
      ce_read_op.now(d, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_op.recover(r: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<Sv.Op>:
  match r:
    case Wr.Got{xs, s}:
      Wr.Got{Sv.ORecover{xs}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_op.at(d: String, a: Bool, b: Bool, r: Wr.Dec<Nat>) -> Wr.Dec<Sv.Op>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{Sv.OFinish{d, a, b, n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_op.failed(d: String, a: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<Sv.Op>:
  match r:
    case Wr.Got{b, s}:
      ce_read_op.at(d, a, b, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_op.ran(d: String, r: Wr.Dec<Bool>) -> Wr.Dec<Sv.Op>:
  match r:
    case Wr.Got{a, s}:
      ce_read_op.failed(d, a, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_op.finish(r: Wr.Dec<String>) -> Wr.Dec<Sv.Op>:
  match r:
    case Wr.Got{d, s}:
      ce_read_op.ran(d, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_op.cancel(r: Wr.Dec<Nat>) -> Wr.Dec<Sv.Op>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{Sv.OCancel{n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_op.when(n: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Sv.Op>:
  match r:
    case Wr.Got{c, s}:
      Wr.Got{Sv.OResume{n, c}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_op.resume(r: Wr.Dec<Nat>) -> Wr.Dec<Sv.Op>:
  match r:
    case Wr.Got{n, s}:
      ce_read_op.when(n, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_op.made(n: Nat, r: Wr.Dec<CS.Fact>) -> Wr.Dec<Sv.Op>:
  match r:
    case Wr.Got{f, s}:
      Wr.Got{Sv.OCreate{n, f}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_op.create(r: Wr.Dec<Nat>) -> Wr.Dec<Sv.Op>:
  match r:
    case Wr.Got{n, s}:
      ce_read_op.made(n, Cron.read_fact(s))
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_op.tag(t: Nat, s: String) -> Wr.Dec<Sv.Op>:
  match t:
    case 0n:
      ce_read_op.claim(Wr.get_nat(s))
    case 1n:
      ce_read_op.recover(Wr.get_list(~Nat, ~Wr.get_nat, s))
    case 2n:
      ce_read_op.finish(Wr.get_str(s))
    case 3n:
      ce_read_op.cancel(Wr.get_nat(s))
    case 4n:
      ce_read_op.resume(Wr.get_nat(s))
    case 5n:
      ce_read_op.create(Wr.get_nat(s))
    case 6n+p:
      Wr.Bad{}

def ce_read_op(r: Wr.Dec<Nat>) -> Wr.Dec<Sv.Op>:
  match r:
    case Wr.Got{t, s}:
      ce_read_op.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_ev.op(me: Nat, k: Sv.Disk, r: Wr.Dec<Sv.Op>) -> Wr.Dec<FC.Ev>:
  match r:
    case Wr.Got{o, s}:
      Wr.Got{FC.EServe{me, k, o}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_ev.disk(me: Nat, r: Wr.Dec<Sv.Disk>) -> Wr.Dec<FC.Ev>:
  match r:
    case Wr.Got{k, s}:
      ce_read_ev.op(me, k, ce_read_op(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_ev.serve(r: Wr.Dec<Nat>) -> Wr.Dec<FC.Ev>:
  match r:
    case Wr.Got{me, s}:
      ce_read_ev.disk(me, ce_read_disk(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_ev.end(r: Wr.Dec<String>) -> Wr.Dec<FC.Ev>:
  match r:
    case Wr.Got{d, s}:
      Wr.Got{FC.EEnd{d}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_ev.tag(t: Nat, s: String) -> Wr.Dec<FC.Ev>:
  match t:
    case 0n:
      ce_read_ev.serve(Wr.get_nat(s))
    case 1n:
      ce_read_ev.end(Wr.get_str(s))
    case 2n+p:
      Wr.Bad{}

def ce_read_ev.go(r: Wr.Dec<Nat>) -> Wr.Dec<FC.Ev>:
  match r:
    case Wr.Got{t, s}:
      ce_read_ev.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def ce_whole(-A: Data, whole: Bool, x: A) -> Maybe<&2, A>:
  match whole:
    case True{}:
      Some{x}
    case False{}:
      None{}

def ce_read_ev.whole(r: Wr.Dec<FC.Ev>) -> Maybe<&2, FC.Ev>:
  match r:
    case Wr.Got{e, s}:
      ce_whole(FC.Ev, Wr.end(s), e)
    case Wr.Bad{}:
      None{}

# the event s is, when s is exactly one event
def ce_read_ev(s: String) -> Maybe<&2, FC.Ev>:
  ce_read_ev.whole(ce_read_ev.go(Wr.get_nat(s)))

# a question: whether job f is due at now
type CeAsk is Data:
  CeAsk{now: Nat, f: CS.Fact}

def ce_read_ask.fact(n: Nat, r: Wr.Dec<CS.Fact>) -> Maybe<&2, CeAsk>:
  match r:
    case Wr.Got{f, s}:
      ce_whole(CeAsk, Wr.end(s), CeAsk{n, f})
    case Wr.Bad{}:
      None{}

def ce_read_ask.go(r: Wr.Dec<Nat>) -> Maybe<&2, CeAsk>:
  match r:
    case Wr.Got{n, s}:
      ce_read_ask.fact(n, Cron.read_fact(s))
    case Wr.Bad{}:
      None{}

# the question s is, when s is exactly one question
def ce_read_ask(s: String) -> Maybe<&2, CeAsk>:
  ce_read_ask.go(Wr.get_nat(s))

# The answers, stated on their own
# --------------------------------

def ce_err_event() -> String:
  SCon{'E', SCon{' ', "cron_serve: malformed event"}}

def ce_served(r: Sv.Served) -> FC.St & String:
  match r:
    case Sv.Served{runs, o}:
      (FC.Open{runs}, ce_spell_out(o))

# the stepper after event e from the runs, and its reply: an update is the
# spec's (CronServe.sv_serve), spelled; the end of a run takes its
# dispatch id out of the runs (CronServe.sv_out) and answers empty
def ce_step(+runs: List<&2, String>, e: FC.Ev) -> FC.St & String:
  match e:
    case FC.EServe{me, k, op}:
      ce_served(CronServe.sv_serve(runs, me, k, op))
    case FC.EEnd{d}:
      (FC.Open{CronServe.sv_out(d, runs)}, "")

# the reply to the question whether f is due at now
def ce_due(+now: Nat, f: CS.Fact) -> String:
  Wr.put_bool(CronServe.sv_due(f, now), "")

def ce_ask(m: Maybe<&2, CeAsk>) -> String:
  match m:
    case None{}:
      SCon{'E', SCon{' ', "cron_serve: malformed question"}}
    case Some{q}:
      match q:
        case CeAsk{n, f}:
          ce_due(n, f)

# The stepper the safety laws run
# -------------------------------
# laws/cron_serve/safety.bend runs processes that update one file with the
# code (Sv.serve) and end runs with it (Sv.end). ce_entry states the entry
# over that code, from every state and for every input.

def ce_entry.run(+runs: List<&2, String>, e: FC.Ev) -> FC.St & String:
  match e:
    case FC.EServe{me, k, op}:
      ce_served(Sv.serve(runs, me, k, op))
    case FC.EEnd{d}:
      (FC.Open{Sv.end(d, runs)}, "")

def ce_entry.at(+runs: List<&2, String>, m: Maybe<&2, FC.Ev>) -> FC.St & String:
  match m:
    case None{}:
      (FC.Open{runs}, ce_err_event())
    case Some{e}:
      ce_entry.run(runs, e)

def ce_entry(st: FC.St, s: String) -> FC.St & String:
  match st:
    case FC.Open{+runs}:
      ce_entry.at(runs, ce_read_ev(s))
    case FC.Shut{}:
      (FC.Shut{}, SCon{'E', SCon{' ', "cron_serve: the open was refused"}})

# every reply, from the state and reply r through the inputs ins
def ce_feed(ins: List<&2, String>, r: FC.St & String) -> List<&2, String>:
  match ins:
    case Nil{}:
      (st, out) = r
      [out]
    case i <> t:
      (st, out) = r
      out <> ce_feed(t, FC.step(st, i))

# Laws
# ----

# LAW cron_serve_open_empty: the stepper opens on the empty input with no
# runs and the empty reply
# EXCLUDES: a process that starts running dispatches it never claimed
law cron_serve_open_empty:
  {FC.open("") == (FC.Open{Nil{}}, "") : FC.St & String}

# LAW cron_serve_open_refuses: any other open is refused with exactly the
# error form, and the refused stepper answers every input with exactly the
# error form
# EXCLUDES: runs opened from input Rust never writes, a refused stepper
#   that decides
law cron_serve_open_refuses:
  for +s: String
  for ne: {String.is_empty(s) == False{} : Bool}
  for +e: String
  {FC.open(s) == (FC.Shut{}, SCon{'E', SCon{' ', "cron_serve: malformed open"}}) : FC.St & String} & {FC.step(FC.Shut{}, e) == (FC.Shut{}, SCon{'E', SCon{' ', "cron_serve: the open was refused"}}) : FC.St & String}

# LAW cron_serve_step_answers: on every event Rust writes whose numbers
# and lengths fit the wire, from every runs, the stepper's runs and reply
# are the spec's: an update's whole new file (every record's answer in
# file order, the claims dropped and made, aside, write) and the runs
# after it; the end of a run's runs; spelled
# EXCLUDES: a misread record, claim, owner, op or fact; any decision but
#   the spec's (laws/cron_serve/serve.bend); a reply in another order or
#   tag; runs not updated
law cron_serve_step_answers:
  for +runs: List<&2, String>
  for +e: FC.Ev
  for fits: {ce_ev_fits(e) == True{} : Bool}
  {FC.step(FC.Open{runs}, ce_spell_ev(e)) == ce_step(runs, e) : FC.St & String}

# LAW cron_serve_step_reads: every input that is exactly one event (as the
# wire primitives read it) steps the runs as that event
# EXCLUDES: a decision on another reading of the input
law cron_serve_step_reads:
  for +runs: List<&2, String>
  for +s: String
  for +e: FC.Ev
  for got: {ce_read_ev(s) == Some{e} : Maybe<&2, FC.Ev>}
  {FC.step(FC.Open{runs}, s) == ce_step(runs, e) : FC.St & String}

# LAW cron_serve_step_malformed_exact: every input that is not exactly one
# event keeps the runs and answers exactly the error form 'E ', then
# "cron_serve: malformed event"
# EXCLUDES: a guessed event, runs changed by garbage, an event with input
#   after it decided
law cron_serve_step_malformed_exact:
  for +runs: List<&2, String>
  for +s: String
  for no: {ce_read_ev(s) == None{} : Maybe<&2, FC.Ev>}
  {FC.step(FC.Open{runs}, s) == (FC.Open{runs}, ce_err_event()) : FC.St & String}

# LAW cron_serve_step_unknown_tag: an event tag past 1, a file tag past 2
# (after a process number), or an op tag past 5 (after a process number
# and a missing file), with any number of digits and whatever follows,
# keeps the runs and answers exactly the malformed-event error form
# EXCLUDES: an unknown event, file or op read as a known one (an unknown
#   op read as a claim pass)
law cron_serve_step_unknown_tag:
  for +runs: List<&2, String>
  for +n: Nat
  for +rest: String
  for +me: Nat
  for +fits: {LawsBase.wire_fits(me) == True{} : Bool}
  {FC.step(FC.Open{runs}, Wr.put_nat(2n+n, rest)) == (FC.Open{runs}, ce_err_event()) : FC.St & String} & {FC.step(FC.Open{runs}, Wr.put_nat(0n, Wr.put_nat(me, Wr.put_nat(3n+n, rest)))) == (FC.Open{runs}, ce_err_event()) : FC.St & String} & {FC.step(FC.Open{runs}, Wr.put_nat(0n, Wr.put_nat(me, Wr.put_nat(0n, Wr.put_nat(6n+n, rest))))) == (FC.Open{runs}, ce_err_event()) : FC.St & String}

# LAW cron_serve_is_entry: the stepper the safety laws run (an update is
# Sv.serve, the end of a run Sv.end) is the entry's step, from every state
# and for every input: the laws over processes updating one file speak of
# the stepper Rust runs
# EXCLUDES: safety laws made vacuous by a serve or an end the entry does
#   not run (a frozen copy beside the entry's own helper)
law cron_serve_is_entry:
  for +st: FC.St
  for +s: String
  {FC.step(st, s) == ce_entry(st, s) : FC.St & String}

# LAW cron_serve_due_answers: on every question Rust writes whose numbers
# fit the wire, the call answers whether the job is due at now
# (CronServe.sv_due: a claim pass at now would claim it or roll its next
# run)
# EXCLUDES: a misread clock or fact, a due question answered by another
#   rule, a reply in another spelling
law cron_serve_due_answers:
  for +now: Nat
  for +f: CS.Fact
  for fits: {Bool.and(LawsBase.wire_fits(now), Cron.fact_fits(f)) == True{} : Bool}
  {FC.ffi(ce_spell_ask(now, f)) == ce_due(now, f) : String}

# LAW cron_serve_due_exact_input: the call answers every input as the laws'
# reader reads it: exactly one question is answered as that question, any
# other input with exactly the error form 'E ', then "cron_serve:
# malformed question"
# EXCLUDES: a guessed question, a question with input after it answered, a
#   default for garbage
law cron_serve_due_exact_input:
  for +s: String
  {FC.ffi(s) == ce_ask(ce_read_ask(s)) : String}

# LAW cron_serve_entry_example: anchor: the bytes Rust writes and reads: a
# due interval job and a record this build cannot read, with a claim it
# cannot read: the job is claimed with the first fresh id, its next run
# rolled; the end of that run; a finish of the run: it ran, the claim
# goes, the job counts it; a recovery of a dead owner's claim; an unknown
# event tag and input left over are malformed; the due question
# EXCLUDES: a tag numbering or field order other than Rust's
law cron_serve_entry_example:
  {ce_feed(["0,0,2,2,0,0,0,1,10,1,5,0,1,1,1,0,5,5,2,1,a1,b", "0,0,2,1,0,0,0,1,10,1,15,0,1,0,1,a0,0,2,1,aTF20,", "1,1,a", "0,0,2,1,0,0,0,1,10,1,15,0,1,0,1,b0,1,1,1,1,", "2,", "1,1,ax"], FC.open("")) == ["", "FT2,1,2,1,15,0,2,0,2,0,1,a", "FT1,3,1,0,1,15,0,1,1,", "", "FT1,2,1,0,1,15,1,1,", "E cron_serve: malformed event", "E cron_serve: malformed event"] : List<&2, String>} &
  {[FC.ffi("5,0,1,10,1,5,0,"), FC.ffi("4,0,1,10,1,5,0,"), FC.ffi("5,0,1,10,1,5,0,x")] == ["T", "F", "E cron_serve: malformed question"] : List<&2, String>}

# LAW cron_serve_entry_witness: anchor: the premises of the laws above hold
# on concrete inputs, so none is vacuous: an update and an end that fit,
# a question that fits, an input that is no event and one that is an event
# EXCLUDES: cron_serve_step_answers, cron_serve_step_reads,
#   cron_serve_step_malformed_exact or cron_serve_due_answers made vacuous
#   by premises no input meets
law cron_serve_entry_witness:
  {[ce_ev_fits(FC.EServe{0n, Sv.Parsed{[Sv.JKnown{0n, CS.Fact{Cr.Active{}, CS.PEvery{10n}, Some{5n}, 0n}}, Sv.JRaw{}], [Sv.CKnown{"a", 0n, 1n}, Sv.CRaw{}]}, Sv.OClaim{5n, 5n, ["b"]}}), ce_ev_fits(FC.EEnd{"a"}), Bool.and(LawsBase.wire_fits(5n), Cron.fact_fits(CS.Fact{Cr.Active{}, CS.POnce{}, None{}, 0n}))] == [True{}, True{}, True{}] : List<&2, Bool>} &
  {ce_read_ev("2,") == None{} : Maybe<&2, FC.Ev>} &
  {ce_read_ev("1,1,a") == Some{FC.EEnd{"a"}} : Maybe<&2, FC.Ev>}
