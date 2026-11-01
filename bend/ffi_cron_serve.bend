# ffi_cron_serve: the compiled Bend core's stepper for the cron job store
# of one process (bend/cron_serve.bend). Rust `cron::store` opens one per
# process (the owner of the claims it makes), sends it each update of a
# jobs file under the file's lock, and the end of each run it guards, and
# does what each reply says. Its state is the process's runs: the dispatch
# ids it runs now. The codec is the wire format of bend/wire.bend
# (crates/eukhe-bend/WIRE.md):
#
#   open    the empty input (no runs)                       reply: empty
#   call    the due question: now (Nat), Fact               reply: Bool
#   step    Ev
#   Ev      0 an update: me (Nat: this process, numbered as the owners
#             on record), Disk, Op
#           1 the run of a dispatch ended (d: String)       reply: empty
#   Disk    0 missing | 1 unreadable | 2 read: List JRec, List CRec
#   JRec    0 known: id (Nat), Fact | 1 a record this build cannot read
#   CRec    0 known: dispatch id (String), job id (Nat), owner (Nat) |
#           1 a record this build cannot read
#   Fact    status (0 active | 1 paused | 2 finished | 3 cancelled), plan
#           (0 a one-shot | 1 an interval, then its ms | 2 a rule), the
#           next run (Maybe ms), the failures in a row (Nat)
#   Op      0 claim: due (Nat), now (Nat), fresh dispatch ids (List String)
#           1 recover: the dead owners (List Nat)
#           2 finish: d (String), ran (Bool), failed (Bool), now (Nat)
#           3 cancel: job (Nat)
#           4 resume: job (Nat), now (Nat)
#           5 create: job (Nat), Fact
#   reply to 0: aside (Bool), write (Bool), List JOut, List COut
#   JOut    0 kept as read | 1 a claim pass (0 not due | 1 roll | 2 claim;
#           then a next run) | 2 a recovery (0 kept | 1 interrupted: a
#           status, a Maybe ms) | 3 a finish (0 untouched | 1 ran |
#           2 skipped; then a status, a next run, a Nat) | 4 a cancel
#           (0 already | 1 cut: a status, a Maybe ms) | 5 a resume
#           (0 resumed: a status, a next run, a Nat | 1 ended | 2 not
#           recurring) | 6 the new job
#   Next    0 none | 1 at, then the ms | 2 the rule's next match
#   COut    0 kept | 1 dropped | 2 new: the job record's position (Nat),
#           the dispatch id (String)
#
# A malformed event (an unknown tag, a bad number or string, input left
# over) answers "cron_serve: malformed event" and keeps the runs; an open
# that is not empty answers "cron_serve: malformed open" and the refused
# stepper answers every step "cron_serve: the open was refused"; a
# malformed question answers "cron_serve: malformed question".
# laws/cron_serve/ pins the entry. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./cron.bend as Cr
import ./cron_store.bend as CS
import ./cron_serve.bend as Sv

# the runs, or a refused open
type St is Data:
  Open{runs: List<&2, String>}
  Shut{}

# one event
type Ev is Data:
  EServe{me: Nat, disk: Sv.Disk, op: Sv.Op}
  EEnd{d: String}

# Decoding
# --------

def get_status.tag(t: Nat, s: String) -> W.Dec<Cr.Status>:
  match t:
    case 0n:
      W.Got{Cr.Active{}, s}
    case 1n:
      W.Got{Cr.Paused{}, s}
    case 2n:
      W.Got{Cr.Finished{}, s}
    case 3n:
      W.Got{Cr.Cancelled{}, s}
    case 4n+p:
      W.Bad{}

def get_status(r: W.Dec<Nat>) -> W.Dec<Cr.Status>:
  match r:
    case W.Got{t, s}:
      get_status.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_plan.every(r: W.Dec<Nat>) -> W.Dec<CS.Plan>:
  match r:
    case W.Got{n, s}:
      W.Got{CS.PEvery{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_plan.tag(t: Nat, s: String) -> W.Dec<CS.Plan>:
  match t:
    case 0n:
      W.Got{CS.POnce{}, s}
    case 1n:
      get_plan.every(W.get_nat(s))
    case 2n:
      W.Got{CS.PRule{}, s}
    case 3n+p:
      W.Bad{}

def get_plan(r: W.Dec<Nat>) -> W.Dec<CS.Plan>:
  match r:
    case W.Got{t, s}:
      get_plan.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_mnat.some(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{n, s}:
      W.Got{Some{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_mnat.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_mnat.some(W.get_nat(s))
    case 2n+p:
      W.Bad{}

def get_mnat(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{t, s}:
      get_mnat.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_fact.streak(st: Cr.Status, p: CS.Plan, m: Maybe<&2, Nat>, r: W.Dec<Nat>) -> W.Dec<CS.Fact>:
  match r:
    case W.Got{k, s}:
      W.Got{CS.Fact{st, p, m, k}, s}
    case W.Bad{}:
      W.Bad{}

def get_fact.next(st: Cr.Status, p: CS.Plan, r: W.Dec<Maybe<&2, Nat>>) -> W.Dec<CS.Fact>:
  match r:
    case W.Got{m, s}:
      get_fact.streak(st, p, m, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_fact.plan(st: Cr.Status, r: W.Dec<CS.Plan>) -> W.Dec<CS.Fact>:
  match r:
    case W.Got{p, s}:
      get_fact.next(st, p, get_mnat(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_fact.status(r: W.Dec<Cr.Status>) -> W.Dec<CS.Fact>:
  match r:
    case W.Got{st, s}:
      get_fact.plan(st, get_plan(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

# the fact at the start of s
def get_fact(s: String) -> W.Dec<CS.Fact>:
  get_fact.status(get_status(W.get_nat(s)))

def get_jrec.fact(i: Nat, r: W.Dec<CS.Fact>) -> W.Dec<Sv.JRec>:
  match r:
    case W.Got{f, s}:
      W.Got{Sv.JKnown{i, f}, s}
    case W.Bad{}:
      W.Bad{}

def get_jrec.known(r: W.Dec<Nat>) -> W.Dec<Sv.JRec>:
  match r:
    case W.Got{i, s}:
      get_jrec.fact(i, get_fact(s))
    case W.Bad{}:
      W.Bad{}

def get_jrec.tag(t: Nat, s: String) -> W.Dec<Sv.JRec>:
  match t:
    case 0n:
      get_jrec.known(W.get_nat(s))
    case 1n:
      W.Got{Sv.JRaw{}, s}
    case 2n+p:
      W.Bad{}

def get_jrec.go(r: W.Dec<Nat>) -> W.Dec<Sv.JRec>:
  match r:
    case W.Got{t, s}:
      get_jrec.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# a job record at the start of s
def get_jrec(s: String) -> W.Dec<Sv.JRec>:
  get_jrec.go(W.get_nat(s))

def get_crec.owner(d: String, j: Nat, r: W.Dec<Nat>) -> W.Dec<Sv.CRec>:
  match r:
    case W.Got{o, s}:
      W.Got{Sv.CKnown{d, j, o}, s}
    case W.Bad{}:
      W.Bad{}

def get_crec.job(d: String, r: W.Dec<Nat>) -> W.Dec<Sv.CRec>:
  match r:
    case W.Got{j, s}:
      get_crec.owner(d, j, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_crec.known(r: W.Dec<String>) -> W.Dec<Sv.CRec>:
  match r:
    case W.Got{d, s}:
      get_crec.job(d, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_crec.tag(t: Nat, s: String) -> W.Dec<Sv.CRec>:
  match t:
    case 0n:
      get_crec.known(W.get_str(s))
    case 1n:
      W.Got{Sv.CRaw{}, s}
    case 2n+p:
      W.Bad{}

def get_crec.go(r: W.Dec<Nat>) -> W.Dec<Sv.CRec>:
  match r:
    case W.Got{t, s}:
      get_crec.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# a claim record at the start of s
def get_crec(s: String) -> W.Dec<Sv.CRec>:
  get_crec.go(W.get_nat(s))

def get_disk.claims(js: List<&2, Sv.JRec>, r: W.Dec<List<&2, Sv.CRec>>) -> W.Dec<Sv.Disk>:
  match r:
    case W.Got{cs, s}:
      W.Got{Sv.Parsed{js, cs}, s}
    case W.Bad{}:
      W.Bad{}

def get_disk.jobs(r: W.Dec<List<&2, Sv.JRec>>) -> W.Dec<Sv.Disk>:
  match r:
    case W.Got{js, s}:
      get_disk.claims(js, W.get_list(~Sv.CRec, ~get_crec, s))
    case W.Bad{}:
      W.Bad{}

def get_disk.tag(t: Nat, s: String) -> W.Dec<Sv.Disk>:
  match t:
    case 0n:
      W.Got{Sv.Missing{}, s}
    case 1n:
      W.Got{Sv.Torn{}, s}
    case 2n:
      get_disk.jobs(W.get_list(~Sv.JRec, ~get_jrec, s))
    case 3n+p:
      W.Bad{}

def get_disk(r: W.Dec<Nat>) -> W.Dec<Sv.Disk>:
  match r:
    case W.Got{t, s}:
      get_disk.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_claim.fresh(d: Nat, n: Nat, r: W.Dec<List<&2, String>>) -> W.Dec<Sv.Op>:
  match r:
    case W.Got{xs, s}:
      W.Got{Sv.OClaim{d, n, xs}, s}
    case W.Bad{}:
      W.Bad{}

def get_claim.now(d: Nat, r: W.Dec<Nat>) -> W.Dec<Sv.Op>:
  match r:
    case W.Got{n, s}:
      get_claim.fresh(d, n, W.get_list(~String, ~W.get_str, s))
    case W.Bad{}:
      W.Bad{}

def get_claim(r: W.Dec<Nat>) -> W.Dec<Sv.Op>:
  match r:
    case W.Got{d, s}:
      get_claim.now(d, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_recover(r: W.Dec<List<&2, Nat>>) -> W.Dec<Sv.Op>:
  match r:
    case W.Got{xs, s}:
      W.Got{Sv.ORecover{xs}, s}
    case W.Bad{}:
      W.Bad{}

def get_finish.now(d: String, a: Bool, b: Bool, r: W.Dec<Nat>) -> W.Dec<Sv.Op>:
  match r:
    case W.Got{n, s}:
      W.Got{Sv.OFinish{d, a, b, n}, s}
    case W.Bad{}:
      W.Bad{}

def get_finish.failed(d: String, a: Bool, r: W.Dec<Bool>) -> W.Dec<Sv.Op>:
  match r:
    case W.Got{b, s}:
      get_finish.now(d, a, b, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_finish.ran(d: String, r: W.Dec<Bool>) -> W.Dec<Sv.Op>:
  match r:
    case W.Got{a, s}:
      get_finish.failed(d, a, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_finish(r: W.Dec<String>) -> W.Dec<Sv.Op>:
  match r:
    case W.Got{d, s}:
      get_finish.ran(d, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_cancel(r: W.Dec<Nat>) -> W.Dec<Sv.Op>:
  match r:
    case W.Got{n, s}:
      W.Got{Sv.OCancel{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_resume.now(n: Nat, r: W.Dec<Nat>) -> W.Dec<Sv.Op>:
  match r:
    case W.Got{c, s}:
      W.Got{Sv.OResume{n, c}, s}
    case W.Bad{}:
      W.Bad{}

def get_resume(r: W.Dec<Nat>) -> W.Dec<Sv.Op>:
  match r:
    case W.Got{n, s}:
      get_resume.now(n, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_create.fact(n: Nat, r: W.Dec<CS.Fact>) -> W.Dec<Sv.Op>:
  match r:
    case W.Got{f, s}:
      W.Got{Sv.OCreate{n, f}, s}
    case W.Bad{}:
      W.Bad{}

def get_create(r: W.Dec<Nat>) -> W.Dec<Sv.Op>:
  match r:
    case W.Got{n, s}:
      get_create.fact(n, get_fact(s))
    case W.Bad{}:
      W.Bad{}

def get_op.tag(t: Nat, s: String) -> W.Dec<Sv.Op>:
  match t:
    case 0n:
      get_claim(W.get_nat(s))
    case 1n:
      get_recover(W.get_list(~Nat, ~W.get_nat, s))
    case 2n:
      get_finish(W.get_str(s))
    case 3n:
      get_cancel(W.get_nat(s))
    case 4n:
      get_resume(W.get_nat(s))
    case 5n:
      get_create(W.get_nat(s))
    case 6n+p:
      W.Bad{}

def get_op(r: W.Dec<Nat>) -> W.Dec<Sv.Op>:
  match r:
    case W.Got{t, s}:
      get_op.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_serve.op(me: Nat, k: Sv.Disk, r: W.Dec<Sv.Op>) -> W.Dec<Ev>:
  match r:
    case W.Got{o, s}:
      W.Got{EServe{me, k, o}, s}
    case W.Bad{}:
      W.Bad{}

def get_serve.disk(me: Nat, r: W.Dec<Sv.Disk>) -> W.Dec<Ev>:
  match r:
    case W.Got{k, s}:
      get_serve.op(me, k, get_op(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_serve(r: W.Dec<Nat>) -> W.Dec<Ev>:
  match r:
    case W.Got{me, s}:
      get_serve.disk(me, get_disk(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_end(r: W.Dec<String>) -> W.Dec<Ev>:
  match r:
    case W.Got{d, s}:
      W.Got{EEnd{d}, s}
    case W.Bad{}:
      W.Bad{}

def get_ev.tag(t: Nat, s: String) -> W.Dec<Ev>:
  match t:
    case 0n:
      get_serve(W.get_nat(s))
    case 1n:
      get_end(W.get_str(s))
    case 2n+p:
      W.Bad{}

# the event at the start of s
def get_ev(r: W.Dec<Nat>) -> W.Dec<Ev>:
  match r:
    case W.Got{t, s}:
      get_ev.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# Encoding
# --------

def put_status(st: Cr.Status, rest: String) -> String:
  match st:
    case Cr.Active{}:
      W.put_nat(0n, rest)
    case Cr.Paused{}:
      W.put_nat(1n, rest)
    case Cr.Finished{}:
      W.put_nat(2n, rest)
    case Cr.Cancelled{}:
      W.put_nat(3n, rest)

def put_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{n}:
      W.put_nat(1n, W.put_nat(n, rest))

def put_next(n: CS.Next, rest: String) -> String:
  match n:
    case CS.NNone{}:
      W.put_nat(0n, rest)
    case CS.NAt{x}:
      W.put_nat(1n, W.put_nat(x, rest))
    case CS.NRoll{}:
      W.put_nat(2n, rest)

def put_took(t: CS.Took, rest: String) -> String:
  match t:
    case CS.Keep{}:
      W.put_nat(0n, rest)
    case CS.Roll{n}:
      W.put_nat(1n, put_next(n, rest))
    case CS.Claimed{n}:
      W.put_nat(2n, put_next(n, rest))

def put_back(b: CS.Back, rest: String) -> String:
  match b:
    case CS.Kept{}:
      W.put_nat(0n, rest)
    case CS.Interrupted{st, m}:
      W.put_nat(1n, put_status(st, put_mnat(m, rest)))

def put_fin(x: CS.Fin, rest: String) -> String:
  match x:
    case CS.Untouched{}:
      W.put_nat(0n, rest)
    case CS.Ran{st, n, k}:
      W.put_nat(1n, put_status(st, put_next(n, W.put_nat(k, rest))))
    case CS.Skipped{st, n, k}:
      W.put_nat(2n, put_status(st, put_next(n, W.put_nat(k, rest))))

def put_cut(x: CS.Cut, rest: String) -> String:
  match x:
    case CS.Same{}:
      W.put_nat(0n, rest)
    case CS.Cut{st, m}:
      W.put_nat(1n, put_status(st, put_mnat(m, rest)))

def put_again(x: CS.Again, rest: String) -> String:
  match x:
    case CS.Resumed{st, n, k}:
      W.put_nat(0n, put_status(st, put_next(n, W.put_nat(k, rest))))
    case CS.Ended{}:
      W.put_nat(1n, rest)
    case CS.NotRecurring{}:
      W.put_nat(2n, rest)

def put_jout(o: Sv.JOut, rest: String) -> String:
  match o:
    case Sv.JSame{}:
      W.put_nat(0n, rest)
    case Sv.JTook{t}:
      W.put_nat(1n, put_took(t, rest))
    case Sv.JBack{b}:
      W.put_nat(2n, put_back(b, rest))
    case Sv.JFin{x}:
      W.put_nat(3n, put_fin(x, rest))
    case Sv.JCut{x}:
      W.put_nat(4n, put_cut(x, rest))
    case Sv.JAgain{x}:
      W.put_nat(5n, put_again(x, rest))
    case Sv.JNew{}:
      W.put_nat(6n, rest)

def put_cout(o: Sv.COut, rest: String) -> String:
  match o:
    case Sv.CKeep{}:
      W.put_nat(0n, rest)
    case Sv.CDrop{}:
      W.put_nat(1n, rest)
    case Sv.CNew{k, d}:
      W.put_nat(2n, W.put_nat(k, W.put_str(d, rest)))

def put_out(o: Sv.Out) -> String:
  match o:
    case Sv.Out{a, w, js, cs}:
      W.put_bool(a, W.put_bool(w, W.put_list(~Sv.JOut, ~put_jout, js, W.put_list(~Sv.COut, ~put_cout, cs, ""))))

# The stepper
# -----------

def malformed() -> String:
  W.err("cron_serve: malformed event")

def open.fin(empty: Bool) -> St & String:
  match empty:
    case True{}:
      (Open{Nil{}}, "")
    case False{}:
      (Shut{}, W.err("cron_serve: malformed open"))

# open: no runs
def open(input: String) -> St & String:
  open.fin(String.is_empty(input))

def step.put(r: Sv.Served) -> St & String:
  match r:
    case Sv.Served{runs, o}:
      (Open{runs}, put_out(o))

def step.run(+runs: List<&2, String>, e: Ev) -> St & String:
  match e:
    case EServe{me, k, o}:
      step.put(Sv.serve(runs, me, k, o))
    case EEnd{d}:
      (Open{Sv.end(d, runs)}, "")

def step.fin(done: Bool, +runs: List<&2, String>, e: Ev) -> St & String:
  match done:
    case True{}:
      step.run(runs, e)
    case False{}:
      (Open{runs}, malformed())

def step.go(+runs: List<&2, String>, r: W.Dec<Ev>) -> St & String:
  match r:
    case W.Got{e, s}:
      step.fin(W.end(s), runs, e)
    case W.Bad{}:
      (Open{runs}, malformed())

# step: one update, or the end of one run
def step(st: St, input: String) -> St & String:
  match st:
    case Open{+runs}:
      step.go(runs, get_ev(W.get_nat(input)))
    case Shut{}:
      (Shut{}, W.err("cron_serve: the open was refused"))

# The due question
# ----------------

def ffi.malformed() -> String:
  W.err("cron_serve: malformed question")

def ffi.end(whole: Bool, f: CS.Fact, +now: Nat) -> String:
  match whole:
    case True{}:
      W.put_bool(Sv.due(f, now), "")
    case False{}:
      ffi.malformed()

def ffi.fact(+now: Nat, r: W.Dec<CS.Fact>) -> String:
  match r:
    case W.Got{f, s}:
      ffi.end(W.end(s), f, now)
    case W.Bad{}:
      ffi.malformed()

def ffi.go(r: W.Dec<Nat>) -> String:
  match r:
    case W.Got{n, s}:
      ffi.fact(n, get_fact(s))
    case W.Bad{}:
      ffi.malformed()

# call: whether a job is due at now (Sv.due)
def ffi(input: String) -> String:
  ffi.go(W.get_nat(input))
