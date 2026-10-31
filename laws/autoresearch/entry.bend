# eukhe: the laws of area autoresearch: the stepper entry
# bend/ffi_autoresearch.bend (entry 430 of the compiled core), bytes in
# and out. The laws spell requests and replies with the wire primitives
# (bend/wire.bend, pinned by laws/wire.bend) in the grammar of the
# entry's header; the model's answers are those of
# laws/autoresearch/model.bend.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_autoresearch.bend as FAr
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/line.bend as ArL
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/step.bend as ArP
import ../../bend/autoresearch/stats.bend as ArT
import ../base.bend as LawsBase
import ./model.bend as ArM

# Requests
# --------

def ar_w_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))

def ar_w_mstr(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{t}:
      Wr.put_nat(1n, Wr.put_str(t, rest))

def ar_w_dir(d: ArS.Dir) -> Nat:
  match d:
    case ArS.Lower{}:
      0n
    case ArS.Higher{}:
      1n

def ar_w_mode(m: ArS.Mode) -> Nat:
  match m:
    case ArS.On{}:
      0n
    case ArS.Off{}:
      1n

def ar_w_status(t: ArS.Status) -> Nat:
  match t:
    case ArS.Keep{}:
      0n
    case ArS.Discard{}:
      1n
    case ArS.Crash{}:
      2n
    case ArS.Checks{}:
      3n

def ar_w_cfg(c: ArS.Cfg, rest: String) -> String:
  match c:
    case ArS.Cfg{a, b, m, u, d, sec, scope, off, max}:
      Wr.put_str(a, Wr.put_str(b, Wr.put_str(m, Wr.put_str(u, Wr.put_nat(ar_w_dir(d), LawsBase.wire_spell_strs(sec, LawsBase.wire_spell_strs(scope, LawsBase.wire_spell_strs(off, ar_w_mnat(max, rest)))))))))

# the bytes the host sends for an event
def ar_w_ev(e: ArS.Ev) -> String:
  match e:
    case ArS.Init{c, fresh, harness}:
      Wr.put_nat(0n, ar_w_cfg(c, Wr.put_bool(fresh, Wr.put_bool(harness, ""))))
    case ArS.Begin{n}:
      Wr.put_nat(1n, Wr.put_nat(n, ""))
    case ArS.Line{t}:
      Wr.put_nat(2n, Wr.put_str(t, ""))
    case ArS.Finish{neg, code, timeout}:
      Wr.put_nat(3n, Wr.put_bool(neg, Wr.put_nat(code, Wr.put_bool(timeout, ""))))
    case ArS.Log{st, desc, why, devs}:
      Wr.put_nat(4n, Wr.put_nat(ar_w_status(st), Wr.put_str(desc, ar_w_mstr(why, Wr.put_nat(devs, "")))))
    case ArS.Flag{n, reason}:
      Wr.put_nat(5n, Wr.put_nat(n, Wr.put_str(reason, "")))
    case ArS.SetMode{m}:
      Wr.put_nat(6n, Wr.put_nat(ar_w_mode(m), ""))

# the bytes the host sends for a request
def ar_w_req(q: FAr.Q) -> String:
  match q:
    case FAr.QEv{e}:
      ar_w_ev(e)
    case FAr.QSnap{}:
      Wr.put_nat(7n, "")

def ar_fits_str(+t: String) -> Bool:
  LawsBase.wire_fits(String.length(t))

def ar_fits_mnat(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+n}:
      LawsBase.wire_fits(n)

def ar_fits_mstr(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+t}:
      ar_fits_str(t)

def ar_fits_cfg(c: ArS.Cfg) -> Bool:
  match c:
    case ArS.Cfg{+a, +b, +m, +u, d, +sec, +scope, +off, max}:
      Bool.and(Bool.and(ar_fits_str(a), Bool.and(ar_fits_str(b), Bool.and(ar_fits_str(m), ar_fits_str(u)))), Bool.and(Bool.and(LawsBase.wire_strs_fit(sec), Bool.and(LawsBase.wire_strs_fit(scope), LawsBase.wire_strs_fit(off))), ar_fits_mnat(max)))

# every Nat and length of the event fits the wire (the host writes none
# past it: its numbers are u32, its strings at most 8 Mi chars)
def ar_fits_ev(e: ArS.Ev) -> Bool:
  match e:
    case ArS.Init{c, fresh, harness}:
      ar_fits_cfg(c)
    case ArS.Begin{+n}:
      LawsBase.wire_fits(n)
    case ArS.Line{+t}:
      ar_fits_str(t)
    case ArS.Finish{neg, +code, timeout}:
      LawsBase.wire_fits(code)
    case ArS.Log{st, +desc, why, +devs}:
      Bool.and(ar_fits_str(desc), Bool.and(ar_fits_mstr(why), LawsBase.wire_fits(devs)))
    case ArS.Flag{+n, +reason}:
      Bool.and(LawsBase.wire_fits(n), ar_fits_str(reason))
    case ArS.SetMode{m}:
      True{}

def ar_fits(q: FAr.Q) -> Bool:
  match q:
    case FAr.QEv{e}:
      ar_fits_ev(e)
    case FAr.QSnap{}:
      True{}

# Replies
# -------

def ar_w_eff(e: ArS.Eff) -> Nat:
  match e:
    case ArS.Nothing{}:
      0n
    case ArS.Commit{}:
      1n
    case ArS.Reset{}:
      2n

# an event's reply: 0, the effect and the stop; or 1, the refusal
def ar_w_res(r: ArS.Res) -> String:
  match r:
    case ArS.Took{s2, e, stop}:
      Wr.put_nat(0n, Wr.put_nat(ar_w_eff(e), Wr.put_bool(stop, "")))
    case ArS.Refuse{t}:
      Wr.put_nat(1n, Wr.put_str(t, ""))

def ar_w_mcfg(m: Maybe<&2, ArS.Cfg>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{c}:
      Wr.put_nat(1n, ar_w_cfg(c, rest))

def ar_w_dec(d: ArD.Dec, rest: String) -> String:
  match d:
    case ArD.Dec{neg, ds, scale}:
      Wr.put_bool(neg, LawsBase.wire_spell_nats(ds, Wr.put_nat(scale, rest)))

def ar_w_mdec(m: Maybe<&2, ArD.Dec>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{d}:
      Wr.put_nat(1n, ar_w_dec(d, rest))

def ar_w_kvs.items(kvs: List<&2, ArL.Kv>, rest: String) -> String:
  match kvs:
    case Nil{}:
      rest
    case ArL.Kv{n, v} <> t:
      Wr.put_str(n, ar_w_dec(v, ar_w_kvs.items(t, rest)))

def ar_w_kvs(+kvs: List<&2, ArL.Kv>, rest: String) -> String:
  Wr.put_nat(List.length(&2, ArL.Kv, kvs), ar_w_kvs.items(kvs, rest))

def ar_w_mstatus(m: Maybe<&2, ArS.Status>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{t}:
      Wr.put_nat(1n, Wr.put_nat(ar_w_status(t), rest))

def ar_w_row(abandoned: Bool, r: ArS.Row, rest: String) -> String:
  match r:
    case ArS.Row{id, sg, st, m, ms, ps, fn, fl, desc}:
      Wr.put_nat(id, Wr.put_nat(sg, ar_w_mstatus(st, Wr.put_bool(abandoned, Wr.put_bool(fn, ar_w_mdec(m, ar_w_kvs(ms, Wr.put_bool(ps, Wr.put_bool(fl, Wr.put_str(desc, rest))))))))))

# an ended row is abandoned when it has no status
def ar_ended_abandoned(r: ArS.Row) -> Bool:
  match r:
    case ArS.Row{id, sg, st, m, ms, ps, fn, fl, desc}:
      Bool.not(ArS.has(st))

def ar_w_rows.items(rs: List<&2, ArS.Row>, rest: String) -> String:
  match rs:
    case Nil{}:
      rest
    case +r <> t:
      ar_w_row(ar_ended_abandoned(r), r, ar_w_rows.items(t, rest))

def ar_mpending(p: Maybe<&2, ArS.Pend>) -> Maybe<&2, Nat>:
  match p:
    case None{}:
      None{}
    case Some{ArS.Pend{id, kvs, fin}}:
      Some{id}

# every run of s, oldest first (the ended ones, then the pending one)
def ar_w_rows(+s: ArS.St, rest: String) -> String:
  match s:
    case ArS.St{+c, +seg, mode, +runs, pend}:
      match pend:
        case None{}:
          Wr.put_nat(ArM.ar_count_runs(runs), ar_w_rows.items(runs, rest))
        case Some{p}:
          Wr.put_nat(1n+ArM.ar_count_runs(runs), ar_w_rows.items(runs, ar_w_row(False{}, ArM.ar_row(c, seg, p, None{}, ""), rest)))

# a snapshot of s: configuration, segment, mode, runs, pending run,
# baseline, best, logged count, confidence
def ar_w_snap(+s: ArS.St) -> String:
  ar_w_mcfg(ArM.ar_cfg(s), Wr.put_nat(ArM.ar_seg(s), Wr.put_nat(ar_w_mode(ArM.ar_mode(s)), ar_w_rows(s, ar_w_mnat(ar_mpending(ArM.ar_pend(s)), ar_w_mdec(ArS.St.baseline(s), ar_w_mdec(ArS.St.best(s), Wr.put_nat(ArS.St.logged(s), ar_w_mnat(ArT.St.confidence(s), "")))))))))

# the model's state after a request, and its reply
def ar_next(+s: ArS.St, q: FAr.Q) -> ArS.St:
  match q:
    case FAr.QEv{e}:
      ArM.ar_after(ArP.step(s, e), s)
    case FAr.QSnap{}:
      s

def ar_reply(+s: ArS.St, q: FAr.Q) -> String:
  match q:
    case FAr.QEv{e}:
      ar_w_res(ArP.step(s, e))
    case FAr.QSnap{}:
      ar_w_snap(s)

def ar_malformed() -> String:
  Wr.err("autoresearch: malformed request")

# Laws
# ----

# LAW autoresearch_entry_answers: in every state, every request the host
# spells (an event or the snapshot, every Nat and length within the
# wire) answers what the model answers: an event moves the state as the
# model's step does (a refusal keeps it) and answers its effect and stop,
# or its refusal; the snapshot moves nothing and shows the configuration,
# segment, mode, every run (ended ones oldest first, abandoned when they
# have no status, then the pending one), the pending id, baseline, best,
# logged count and confidence
# EXCLUDES: fields read in another order, a tag misread, a refusal that
# moves the state, a reply other than the model's, a snapshot that moves
# the state or drops a run
law autoresearch_entry_answers:
  for +s: ArS.St
  for +q: FAr.Q
  for fits: {ar_fits(q) == True{} : Bool}
  {FAr.step(FAr.Live{s}, ar_w_req(q)) == (FAr.Live{ar_next(s, q)}, ar_reply(s, q)) : FAr.St & String}

def ar_answered(+s: ArS.St, +i: String) -> Type:
  {FAr.step(FAr.Live{s}, i) == (FAr.Live{s}, ar_malformed()) : FAr.St & String} | (&q: FAr.Q -> ({ar_w_req(q) == i : String} & {ar_fits(q) == True{} : Bool}))

# LAW autoresearch_entry_exact: in every state, every input is either
# answered with exactly `E autoresearch: malformed request`, keeping the
# state, or is the spelling of a request that fits the wire (which
# autoresearch_entry_answers then answers)
# EXCLUDES: garbage read as an event (a guessed init, keep or flag),
# input left over ignored, a state moved by garbage, another error text
law autoresearch_entry_exact:
  for +s: ArS.St
  for +i: String
  ar_answered(s, i)

# LAW autoresearch_entry_open: the open with no input opens the empty
# state (no experiment, no run, mode Off) and answers T
# EXCLUDES: an open that starts with a stale experiment or run
law autoresearch_entry_open:
  {FAr.open("") == (FAr.Live{ArS.St.empty()}, "T") : FAr.St & String}

# LAW autoresearch_entry_open_malformed_exact: an open with any input
# opens the refused state and answers exactly `E autoresearch: malformed
# open`
# EXCLUDES: a default state opened for garbage
law autoresearch_entry_open_malformed_exact:
  for +c: Char
  for +t: String
  {FAr.open(SCon{c, t}) == (FAr.Refused{}, Wr.err("autoresearch: malformed open")) : FAr.St & String}

# LAW autoresearch_entry_shut: the refused state answers every step with
# exactly `E autoresearch: the open was refused`
# EXCLUDES: a refused stepper that takes an event
law autoresearch_entry_shut:
  for +i: String
  {FAr.step(FAr.Refused{}, i) == (FAr.Refused{}, Wr.err("autoresearch: the open was refused")) : FAr.St & String}

def ar_state(r: FAr.St & String) -> FAr.St:
  (st, reply) = r
  st

def ar_reply_of(r: FAr.St & String) -> String:
  (st, reply) = r
  reply

# the stepper's replies to the requests qs, spelled, in order
def ar_replies(qs: List<&2, FAr.Q>, +st: FAr.St) -> List<&2, String>:
  match qs:
    case Nil{}:
      Nil{}
    case +q <> rest:
      ar_reply_of(FAr.step(st, ar_w_req(q))) <> ar_replies(rest, ar_state(FAr.step(st, ar_w_req(q))))

# the stepper after the requests qs
def ar_feed(qs: List<&2, FAr.Q>, st: FAr.St) -> FAr.St:
  match qs:
    case Nil{}:
      st
    case q <> rest:
      ar_feed(rest, ar_state(FAr.step(st, ar_w_req(q))))

# the model's replies to qs from s, in order
def ar_spec(qs: List<&2, FAr.Q>, +s: ArS.St) -> List<&2, String>:
  match qs:
    case Nil{}:
      Nil{}
    case +q <> rest:
      ar_reply(s, q) <> ar_spec(rest, ar_next(s, q))

# the model's state after qs from s
def ar_fold(qs: List<&2, FAr.Q>, +s: ArS.St) -> ArS.St:
  match qs:
    case Nil{}:
      s
    case +q <> rest:
      ar_fold(rest, ar_next(s, q))

def ar_all_fit(qs: List<&2, FAr.Q>) -> Bool:
  match qs:
    case Nil{}:
      True{}
    case q <> rest:
      Bool.and(ar_fits(q), ar_all_fit(rest))

# LAW autoresearch_step_is_model: the stepper opened and sent any
# requests the host spells, in any order, answers each as the model run
# from the empty state answers it, and ends in the state the model's
# steps fold to (so a replay of the host's event log rebuilds the state)
# EXCLUDES: a stepper whose state drifts from the model's after some
# order of events, a replay that rebuilds another state
law autoresearch_step_is_model:
  for +qs: List<&2, FAr.Q>
  for fits: {ar_all_fit(qs) == True{} : Bool}
  {ar_replies(qs, ar_state(FAr.open(""))) == ar_spec(qs, ArS.St.empty()) : List<&2, String>} & {ar_feed(qs, ar_state(FAr.open(""))) == FAr.Live{ar_fold(qs, ArS.St.empty())} : FAr.St}

# LAW autoresearch_entry_example: anchor: the bytes the host sends and the
# replies: an open; a start refused before init; an init (metric ms,
# lower, max 2, no lists); start 1; a METRIC line; its end; a keep
# (commit); a snapshot; garbage; input left over; a step of the refused
# state
# EXCLUDES: an entry that answers other bytes than the grammar's
law autoresearch_entry_example:
  {ar_reply_of(FAr.open("")) == "T" : String} & {ar_replies([FAr.QEv{ArS.Begin{1n}}, FAr.QEv{ArS.Init{ArS.Cfg{"n", "g", "ms", "", ArS.Lower{}, [], [], [], Some{2n}}, False{}, True{}}}, FAr.QEv{ArS.Begin{1n}}, FAr.QEv{ArS.Line{"METRIC ms=1.5"}}, FAr.QEv{ArS.Finish{False{}, 0n, False{}}}, FAr.QEv{ArS.Log{ArS.Keep{}, "d", None{}, 0n}}, FAr.QSnap{}], ar_state(FAr.open(""))) == ["1,63,autoresearch: no experiment yet; call autoresearch.init() first", "0,0,F", "0,0,F", "0,0,F", "0,0,F", "0,1,F", "1,1,n1,g2,ms0,0,0,0,0,1,2,0,0,1,1,0,1,0,FT1,F2,1,5,1,0,TF1,d0,1,F2,1,5,1,1,F2,1,5,1,1,0,"] : List<&2, String>} & {[ar_reply_of(FAr.step(ar_state(FAr.open("")), "8,")), ar_reply_of(FAr.step(ar_state(FAr.open("")), "7,x")), ar_reply_of(FAr.step(FAr.Refused{}, "7,"))] == [ar_malformed(), ar_malformed(), Wr.err("autoresearch: the open was refused")] : List<&2, String>}
