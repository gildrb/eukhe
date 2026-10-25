# eukhe: the laws of area work

import Base
import ../bend/ffi_work.bend as FW
import ../bend/progress.bend as Pr
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- the work ledger and the prior check (bend/ffi_work.bend, id 83) ----
#
# LAWS: the entry of the compiled Bend core for the session's work: a
# stepper, the work ledger the host keeps per conversation
# (crates/eukhe-core/src/durable/children/work.rs `WorkLedger`, read by the
# subagent watch in eukhe-daemon worker/run_outcome.rs and by the goal
# loop in durable/goals/hooks.rs), and a call, the prior check the goal's
# progress check compares with (durable/goals/state.rs; the check itself is
# bend/ffi_progress.bend, laws/progress.bend). Rust writes the events and
# requests and fingerprints bytes: a tool call's name and arguments, a
# result's tool name, content and error flag, the key of a call id, a
# progress note's text. The entry decides the rest. The events below are
# spelled from the primitives of bend/wire.bend, never with the entry's own
# encoders; the readers are the laws' own. Every input is free: any
# fingerprints, keys, ids, entries, views, pages, notes and checks, in any
# order. The model is bend/progress.bend (`next`, `compared`).
#
# W1: an act is a tool result with the call of its id that waited for it,
#     or a progress note; text, thinking, user and system messages are no
#     act, and a call is none until its result.
# W2: a result's call is the newest call of its id among the blocks read
#     since the ledger started, unless a result of that id came after that
#     call (each call waits for one result).
# W3: acts that differ in their call, in their result, or in having a call
#     at all are different acts; two notes are the same act exactly when
#     their fingerprints are, and a note is never a result's act.
# W4: the work the ledger answers is the number of distinct acts it read
#     since it started (`Pr.work` of their numbers `Pr.act`, `Pr.note`):
#     the laws of the goal's check and of the subagent watch in
#     laws/progress.bend hold for it.
# W5: a view that no longer holds the last entry read at its place starts
#     the ledger over (the answer Again: the host sends the view from its
#     start); else the ledger reads the view's entries from that place on,
#     and counts them read. A page reads only the entries newer than the
#     last entry read.
# W6: the stepper reads exactly the events Rust spells and answers the
#     ledger's answer; any other input answers exactly the error form
#     "work: malformed event" and keeps the ledger; an open with input is
#     refused, and a refused open answers every step with the error form.
# W7: the goal's check compares with the last check only when that one was
#     of the same run and the same goal; the call reads exactly the
#     requests Rust spells, and answers exactly the error form "work:
#     malformed request" to any other input.

# Spec helpers: the prior check compared with (the call)
# ------------------------------------------------------

# the request Rust writes: the last check stored, if any
def pe_spell_req(m: Maybe<&2, Pr.Last>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{x}:
      match x:
        case Pr.Last{r, g, s, w}:
          Wr.put_nat(1n, Wr.put_bool(r, Wr.put_bool(g, Wr.put_nat(s, Wr.put_nat(w, "")))))

def pe_answer.goal(g: Bool, +s: Nat, +w: Nat) -> String:
  match g:
    case True{}:
      Wr.put_nat(1n, Wr.put_nat(s, Wr.put_nat(w, "")))
    case False{}:
      Wr.put_nat(0n, "")

# the reply: the last check's stalls and work when it was of the same run
# and the same goal, else none (W7)
def pe_answer(m: Maybe<&2, Pr.Last>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{x}:
      match x:
        case Pr.Last{r, g, s, w}:
          match r:
            case True{}:
              pe_answer.goal(g, s, w)
            case False{}:
              Wr.put_nat(0n, "")

def pe_fits(m: Maybe<&2, Pr.Last>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      match x:
        case Pr.Last{r, g, s, w}:
          Bool.and(LawsBase.wire_fits(s), LawsBase.wire_fits(w))

def pe_read.work(r: Bool, g: Bool, +n: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Pr.Last>>:
  match d:
    case Wr.Got{w, s}:
      Wr.Got{Some{Pr.Last{r, g, n, w}}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def pe_read.stalls(r: Bool, g: Bool, d: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Pr.Last>>:
  match d:
    case Wr.Got{+n, s}:
      pe_read.work(r, g, n, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def pe_read.goal(r: Bool, d: Wr.Dec<Bool>) -> Wr.Dec<Maybe<&2, Pr.Last>>:
  match d:
    case Wr.Got{g, s}:
      pe_read.stalls(r, g, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def pe_read.run(d: Wr.Dec<Bool>) -> Wr.Dec<Maybe<&2, Pr.Last>>:
  match d:
    case Wr.Got{r, s}:
      pe_read.goal(r, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def pe_read.tag(n: Nat, s: String) -> Wr.Dec<Maybe<&2, Pr.Last>>:
  match n:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      pe_read.run(Wr.get_bool(s))
    case 2n+q:
      Wr.Bad{}

def pe_read.go(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Pr.Last>>:
  match r:
    case Wr.Got{n, s}:
      pe_read.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

def pe_read.end(whole: Bool, m: Maybe<&2, Pr.Last>) -> Maybe<&2, Maybe<&2, Pr.Last>>:
  match whole:
    case True{}:
      Some{m}
    case False{}:
      None{}

def pe_read.whole(r: Wr.Dec<Maybe<&2, Pr.Last>>) -> Maybe<&2, Maybe<&2, Pr.Last>>:
  match r:
    case Wr.Got{m, s}:
      pe_read.end(Wr.end(s), m)
    case Wr.Bad{}:
      None{}

# the request s is, when s is exactly one request
def pe_read(s: String) -> Maybe<&2, Maybe<&2, Pr.Last>>:
  pe_read.whole(pe_read.go(Wr.get_nat(s)))

# Spec helpers: the work ledger (the stepper)
# -------------------------------------------

def wk_pick(b: Bool, x: Maybe<&2, Nat>, y: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      x
    case False{}:
      y

# the fingerprint of the call of key k that still waits after the blocks
# past (newest first): the newest block of key k, when it is a call (W2)
def wk_look(past: List<&2, Pr.Blk>, +k: Nat) -> Maybe<&2, Nat>:
  match past:
    case Nil{}:
      None{}
    case b <> t:
      match b:
        case Pr.Call{j, f}:
          wk_pick(Nat.is_eq(j, k), Some{f}, wk_look(t, k))
        case Pr.Res{j, x}:
          wk_pick(Nat.is_eq(j, k), None{}, wk_look(t, k))
        case Pr.Txt{}:
          wk_look(t, k)
        case Pr.Think{}:
          wk_look(t, k)
        case Pr.User{}:
          wk_look(t, k)
        case Pr.Sys{}:
          wk_look(t, k)

# the act a block adds after the blocks past: a result's, with its call
# (W1)
def wk_new(+past: List<&2, Pr.Blk>, b: Pr.Blk) -> List<&2, Pr.Act>:
  match b:
    case Pr.Call{k, f}:
      Nil{}
    case Pr.Res{k, x}:
      [Pr.ARes{wk_look(past, k), x}]
    case Pr.Txt{}:
      Nil{}
    case Pr.Think{}:
      Nil{}
    case Pr.User{}:
      Nil{}
    case Pr.Sys{}:
      Nil{}

# the spec's ledger: every act since it started (oldest first, repeats
# kept), the blocks read since then (newest first), the entries of the view
# read since then, the last entry read
type wk.S is Data:
  wk.S{acts: List<&2, Pr.Act>, past: List<&2, Pr.Blk>, read: Nat, last: Maybe<&2, Nat>}

def wk_start() -> wk.S:
  wk.S{Nil{}, Nil{}, 0n, None{}}

def wk_blk(st: wk.S, +b: Pr.Blk) -> wk.S:
  match st:
    case wk.S{a, +p, r, z}:
      wk.S{List.append(&2, Pr.Act, a, wk_new(p, b)), b <> p, r, z}

def wk_blks(bs: List<&2, Pr.Blk>, st: wk.S) -> wk.S:
  match bs:
    case Nil{}:
      st
    case b <> t:
      wk_blks(t, wk_blk(st, b))

def wk_ent(st: wk.S, e: Pr.Ent) -> wk.S:
  match st:
    case wk.S{a, p, r, z}:
      match e:
        case Pr.Ent{i, bs}:
          wk_blks(bs, wk.S{a, p, r, Some{i}})

def wk_ents(es: List<&2, Pr.Ent>, st: wk.S) -> wk.S:
  match es:
    case Nil{}:
      st
    case e <> t:
      wk_ents(t, wk_ent(st, e))

# an entry of id i comes after the last entry read
def wk_after(z: Maybe<&2, Nat>, +i: Nat) -> Bool:
  match z:
    case None{}:
      True{}
    case Some{x}:
      Nat.is_lt(x, i)

def wk_id(e: Pr.Ent) -> Nat:
  match e:
    case Pr.Ent{i, bs}:
      i

def wk_last(st: wk.S) -> Maybe<&2, Nat>:
  match st:
    case wk.S{a, p, r, z}:
      z

def wk_page.at(b: Bool, st: wk.S, e: Pr.Ent) -> wk.S:
  match b:
    case True{}:
      wk_ent(st, e)
    case False{}:
      st

# a page reads the entries that come after the last entry read (W5)
def wk_page(es: List<&2, Pr.Ent>, st: wk.S) -> wk.S:
  match es:
    case Nil{}:
      st
    case +e <> t:
      +s = st
      wk_page(t, wk_page.at(wk_after(wk_last(s), wk_id(e)), s, e))

def wk_same(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Bool:
  match a:
    case None{}:
      match b:
        case None{}:
          True{}
        case Some{y}:
          False{}
    case Some{x}:
      match b:
        case None{}:
          False{}
        case Some{y}:
          Nat.is_eq(x, y)

# the view still holds what the ledger read: it read nothing of the view,
# or the view's entry at the place of the last one read is that entry (W5)
def wk_holds(r: Nat, at: Maybe<&2, Nat>, z: Maybe<&2, Nat>) -> Bool:
  Bool.or(Nat.is_eq(r, 0n), wk_same(at, z))

def wk_spell_at(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_nat(x, rest))

# an answer of the ledger as Rust reads it
def wk_spell_out(o: Pr.Out) -> String:
  match o:
    case Pr.Read{w, r, z}:
      Wr.put_nat(0n, Wr.put_nat(w, Wr.put_nat(r, wk_spell_at(z, ""))))
    case Pr.Again{}:
      Wr.put_nat(1n, "")

# the number of an act (W3)
def wk_num(x: Pr.Act) -> Nat:
  match x:
    case Pr.ARes{m, r}:
      Pr.act(m, r)
    case Pr.ANote{f}:
      Pr.note(f)

def wk_nums(xs: List<&2, Pr.Act>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      wk_num(x) <> wk_nums(t)

# the answer of the spec's ledger: its work is the number of distinct acts
# among those it read (W4)
def wk_done(st: wk.S) -> wk.S & String:
  match st:
    case wk.S{+a, p, +r, +z}:
      (wk.S{a, p, r, z}, wk_spell_out(Pr.Read{Pr.work(wk_nums(a)), r, z}))

def wk_seen(st: wk.S, n: Nat) -> wk.S:
  match st:
    case wk.S{a, p, r, z}:
      wk.S{a, p, Nat.add(r, n), z}

def wk_view(b: Bool, +es: List<&2, Pr.Ent>, st: wk.S) -> wk.S & String:
  match b:
    case True{}:
      wk_done(wk_seen(wk_ents(es, st), List.length(&2, Pr.Ent, es)))
    case False{}:
      (wk_start(), wk_spell_out(Pr.Again{}))

# the spec's ledger after the event e, and its reply
def wk_next(st: wk.S, e: Pr.Ev) -> wk.S & String:
  match st:
    case wk.S{a, p, +r, +z}:
      match e:
        case Pr.View{at, es}:
          wk_view(wk_holds(r, at, z), es, wk.S{a, p, r, z})
        case Pr.Page{es}:
          wk_done(wk_page(es, wk.S{a, p, r, z}))
        case Pr.Note{x}:
          wk_done(wk.S{List.append(&2, Pr.Act, a, [Pr.ANote{x}]), p, r, z})

# the reply of r, then the spec's replies to evs from the state of r
def wk_spec(evs: List<&2, Pr.Ev>, r: wk.S & String) -> List<&2, String>:
  match evs:
    case Nil{}:
      (st, out) = r
      [out]
    case e <> t:
      (st, out) = r
      out <> wk_spec(t, wk_next(st, e))

# The wire of the ledger (spellers over the primitives of bend/wire.bend)
# ------------------------------------------------------------------------

def wk_spell_blk(b: Pr.Blk, rest: String) -> String:
  match b:
    case Pr.Call{k, f}:
      Wr.put_nat(0n, Wr.put_nat(k, Wr.put_nat(f, rest)))
    case Pr.Res{k, f}:
      Wr.put_nat(1n, Wr.put_nat(k, Wr.put_nat(f, rest)))
    case Pr.Txt{}:
      Wr.put_nat(2n, rest)
    case Pr.Think{}:
      Wr.put_nat(3n, rest)
    case Pr.User{}:
      Wr.put_nat(4n, rest)
    case Pr.Sys{}:
      Wr.put_nat(5n, rest)

def wk_spell_ent(e: Pr.Ent, rest: String) -> String:
  match e:
    case Pr.Ent{i, bs}:
      Wr.put_nat(i, Wr.put_list(~Pr.Blk, ~wk_spell_blk, bs, rest))

# an event as Rust writes it
def wk_spell_ev(e: Pr.Ev, rest: String) -> String:
  match e:
    case Pr.View{at, es}:
      Wr.put_nat(0n, wk_spell_at(at, Wr.put_list(~Pr.Ent, ~wk_spell_ent, es, rest)))
    case Pr.Page{es}:
      Wr.put_nat(1n, Wr.put_list(~Pr.Ent, ~wk_spell_ent, es, rest))
    case Pr.Note{x}:
      Wr.put_nat(2n, Wr.put_nat(x, rest))

# the stepper's state and reply after an answer of the ledger
def wk_spell_step(r: Pr.Led & Pr.Out) -> FW.St & String:
  (l, o) = r
  (FW.Live{l}, wk_spell_out(o))

def wk_blk_fits(b: Pr.Blk) -> Bool:
  match b:
    case Pr.Call{k, f}:
      Bool.and(LawsBase.wire_fits(k), LawsBase.wire_fits(f))
    case Pr.Res{k, f}:
      Bool.and(LawsBase.wire_fits(k), LawsBase.wire_fits(f))
    case Pr.Txt{}:
      True{}
    case Pr.Think{}:
      True{}
    case Pr.User{}:
      True{}
    case Pr.Sys{}:
      True{}

def wk_blks_fit(bs: List<&2, Pr.Blk>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case b <> t:
      Bool.and(wk_blk_fits(b), wk_blks_fit(t))

def wk_ent_fits(e: Pr.Ent) -> Bool:
  match e:
    case Pr.Ent{i, +bs}:
      Bool.and(LawsBase.wire_fits(i), Bool.and(LawsBase.wire_fits(List.length(&2, Pr.Blk, bs)), wk_blks_fit(bs)))

def wk_ents_fit(es: List<&2, Pr.Ent>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> t:
      Bool.and(wk_ent_fits(e), wk_ents_fit(t))

# every number, count and list length of an event fits the wire
def wk_ev_fits(e: Pr.Ev) -> Bool:
  match e:
    case Pr.View{at, +es}:
      Bool.and(LawsBase.core_mfits(at), Bool.and(LawsBase.wire_fits(List.length(&2, Pr.Ent, es)), wk_ents_fit(es)))
    case Pr.Page{+es}:
      Bool.and(LawsBase.wire_fits(List.length(&2, Pr.Ent, es)), wk_ents_fit(es))
    case Pr.Note{x}:
      LawsBase.wire_fits(x)

def wk_evs_fit(evs: List<&2, Pr.Ev>) -> Bool:
  match evs:
    case Nil{}:
      True{}
    case e <> t:
      Bool.and(wk_ev_fits(e), wk_evs_fit(t))

# the reply r, then the replies of the shipped stepper to the events evs
# spelled on the wire, one step each from the state of r
def wk_run(evs: List<&2, Pr.Ev>, r: FW.St & String) -> List<&2, String>:
  match evs:
    case Nil{}:
      (st, out) = r
      [out]
    case e <> t:
      (st, out) = r
      out <> wk_run(t, FW.step(st, wk_spell_ev(e, "")))

# the same over raw inputs
def wk_feed(ins: List<&2, String>, r: FW.St & String) -> List<&2, String>:
  match ins:
    case Nil{}:
      (st, out) = r
      [out]
    case i <> t:
      (st, out) = r
      out <> wk_feed(t, FW.step(st, i))

# The laws' reader of an event
# ----------------------------

def wk_read_blk.res(+k: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Pr.Blk>:
  match r:
    case Wr.Got{f, s}:
      Wr.Got{Pr.Res{k, f}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def wk_read_blk.call(+k: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Pr.Blk>:
  match r:
    case Wr.Got{f, s}:
      Wr.Got{Pr.Call{k, f}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def wk_read_blk.rkey(r: Wr.Dec<Nat>) -> Wr.Dec<Pr.Blk>:
  match r:
    case Wr.Got{+k, s}:
      wk_read_blk.res(k, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def wk_read_blk.ckey(r: Wr.Dec<Nat>) -> Wr.Dec<Pr.Blk>:
  match r:
    case Wr.Got{+k, s}:
      wk_read_blk.call(k, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def wk_read_blk.tag(n: Nat, s: String) -> Wr.Dec<Pr.Blk>:
  match n:
    case 0n:
      wk_read_blk.ckey(Wr.get_nat(s))
    case 1n:
      wk_read_blk.rkey(Wr.get_nat(s))
    case 2n:
      Wr.Got{Pr.Txt{}, s}
    case 3n:
      Wr.Got{Pr.Think{}, s}
    case 4n:
      Wr.Got{Pr.User{}, s}
    case 5n:
      Wr.Got{Pr.Sys{}, s}
    case 6n+q:
      Wr.Bad{}

def wk_read_blk.go(r: Wr.Dec<Nat>) -> Wr.Dec<Pr.Blk>:
  match r:
    case Wr.Got{n, s}:
      wk_read_blk.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

def wk_read_blk(s: String) -> Wr.Dec<Pr.Blk>:
  wk_read_blk.go(Wr.get_nat(s))

def wk_read_ent.bs(+i: Nat, r: Wr.Dec<List<&2, Pr.Blk>>) -> Wr.Dec<Pr.Ent>:
  match r:
    case Wr.Got{bs, s}:
      Wr.Got{Pr.Ent{i, bs}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def wk_read_ent.go(r: Wr.Dec<Nat>) -> Wr.Dec<Pr.Ent>:
  match r:
    case Wr.Got{+i, s}:
      wk_read_ent.bs(i, Wr.get_list(~Pr.Blk, ~wk_read_blk, s))
    case Wr.Bad{}:
      Wr.Bad{}

def wk_read_ent(s: String) -> Wr.Dec<Pr.Ent>:
  wk_read_ent.go(Wr.get_nat(s))

def wk_read_at.some(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{Some{x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def wk_read_at.tag(n: Nat, s: String) -> Wr.Dec<Maybe<&2, Nat>>:
  match n:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      wk_read_at.some(Wr.get_nat(s))
    case 2n+q:
      Wr.Bad{}

def wk_read_at.go(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{n, s}:
      wk_read_at.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

def wk_read_ev.view(at: Maybe<&2, Nat>, r: Wr.Dec<List<&2, Pr.Ent>>) -> Wr.Dec<Pr.Ev>:
  match r:
    case Wr.Got{es, s}:
      Wr.Got{Pr.View{at, es}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def wk_read_ev.at(r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<Pr.Ev>:
  match r:
    case Wr.Got{at, s}:
      wk_read_ev.view(at, Wr.get_list(~Pr.Ent, ~wk_read_ent, s))
    case Wr.Bad{}:
      Wr.Bad{}

def wk_read_ev.page(r: Wr.Dec<List<&2, Pr.Ent>>) -> Wr.Dec<Pr.Ev>:
  match r:
    case Wr.Got{es, s}:
      Wr.Got{Pr.Page{es}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def wk_read_ev.note(r: Wr.Dec<Nat>) -> Wr.Dec<Pr.Ev>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{Pr.Note{x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def wk_read_ev.tag(n: Nat, s: String) -> Wr.Dec<Pr.Ev>:
  match n:
    case 0n:
      wk_read_ev.at(wk_read_at.go(Wr.get_nat(s)))
    case 1n:
      wk_read_ev.page(Wr.get_list(~Pr.Ent, ~wk_read_ent, s))
    case 2n:
      wk_read_ev.note(Wr.get_nat(s))
    case 3n+q:
      Wr.Bad{}

def wk_read_ev.go(r: Wr.Dec<Nat>) -> Wr.Dec<Pr.Ev>:
  match r:
    case Wr.Got{n, s}:
      wk_read_ev.tag(n, s)
    case Wr.Bad{}:
      Wr.Bad{}

def wk_read.end(whole: Bool, e: Pr.Ev) -> Maybe<&2, Pr.Ev>:
  match whole:
    case True{}:
      Some{e}
    case False{}:
      None{}

def wk_read.whole(r: Wr.Dec<Pr.Ev>) -> Maybe<&2, Pr.Ev>:
  match r:
    case Wr.Got{e, s}:
      wk_read.end(Wr.end(s), e)
    case Wr.Bad{}:
      None{}

# the event s is, when s is exactly one event
def wk_read(s: String) -> Maybe<&2, Pr.Ev>:
  wk_read.whole(wk_read_ev.go(Wr.get_nat(s)))

# Laws: the prior check compared with (the call)
# ----------------------------------------------

# LAW prior_entry_answers (W7): on every request Rust spells whose numbers fit the wire, the
# call answers the last check's stalls and work exactly when it was of the
# same run and the same goal, else none
# EXCLUDES: a prior of another run or goal compared with, a prior dropped
#   when both match, stalls and work swapped or misread
law prior_entry_answers:
  for +m: Maybe<&2, Pr.Last>
  for h: {pe_fits(m) == True{} : Bool}
  {FW.ffi(pe_spell_req(m)) == pe_answer(m) : String}

# LAW prior_entry_malformed_exact (W7): every input that is not exactly one request (the laws'
# reader) answers exactly the error form 'E ' then "work: malformed request"
# EXCLUDES: a default prior for malformed input, input left over ignored,
#   another error text
law prior_entry_malformed_exact:
  for +s: String
  for no: {pe_read(s) == None{} : Maybe<&2, Maybe<&2, Pr.Last>>}
  {FW.ffi(s) == SCon{'E', SCon{' ', "work: malformed request"}} : String}

# LAW prior_entry_example (W7): anchor: the requests Rust sends: no last check; one of the
# same run and goal; another goal; another run; input left over
# EXCLUDES: another spelling of the requests or the replies Rust reads
law prior_entry_example:
  {[FW.ffi("0,"), FW.ffi("1,TT2,5,"), FW.ffi("1,TF2,5,"), FW.ffi("1,FT2,5,"), FW.ffi("1,TT2,5,x")] == ["0,", "1,2,5,", "0,", "0,", Wr.err("work: malformed request")] : List<&2, String>}

# LAW prior_req_fits_example: witness: requests that fit the wire exist (prior_entry_answers
# is not vacuous)
law prior_req_fits_example:
  {[pe_fits(None{}), pe_fits(Some{Pr.Last{True{}, True{}, 2n, 5n}})] == [True{}, True{}] : List<&2, Bool>}

# Laws: the work ledger (the stepper)
# -----------------------------------

# LAW work_entry_open (W6): the open with no input is a ledger that read nothing, and
# replies nothing
# EXCLUDES: a ledger that starts with work, waiting calls or entries read
law work_entry_open:
  {FW.open("") == (FW.Live{Pr.Led{Nil{}, Nil{}, 0n, None{}}}, "") : FW.St & String}

# LAW work_entry_open_refused (W6): an open with input is refused, with the error form
# EXCLUDES: a default ledger for an open Rust never sends
law work_entry_open_refused:
  for +s: String
  for h: {String.is_empty(s) == False{} : Bool}
  {FW.open(s) == (FW.Shut{}, Wr.err("work: the open takes no input")) : FW.St & String}

# LAW work_entry_shut (W6): a refused open answers every step with the error form
# EXCLUDES: a refused stepper that answers a count
law work_entry_shut:
  for +s: String
  {FW.step(FW.Shut{}, s) == (FW.Shut{}, Wr.err("work: the open was refused")) : FW.St & String}

# LAW work_entry_answers (W6): an event Rust spells, whose numbers fit the wire, steps the
# ledger as the model steps it and answers the model's answer, spelled
# EXCLUDES: a field misread (a key, a fingerprint, an id, a block's kind,
#   the view's place, an entry of a list), an answer other than the
#   model's, a ledger kept that the model changed or changed that it kept
law work_entry_answers:
  for +l: Pr.Led
  for +e: Pr.Ev
  for h: {wk_ev_fits(e) == True{} : Bool}
  {FW.step(FW.Live{l}, wk_spell_ev(e, "")) == wk_spell_step(Pr.next(l, e)) : FW.St & String}

# LAW work_entry_malformed_exact (W6): every input that is not exactly one event (the laws'
# reader) answers exactly the error form 'E ' then "work: malformed event",
# and keeps the ledger
# EXCLUDES: a malformed or trailing event read as an act, a ledger changed
#   or lost by one, another error text
law work_entry_malformed_exact:
  for +l: Pr.Led
  for +s: String
  for no: {wk_read(s) == None{} : Maybe<&2, Pr.Ev>}
  {FW.step(FW.Live{l}, s) == (FW.Live{l}, SCon{'E', SCon{' ', "work: malformed event"}}) : FW.St & String}

# LAW work_entry_history (W1, W2, W4, W5, W6): the shipped stepper, opened with no input and
# fed any events Rust spells, answers each what the spec ledger answers:
# the number of distinct acts since it started (`Pr.work` of their numbers), each act a
# result with the newest call of its id that waited for it, or a note;
# the entries of the view read; the last entry read; Again when the view
# no longer holds what it read
# EXCLUDES: a work count that counts a repeat, misses a new act, counts a
#   call, text, thinking, user or system message, pairs a result with
#   another call or with a call that already had its result, keeps the work
#   of a replaced view, reads a view's entries again, or reads a page's
#   entries the ledger read before
law work_entry_history:
  for +evs: List<&2, Pr.Ev>
  for h: {wk_evs_fit(evs) == True{} : Bool}
  {wk_run(evs, FW.open("")) == wk_spec(evs, (wk_start(), "")) : List<&2, String>}

# LAW work_act_apart (W3): acts that differ in their result, in their call, or in having a
# call at all are different acts
# EXCLUDES: an act that ignores its call (two calls with the same result
#   count once) or its result, a result with no call taken for one with
#   a call
law work_act_apart:
  for +m: Maybe<&2, Nat>
  for +c: Nat
  for +d: Nat
  for +r: Nat
  for +x: Nat
  {Nat.is_eq(Pr.act(m, r), Pr.act(m, x)) == Nat.is_eq(r, x) : Bool} & {Nat.is_eq(Pr.act(Some{c}, r), Pr.act(Some{d}, r)) == Nat.is_eq(c, d) : Bool} & {Nat.is_eq(Pr.act(None{}, r), Pr.act(Some{c}, r)) == False{} : Bool}

# LAW work_act_one (W3): two results are the same act exactly when they have the same call
# (or both none) and the same result: the act joins both fingerprints
# with no loss, whatever they are
# EXCLUDES: two acts merged because their call and result differ together
#   (an act that sums or otherwise mixes the two fingerprints), a call
#   with a result taken for a result alone
law work_act_one:
  for +a: Maybe<&2, Nat>
  for +b: Maybe<&2, Nat>
  for +x: Nat
  for +y: Nat
  {Nat.is_eq(Pr.act(a, x), Pr.act(b, y)) == Bool.and(wk_same(a, b), Nat.is_eq(x, y)) : Bool}

# LAW work_note_apart (W3): two notes are the same act exactly when their fingerprints are
# equal, and a note is never the act of a result
# EXCLUDES: notes merged with each other, a note counted as a result
#   already read (or a result as a note)
law work_note_apart:
  for +m: Maybe<&2, Nat>
  for +r: Nat
  for +x: Nat
  for +y: Nat
  {Nat.is_eq(Pr.note(x), Pr.note(y)) == Nat.is_eq(x, y) : Bool} & {Nat.is_eq(Pr.note(x), Pr.act(m, r)) == False{} : Bool}

# LAW work_entry_example (W1-W6): anchor: the events Rust sends and the answers: a view with
# a call, text and its result; a note twice; the view grown by the same
# act under another call id; grown by a new act; the view replaced; the
# view again from its start; a page with an old and a new entry; an
# unknown tag; input left over
# EXCLUDES: an entry that answers other bytes than the grammar's
law work_entry_example:
  {wk_feed(["0,0,1,1,3,0,7,11,2,1,7,13,", "2,99,", "2,99,", "0,1,1,1,2,2,0,8,11,1,8,13,", "0,1,2,1,3,2,0,9,11,1,9,14,", "0,1,7,0,", "0,0,1,1,3,0,7,11,2,1,7,13,", "1,2,1,0,13,2,0,7,12,1,7,14,", "3,", "2,5,x"], FW.open("")) == ["", "0,1,1,1,1,", "0,2,1,1,1,", "0,2,1,1,1,", "0,2,2,1,2,", "0,3,3,1,3,", "1,", "0,1,1,1,1,", "0,2,1,1,13,", Wr.err("work: malformed event"), Wr.err("work: malformed event")] : List<&2, String>}

# LAW work_spell_example (W6): anchor: the events eukhe's ledger writes, spelled: a view of
# one entry (a call, text, its result), a page of one entry, a note
# EXCLUDES: a speller other than the one Rust writes (field order, tags,
#   counts)
law work_spell_example:
  {[wk_spell_ev(Pr.View{None{}, [Pr.Ent{1n, [Pr.Call{7n, 11n}, Pr.Txt{}, Pr.Res{7n, 13n}]}]}, ""), wk_spell_ev(Pr.Page{[Pr.Ent{4n, [Pr.User{}, Pr.Sys{}, Pr.Think{}]}]}, ""), wk_spell_ev(Pr.Note{99n}, "")] == ["0,0,1,1,3,0,7,11,2,1,7,13,", "1,1,4,3,4,5,3,", "2,99,"] : List<&2, String>}

# LAW work_ev_fits_example: witness: event sequences that fit the wire exist
# (work_entry_answers and work_entry_history are not vacuous)
law work_ev_fits_example:
  {wk_evs_fit([Pr.View{Some{1n}, [Pr.Ent{2n, [Pr.Call{7n, 11n}, Pr.Res{7n, 13n}]}]}, Pr.Page{Nil{}}, Pr.Note{99n}]) == True{} : Bool}
