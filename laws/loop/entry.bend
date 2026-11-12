# eukhe: the laws of area loop, section entry: the entry of the compiled
# core for `/loop` (bend/ffi_loop.bend) on every input, stated with
# spellers built only from the wire primitives of bend/wire.bend, never
# with the entry's own encoders. Section model (laws/loop/model.bend)
# states each decision of bend/loop.bend, section history
# (laws/loop/history.bend) what holds over whole histories.

import Base
import ../../bend/loop.bend as Lp
import ../../bend/ffi_loop.bend as FLp
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase

# Requirement (spec/README.md L10)
# --------------------------------
#   L10 the entry answers every request Rust spells with the spelling of
#       the model's answer, refuses input left over and any input that is
#       not a spelled request with the exact error form, and reads back
#       every state it wrote.
#                     loop_ffi_decides, loop_ffi_spelled_left_over,
#                     loop_ffi_reads_only_requests,
#                     loop_ffi_malformed_unless_request,
#                     loop_ffi_st_reads_spelled, loop_ffi_example

# Spec spellers: the entry
# ------------------------
# The grammar of the header of bend/ffi_loop.bend, spelled with the wire
# primitives (Wr.put_nat, Wr.put_str, Wr.put_bool) only.

# a condition: tag 0 none, 1 until (its command), 2 while (its command)
def lp_spell_cond(c: Lp.Cond, rest: String) -> String:
  match c:
    case Lp.NoCond{}:
      Wr.put_nat(0n, rest)
    case Lp.Until{cmd}:
      Wr.put_nat(1n, Wr.put_str(cmd, rest))
    case Lp.While{cmd}:
      Wr.put_nat(2n, Wr.put_str(cmd, rest))

# the evidence: tag 0 exited (its code), 1 no status, 2 timed out, 3 spawn
# failed, 4 cancelled
def lp_spell_evid(e: Lp.Evid, rest: String) -> String:
  match e:
    case Lp.Exited{code}:
      Wr.put_nat(0n, Wr.put_nat(code, rest))
    case Lp.NoStatus{}:
      Wr.put_nat(1n, rest)
    case Lp.TimedOut{}:
      Wr.put_nat(2n, rest)
    case Lp.SpawnFailed{}:
      Wr.put_nat(3n, rest)
    case Lp.Cancelled{}:
      Wr.put_nat(4n, rest)

# why a loop ended: tag 0 satisfied, 1 check broke, 2 out of turns, 3 out
# of time, 4 turns failed, 5 out of budget, 6 stopped
def lp_spell_end(w: Lp.End, rest: String) -> String:
  match w:
    case Lp.Satisfied{}:
      Wr.put_nat(0n, rest)
    case Lp.CheckBroke{}:
      Wr.put_nat(1n, rest)
    case Lp.OutOfTurns{}:
      Wr.put_nat(2n, rest)
    case Lp.OutOfTime{}:
      Wr.put_nat(3n, rest)
    case Lp.TurnsFailed{}:
      Wr.put_nat(4n, rest)
    case Lp.OutOfBudget{}:
      Wr.put_nat(5n, rest)
    case Lp.Stopped{}:
      Wr.put_nat(6n, rest)

# a phase: tag 0 off, 1 armed, 2 turn, 3 judging, 4 paused, 5 ended (why)
def lp_spell_phase(p: Lp.Phase, rest: String) -> String:
  match p:
    case Lp.Off{}:
      Wr.put_nat(0n, rest)
    case Lp.Armed{}:
      Wr.put_nat(1n, rest)
    case Lp.Turn{}:
      Wr.put_nat(2n, rest)
    case Lp.Judging{}:
      Wr.put_nat(3n, rest)
    case Lp.Paused{}:
      Wr.put_nat(4n, rest)
    case Lp.Ended{w}:
      Wr.put_nat(5n, lp_spell_end(w, rest))

# the last evidence: tag 0 none, 1 then the iteration and the evidence
def lp_spell_last(x: Lp.Last, rest: String) -> String:
  match x:
    case Lp.NoCheck{}:
      Wr.put_nat(0n, rest)
    case Lp.Check{at, ev}:
      Wr.put_nat(1n, Wr.put_nat(at, lp_spell_evid(ev, rest)))

# a Nat that may be absent: tag 0 none, 1 then the Nat
def lp_spell_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_nat(x, rest))

# a state: phase, iterations started, iterations left, deadline,
# condition, prompt, failed turns, last evidence
def lp_spell_st(s: Lp.St, rest: String) -> String:
  match s:
    case Lp.St{p, i, l, d, c, b, f, z}:
      lp_spell_phase(p, Wr.put_nat(i, lp_spell_mnat(l, lp_spell_mnat(d, lp_spell_cond(c, Wr.put_str(b, Wr.put_nat(f, lp_spell_last(z, rest))))))))

# a bound: tag 0 none, 1 a count, 2 a span of ms
def lp_spell_limit(lim: Lp.Limit, rest: String) -> String:
  match lim:
    case Lp.NoLimit{}:
      Wr.put_nat(0n, rest)
    case Lp.Count{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))
    case Lp.Span{ms}:
      Wr.put_nat(2n, Wr.put_nat(ms, rest))

# how a turn settled: tag 0 ran, 1 errored, 2 halted
def lp_spell_out(o: Lp.Out, rest: String) -> String:
  match o:
    case Lp.Ran{}:
      Wr.put_nat(0n, rest)
    case Lp.Errored{}:
      Wr.put_nat(1n, rest)
    case Lp.Halted{}:
      Wr.put_nat(2n, rest)

# a text that may be absent: tag 0 none, 1 then the text
def lp_spell_mstr(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{t}:
      Wr.put_nat(1n, Wr.put_str(t, rest))

# an event: tag 0 enter (bound, condition, prompt, clock), 1 stop, 2 abort,
# 3 prompt (text), 4 settled (iteration, outcome, blocked, clock, funded),
# 5 judged (iteration, evidence, blocked, clock, funded), 6 restart
def lp_spell_ev(e: Lp.Ev, rest: String) -> String:
  match e:
    case Lp.Enter{lim, c, pr, now}:
      Wr.put_nat(0n, lp_spell_limit(lim, lp_spell_cond(c, lp_spell_mstr(pr, Wr.put_nat(now, rest)))))
    case Lp.Stop{}:
      Wr.put_nat(1n, rest)
    case Lp.Abort{}:
      Wr.put_nat(2n, rest)
    case Lp.Prompt{t}:
      Wr.put_nat(3n, Wr.put_str(t, rest))
    case Lp.Settled{k, o, b, now, fu}:
      Wr.put_nat(4n, Wr.put_nat(k, lp_spell_out(o, Wr.put_bool(b, Wr.put_nat(now, Wr.put_bool(fu, rest))))))
    case Lp.Judged{k, ev, b, now, fu}:
      Wr.put_nat(5n, Wr.put_nat(k, lp_spell_evid(ev, Wr.put_bool(b, Wr.put_nat(now, Wr.put_bool(fu, rest))))))
    case Lp.Restart{}:
      Wr.put_nat(6n, rest)

# a request: tag 0 a step (state, event), 1 a verdict (until, evidence)
def lp_spell_req(r: FLp.Req, rest: String) -> String:
  match r:
    case FLp.Step{s, e}:
      Wr.put_nat(0n, lp_spell_st(s, lp_spell_ev(e, rest)))
    case FLp.Verdict{u, ev}:
      Wr.put_nat(1n, Wr.put_bool(u, lp_spell_evid(ev, rest)))

# what Rust does: tag 0 rest, 1 submit (iteration, text), 2 adopt
# (iteration), 3 judge (iteration), 4 resume (iteration, text), 5 report
# (why), 6 defer
def lp_spell_act(a: Lp.Act, rest: String) -> String:
  match a:
    case Lp.Rest{}:
      Wr.put_nat(0n, rest)
    case Lp.Submit{i, t}:
      Wr.put_nat(1n, Wr.put_nat(i, Wr.put_str(t, rest)))
    case Lp.Adopt{i}:
      Wr.put_nat(2n, Wr.put_nat(i, rest))
    case Lp.Judge{i}:
      Wr.put_nat(3n, Wr.put_nat(i, rest))
    case Lp.Resume{i, t}:
      Wr.put_nat(4n, Wr.put_nat(i, Wr.put_str(t, rest)))
    case Lp.Report{w}:
      Wr.put_nat(5n, lp_spell_end(w, rest))
    case Lp.Defer{}:
      Wr.put_nat(6n, rest)

# a verdict: tag 0 confirmed, 1 refuted, 2 broken, 3 unjudged
def lp_spell_verdict(v: Lp.Verdict, rest: String) -> String:
  match v:
    case Lp.Confirmed{}:
      Wr.put_nat(0n, rest)
    case Lp.Refuted{}:
      Wr.put_nat(1n, rest)
    case Lp.Broken{}:
      Wr.put_nat(2n, rest)
    case Lp.Unjudged{}:
      Wr.put_nat(3n, rest)

# a step's reply: the new state, then what Rust does
def lp_spell_stepped(r: Lp.St & Lp.Act) -> String:
  (s, a) = r
  lp_spell_st(s, lp_spell_act(a, ""))

# the spelling of the model's answer to request r
def lp_spell_reply(r: FLp.Req) -> String:
  match r:
    case FLp.Step{s, e}:
      lp_spell_stepped(Lp.step(s, e))
    case FLp.Verdict{u, ev}:
      lp_spell_verdict(Lp.judge(u, ev), "")

# Spec helpers: what fits the wire
# --------------------------------

def lp_cond_fits(c: Lp.Cond) -> Bool:
  match c:
    case Lp.NoCond{}:
      True{}
    case Lp.Until{cmd}:
      LawsBase.wire_fits(String.length(cmd))
    case Lp.While{cmd}:
      LawsBase.wire_fits(String.length(cmd))

def lp_evid_fits(e: Lp.Evid) -> Bool:
  match e:
    case Lp.Exited{code}:
      LawsBase.wire_fits(code)
    case Lp.NoStatus{}:
      True{}
    case Lp.TimedOut{}:
      True{}
    case Lp.SpawnFailed{}:
      True{}
    case Lp.Cancelled{}:
      True{}

def lp_last_fits(x: Lp.Last) -> Bool:
  match x:
    case Lp.NoCheck{}:
      True{}
    case Lp.Check{at, ev}:
      Bool.and(LawsBase.wire_fits(at), lp_evid_fits(ev))

def lp_mstr_fits(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{t}:
      LawsBase.wire_fits(String.length(t))

# every Nat and every string length of a state fits the wire
def lp_st_fits(s: Lp.St) -> Bool:
  match s:
    case Lp.St{p, i, l, d, c, b, f, z}:
      Bool.and(LawsBase.wire_fits(i), Bool.and(LawsBase.wire_mfits(l), Bool.and(LawsBase.wire_mfits(d), Bool.and(lp_cond_fits(c), Bool.and(LawsBase.wire_fits(String.length(b)), Bool.and(LawsBase.wire_fits(f), lp_last_fits(z)))))))

def lp_limit_fits(lim: Lp.Limit) -> Bool:
  match lim:
    case Lp.NoLimit{}:
      True{}
    case Lp.Count{n}:
      LawsBase.wire_fits(n)
    case Lp.Span{ms}:
      LawsBase.wire_fits(ms)

def lp_ev_fits(e: Lp.Ev) -> Bool:
  match e:
    case Lp.Enter{lim, c, pr, now}:
      Bool.and(lp_limit_fits(lim), Bool.and(lp_cond_fits(c), Bool.and(lp_mstr_fits(pr), LawsBase.wire_fits(now))))
    case Lp.Stop{}:
      True{}
    case Lp.Abort{}:
      True{}
    case Lp.Prompt{t}:
      LawsBase.wire_fits(String.length(t))
    case Lp.Settled{k, o, b, now, fu}:
      Bool.and(LawsBase.wire_fits(k), LawsBase.wire_fits(now))
    case Lp.Judged{k, ev, b, now, fu}:
      Bool.and(LawsBase.wire_fits(k), Bool.and(lp_evid_fits(ev), LawsBase.wire_fits(now)))
    case Lp.Restart{}:
      True{}

# every Nat and every string length of a request fits the wire
def lp_req_fits(r: FLp.Req) -> Bool:
  match r:
    case FLp.Step{s, e}:
      Bool.and(lp_st_fits(s), lp_ev_fits(e))
    case FLp.Verdict{u, ev}:
      lp_evid_fits(ev)

# Laws: the entry
# ---------------

# LAW loop_ffi_decides (L10): a request spelled by the grammar, whose Nats
# and string lengths fit the wire, is answered with the spelling of the
# model's answer: the new state and the act of a step, the verdict of a
# piece of evidence
# EXCLUDES: an entry that answers another event, state or evidence, a
#   field lost or swapped on the way to the model, a reply in another tag
#   or order, a default
law loop_ffi_decides:
  for +r: FLp.Req
  for h: {lp_req_fits(r) == True{} : Bool}
  {FLp.ffi(lp_spell_req(r, "")) == lp_spell_reply(r) : String}

# LAW loop_ffi_spelled_left_over (L10): input left over after a spelled
# request is refused
# EXCLUDES: trailing input ignored, or read as part of the request
law loop_ffi_spelled_left_over:
  for +r: FLp.Req
  for +rest: String
  for h: {lp_req_fits(r) == True{} : Bool}
  for more: {String.is_empty(rest) == False{} : Bool}
  {FLp.ffi(lp_spell_req(r, rest)) == Wr.err("loop: input left over") : String}

# LAW loop_ffi_reads_only_requests (L10): an answer that is not the error
# form answers a request: the input is the spelling of a request that fits
# the wire, and the answer is the model's answer to it
# EXCLUDES: a decoder that accepts an unknown tag, a bad flag, a short
#   string, a Nat past the wire, or a missing field, and answers it anyway
#   (a default instead of the error form)
law loop_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FLp.ffi(s)) == False{} : Bool}
  exs r: FLp.Req
  {(s, (lp_req_fits(r), FLp.ffi(s))) == (lp_spell_req(r, ""), (True{}, lp_spell_reply(r))) : String & (Bool & String)}

# LAW loop_ffi_malformed_unless_request (L10): an input that does not
# begin with a spelled request that fits answers the malformed error: any
# other answer comes from an input that is a spelled request that fits,
# then possibly more
# EXCLUDES: the left-over error, another error text, or a reply, for input
#   that holds no request
law loop_ffi_malformed_unless_request:
  for +s: String
  for other: {String.eq(FLp.ffi(s), Wr.err("loop: malformed request")) == False{} : Bool}
  exs r: FLp.Req
  exs rest: String
  {(s, lp_req_fits(r)) == (lp_spell_req(r, rest), True{}) : String & Bool}

# LAW loop_ffi_st_reads_spelled (L10): the state reader reads every state
# the grammar spells back as itself, the rest untouched: the state Rust
# stores (the text of a reply) is the state the next request carries
# EXCLUDES: a reader (and its own writer) that swap the fields or tags of
#   a state both ways, a stored loop that comes back in another phase,
#   with another count, deadline, condition or prompt
law loop_ffi_st_reads_spelled:
  for +s: Lp.St
  for +rest: String
  for h: {lp_st_fits(s) == True{} : Bool}
  {FLp.get_st(lp_spell_st(s, rest)) == Wr.Got{s, rest} : Wr.Dec<Lp.St>}

# LAW loop_ffi_example (L10): anchor: the exact strings Rust sends and
# reads: `/loop` with a count of 3, `--until abc` and the prompt "fix" at
# clock 5 starts iteration 1 and submits "fix"; exit status 0 after
# iteration 1 ends that loop satisfied; a settled turn of a loop with no
# condition and 2 iterations left submits iteration 2; exit status 0
# confirms an until and refutes a while; a cancelled check is unjudged; an
# empty input, event tag 7 and request tag 2 are malformed; a char after a
# request is left over
# EXCLUDES: a request or a reply in another order, tag or spelling than
#   the documented texts
law loop_ffi_example:
  {[FLp.ffi("0,0,0,0,0,0,0,0,0,0,1,3,1,3,abc1,3,fix5,"), FLp.ffi("0,3,1,1,3,0,1,3,abc3,fix0,0,5,1,0,0,F9,T"), FLp.ffi("0,2,1,1,2,0,0,3,fix0,0,4,1,0,F7,T"), FLp.ffi("1,T0,0,"), FLp.ffi("1,F0,0,"), FLp.ffi("1,T4,"), FLp.ffi(""), FLp.ffi("0,0,0,0,0,0,0,0,0,7,"), FLp.ffi("2,"), FLp.ffi("1,T0,0,x")] == ["2,1,1,3,0,1,3,abc3,fix0,0,1,1,3,fix", "5,0,1,1,3,0,1,3,abc3,fix0,1,1,0,0,5,0,", "2,2,1,1,0,0,3,fix0,0,1,2,3,fix", "0,", "1,", "3,", "E loop: malformed request", "E loop: malformed request", "E loop: malformed request", "E loop: input left over"] : List<&2, String>}
