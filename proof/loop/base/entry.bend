# eukhe: lemmas the entry proofs of area loop share: the entry's own
# encoders write what the spec spellers of laws/loop/entry.bend spell
# (le.e_*), its readers read every spelled value that fits back (le.r_*:
# the decoder of a request, and the reader of a stored state), and its
# answer to a request is the spelled reply of the model (le.run).

import Base
import ../../../bend/loop.bend as Lp
import ../../../bend/ffi_loop.bend as FLp
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/loop/entry.bend as LoopEntry
import ../../base/wire.bend as LWire
import ../../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip
import ../../wire/base/spell.bend as LAWireSpell

# ---- Bool ----

def le.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def le.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      LAWireSpell.ws_absurd({b == True{} : Bool}, Equal.sym(Bool, False{}, True{}, e))

# ---- the encoders spell the spec ----

def le.e_mnat(m: Maybe<&2, Nat>, -rest: String) -> {FLp.put_mnat(m, rest) == LoopEntry.lp_spell_mnat(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def le.e_cond(c: Lp.Cond, -rest: String) -> {FLp.put_cond(c, rest) == LoopEntry.lp_spell_cond(c, rest) : String}:
  match c:
    case Lp.NoCond{}:
      {==}
    case Lp.Until{cmd}:
      {==}
    case Lp.While{cmd}:
      {==}

def le.e_evid(e: Lp.Evid, -rest: String) -> {FLp.put_evid(e, rest) == LoopEntry.lp_spell_evid(e, rest) : String}:
  match e:
    case Lp.Exited{code}:
      {==}
    case Lp.NoStatus{}:
      {==}
    case Lp.TimedOut{}:
      {==}
    case Lp.SpawnFailed{}:
      {==}
    case Lp.Cancelled{}:
      {==}

def le.e_end(w: Lp.End, -rest: String) -> {FLp.put_end(w, rest) == LoopEntry.lp_spell_end(w, rest) : String}:
  match w:
    case Lp.Satisfied{}:
      {==}
    case Lp.CheckBroke{}:
      {==}
    case Lp.OutOfTurns{}:
      {==}
    case Lp.OutOfTime{}:
      {==}
    case Lp.TurnsFailed{}:
      {==}
    case Lp.OutOfBudget{}:
      {==}
    case Lp.Stopped{}:
      {==}

def le.e_phase(p: Lp.Phase, -rest: String) -> {FLp.put_phase(p, rest) == LoopEntry.lp_spell_phase(p, rest) : String}:
  match p:
    case Lp.Off{}:
      {==}
    case Lp.Armed{}:
      {==}
    case Lp.Turn{}:
      {==}
    case Lp.Judging{}:
      {==}
    case Lp.Paused{}:
      {==}
    case Lp.Ended{+w}:
      %le.e_end(w, rest) : {FLp.put_phase(Lp.Ended{w}, rest) == Wr.put_nat(5n, _) : String}
      {==}

def le.e_last(x: Lp.Last, -rest: String) -> {FLp.put_last(x, rest) == LoopEntry.lp_spell_last(x, rest) : String}:
  match x:
    case Lp.NoCheck{}:
      {==}
    case Lp.Check{+at, +ev}:
      %le.e_evid(ev, rest) : {FLp.put_last(Lp.Check{at, ev}, rest) == Wr.put_nat(1n, Wr.put_nat(at, _)) : String}
      {==}

# a state: phase, iter, left, deadline, cond, body, fails, last
def le.e_st(x: Lp.St, -rest: String) -> {FLp.put_st(x, rest) == LoopEntry.lp_spell_st(x, rest) : String}:
  match x:
    case Lp.St{+p, +i, +l, +d, +c, +b, +f, +z}:
      -a5 = Wr.put_str(b, Wr.put_nat(f, LoopEntry.lp_spell_last(z, rest)))
      -a4 = LoopEntry.lp_spell_cond(c, a5)
      -a3 = LoopEntry.lp_spell_mnat(d, a4)
      -a1 = Wr.put_nat(i, LoopEntry.lp_spell_mnat(l, a3))
      -lhs = FLp.put_st(Lp.St{p, i, l, d, c, b, f, z}, rest)
      %le.e_phase(p, a1) : {lhs == _ : String}
      %le.e_mnat(l, a3) : {lhs == FLp.put_phase(p, Wr.put_nat(i, _)) : String}
      %le.e_mnat(d, a4) : {lhs == FLp.put_phase(p, Wr.put_nat(i, FLp.put_mnat(l, _))) : String}
      %le.e_cond(c, a5) : {lhs == FLp.put_phase(p, Wr.put_nat(i, FLp.put_mnat(l, FLp.put_mnat(d, _)))) : String}
      %le.e_last(z, rest) : {lhs == FLp.put_phase(p, Wr.put_nat(i, FLp.put_mnat(l, FLp.put_mnat(d, FLp.put_cond(c, Wr.put_str(b, Wr.put_nat(f, _))))))) : String}
      {==}

# what Rust does
def le.e_act(a: Lp.Act, -rest: String) -> {FLp.put_act(a, rest) == LoopEntry.lp_spell_act(a, rest) : String}:
  match a:
    case Lp.Rest{}:
      {==}
    case Lp.Submit{i, t}:
      {==}
    case Lp.Adopt{i}:
      {==}
    case Lp.Judge{i}:
      {==}
    case Lp.Resume{i, t}:
      {==}
    case Lp.Report{+w}:
      %le.e_end(w, rest) : {FLp.put_act(Lp.Report{w}, rest) == Wr.put_nat(5n, _) : String}
      {==}
    case Lp.Defer{}:
      {==}

# a verdict
def le.e_verdict(v: Lp.Verdict, -rest: String) -> {FLp.put_verdict(v, rest) == LoopEntry.lp_spell_verdict(v, rest) : String}:
  match v:
    case Lp.Confirmed{}:
      {==}
    case Lp.Refuted{}:
      {==}
    case Lp.Broken{}:
      {==}
    case Lp.Unjudged{}:
      {==}

# a step's reply: the state, then the act
def le.e_stepped(r: Lp.St & Lp.Act) -> {FLp.ffi.stepped(r) == LoopEntry.lp_spell_stepped(r) : String}:
  (+x, +a) = r
  Equal.trans(String, FLp.put_st(x, FLp.put_act(a, "")), FLp.put_st(x, LoopEntry.lp_spell_act(a, "")), LoopEntry.lp_spell_st(x, LoopEntry.lp_spell_act(a, "")),
    Equal.cong(String, String, z => FLp.put_st(x, z), FLp.put_act(a, ""), LoopEntry.lp_spell_act(a, ""), le.e_act(a, "")),
    le.e_st(x, LoopEntry.lp_spell_act(a, "")))

# the entry's answer to a request is the spelled reply of the model
def le.run(r: FLp.Req) -> {FLp.ffi.run(r) == LoopEntry.lp_spell_reply(r) : String}:
  match r:
    case FLp.Step{x, e}:
      le.e_stepped(Lp.step(x, e))
    case FLp.Verdict{u, ev}:
      le.e_verdict(Lp.judge(u, ev), "")

# ---- the readers read the spelling ----

def le.r_nat(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

def le.r_str(+t: String, +rest: String, h: {LawsBase.wire_fits(String.length(t)) == True{} : Bool}) -> {Wr.Got{t, rest} == Wr.get_str(Wr.put_str(t, rest)) : Wr.Dec<String>}:
  Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(t, rest)), Wr.Got{t, rest}, Wire.wire_str_round_trip(t, rest, h))

def le.r_bool(+b: Bool, +rest: String) -> {Wr.Got{b, rest} == Wr.get_bool(Wr.put_bool(b, rest)) : Wr.Dec<Bool>}:
  Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(b, rest)), Wr.Got{b, rest}, Wire.wire_bool_round_trip(b, rest))

def le.r_mnat(m: Maybe<&2, Nat>, +rest: String, h: {LawsBase.wire_mfits(m) == True{} : Bool}) -> {FLp.get_mnat(LoopEntry.lp_spell_mnat(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, Nat>>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %le.r_nat(x, rest, h) : {FLp.get_mnat.some(_) == Wr.Got{Some{x}, rest} : Wr.Dec<Maybe<&2, Nat>>}
      {==}

def le.r_mstr(m: Maybe<&2, String>, +rest: String, h: {LoopEntry.lp_mstr_fits(m) == True{} : Bool}) -> {FLp.get_mstr(LoopEntry.lp_spell_mstr(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, String>>}:
  match m:
    case None{}:
      {==}
    case Some{+t}:
      %le.r_str(t, rest, h) : {FLp.get_mstr.some(_) == Wr.Got{Some{t}, rest} : Wr.Dec<Maybe<&2, String>>}
      {==}

def le.r_cond(c: Lp.Cond, +rest: String, h: {LoopEntry.lp_cond_fits(c) == True{} : Bool}) -> {FLp.get_cond(LoopEntry.lp_spell_cond(c, rest)) == Wr.Got{c, rest} : Wr.Dec<Lp.Cond>}:
  match c:
    case Lp.NoCond{}:
      {==}
    case Lp.Until{+cmd}:
      %le.r_str(cmd, rest, h) : {FLp.get_cond.until(_) == Wr.Got{Lp.Until{cmd}, rest} : Wr.Dec<Lp.Cond>}
      {==}
    case Lp.While{+cmd}:
      %le.r_str(cmd, rest, h) : {FLp.get_cond.while(_) == Wr.Got{Lp.While{cmd}, rest} : Wr.Dec<Lp.Cond>}
      {==}

def le.r_evid(e: Lp.Evid, +rest: String, h: {LoopEntry.lp_evid_fits(e) == True{} : Bool}) -> {FLp.get_evid(LoopEntry.lp_spell_evid(e, rest)) == Wr.Got{e, rest} : Wr.Dec<Lp.Evid>}:
  match e:
    case Lp.Exited{+code}:
      %le.r_nat(code, rest, h) : {FLp.get_evid.code(_) == Wr.Got{Lp.Exited{code}, rest} : Wr.Dec<Lp.Evid>}
      {==}
    case Lp.NoStatus{}:
      {==}
    case Lp.TimedOut{}:
      {==}
    case Lp.SpawnFailed{}:
      {==}
    case Lp.Cancelled{}:
      {==}

def le.r_end(w: Lp.End, -rest: String) -> {FLp.get_end(LoopEntry.lp_spell_end(w, rest)) == Wr.Got{w, rest} : Wr.Dec<Lp.End>}:
  match w:
    case Lp.Satisfied{}:
      {==}
    case Lp.CheckBroke{}:
      {==}
    case Lp.OutOfTurns{}:
      {==}
    case Lp.OutOfTime{}:
      {==}
    case Lp.TurnsFailed{}:
      {==}
    case Lp.OutOfBudget{}:
      {==}
    case Lp.Stopped{}:
      {==}

def le.r_phase(p: Lp.Phase, -rest: String) -> {FLp.get_phase(LoopEntry.lp_spell_phase(p, rest)) == Wr.Got{p, rest} : Wr.Dec<Lp.Phase>}:
  match p:
    case Lp.Off{}:
      {==}
    case Lp.Armed{}:
      {==}
    case Lp.Turn{}:
      {==}
    case Lp.Judging{}:
      {==}
    case Lp.Paused{}:
      {==}
    case Lp.Ended{+w}:
      %Equal.sym(Wr.Dec<Lp.End>, FLp.get_end(LoopEntry.lp_spell_end(w, rest)), Wr.Got{w, rest}, le.r_end(w, rest)) : {FLp.get_phase.ended(_) == Wr.Got{Lp.Ended{w}, rest} : Wr.Dec<Lp.Phase>}
      {==}

def le.r_last(x: Lp.Last, +rest: String, h: {LoopEntry.lp_last_fits(x) == True{} : Bool}) -> {FLp.get_last(LoopEntry.lp_spell_last(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Lp.Last>}:
  match x:
    case Lp.NoCheck{}:
      {==}
    case Lp.Check{+at, +ev}:
      +hh = h
      %le.r_nat(at, LoopEntry.lp_spell_evid(ev, rest), le.and_l(LawsBase.wire_fits(at), LoopEntry.lp_evid_fits(ev), hh)) : {FLp.get_last.at(_) == Wr.Got{Lp.Check{at, ev}, rest} : Wr.Dec<Lp.Last>}
      %Equal.sym(Wr.Dec<Lp.Evid>, FLp.get_evid(LoopEntry.lp_spell_evid(ev, rest)), Wr.Got{ev, rest}, le.r_evid(ev, rest, le.and_r(LawsBase.wire_fits(at), LoopEntry.lp_evid_fits(ev), hh))) : {FLp.get_last.ev(at, _) == Wr.Got{Lp.Check{at, ev}, rest} : Wr.Dec<Lp.Last>}
      {==}

# a state that fits
def le.r_st(x: Lp.St, +rest: String, h: {LoopEntry.lp_st_fits(x) == True{} : Bool}) -> {FLp.get_st(LoopEntry.lp_spell_st(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Lp.St>}:
  match x:
    case Lp.St{+p, +i, +l, +d, +c, +b, +f, +z}:
      -fi = LawsBase.wire_fits(i)
      -fl = LawsBase.wire_mfits(l)
      -fd = LawsBase.wire_mfits(d)
      -fc = LoopEntry.lp_cond_fits(c)
      -fb = LawsBase.wire_fits(String.length(b))
      -ff = LawsBase.wire_fits(f)
      -fz = LoopEntry.lp_last_fits(z)
      +h1 = h
      +h2 = le.and_r(LawsBase.wire_fits(i), Bool.and(fl, Bool.and(fd, Bool.and(fc, Bool.and(fb, Bool.and(ff, fz))))), h1)
      +h3 = le.and_r(LawsBase.wire_mfits(l), Bool.and(fd, Bool.and(fc, Bool.and(fb, Bool.and(ff, fz)))), h2)
      +h4 = le.and_r(LawsBase.wire_mfits(d), Bool.and(fc, Bool.and(fb, Bool.and(ff, fz))), h3)
      +h5 = le.and_r(LoopEntry.lp_cond_fits(c), Bool.and(fb, Bool.and(ff, fz)), h4)
      +h6 = le.and_r(LawsBase.wire_fits(String.length(b)), Bool.and(ff, fz), h5)
      +s7 = LoopEntry.lp_spell_last(z, rest)
      +s6 = Wr.put_nat(f, s7)
      +s5 = Wr.put_str(b, s6)
      +s4 = LoopEntry.lp_spell_cond(c, s5)
      +s3 = LoopEntry.lp_spell_mnat(d, s4)
      +s2 = LoopEntry.lp_spell_mnat(l, s3)
      +s1 = Wr.put_nat(i, s2)
      -got = {Wr.Got{Lp.St{p, i, l, d, c, b, f, z}, rest} : Wr.Dec<Lp.St>}
      %Equal.sym(Wr.Dec<Lp.Phase>, FLp.get_phase(LoopEntry.lp_spell_phase(p, s1)), Wr.Got{p, s1}, le.r_phase(p, s1)) : {FLp.get_st.phase(_) == got : Wr.Dec<Lp.St>}
      %le.r_nat(i, s2, le.and_l(LawsBase.wire_fits(i), Bool.and(fl, Bool.and(fd, Bool.and(fc, Bool.and(fb, Bool.and(ff, fz))))), h1)) : {FLp.get_st.iter(p, _) == got : Wr.Dec<Lp.St>}
      %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, FLp.get_mnat(s2), Wr.Got{l, s3}, le.r_mnat(l, s3, le.and_l(LawsBase.wire_mfits(l), Bool.and(fd, Bool.and(fc, Bool.and(fb, Bool.and(ff, fz)))), h2))) : {FLp.get_st.left(p, i, _) == got : Wr.Dec<Lp.St>}
      %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, FLp.get_mnat(s3), Wr.Got{d, s4}, le.r_mnat(d, s4, le.and_l(LawsBase.wire_mfits(d), Bool.and(fc, Bool.and(fb, Bool.and(ff, fz))), h3))) : {FLp.get_st.deadline(p, i, l, _) == got : Wr.Dec<Lp.St>}
      %Equal.sym(Wr.Dec<Lp.Cond>, FLp.get_cond(s4), Wr.Got{c, s5}, le.r_cond(c, s5, le.and_l(LoopEntry.lp_cond_fits(c), Bool.and(fb, Bool.and(ff, fz)), h4))) : {FLp.get_st.cond(p, i, l, d, _) == got : Wr.Dec<Lp.St>}
      %le.r_str(b, s6, le.and_l(LawsBase.wire_fits(String.length(b)), Bool.and(ff, fz), h5)) : {FLp.get_st.body(p, i, l, d, c, _) == got : Wr.Dec<Lp.St>}
      %le.r_nat(f, s7, le.and_l(LawsBase.wire_fits(f), fz, h6)) : {FLp.get_st.fails(p, i, l, d, c, b, _) == got : Wr.Dec<Lp.St>}
      %Equal.sym(Wr.Dec<Lp.Last>, FLp.get_last(s7), Wr.Got{z, rest}, le.r_last(z, rest, le.and_r(LawsBase.wire_fits(f), fz, h6))) : {FLp.get_st.last(p, i, l, d, c, b, f, _) == got : Wr.Dec<Lp.St>}
      {==}

def le.r_limit(lim: Lp.Limit, +rest: String, h: {LoopEntry.lp_limit_fits(lim) == True{} : Bool}) -> {FLp.get_limit(LoopEntry.lp_spell_limit(lim, rest)) == Wr.Got{lim, rest} : Wr.Dec<Lp.Limit>}:
  match lim:
    case Lp.NoLimit{}:
      {==}
    case Lp.Count{+n}:
      %le.r_nat(n, rest, h) : {FLp.get_limit.count(_) == Wr.Got{Lp.Count{n}, rest} : Wr.Dec<Lp.Limit>}
      {==}
    case Lp.Span{+ms}:
      %le.r_nat(ms, rest, h) : {FLp.get_limit.span(_) == Wr.Got{Lp.Span{ms}, rest} : Wr.Dec<Lp.Limit>}
      {==}

def le.r_out(o: Lp.Out, -rest: String) -> {FLp.get_out(LoopEntry.lp_spell_out(o, rest)) == Wr.Got{o, rest} : Wr.Dec<Lp.Out>}:
  match o:
    case Lp.Ran{}:
      {==}
    case Lp.Errored{}:
      {==}
    case Lp.Halted{}:
      {==}

# an event that fits
def le.r_ev(e: Lp.Ev, +rest: String, h: {LoopEntry.lp_ev_fits(e) == True{} : Bool}) -> {FLp.get_ev(LoopEntry.lp_spell_ev(e, rest)) == Wr.Got{e, rest} : Wr.Dec<Lp.Ev>}:
  match e:
    case Lp.Enter{+lim, +c, +pr, +now}:
      -fc = LoopEntry.lp_cond_fits(c)
      -fp = LoopEntry.lp_mstr_fits(pr)
      -fn = LawsBase.wire_fits(now)
      +h1 = h
      +h2 = le.and_r(LoopEntry.lp_limit_fits(lim), Bool.and(fc, Bool.and(fp, fn)), h1)
      +h3 = le.and_r(LoopEntry.lp_cond_fits(c), Bool.and(fp, fn), h2)
      +s3 = Wr.put_nat(now, rest)
      +s2 = LoopEntry.lp_spell_mstr(pr, s3)
      +s1 = LoopEntry.lp_spell_cond(c, s2)
      -got = {Wr.Got{Lp.Enter{lim, c, pr, now}, rest} : Wr.Dec<Lp.Ev>}
      %Equal.sym(Wr.Dec<Lp.Limit>, FLp.get_limit(LoopEntry.lp_spell_limit(lim, s1)), Wr.Got{lim, s1}, le.r_limit(lim, s1, le.and_l(LoopEntry.lp_limit_fits(lim), Bool.and(fc, Bool.and(fp, fn)), h1))) : {FLp.get_ev.enter(_) == got : Wr.Dec<Lp.Ev>}
      %Equal.sym(Wr.Dec<Lp.Cond>, FLp.get_cond(s1), Wr.Got{c, s2}, le.r_cond(c, s2, le.and_l(LoopEntry.lp_cond_fits(c), Bool.and(fp, fn), h2))) : {FLp.get_ev.enter.cond(lim, _) == got : Wr.Dec<Lp.Ev>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FLp.get_mstr(s2), Wr.Got{pr, s3}, le.r_mstr(pr, s3, le.and_l(LoopEntry.lp_mstr_fits(pr), fn, h3))) : {FLp.get_ev.enter.prompt(lim, c, _) == got : Wr.Dec<Lp.Ev>}
      %le.r_nat(now, rest, le.and_r(LoopEntry.lp_mstr_fits(pr), fn, h3)) : {FLp.get_ev.enter.now(lim, c, pr, _) == got : Wr.Dec<Lp.Ev>}
      {==}
    case Lp.Stop{}:
      {==}
    case Lp.Abort{}:
      {==}
    case Lp.Prompt{+t}:
      %le.r_str(t, rest, h) : {FLp.get_ev.prompt(_) == Wr.Got{Lp.Prompt{t}, rest} : Wr.Dec<Lp.Ev>}
      {==}
    case Lp.Settled{+k, +o, +b, +now, +fu}:
      +h1 = h
      +s4 = Wr.put_bool(fu, rest)
      +s3 = Wr.put_nat(now, s4)
      +s2 = Wr.put_bool(b, s3)
      +s1 = LoopEntry.lp_spell_out(o, s2)
      -got = {Wr.Got{Lp.Settled{k, o, b, now, fu}, rest} : Wr.Dec<Lp.Ev>}
      %le.r_nat(k, s1, le.and_l(LawsBase.wire_fits(k), LawsBase.wire_fits(now), h1)) : {FLp.get_ev.settled(_) == got : Wr.Dec<Lp.Ev>}
      %Equal.sym(Wr.Dec<Lp.Out>, FLp.get_out(s1), Wr.Got{o, s2}, le.r_out(o, s2)) : {FLp.get_ev.settled.out(k, _) == got : Wr.Dec<Lp.Ev>}
      %le.r_bool(b, s3) : {FLp.get_ev.settled.blocked(k, o, _) == got : Wr.Dec<Lp.Ev>}
      %le.r_nat(now, s4, le.and_r(LawsBase.wire_fits(k), LawsBase.wire_fits(now), h1)) : {FLp.get_ev.settled.now(k, o, b, _) == got : Wr.Dec<Lp.Ev>}
      %le.r_bool(fu, rest) : {FLp.get_ev.settled.funded(k, o, b, now, _) == got : Wr.Dec<Lp.Ev>}
      {==}
    case Lp.Judged{+k, +ev, +b, +now, +fu}:
      -fe = LoopEntry.lp_evid_fits(ev)
      -fn = LawsBase.wire_fits(now)
      +h1 = h
      +h2 = le.and_r(LawsBase.wire_fits(k), Bool.and(fe, fn), h1)
      +s4 = Wr.put_bool(fu, rest)
      +s3 = Wr.put_nat(now, s4)
      +s2 = Wr.put_bool(b, s3)
      +s1 = LoopEntry.lp_spell_evid(ev, s2)
      -got = {Wr.Got{Lp.Judged{k, ev, b, now, fu}, rest} : Wr.Dec<Lp.Ev>}
      %le.r_nat(k, s1, le.and_l(LawsBase.wire_fits(k), Bool.and(fe, fn), h1)) : {FLp.get_ev.judged(_) == got : Wr.Dec<Lp.Ev>}
      %Equal.sym(Wr.Dec<Lp.Evid>, FLp.get_evid(s1), Wr.Got{ev, s2}, le.r_evid(ev, s2, le.and_l(LoopEntry.lp_evid_fits(ev), fn, h2))) : {FLp.get_ev.judged.ev(k, _) == got : Wr.Dec<Lp.Ev>}
      %le.r_bool(b, s3) : {FLp.get_ev.judged.blocked(k, ev, _) == got : Wr.Dec<Lp.Ev>}
      %le.r_nat(now, s4, le.and_r(LoopEntry.lp_evid_fits(ev), fn, h2)) : {FLp.get_ev.judged.now(k, ev, b, _) == got : Wr.Dec<Lp.Ev>}
      %le.r_bool(fu, rest) : {FLp.get_ev.judged.funded(k, ev, b, now, _) == got : Wr.Dec<Lp.Ev>}
      {==}
    case Lp.Restart{}:
      {==}

# a request that fits
def le.r_req(r: FLp.Req, +rest: String, h: {LoopEntry.lp_req_fits(r) == True{} : Bool}) -> {FLp.get_req(LoopEntry.lp_spell_req(r, rest)) == Wr.Got{r, rest} : Wr.Dec<FLp.Req>}:
  match r:
    case FLp.Step{+x, +e}:
      +hh = h
      +s1 = LoopEntry.lp_spell_ev(e, rest)
      %Equal.sym(Wr.Dec<Lp.St>, FLp.get_st(LoopEntry.lp_spell_st(x, s1)), Wr.Got{x, s1}, le.r_st(x, s1, le.and_l(LoopEntry.lp_st_fits(x), LoopEntry.lp_ev_fits(e), hh))) : {FLp.get_req.st(_) == Wr.Got{FLp.Step{x, e}, rest} : Wr.Dec<FLp.Req>}
      %Equal.sym(Wr.Dec<Lp.Ev>, FLp.get_ev(s1), Wr.Got{e, rest}, le.r_ev(e, rest, le.and_r(LoopEntry.lp_st_fits(x), LoopEntry.lp_ev_fits(e), hh))) : {FLp.get_req.ev(x, _) == Wr.Got{FLp.Step{x, e}, rest} : Wr.Dec<FLp.Req>}
      {==}
    case FLp.Verdict{+u, +ev}:
      +s1 = LoopEntry.lp_spell_evid(ev, rest)
      %le.r_bool(u, s1) : {FLp.get_req.until(_) == Wr.Got{FLp.Verdict{u, ev}, rest} : Wr.Dec<FLp.Req>}
      %Equal.sym(Wr.Dec<Lp.Evid>, FLp.get_evid(s1), Wr.Got{ev, rest}, le.r_evid(ev, rest, h)) : {FLp.get_req.evid(u, _) == Wr.Got{FLp.Verdict{u, ev}, rest} : Wr.Dec<FLp.Req>}
      {==}

# the entry on a spelled request that fits, then rest: the request is read
# whole, then the rest decides
def le.spelled(+r: FLp.Req, +rest: String, h: {LoopEntry.lp_req_fits(r) == True{} : Bool}) -> {FLp.ffi(LoopEntry.lp_spell_req(r, rest)) == FLp.ffi.whole(r, Wr.end(rest)) : String}:
  Equal.cong(Wr.Dec<FLp.Req>, String, d => FLp.ffi.go(d), FLp.get_req(LoopEntry.lp_spell_req(r, rest)), Wr.Got{r, rest}, le.r_req(r, rest, h))
