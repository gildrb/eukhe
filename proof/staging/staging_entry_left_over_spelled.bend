# eukhe: the proof of LAW staging_entry_left_over_spelled
#
# PROOF: a spelled request that fits reads back whole with the rest after
# it untouched (slo.req: staging_entry_answers' item lemmas, which carry
# any rest); the end check then sees the char left and answers the
# left-over error.

import Base
import ../../bend/ffi_staging.bend as FSg
import ../../bend/staging.bend as Sg
import ../../bend/listing.bend as Ls
import ../../bend/wire.bend as Wr
import ../../laws/staging.bend as Staging
import ./staging_entry_answers.bend as PA

# the times of a judge request, after its tags (c and l concrete)
def slo.judge.t(-c: Sg.Cand, -l: Sg.Lock, +now: Sg.Time, +own: Sg.Time, +inner: List<&2, Sg.Time>, +rest: String,
  e1: {FSg.get_time(Staging.sp_w_time(now, Staging.sp_w_time(own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, rest)))) == Wr.Got{now, Staging.sp_w_time(own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, rest))} : Wr.Dec<Sg.Time>},
  e2: {FSg.get_time(Staging.sp_w_time(own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, rest))) == Wr.Got{own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, rest)} : Wr.Dec<Sg.Time>},
  e3: {Wr.get_list(~Sg.Time, ~FSg.get_time, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, rest)) == Wr.Got{inner, rest} : Wr.Dec<List<&2, Sg.Time>>}) ->
  {FSg.get_judge.now(c, l, FSg.get_time(Staging.sp_w_time(now, Staging.sp_w_time(own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, rest))))) == Wr.Got{FSg.Judge{c, l, now, own, inner}, rest} : Wr.Dec<FSg.Req>}:
  %Equal.sym(Wr.Dec<Sg.Time>, FSg.get_time(Staging.sp_w_time(now, Staging.sp_w_time(own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, rest)))), Wr.Got{now, Staging.sp_w_time(own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, rest))}, e1) : {FSg.get_judge.now(c, l, _) == Wr.Got{FSg.Judge{c, l, now, own, inner}, rest} : Wr.Dec<FSg.Req>}
  %Equal.sym(Wr.Dec<Sg.Time>, FSg.get_time(Staging.sp_w_time(own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, rest))), Wr.Got{own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, rest)}, e2) : {FSg.get_judge.own(c, l, now, _) == Wr.Got{FSg.Judge{c, l, now, own, inner}, rest} : Wr.Dec<FSg.Req>}
  %Equal.sym(Wr.Dec<List<&2, Sg.Time>>, Wr.get_list(~Sg.Time, ~FSg.get_time, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, rest)), Wr.Got{inner, rest}, e3) : {FSg.get_judge.inner(c, l, now, own, _) == Wr.Got{FSg.Judge{c, l, now, own, inner}, rest} : Wr.Dec<FSg.Req>}
  {==}

# the body of a judge request reads back, its times by the lemmas e1 e2 e3
def slo.judge(c: Sg.Cand, l: Sg.Lock, +now: Sg.Time, +own: Sg.Time, +inner: List<&2, Sg.Time>, +rest: String,
  e1: {FSg.get_time(Staging.sp_w_time(now, Staging.sp_w_time(own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, rest)))) == Wr.Got{now, Staging.sp_w_time(own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, rest))} : Wr.Dec<Sg.Time>},
  e2: {FSg.get_time(Staging.sp_w_time(own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, rest))) == Wr.Got{own, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, rest)} : Wr.Dec<Sg.Time>},
  e3: {Wr.get_list(~Sg.Time, ~FSg.get_time, Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, rest)) == Wr.Got{inner, rest} : Wr.Dec<List<&2, Sg.Time>>}) ->
  {FSg.get_req(Staging.sp_w_req(FSg.Judge{c, l, now, own, inner}, rest)) == Wr.Got{FSg.Judge{c, l, now, own, inner}, rest} : Wr.Dec<FSg.Req>}:
  match c l:
    case Sg.CDir{} Sg.LHeld{}:
      slo.judge.t(Sg.CDir{}, Sg.LHeld{}, now, own, inner, rest, e1, e2, e3)
    case Sg.CDir{} Sg.LFree{}:
      slo.judge.t(Sg.CDir{}, Sg.LFree{}, now, own, inner, rest, e1, e2, e3)
    case Sg.CDir{} Sg.LAbsent{}:
      slo.judge.t(Sg.CDir{}, Sg.LAbsent{}, now, own, inner, rest, e1, e2, e3)
    case Sg.CLock{} Sg.LHeld{}:
      slo.judge.t(Sg.CLock{}, Sg.LHeld{}, now, own, inner, rest, e1, e2, e3)
    case Sg.CLock{} Sg.LFree{}:
      slo.judge.t(Sg.CLock{}, Sg.LFree{}, now, own, inner, rest, e1, e2, e3)
    case Sg.CLock{} Sg.LAbsent{}:
      slo.judge.t(Sg.CLock{}, Sg.LAbsent{}, now, own, inner, rest, e1, e2, e3)

# a spelled request that fits reads back, the rest after it untouched
def slo.req(r: FSg.Req, +rest: String, h: {Staging.sp_fit_req(r) == True{} : Bool}) -> {FSg.get_req(Staging.sp_w_req(r, rest)) == Wr.Got{r, rest} : Wr.Dec<FSg.Req>}:
  match r:
    case FSg.Publish{b}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case FSg.Meet{+es}:
      %Equal.sym(Wr.Dec<List<&2, Sg.Seen>>, Wr.get_list(~Sg.Seen, ~FSg.get_seen, Wr.put_list(~Sg.Seen, ~Staging.sp_w_seen, es, rest)), Wr.Got{es, rest}, PA.se.seens_rt(es, rest, h)) : {FSg.get_meet(_) == Wr.Got{FSg.Meet{es}, rest} : Wr.Dec<FSg.Req>}
      {==}
    case FSg.Judge{c, l, +now, +own, +inner}:
      +hh = h
      +rest2 = Wr.put_list(~Sg.Time, ~Staging.sp_w_time, inner, rest)
      +rest1 = Staging.sp_w_time(own, rest2)
      +h_now = PA.se.and_l(Staging.sp_fit_time(now), Bool.and(Staging.sp_fit_time(own), Staging.sp_fit_times(inner)), hh)
      +h_own = PA.se.and_l(Staging.sp_fit_time(own), Staging.sp_fit_times(inner), PA.se.and_r(Staging.sp_fit_time(now), Bool.and(Staging.sp_fit_time(own), Staging.sp_fit_times(inner)), hh))
      +h_in = PA.se.and_r(Staging.sp_fit_time(own), Staging.sp_fit_times(inner), PA.se.and_r(Staging.sp_fit_time(now), Bool.and(Staging.sp_fit_time(own), Staging.sp_fit_times(inner)), hh))
      slo.judge(c, l, now, own, inner, rest, PA.se.time(now, rest1, h_now), PA.se.time(own, rest2, h_own), PA.se.times_rt(inner, rest, h_in))
    case FSg.Scan{+es}:
      %Equal.sym(Wr.Dec<List<&2, Sg.Seen>>, Wr.get_list(~Sg.Seen, ~FSg.get_seen, Wr.put_list(~Sg.Seen, ~Staging.sp_w_seen, es, rest)), Wr.Got{es, rest}, PA.se.seens_rt(es, rest, h)) : {FSg.get_scan(_) == Wr.Got{FSg.Scan{es}, rest} : Wr.Dec<FSg.Req>}
      {==}
    case FSg.Rows{+os}:
      %Equal.sym(Wr.Dec<List<&2, Ls.Obs>>, Wr.get_list(~Ls.Obs, ~FSg.get_obs, Wr.put_list(~Ls.Obs, ~Staging.sp_w_obs, os, rest)), Wr.Got{os, rest}, PA.se.obss_rt(os, rest, h)) : {FSg.get_rows(_) == Wr.Got{FSg.Rows{os}, rest} : Wr.Dec<FSg.Req>}
      {==}

def Staging.staging_entry_left_over_spelled(r, h, c, t):
  %Equal.sym(Wr.Dec<FSg.Req>, FSg.get_req(Staging.sp_w_req(r, SCon{c, t})), Wr.Got{r, SCon{c, t}}, slo.req(r, SCon{c, t}, h)) : {FSg.answer(_) == Wr.err("staging: input left over") : String}
  {==}
