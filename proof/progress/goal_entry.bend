# eukhe: the proof of LAW goal_entry

import Base
import ../../bend/ffi_progress.bend as FPr
import ../../bend/progress.bend as Pr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/progress.bend as Progress
import ../base.bend as L

# Progress
# --------

def pw6.prior(p: Maybe<&2, Pr.Prior>, +rest: String, +h: {Progress.wire_prior_fits(p) == True{} : Bool}) -> {Wr.Got{p, rest} == FPr.get_prior(FPr.put_prior(p, rest)) : Wr.Dec<Maybe<&2, Pr.Prior>>}:
  match p:
    case None{}:
      %L.pw6.nat(0n, rest, {==}) : {Wr.Got{None{}, rest} == FPr.get_prior.go(_) : Wr.Dec<Maybe<&2, Pr.Prior>>}
      {==}
    case Some{x}:
      match x:
        case Pr.Prior{+s, +w}:
          %L.pw6.nat(1n, Wr.put_nat(s, Wr.put_nat(w, rest)), {==}) : {Wr.Got{Some{Pr.Prior{s, w}}, rest} == FPr.get_prior.go(_) : Wr.Dec<Maybe<&2, Pr.Prior>>}
          %L.pw6.nat(s, Wr.put_nat(w, rest), L.wr_and_l(LawsBase.wire_fits(s), LawsBase.wire_fits(w), h)) : {Wr.Got{Some{Pr.Prior{s, w}}, rest} == FPr.get_prior.s(_) : Wr.Dec<Maybe<&2, Pr.Prior>>}
          %L.pw6.nat(w, rest, L.wr_and_r(LawsBase.wire_fits(s), LawsBase.wire_fits(w), h)) : {Wr.Got{Some{Pr.Prior{s, w}}, rest} == FPr.get_prior.w(s, _) : Wr.Dec<Maybe<&2, Pr.Prior>>}
          {==}

def Progress.goal_entry(t, cap, p, work, ht, hc, hp, hw):
  +R = FPr.put_goal(Pr.judge(t, cap, p, work), "")
  %L.pw6.nat(t, Wr.put_nat(cap, FPr.put_prior(p, Wr.put_nat(work, ""))), ht) : {FPr.run.t(_) == R : String}
  %L.pw6.nat(cap, FPr.put_prior(p, Wr.put_nat(work, "")), hc) : {FPr.run.cap(t, _) == R : String}
  %pw6.prior(p, Wr.put_nat(work, ""), hp) : {FPr.run.prior(t, cap, _) == R : String}
  %L.pw6.nat(work, "", hw) : {FPr.run.work(t, cap, p, _) == R : String}
  {==}
