# eukhe: the proof of LAW run_retry_resends_the_request
#
# PROOF: the run and the requests after evs, e, f go on from those after
# evs (rs.run_app, rs.reqs_app). The invariant of
# run_cut_names_the_last_sent (ct.Inv) holds after any inputs (rs.inv);
# in the call phase it says the request sent last is the one the
# requests name. An error that is no cut leaves the context and the note
# as they are and either fails the run or prepares again; preparation
# that ends in a call sends the request the requests name, which is the
# one sent last before the error.

import Base
import ../../bend/run/request.bend as RnRequest
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run/model.bend as Run
import ./run_cut_names_the_last_sent.bend as PCut

# the claim from state s with requests t, by inputs e then f
def rs.goal(+cfg: RnState.Cfg, +s: RnState.St, +t: RnRequest.Reqs, +e: RnState.Ev, +f: RnState.Ev) -> Bool:
  Bool.or(Bool.not(Bool.and(Run.in_call(RnState.St.ph(s)), Run.in_call(RnState.St.ph(RnStep.run.go(e <> f <> Nil{}, cfg, s))))), Run.resent(RnRequest.Reqs.log(RnRequest.reqs.go(e <> f <> Nil{}, cfg, s, t))))

# the run after evs then more goes on from the run after evs
def rs.run_app(evs: List<&2, RnState.Ev>, -more: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +s: RnState.St) -> {RnStep.run.go(more, cfg, RnStep.run.go(evs, cfg, s)) == RnStep.run.go(List.append(&2, RnState.Ev, evs, more), cfg, s) : RnState.St}:
  match evs:
    case Nil{}:
      {==}
    case +e <> rest:
      rs.run_app(rest, more, cfg, RnStep.step(cfg, s, e))

# the requests after evs then more go on from the requests after evs
def rs.reqs_app(evs: List<&2, RnState.Ev>, -more: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +s: RnState.St, +t: RnRequest.Reqs) -> {RnRequest.reqs.go(more, cfg, RnStep.run.go(evs, cfg, s), RnRequest.reqs.go(evs, cfg, s, t)) == RnRequest.reqs.go(List.append(&2, RnState.Ev, evs, more), cfg, s, t) : RnRequest.Reqs}:
  match evs:
    case Nil{}:
      {==}
    case +e <> rest:
      +s2 = RnStep.step(cfg, s, e)
      rs.reqs_app(rest, more, cfg, s2, RnRequest.Reqs.step(RnState.St.ph(s), e, RnState.St.ph(s2), t))

# the invariant holds after any inputs, by induction on the inputs
def rs.inv(evs: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +s: RnState.St, +t: RnRequest.Reqs, i: PCut.ct.Inv(RnState.St.ph(s), t)) -> PCut.ct.Inv(RnState.St.ph(RnStep.run.go(evs, cfg, s)), RnRequest.reqs.go(evs, cfg, s, t)):
  match evs:
    case Nil{}:
      i
    case +e <> rest:
      +s2 = RnStep.step(cfg, s, e)
      rs.inv(rest, cfg, s2, RnRequest.Reqs.step(RnState.St.ph(s), e, RnState.St.ph(s2), t), PCut.ct.step(cfg, s, e, t, i))

# in the call phase the request sent last is the one the requests name
def rs.head(-ctx: Nat, -k: Nat, -note: Nat, -log: List<&2, RnRequest.Sent>, i: PCut.ct.Inv(RnState.Call{}, RnRequest.Reqs{ctx, k, note, log})) -> {Run.sent_last_is(RnRequest.Req{ctx, note}, log) == True{} : Bool}:
  (cu, hd) = i
  hd

# a retry from the call phase prepares again; preparation that ends in a
# call sends the request the requests name
def rs.prep(+cfg: RnState.Cfg, c: Nat, reply: RnState.Reply, -r: Nat, -b: Nat, -n: Nat, -p: Nat, -ctx: Nat, -k: Nat, -note: Nat, -log: List<&2, RnRequest.Sent>, -fin: RnState.Fin, -got: RnState.Got, -fin2: RnState.Fin, -got2: RnState.Got, hd: {Run.sent_last_is(RnRequest.Req{ctx, note}, log) == True{} : Bool}) -> {rs.goal(cfg, RnState.St{RnState.Call{}, r, c, 1n+b, n, p}, RnRequest.Reqs{ctx, k, note, log}, RnState.Go{RnState.Error{True{}, False{}}, fin, got}, RnState.Go{reply, fin2, got2}) == True{} : Bool}:
  match c:
    case 0n:
      match reply:
        case RnState.Overflow{cut}:
          match cut:
            case True{}:
              hd
            case False{}:
              hd
        case RnState.Plain{}:
          hd
        case RnState.Calls{}:
          hd
        case RnState.Deferred{}:
          hd
        case RnState.Error{rt, nt}:
          hd
    case 1n+d:
      match reply:
        case RnState.Overflow{cut}:
          match cut:
            case True{}:
              {==}
            case False{}:
              hd
        case RnState.Plain{}:
          hd
        case RnState.Calls{}:
          hd
        case RnState.Deferred{}:
          hd
        case RnState.Error{rt, nt}:
          hd

# from any requests and state that keep the invariant: an error that is
# no cut, then any reply
def rs.at(+cfg: RnState.Cfg, t: RnRequest.Reqs, s: RnState.St, retryable: Bool, -fin: RnState.Fin, -got: RnState.Got, reply: RnState.Reply, -fin2: RnState.Fin, -got2: RnState.Got, i: PCut.ct.Inv(RnState.St.ph(s), t)) -> {rs.goal(cfg, s, t, RnState.Go{RnState.Error{retryable, False{}}, fin, got}, RnState.Go{reply, fin2, got2}) == True{} : Bool}:
  match t:
    case RnRequest.Reqs{ctx, k, note, log}:
      match s:
        case RnState.St{ph, r, c, a, n, p}:
          match ph:
            case RnState.Call{}:
              match a retryable:
                case 1n+b True{}:
                  rs.prep(cfg, c, reply, r, b, n, p, ctx, k, note, log, fin, got, fin2, got2, rs.head(ctx, k, note, log, i))
                case 1n+b False{}:
                  {==}
                case 0n True{}:
                  {==}
                case 0n False{}:
                  {==}
            case RnState.Prepare{}:
              {==}
            case RnState.Compact{over}:
              {==}
            case RnState.Tools{}:
              {==}
            case RnState.Answered{}:
              {==}
            case RnState.Aborted{}:
              {==}
            case RnState.Failed{why}:
              {==}

def Run.run_retry_resends_the_request(cfg, evs, retryable, fin, got, reply, fin2, got2):
  %rs.run_app(evs, RnState.Go{RnState.Error{retryable, False{}}, fin, got} <> RnState.Go{reply, fin2, got2} <> Nil{}, cfg, RnState.init(cfg)) : {Bool.or(Bool.not(Bool.and(Run.in_call(RnState.St.ph(RnStep.run(cfg, evs))), Run.in_call(RnState.St.ph(_)))), Run.resent(RnRequest.Reqs.log(RnRequest.reqs(cfg, List.append(&2, RnState.Ev, evs, RnState.Go{RnState.Error{retryable, False{}}, fin, got} <> RnState.Go{reply, fin2, got2} <> Nil{}))))) == True{} : Bool}
  %rs.reqs_app(evs, RnState.Go{RnState.Error{retryable, False{}}, fin, got} <> RnState.Go{reply, fin2, got2} <> Nil{}, cfg, RnState.init(cfg), RnRequest.Reqs.init()) : {Bool.or(Bool.not(Bool.and(Run.in_call(RnState.St.ph(RnStep.run(cfg, evs))), Run.in_call(RnState.St.ph(RnStep.run.go(RnState.Go{RnState.Error{retryable, False{}}, fin, got} <> RnState.Go{reply, fin2, got2} <> Nil{}, cfg, RnStep.run.go(evs, cfg, RnState.init(cfg))))))), Run.resent(RnRequest.Reqs.log(_))) == True{} : Bool}
  rs.at(cfg, RnRequest.reqs(cfg, evs), RnStep.run(cfg, evs), retryable, fin, got, reply, fin2, got2, rs.inv(evs, cfg, RnState.init(cfg), RnRequest.Reqs.init(), ({==}, Unit{})))
