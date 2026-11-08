# eukhe: the proof of LAW restart_ffi_exact
#
# PROOF: the entry's decoder takes, stage by stage, the same branches on
# the same wire primitives as the spec's reader (svx.k .. svx.gap), so it
# reads every input as the spec does. On a request with nothing after it
# the entry answers the model's decision, which computes to the kept ages
# and the verdict on their count; the kept ages are the spec's window
# (LA.ps.rs_window), the verdict the spec's (PV.ps.rs_verdict), spelled as
# the spec spells it (svx.verdict). The two error texts are the spec's.

import Base
import ../../bend/ffi_supervise.bend as FS
import ../../bend/supervise.bend as Su
import ../../bend/wire.bend as Wr
import ../../laws/supervise.bend as Supervise
import ./base.bend as LA
import ./restart_decide_verdict.bend as PV

def svx.gap(+c: Su.Cfg, +a: List<&2, Nat>, d: Wr.Dec<Nat>) -> {FS.get_req.gap(c, a, d) == Supervise.sv_read.gap(c, a, d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{g, s}:
      {==}
    case Wr.Bad{}:
      {==}

def svx.ages(+c: Su.Cfg, d: Wr.Dec<List<&2, Nat>>) -> {FS.get_req.ages(c, d) == Supervise.sv_read.ages(c, d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{+a, +s}:
      svx.gap(c, a, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def svx.m(+k: Nat, +w: Nat, +b: Nat, d: Wr.Dec<Nat>) -> {FS.get_req.cfg(FS.get_cfg.m(k, w, b, d)) == Supervise.sv_read.m(k, w, b, d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{+m, +s}:
      svx.ages(Su.Cfg{k, w, b, m}, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      {==}

def svx.b(+k: Nat, +w: Nat, d: Wr.Dec<Nat>) -> {FS.get_req.cfg(FS.get_cfg.b(k, w, d)) == Supervise.sv_read.b(k, w, d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{+b, +s}:
      svx.m(k, w, b, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def svx.w(+k: Nat, d: Wr.Dec<Nat>) -> {FS.get_req.cfg(FS.get_cfg.w(k, d)) == Supervise.sv_read.w(k, d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{+w, +s}:
      svx.b(k, w, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

# the entry's decoder reads as the spec's reader
def svx.k(d: Wr.Dec<Nat>) -> {FS.get_req.cfg(FS.get_cfg.k(d)) == Supervise.sv_read.k(d) : Wr.Dec<FS.Req>}:
  match d:
    case Wr.Got{+k, +s}:
      svx.w(k, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def svx.verdict(v: Su.Verdict) -> {FS.put_verdict(v, "") == Supervise.sv_verdict(v, "") : String}:
  match v:
    case Su.Relaunch{f, b}:
      {==}
    case Su.GiveUp{f}:
      {==}

# the entry's reply to a whole request is the spec's
def svx.reply(q: FS.Req) -> {FS.put_reply(FS.decide(q), "") == Supervise.sv_reply(q) : String}:
  match q:
    case FS.Req{c, +a, +g}:
      match c:
        case Su.Cfg{+k, +w, +b, +m}:
          +kw = Su.keep(w, Su.older(g, a))
          +rw = Supervise.restart_window(w, g, a)
          +c2 = {Su.Cfg{k, w, b, m} : Su.Cfg}
          %Equal.sym(List<&2, Nat>, kw, rw, LA.ps.rs_window(w, g, a)) : {Wr.put_list(~Nat, ~Wr.put_nat, 0n <> _, FS.put_verdict(Su.verdict.put(Nat.is_lt(k, 1n+List.length(&2, Nat, _)), c2, 1n+List.length(&2, Nat, _)), "")) == Supervise.sv_reply(FS.Req{c2, a, g}) : String}
          +n = {1n+List.length(&2, Nat, rw) : Nat}
          %Equal.sym(Su.Verdict, Su.verdict.put(Nat.is_lt(k, n), c2, n), Supervise.restart_verdict_put(Nat.is_lt(k, n), c2, n), PV.ps.rs_verdict(Nat.is_lt(k, n), c2, n)) : {Wr.put_list(~Nat, ~Wr.put_nat, 0n <> rw, FS.put_verdict(_, "")) == Supervise.sv_reply(FS.Req{c2, a, g}) : String}
          +v = Supervise.restart_verdict_put(Nat.is_lt(k, n), c2, n)
          %Equal.sym(String, FS.put_verdict(v, ""), Supervise.sv_verdict(v, ""), svx.verdict(v)) : {Wr.put_list(~Nat, ~Wr.put_nat, 0n <> rw, _) == Supervise.sv_reply(FS.Req{c2, a, g}) : String}
          {==}

def svx.end(q: FS.Req, r: String) -> {FS.ffi.fin(Wr.end(r), q) == Supervise.sv_entry.of(Wr.Got{q, r}) : String}:
  match r:
    case SNil{}:
      svx.reply(q)
    case SCon{c, t}:
      {==}

def svx.go(d: Wr.Dec<FS.Req>) -> {FS.ffi.go(d) == Supervise.sv_entry.of(d) : String}:
  match d:
    case Wr.Got{q, r}:
      svx.end(q, r)
    case Wr.Bad{}:
      {==}

def Supervise.restart_ffi_exact(s):
  %svx.k(Wr.get_nat(s)) : {FS.ffi(s) == Supervise.sv_entry.of(_) : String}
  svx.go(FS.get_req(s))
