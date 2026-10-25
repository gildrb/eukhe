# eukhe: the proof of LAW goal_entry_malformed_exact
# The laws' reader and the entry read each stage alike; where the reader
# finds no whole request, the entry answers its error form.

import Base
import ../../laws/progress.bend as Progress
import ../../bend/ffi_progress.bend as FPr
import ../../bend/progress.bend as Pr
import ../../bend/wire.bend as Wr
import ../base/progress.bend as LProgress

def gme.w(+s: Nat, r: Wr.Dec<Nat>) -> {Progress.gs_read_prior.w(s, r) == FPr.get_prior.w(s, r) : Wr.Dec<Maybe<&2, Pr.Prior>>}:
  match r:
    case Wr.Got{w, rest}:
      {==}
    case Wr.Bad{}:
      {==}

def gme.s(r: Wr.Dec<Nat>) -> {Progress.gs_read_prior.s(r) == FPr.get_prior.s(r) : Wr.Dec<Maybe<&2, Pr.Prior>>}:
  match r:
    case Wr.Got{+s, rest}:
      gme.w(s, Wr.get_nat(rest))
    case Wr.Bad{}:
      {==}

def gme.tag(n: Nat, s: String) -> {Progress.gs_read_prior.tag(n, s) == FPr.get_prior.tag(n, s) : Wr.Dec<Maybe<&2, Pr.Prior>>}:
  match n:
    case 0n:
      {==}
    case 1n:
      gme.s(Wr.get_nat(s))
    case 2n+q:
      {==}

# the laws' reader of a prior is the entry's
def gme.prior_eq(r: Wr.Dec<Nat>) -> {Progress.gs_read_prior.go(r) == FPr.get_prior.go(r) : Wr.Dec<Maybe<&2, Pr.Prior>>}:
  match r:
    case Wr.Got{n, s}:
      gme.tag(n, s)
    case Wr.Bad{}:
      {==}

def gme.end(b: Bool, +t: Nat, +cap: Nat, p: Maybe<&2, Pr.Prior>, +work: Nat, no: {Progress.gs_read.end(b, Progress.gs.Req{t, cap, p, work}) == None{} : Maybe<&2, Progress.gs.Req>}) -> {FPr.run.end(b, t, cap, p, work) == SCon{'E', SCon{' ', "progress: malformed request"}} : String}:
  match b:
    case True{}:
      LProgress.pw.some_none(Progress.gs.Req, Progress.gs.Req{t, cap, p, work}, {FPr.put_goal(Pr.judge(t, cap, p, work), "") == SCon{'E', SCon{' ', "progress: malformed request"}} : String}, no)
    case False{}:
      {==}

def gme.work(+t: Nat, +cap: Nat, p: Maybe<&2, Pr.Prior>, r: Wr.Dec<Nat>, no: {Progress.gs_read.work(t, cap, p, r) == None{} : Maybe<&2, Progress.gs.Req>}) -> {FPr.run.work(t, cap, p, r) == SCon{'E', SCon{' ', "progress: malformed request"}} : String}:
  match r:
    case Wr.Got{+work, s}:
      gme.end(Wr.end(s), t, cap, p, work, no)
    case Wr.Bad{}:
      {==}

def gme.prior(+t: Nat, +cap: Nat, r: Wr.Dec<Maybe<&2, Pr.Prior>>, no: {Progress.gs_read.prior(t, cap, r) == None{} : Maybe<&2, Progress.gs.Req>}) -> {FPr.run.prior(t, cap, r) == SCon{'E', SCon{' ', "progress: malformed request"}} : String}:
  match r:
    case Wr.Got{p, s}:
      gme.work(t, cap, p, Wr.get_nat(s), no)
    case Wr.Bad{}:
      {==}

def gme.cap(+t: Nat, r: Wr.Dec<Nat>, no: {Progress.gs_read.cap(t, r) == None{} : Maybe<&2, Progress.gs.Req>}) -> {FPr.run.cap(t, r) == SCon{'E', SCon{' ', "progress: malformed request"}} : String}:
  match r:
    case Wr.Got{+cap, +s}:
      %gme.prior_eq(Wr.get_nat(s)) : {FPr.run.prior(t, cap, _) == SCon{'E', SCon{' ', "progress: malformed request"}} : String}
      gme.prior(t, cap, Progress.gs_read_prior.go(Wr.get_nat(s)), no)
    case Wr.Bad{}:
      {==}

def gme.t(r: Wr.Dec<Nat>, no: {Progress.gs_read.t(r) == None{} : Maybe<&2, Progress.gs.Req>}) -> {FPr.run.t(r) == SCon{'E', SCon{' ', "progress: malformed request"}} : String}:
  match r:
    case Wr.Got{+t, s}:
      gme.cap(t, Wr.get_nat(s), no)
    case Wr.Bad{}:
      {==}

def Progress.goal_entry_malformed_exact(s, no):
  gme.t(Wr.get_nat(s), no)
