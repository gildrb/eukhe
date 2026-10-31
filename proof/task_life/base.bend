# eukhe: lemmas shared by the proofs of area task_life: the rules' helpers
# are the spec's (an outcome decided, a commit, any and some, the join
# marks, intent and reason of a cascade)

import Base
import ../../bend/task_life.bend as Tl
import ../../bend/ffi_task_life.bend as FTl
import ../../bend/submission.bend as Sb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../spec/durable/task_life.bend as Sp
import ../../laws/task_life.bend as TaskLife
import ../base/nat.bend as LNat

# Transitions
# -----------

# an outcome decided is the spec's
def tlb.hold(o: Tl.Outcome, h: Bool) -> {Tl.decided(o, h) == Sp.hold_spec(o, h) : Result<&2, &2, Tl.Why, Tl.St>}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

# what a running task commits is the spec's
def tlb.commit(n: Tl.Next, h: Bool) -> {Tl.commit(n, h) == Sp.committed_spec(n, h) : Result<&2, &2, Tl.Why, Tl.St>}:
  match n:
    case Tl.NRun{c}:
      {==}
    case Tl.NWait{c, p}:
      {==}
    case Tl.NEnd{o}:
      tlb.hold(o, h)

# Join
# ----

# any is the spec's some
def tlb.any(xs: List<&2, Bool>) -> {Tl.any(xs) == Sp.some(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      match x:
        case True{}:
          {==}
        case False{}:
          tlb.any(t)

# no marks are the spec's
def tlb.keep(xs: List<&2, Bool>) -> {Tl.keep_all(xs) == Sp.none_marked(xs) : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %tlb.keep(t) : {False{} <> Tl.keep_all(t) == False{} <> _ : List<&2, Bool>}
      {==}

# without a failure, failFast marks nothing
def tlb.ff_none(xs: List<&2, Bool>, fs: List<&2, Bool>) -> {Tl.keep_all(xs) == Sp.ff_marks(xs, fs, False{}) : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %tlb.ff_none(t, Sp.flags_tail(fs)) : {False{} <> Tl.keep_all(t) == False{} <> _ : List<&2, Bool>}
      {==}

# after a failure, failFast marks each live task that did not fail
def tlb.ff_hit(xs: List<&2, Bool>, fs: List<&2, Bool>) -> {Tl.abort_others(xs, fs) == Sp.ff_marks(xs, fs, True{}) : List<&2, Bool>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      match x:
        case True{}:
          match fs:
            case Nil{}:
              %tlb.ff_hit(t, Nil{}) : {True{} <> Tl.abort_others(t, Nil{}) == True{} <> _ : List<&2, Bool>}
              {==}
            case f <> u:
              %tlb.ff_hit(t, u) : {Bool.not(f) <> Tl.abort_others(t, u) == Bool.not(f) <> _ : List<&2, Bool>}
              {==}
        case False{}:
          match fs:
            case Nil{}:
              %tlb.ff_hit(t, Nil{}) : {False{} <> Tl.abort_others(t, Nil{}) == False{} <> _ : List<&2, Bool>}
              {==}
            case f <> u:
              %tlb.ff_hit(t, u) : {False{} <> Tl.abort_others(t, u) == False{} <> _ : List<&2, Bool>}
              {==}

# Cascades
# --------

def tlb.intent_res(m: Tl.Mark, r: Tl.Res) -> {Bool.or(Tl.marked(m), Tl.res_failed(r)) == Bool.or(Nat.is_lt(0n, Sp.mark_rank(m)), Bool.not(Sp.res_ok(r))) : Bool}:
  match m:
    case Tl.Clear{}:
      match r:
        case Tl.RCompleted{}:
          {==}
        case Tl.RFailed{}:
          {==}
        case Tl.RAborted{}:
          {==}
        case Tl.ROrphaned{}:
          {==}
        case Tl.RFaulted{}:
          {==}
    case Tl.Restart{}:
      {==}
    case Tl.Request{}:
      {==}

def tlb.intent_live(m: Tl.Mark) -> {Bool.or(Tl.marked(m), False{}) == Bool.or(Nat.is_lt(0n, Sp.mark_rank(m)), False{}) : Bool}:
  match m:
    case Tl.Clear{}:
      {==}
    case Tl.Restart{}:
      {==}
    case Tl.Request{}:
      {==}

# an owner's intent is the spec's
def tlb.intent(s: Tl.St, m: Tl.Mark) -> {Tl.intent(s, m) == Sp.intent_spec(s, m) : Bool}:
  match s:
    case Tl.Pending{c}:
      tlb.intent_live(m)
    case Tl.Running{c}:
      tlb.intent_live(m)
    case Tl.Waiting{c, p}:
      tlb.intent_live(m)
    case Tl.Completing{o}:
      match o:
        case Tl.Outcome{r, h}:
          tlb.intent_res(m, r)
    case Tl.Terminal{o}:
      {==}

def tlb.reason_res(r: Tl.Res) -> {Tl.reason.restart(Tl.res_failed(r)) == Sp.pick_mark(Bool.not(Bool.not(Sp.res_ok(r))), Tl.Restart{}, Tl.Request{}) : Tl.Mark}:
  match r:
    case Tl.RCompleted{}:
      {==}
    case Tl.RFailed{}:
      {==}
    case Tl.RAborted{}:
      {==}
    case Tl.ROrphaned{}:
      {==}
    case Tl.RFaulted{}:
      {==}

def tlb.reason_restart(s: Tl.St) -> {Tl.reason(s, Tl.Restart{}) == Sp.reason_spec(s, Tl.Restart{}) : Tl.Mark}:
  match s:
    case Tl.Pending{c}:
      {==}
    case Tl.Running{c}:
      {==}
    case Tl.Waiting{c, p}:
      {==}
    case Tl.Completing{o}:
      match o:
        case Tl.Outcome{r, h}:
          tlb.reason_res(r)
    case Tl.Terminal{o}:
      match o:
        case Tl.Outcome{r, h}:
          tlb.reason_res(r)

# the reason an owner passes on is the spec's
def tlb.reason(+s: Tl.St, m: Tl.Mark) -> {Tl.reason(s, m) == Sp.reason_spec(s, m) : Tl.Mark}:
  match m:
    case Tl.Clear{}:
      {==}
    case Tl.Restart{}:
      tlb.reason_restart(s)
    case Tl.Request{}:
      {==}
