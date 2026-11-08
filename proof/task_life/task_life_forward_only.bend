# eukhe: the proof of LAW task_life_forward_only
#
# PROOF: case on the state and the transition: the measure never falls
# (concrete ranks compute), but a handover or a resume of a running task,
# which lands at its own checkpoint (Nat.is_eq(c, c), cb_nat_refl).

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

def tlf.step(+s: Tl.St, e: Tl.Ev) -> {Sp.forward_ok(s, Tl.step(s, e)) == True{} : Bool}:
  match s:
    case Tl.Pending{c}:
      match e:
        case Tl.Reserve{}:
          {==}
        case Tl.Commit{n, h}:
          {==}
        case Tl.Requeue{}:
          {==}
        case Tl.Settle{o, h}:
          match h:
            case True{}:
              {==}
            case False{}:
              {==}
        case Tl.Finalize{h}:
          {==}
    case Tl.Running{+c}:
      match e:
        case Tl.Reserve{}:
          {==}
        case Tl.Commit{n, h}:
          match n:
            case Tl.NRun{d}:
              {==}
            case Tl.NWait{d, p}:
              {==}
            case Tl.NEnd{o}:
              match h:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case Tl.Requeue{}:
          LNat.cb_nat_refl(c)
        case Tl.Settle{o, h}:
          match h:
            case True{}:
              {==}
            case False{}:
              {==}
        case Tl.Finalize{h}:
          {==}
    case Tl.Waiting{c, p}:
      match e:
        case Tl.Reserve{}:
          {==}
        case Tl.Commit{n, h}:
          {==}
        case Tl.Requeue{}:
          {==}
        case Tl.Settle{o, h}:
          match h:
            case True{}:
              {==}
            case False{}:
              {==}
        case Tl.Finalize{h}:
          {==}
    case Tl.Completing{o}:
      match e:
        case Tl.Reserve{}:
          {==}
        case Tl.Commit{n, h}:
          {==}
        case Tl.Requeue{}:
          {==}
        case Tl.Settle{q, h}:
          {==}
        case Tl.Finalize{h}:
          match h:
            case True{}:
              {==}
            case False{}:
              {==}
    case Tl.Terminal{o}:
      {==}

def tlf.resume(+s: Tl.St) -> {Sp.forward_ok(s, Done{Sp.resumed(Tl.resume(s))}) == True{} : Bool}:
  match s:
    case Tl.Pending{c}:
      {==}
    case Tl.Running{+c}:
      LNat.cb_nat_refl(c)
    case Tl.Waiting{c, p}:
      {==}
    case Tl.Completing{o}:
      {==}
    case Tl.Terminal{o}:
      {==}

def TaskLife.task_life_forward_only(s, e):
  (tlf.step(s, e), tlf.resume(s))
