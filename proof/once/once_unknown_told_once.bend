# eukhe: the proof of LAW once_unknown_told_once
#
# PROOF: of every world and every event: the reports owed before it plus
# the restarts it journals unknown are the reports owed after it
# (tt.mean, tt.tick, tt.land, tt.end, tt.crash). Only a restart with
# nothing in flight answers, and only a started effect is interrupted:
# its life turns settled unknown from none owed; every other answer and
# event keeps a settled unknown one and makes none. By induction over the
# history (tt.run), from the first world, which is owed none.

import Base
import ../../bend/once.bend as O
import ../../laws/once.bend as Once
import ../../spec/once/life.bend as S
import ./base.bend as LA

# the reports a world is owed
def tt.owed(w: S.World) -> Nat:
  S.told_spec(S.life(w))

def tt.assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+q:
      %tt.assoc(q, b, c) : {1n+Nat.add(Nat.add(q, b), c) == 1n+_ : Nat}
      {==}

# an intent keeps what is owed
def tt.mean(w: S.World, -p: O.Policy) -> {tt.owed(Once.wd_step(w, S.Mean{}, p)) == tt.owed(w) : Nat}:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      match l:
        case O.Absent{}:
          {==}
        case O.Pending{}:
          {==}
        case O.Running{again}:
          {==}
        case O.Ran{}:
          {==}
        case O.Unsure{}:
          {==}
        case O.Void{}:
          {==}

# any answer to a started effect: owed after it are the restarts that
# journal it unknown
def tt.running(v: O.Verdict, again: Nat, n: Nat, k: Nat, d: Nat, x: Nat) -> {tt.owed(Once.wd_answer(v, O.Running{again}, n, k, d, x)) == S.told.verdict(v) : Nat}:
  match v:
    case O.Skip{}:
      {==}
    case O.Launch{}:
      {==}
    case O.Adopt{}:
      {==}
    case O.Interrupt{}:
      {==}
    case O.Abandon{}:
      {==}
    case O.Settled{}:
      {==}

# a restart: owed after it is owed before it plus 1 when it journals the
# effect unknown
def tt.tick(w: S.World, m: O.Mode, look: Bool, p: O.Policy) -> {tt.owed(Once.wd_step(w, S.Tick{m, look}, p)) == Nat.add(tt.owed(w), S.told(Once.wd_live(w), O.recover(S.life(w), S.seen(look, S.lands(w)), m, p))) : Nat}:
  match w:
    case S.Wd{l, live, hit, n, +k, d, x}:
      match l:
        case O.Absent{}:
          match live:
            case True{}:
              {==}
            case False{}:
              {==}
        case O.Pending{}:
          match live:
            case True{}:
              {==}
            case False{}:
              match m:
                case O.Resume{}:
                  {==}
                case O.Stop{}:
                  {==}
        case O.Running{+again}:
          match live:
            case True{}:
              {==}
            case False{}:
              tt.running(O.recover(O.Running{again}, S.seen(look, k), m, p), again, n, k, d, x)
        case O.Ran{}:
          match live:
            case True{}:
              {==}
            case False{}:
              {==}
        case O.Unsure{}:
          match live:
            case True{}:
              {==}
            case False{}:
              {==}
        case O.Void{}:
          match live:
            case True{}:
              {==}
            case False{}:
              {==}

# a land keeps what is owed
def tt.land(w: S.World, -p: O.Policy) -> {tt.owed(Once.wd_step(w, S.Land{}, p)) == tt.owed(w) : Nat}:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      match live:
        case True{}:
          match hit:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          {==}

# an end keeps what is owed
def tt.end(w: S.World, -p: O.Policy) -> {tt.owed(Once.wd_step(w, S.End{}, p)) == tt.owed(w) : Nat}:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      match l:
        case O.Absent{}:
          match live:
            case True{}:
              {==}
            case False{}:
              {==}
        case O.Pending{}:
          match live:
            case True{}:
              {==}
            case False{}:
              {==}
        case O.Running{again}:
          match live:
            case True{}:
              {==}
            case False{}:
              {==}
        case O.Ran{}:
          match live:
            case True{}:
              {==}
            case False{}:
              {==}
        case O.Unsure{}:
          match live:
            case True{}:
              {==}
            case False{}:
              {==}
        case O.Void{}:
          match live:
            case True{}:
              {==}
            case False{}:
              {==}

# a crash keeps what is owed
def tt.crash(w: S.World, -p: O.Policy) -> {tt.owed(Once.wd_step(w, S.Crash{}, p)) == tt.owed(w) : Nat}:
  match w:
    case S.Wd{l, live, hit, n, k, d, x}:
      {==}

# owed after the events es: owed before them plus the restarts that
# journal the effect unknown
def tt.run(es: List<&2, S.Ev>, +w: S.World, +p: O.Policy) -> {Nat.add(tt.owed(w), Once.wd_told(es, w, p)) == tt.owed(Once.wd_run(es, w, p)) : Nat}:
  match es:
    case Nil{}:
      LA.ob.add_zero(tt.owed(w))
    case e <> rest:
      match e:
        case S.Mean{}:
          %tt.mean(w, p) : {Nat.add(_, Once.wd_told(rest, Once.wd_step(w, S.Mean{}, p), p)) == tt.owed(Once.wd_run(rest, Once.wd_step(w, S.Mean{}, p), p)) : Nat}
          tt.run(rest, Once.wd_step(w, S.Mean{}, p), p)
        case S.Tick{+m, +look}:
          %tt.assoc(tt.owed(w), S.told(Once.wd_live(w), O.recover(S.life(w), S.seen(look, S.lands(w)), m, p)), Once.wd_told(rest, Once.wd_step(w, S.Tick{m, look}, p), p)) : {_ == tt.owed(Once.wd_run(rest, Once.wd_step(w, S.Tick{m, look}, p), p)) : Nat}
          %tt.tick(w, m, look, p) : {Nat.add(_, Once.wd_told(rest, Once.wd_step(w, S.Tick{m, look}, p), p)) == tt.owed(Once.wd_run(rest, Once.wd_step(w, S.Tick{m, look}, p), p)) : Nat}
          tt.run(rest, Once.wd_step(w, S.Tick{m, look}, p), p)
        case S.Land{}:
          %tt.land(w, p) : {Nat.add(_, Once.wd_told(rest, Once.wd_step(w, S.Land{}, p), p)) == tt.owed(Once.wd_run(rest, Once.wd_step(w, S.Land{}, p), p)) : Nat}
          tt.run(rest, Once.wd_step(w, S.Land{}, p), p)
        case S.End{}:
          %tt.end(w, p) : {Nat.add(_, Once.wd_told(rest, Once.wd_step(w, S.End{}, p), p)) == tt.owed(Once.wd_run(rest, Once.wd_step(w, S.End{}, p), p)) : Nat}
          tt.run(rest, Once.wd_step(w, S.End{}, p), p)
        case S.Crash{}:
          %tt.crash(w, p) : {Nat.add(_, Once.wd_told(rest, Once.wd_step(w, S.Crash{}, p), p)) == tt.owed(Once.wd_run(rest, Once.wd_step(w, S.Crash{}, p), p)) : Nat}
          tt.run(rest, Once.wd_step(w, S.Crash{}, p), p)

def Once.once_unknown_told_once(p, es):
  tt.run(es, S.w0(), p)
