# eukhe: the proof of LAW child_read_never_wakes
# Under K a read submission stands newest only (every older one is
# withdrawn), so a read report is the newest submission, read (pc.Rd).
# Every step keeps it: the report rule ends the task on it, the parent's
# acts leave it read, its read reads it again; the older submissions stay
# withdrawn, so none is queued or placed.

import Base
import ../../bend/child.bend as Ch
import ../../laws/child/model.bend as Child
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

def pc.rd(f: Ch.Fate) -> Bool:
  match f:
    case Ch.Queued{}:
      False{}
    case Ch.Withdrawn{}:
      False{}
    case Ch.Placed{}:
      False{}
    case Ch.Read{}:
      True{}

# the newest submission is read
def pc.Rd(inbox: List<&2, Ch.Sub>) -> Bool:
  match inbox:
    case Nil{}:
      False{}
    case s <> rest:
      match s:
        case Ch.Sub{i, f}:
          pc.rd(f)

# a submission is not read and withdrawn at once
def pc.rd_w(-A: Type, f: Ch.Fate, r: {pc.rd(f) == True{} : Bool}, w: {LA.pc.isW(f) == True{} : Bool}) -> A:
  match f:
    case Ch.Queued{}:
      LLogicLogic.child.pc.absurd(A, r)
    case Ch.Withdrawn{}:
      LLogicLogic.child.pc.absurd(A, r)
    case Ch.Placed{}:
      LLogicLogic.child.pc.absurd(A, r)
    case Ch.Read{}:
      LLogicLogic.child.pc.absurd(A, w)

def pc.zero_one(-A: Type, x: Nat, z: {0n == x : Nat}, e: {x == 1n : Nat}) -> A:
  match x:
    case 0n:
      LLogicLogic.zero_succ(A, 0n, e)
    case 1n+p:
      LLogicLogic.zero_succ(A, p, z)

# a report the parent read once is the newest submission, read
def pc.rd_of(inbox: List<&2, Ch.Sub>, +kin: {LA.pc.Kin(inbox) == True{} : Bool}, e: {Ch.reads(inbox) == 1n : Nat}) -> {pc.Rd(inbox) == True{} : Bool}:
  match inbox:
    case Nil{}:
      LLogicLogic.zero_succ({pc.Rd(Nil{}) == True{} : Bool}, 0n, e)
    case s <> +rest:
      match s:
        case Ch.Sub{+m, f}:
          match f:
            case Ch.Queued{}:
              pc.zero_one({pc.Rd(Ch.Sub{m, Ch.Queued{}} <> rest) == True{} : Bool}, Ch.reads(rest), LA.pc.old_reads(rest, m, kin), e)
            case Ch.Withdrawn{}:
              pc.zero_one({pc.Rd(Ch.Sub{m, Ch.Withdrawn{}} <> rest) == True{} : Bool}, Ch.reads(rest), LA.pc.old_reads(rest, m, kin), e)
            case Ch.Placed{}:
              pc.zero_one({pc.Rd(Ch.Sub{m, Ch.Placed{}} <> rest) == True{} : Bool}, Ch.reads(rest), LA.pc.old_reads(rest, m, kin), e)
            case Ch.Read{}:
              {==}

# the report rule leaves the inbox as it is (it submits only when no
# submission n exists: never on a read one)
def pc.rd_owe.at(same: Bool, kr: Ch.Report, +n: Nat, +m: Nat, +f: Ch.Fate, +rest: List<&2, Ch.Sub>, open: Bool, kph: {LA.pc.Kowe.at(same, n, m, f) == True{} : Bool}, r: {pc.rd(f) == True{} : Bool}) -> {pc.Rd(Ch.St.inbox(Ch.owe(Maybe.or(&2, Ch.Fate, Ch.fate.here(same, f), Ch.fate(rest, n)), kr, n, open, Ch.Sub{m, f} <> rest))) == True{} : Bool}:
  match same:
    case True{}:
      match f:
        case Ch.Queued{}:
          r
        case Ch.Withdrawn{}:
          r
        case Ch.Placed{}:
          r
        case Ch.Read{}:
          {==}
    case False{}:
      pc.rd_w({pc.Rd(Ch.St.inbox(Ch.owe(Maybe.or(&2, Ch.Fate, Ch.fate.here(False{}, f), Ch.fate(rest, n)), kr, n, open, Ch.Sub{m, f} <> rest))) == True{} : Bool}, f, r, LA.pc.and_r(Nat.is_eq(1n+m, n), LA.pc.isW(f), kph))

def pc.rd_owe(inbox: List<&2, Ch.Sub>, kr: Ch.Report, +n: Nat, open: Bool, kph: {LA.pc.Kowe(inbox, n) == True{} : Bool}, r: {pc.Rd(inbox) == True{} : Bool}) -> {pc.Rd(Ch.St.inbox(Ch.owe(Ch.fate(inbox, n), kr, n, open, inbox))) == True{} : Bool}:
  match inbox:
    case Nil{}:
      LLogicLogic.child.pc.absurd({pc.Rd(Ch.St.inbox(Ch.owe(Ch.fate(Nil{}, n), kr, n, open, Nil{}))) == True{} : Bool}, r)
    case s <> rest:
      match s:
        case Ch.Sub{+m, f}:
          pc.rd_owe.at(Nat.is_eq(m, n), kr, n, m, f, rest, open, kph, r)

def pc.rd_poll(cut: Maybe<&2, Bool>, ph: Ch.Ph, +inbox: List<&2, Ch.Sub>, +open: Bool, +cfg: Ch.Cfg, +dt: Nat, +o: Ch.Obs, kph: {LA.pc.Kph(ph, inbox) == True{} : Bool}, +r: {pc.Rd(inbox) == True{} : Bool}) -> {pc.Rd(Ch.St.inbox(Ch.task(cfg, ph, cut, open, inbox, dt, o))) == True{} : Bool}:
  match cut:
    case None{}:
      match ph:
        case Ch.Watching{w}:
          r
        case Ch.Owing{kr, +n}:
          pc.rd_owe(inbox, kr, n, open, kph, r)
        case Ch.Ended{}:
          r
    case Some{del}:
      r

# the parent's acts settle only queued submissions: a read one stays read
def pc.rd_fact(f: Ch.Fate, +a: Ch.Act, +i: Nat, r: {pc.rd(f) == True{} : Bool}) -> {pc.rd(Ch.Fate.act(a, i, f)) == True{} : Bool}:
  match f:
    case Ch.Queued{}:
      LLogicLogic.child.pc.absurd({pc.rd(Ch.Fate.act(a, i, Ch.Queued{})) == True{} : Bool}, r)
    case Ch.Withdrawn{}:
      r
    case Ch.Placed{}:
      r
    case Ch.Read{}:
      {==}

def pc.rd_act(inbox: List<&2, Ch.Sub>, +a: Ch.Act, r: {pc.Rd(inbox) == True{} : Bool}) -> {pc.Rd(Ch.act(inbox, a)) == True{} : Bool}:
  match inbox:
    case Nil{}:
      r
    case s <> rest:
      match s:
        case Ch.Sub{+i, f}:
          pc.rd_fact(f, a, i, r)

# the parent's read reads the newest submission again, or stands a read
# one newest
def pc.rd_read.at(same: Bool, +n: Nat, +i: Nat, f: Ch.Fate, rest: List<&2, Ch.Sub>, r: {pc.rd(f) == True{} : Bool}) -> {pc.Rd(Ch.read.at(same, n, Ch.Sub{i, f}, rest)) == True{} : Bool}:
  match same:
    case True{}:
      match f:
        case Ch.Queued{}:
          {==}
        case Ch.Withdrawn{}:
          {==}
        case Ch.Placed{}:
          r
        case Ch.Read{}:
          {==}
    case False{}:
      {==}

def pc.rd_read.sub(inbox: List<&2, Ch.Sub>, +n: Nat, r: {pc.Rd(inbox) == True{} : Bool}) -> {pc.Rd(Ch.read.sub(inbox, n)) == True{} : Bool}:
  match inbox:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Ch.Sub{+i, f}:
          pc.rd_read.at(Nat.is_eq(i, n), n, i, f, rest, r)

def pc.rd_read(ph: Ch.Ph, +inbox: List<&2, Ch.Sub>, r: {pc.Rd(inbox) == True{} : Bool}) -> {pc.Rd(Ch.read(ph, inbox)) == True{} : Bool}:
  match ph:
    case Ch.Watching{w}:
      r
    case Ch.Owing{k, +n}:
      pc.rd_read.sub(inbox, n, r)
    case Ch.Ended{}:
      r

# every event keeps a read report read
def pc.rd_step(+cfg: Ch.Cfg, s: Ch.St, e: Ch.Ev, k: {LA.pc.K(s) == True{} : Bool}, r: {pc.Rd(Ch.St.inbox(s)) == True{} : Bool}) -> {pc.Rd(Ch.St.inbox(Ch.step(cfg, s, e))) == True{} : Bool}:
  match s:
    case Ch.St{+ph, +cut, +open, +inbox}:
      match e:
        case Ch.Poll{+dt, +o}:
          pc.rd_poll(cut, ph, inbox, open, cfg, dt, o, LA.pc.and_l(LA.pc.Kph(ph, inbox), LA.pc.Kin(inbox), k), r)
        case Ch.Deliver{+m}:
          pc.rd_act(inbox, Ch.Place{m}, r)
        case Ch.Withdraw{+m}:
          pc.rd_act(inbox, Ch.Pull{m}, r)
        case Ch.Abort{}:
          pc.rd_act(inbox, Ch.PullAll{}, r)
        case Ch.Shut{}:
          pc.rd_act(inbox, Ch.PullAll{}, r)
        case Ch.Reopen{}:
          r
        case Ch.Cut{del}:
          r
        case Ch.Collect{}:
          pc.rd_read(ph, inbox, r)

def pc.rd_run(evs: List<&2, Ch.Ev>, +cfg: Ch.Cfg, +s: Ch.St, +k: {LA.pc.K(s) == True{} : Bool}, r: {pc.Rd(Ch.St.inbox(s)) == True{} : Bool}) -> {pc.Rd(Ch.St.inbox(Ch.run(evs, cfg, s))) == True{} : Bool}:
  match evs:
    case Nil{}:
      r
    case +e <> t:
      pc.rd_run(t, cfg, Ch.step(cfg, s, e), LA.pc.K_step(cfg, s, e, k), pc.rd_step(cfg, s, e, k, r))

# a read report leaves no submission queued or placed
def pc.quiet(inbox: List<&2, Ch.Sub>, +kin: {LA.pc.Kin(inbox) == True{} : Bool}, r: {pc.Rd(inbox) == True{} : Bool}) -> {Nat.add(Ch.queued(inbox), Ch.placed(inbox)) == 0n : Nat}:
  match inbox:
    case Nil{}:
      LLogicLogic.child.pc.absurd({Nat.add(Ch.queued(Nil{}), Ch.placed(Nil{})) == 0n : Nat}, r)
    case s <> +rest:
      match s:
        case Ch.Sub{+m, f}:
          match f:
            case Ch.Queued{}:
              LLogicLogic.child.pc.absurd({Nat.add(Ch.queued(Ch.Sub{m, Ch.Queued{}} <> rest), Ch.placed(Ch.Sub{m, Ch.Queued{}} <> rest)) == 0n : Nat}, r)
            case Ch.Withdrawn{}:
              LLogicLogic.child.pc.absurd({Nat.add(Ch.queued(Ch.Sub{m, Ch.Withdrawn{}} <> rest), Ch.placed(Ch.Sub{m, Ch.Withdrawn{}} <> rest)) == 0n : Nat}, r)
            case Ch.Placed{}:
              LLogicLogic.child.pc.absurd({Nat.add(Ch.queued(Ch.Sub{m, Ch.Placed{}} <> rest), Ch.placed(Ch.Sub{m, Ch.Placed{}} <> rest)) == 0n : Nat}, r)
            case Ch.Read{}:
              %LA.pc.old_queued(rest, m, kin) : {Nat.add(_, Ch.placed(rest)) == 0n : Nat}
              %LA.pc.old_placed(rest, m, kin) : {Nat.add(0n, _) == 0n : Nat}
              {==}

def pc.read_never_wakes(+cfg: Ch.Cfg, +evs: List<&2, Ch.Ev>, +later: List<&2, Ch.Ev>, rd: {Ch.St.read(Ch.run(evs, cfg, Ch.St.init(cfg))) == 1n : Nat}) -> {Nat.add(Ch.St.queued(Ch.run(later, cfg, Ch.run(evs, cfg, Ch.St.init(cfg)))), Ch.St.placed(Ch.run(later, cfg, Ch.run(evs, cfg, Ch.St.init(cfg))))) == 0n : Nat}:
  pc.quiet(Ch.St.inbox(Ch.run(later, cfg, Ch.run(evs, cfg, Ch.St.init(cfg)))), LA.pc.Kin_of(Ch.run(later, cfg, Ch.run(evs, cfg, Ch.St.init(cfg))), LA.pc.K_run(later, cfg, Ch.run(evs, cfg, Ch.St.init(cfg)), LA.pc.K_run(evs, cfg, Ch.St.init(cfg), {==}))), pc.rd_run(later, cfg, Ch.run(evs, cfg, Ch.St.init(cfg)), LA.pc.K_run(evs, cfg, Ch.St.init(cfg), {==}), pc.rd_of(Ch.St.inbox(Ch.run(evs, cfg, Ch.St.init(cfg))), LA.pc.Kin_of(Ch.run(evs, cfg, Ch.St.init(cfg)), LA.pc.K_run(evs, cfg, Ch.St.init(cfg), {==})), rd)))

def Child.child_read_never_wakes(cfg, evs, later, read):
  pc.read_never_wakes(cfg, evs, later, read)
