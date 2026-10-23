# eukhe: the proof of LAW child_resubmits_per_abort

import Base
import ../../bend/child.bend as Ch
import ../../laws/child.bend as Child
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA

def pc.le_add_mono(+a: Nat, +x: Nat, +y: Nat, e: {Nat.is_le(x, y) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, x), Nat.add(a, y)) == True{} : Bool}:
  match a:
    case 0n:
      e
    case 1n+p:
      pc.le_add_mono(p, x, y, e)

def pc.add_assoc(+a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %pc.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

# ... and leaves an old list as it is
def pc.act_eq(rest: List<&2, Ch.Sub>, +m: Nat, +a: Ch.Act, o: {LA.pc.Old(rest, m) == True{} : Bool}) -> {rest == Ch.act(rest, a) : List<&2, Ch.Sub>}:
  match rest:
    case Nil{}:
      {==}
    case s <> r:
      match s:
        case Ch.Sub{+j, f}:
          match f:
            case Ch.Queued{}:
              LLogicLogic.child.pc.absurd({Ch.Sub{j, Ch.Queued{}} <> r == Ch.act(Ch.Sub{j, Ch.Queued{}} <> r, a) : List<&2, Ch.Sub>}, o)
            case Ch.Withdrawn{}:
              %pc.act_eq(r, j, a, LA.pc.and_r(Nat.is_le(1n+j, m), LA.pc.Old(r, j), o)) : {Ch.Sub{j, Ch.Withdrawn{}} <> r == Ch.Sub{j, Ch.Withdrawn{}} <> _ : List<&2, Ch.Sub>}
              {==}
            case Ch.Placed{}:
              LLogicLogic.child.pc.absurd({Ch.Sub{j, Ch.Placed{}} <> r == Ch.act(Ch.Sub{j, Ch.Placed{}} <> r, a) : List<&2, Ch.Sub>}, o)

# resubmits_per_abort: the potential pot = 1 + the withdrawn submissions
# bounds the inbox (all but the newest are withdrawn) and grows only at a
# withdrawal (only the newest may be queued)
def pc.fwd(f: Ch.Fate) -> Nat:
  match f:
    case Ch.Queued{}:
      0n
    case Ch.Withdrawn{}:
      1n
    case Ch.Placed{}:
      0n

def pc.slots(inbox: List<&2, Ch.Sub>) -> Nat:
  match inbox:
    case Nil{}:
      1n
    case s <> rest:
      match s:
        case Ch.Sub{i, f}:
          Nat.add(pc.fwd(f), pc.slots(rest))

def pc.pot(s: Ch.St) -> Nat:
  pc.slots(Ch.St.inbox(s))

def pc.acut(a: Ch.Act) -> Nat:
  match a:
    case Ch.Place{m}:
      0n
    case Ch.Pull{m}:
      1n
    case Ch.PullAll{}:
      1n

def pc.old_len(rest: List<&2, Ch.Sub>, +m: Nat, o: {LA.pc.Old(rest, m) == True{} : Bool}) -> {Nat.is_le(1n+List.length(&2, Ch.Sub, rest), pc.slots(rest)) == True{} : Bool}:
  match rest:
    case Nil{}:
      {==}
    case s <> r:
      match s:
        case Ch.Sub{+j, f}:
          match f:
            case Ch.Queued{}:
              LLogicLogic.child.pc.absurd({Nat.is_le(1n+List.length(&2, Ch.Sub, Ch.Sub{j, Ch.Queued{}} <> r), pc.slots(Ch.Sub{j, Ch.Queued{}} <> r)) == True{} : Bool}, o)
            case Ch.Withdrawn{}:
              pc.old_len(r, j, LA.pc.and_r(Nat.is_le(1n+j, m), LA.pc.Old(r, j), o))
            case Ch.Placed{}:
              LLogicLogic.child.pc.absurd({Nat.is_le(1n+List.length(&2, Ch.Sub, Ch.Sub{j, Ch.Placed{}} <> r), pc.slots(Ch.Sub{j, Ch.Placed{}} <> r)) == True{} : Bool}, o)

def pc.len_le(inbox: List<&2, Ch.Sub>, kin: {LA.pc.Kin(inbox) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Ch.Sub, inbox), pc.slots(inbox)) == True{} : Bool}:
  match inbox:
    case Nil{}:
      {==}
    case s <> +rest:
      match s:
        case Ch.Sub{+m, +f}:
          LNat.child.pc.le_trans(1n+List.length(&2, Ch.Sub, rest), pc.slots(rest), Nat.add(pc.fwd(f), pc.slots(rest)), pc.old_len(rest, m, kin), LNat.child.pc.le_add(pc.fwd(f), pc.slots(rest)))

def pc.hit_placed(b: Bool, +w: Nat) -> {Nat.is_le(Nat.add(pc.fwd(Ch.Act.hit(b, Ch.Placed{})), w), w) == True{} : Bool}:
  match b:
    case True{}:
      LNat.child.pc.le_refl(w)
    case False{}:
      LNat.child.pc.le_refl(w)

def pc.hit_pulled(b: Bool, +w: Nat) -> {Nat.is_le(Nat.add(pc.fwd(Ch.Act.hit(b, Ch.Withdrawn{})), w), 1n+w) == True{} : Bool}:
  match b:
    case True{}:
      LNat.child.pc.le_refl(w)
    case False{}:
      LNat.pc.le_succ(w, w, LNat.child.pc.le_refl(w))

def pc.slots_queued(a: Ch.Act, +i: Nat, +w: Nat) -> {Nat.is_le(Nat.add(pc.fwd(Ch.Act.queued(a, i)), w), Nat.add(pc.acut(a), Nat.add(0n, w))) == True{} : Bool}:
  match a:
    case Ch.Place{+x}:
      pc.hit_placed(Nat.is_eq(i, x), w)
    case Ch.Pull{+x}:
      pc.hit_pulled(Nat.is_eq(i, x), w)
    case Ch.PullAll{}:
      LNat.child.pc.le_refl(w)

# the newest submission's share of the potential grows by at most the act's
def pc.slots_head(f: Ch.Fate, +a: Ch.Act, +i: Nat, +w: Nat) -> {Nat.is_le(Nat.add(pc.fwd(Ch.Fate.act(a, i, f)), w), Nat.add(pc.acut(a), Nat.add(pc.fwd(f), w))) == True{} : Bool}:
  match f:
    case Ch.Queued{}:
      pc.slots_queued(a, i, w)
    case Ch.Withdrawn{}:
      LNat.child.pc.le_add(pc.acut(a), Nat.add(1n, w))
    case Ch.Placed{}:
      LNat.child.pc.le_add(pc.acut(a), w)

def pc.slots_act(inbox: List<&2, Ch.Sub>, +a: Ch.Act, kin: {LA.pc.Kin(inbox) == True{} : Bool}) -> {Nat.is_le(pc.slots(Ch.act(inbox, a)), Nat.add(pc.acut(a), pc.slots(inbox))) == True{} : Bool}:
  match inbox:
    case Nil{}:
      LNat.child.pc.le_add(pc.acut(a), 1n)
    case s <> +rest:
      match s:
        case Ch.Sub{+m, +f}:
          %pc.act_eq(rest, m, a, kin) : {Nat.is_le(Nat.add(pc.fwd(Ch.Fate.act(a, m, f)), pc.slots(_)), Nat.add(pc.acut(a), Nat.add(pc.fwd(f), pc.slots(rest)))) == True{} : Bool}
          pc.slots_head(f, a, m, pc.slots(rest))

def pc.slots_owe(x: Maybe<&2, Ch.Fate>, +kr: Ch.Report, +n: Nat, open: Bool, +inbox: List<&2, Ch.Sub>) -> {Nat.is_le(pc.slots(Ch.St.inbox(Ch.owe(x, kr, n, open, inbox))), pc.slots(inbox)) == True{} : Bool}:
  match x:
    case None{}:
      match open:
        case True{}:
          LNat.child.pc.le_refl(pc.slots(inbox))
        case False{}:
          LNat.child.pc.le_refl(pc.slots(inbox))
    case Some{y}:
      match y:
        case Ch.Queued{}:
          LNat.child.pc.le_refl(pc.slots(inbox))
        case Ch.Withdrawn{}:
          LNat.child.pc.le_refl(pc.slots(inbox))
        case Ch.Placed{}:
          LNat.child.pc.le_refl(pc.slots(inbox))

def pc.slots_poll(cut: Maybe<&2, Bool>, ph: Ch.Ph, +inbox: List<&2, Ch.Sub>, +open: Bool, +cfg: Ch.Cfg, +dt: Nat, +o: Ch.Obs) -> {Nat.is_le(pc.slots(Ch.St.inbox(Ch.task(cfg, ph, cut, open, inbox, dt, o))), pc.slots(inbox)) == True{} : Bool}:
  match cut:
    case None{}:
      match ph:
        case Ch.Watching{w}:
          LNat.child.pc.le_refl(pc.slots(inbox))
        case Ch.Owing{kr, +n}:
          pc.slots_owe(Ch.fate(inbox, n), kr, n, open, inbox)
        case Ch.Ended{}:
          LNat.child.pc.le_refl(pc.slots(inbox))
    case Some{del}:
      LNat.child.pc.le_refl(pc.slots(inbox))

def pc.pot_step(+cfg: Ch.Cfg, s: Ch.St, e: Ch.Ev, k: {LA.pc.K(s) == True{} : Bool}) -> {Nat.is_le(pc.pot(Ch.step(cfg, s, e)), Nat.add(Ch.Ev.cut(e), pc.pot(s))) == True{} : Bool}:
  match s:
    case Ch.St{+ph, +cut, +open, +inbox}:
      match e:
        case Ch.Poll{+dt, +o}:
          pc.slots_poll(cut, ph, inbox, open, cfg, dt, o)
        case Ch.Deliver{+m}:
          pc.slots_act(inbox, Ch.Place{m}, LA.pc.and_r(LA.pc.Kph(ph, inbox), LA.pc.Kin(inbox), k))
        case Ch.Withdraw{+m}:
          pc.slots_act(inbox, Ch.Pull{m}, LA.pc.and_r(LA.pc.Kph(ph, inbox), LA.pc.Kin(inbox), k))
        case Ch.Abort{}:
          pc.slots_act(inbox, Ch.PullAll{}, LA.pc.and_r(LA.pc.Kph(ph, inbox), LA.pc.Kin(inbox), k))
        case Ch.Shut{}:
          pc.slots_act(inbox, Ch.PullAll{}, LA.pc.and_r(LA.pc.Kph(ph, inbox), LA.pc.Kin(inbox), k))
        case Ch.Reopen{}:
          LNat.child.pc.le_refl(pc.slots(inbox))
        case Ch.Cut{del}:
          LNat.child.pc.le_refl(pc.slots(inbox))

def pc.pot_run(evs: List<&2, Ch.Ev>, +cfg: Ch.Cfg, +s: Ch.St, +k: {LA.pc.K(s) == True{} : Bool}) -> {Nat.is_le(pc.pot(Ch.run(evs, cfg, s)), Nat.add(Ch.cuts(evs), pc.pot(s))) == True{} : Bool}:
  match evs:
    case Nil{}:
      LNat.child.pc.le_refl(pc.pot(s))
    case +e <> +t:
      %Equal.sym(Nat, Nat.add(Nat.add(Ch.cuts(t), Ch.Ev.cut(e)), pc.pot(s)), Nat.add(Ch.cuts(t), Nat.add(Ch.Ev.cut(e), pc.pot(s))), pc.add_assoc(Ch.cuts(t), Ch.Ev.cut(e), pc.pot(s))) : {Nat.is_le(pc.pot(Ch.run(t, cfg, Ch.step(cfg, s, e))), _) == True{} : Bool}
      LNat.child.pc.le_trans(pc.pot(Ch.run(t, cfg, Ch.step(cfg, s, e))), Nat.add(Ch.cuts(t), pc.pot(Ch.step(cfg, s, e))), Nat.add(Ch.cuts(t), Nat.add(Ch.Ev.cut(e), pc.pot(s))), pc.pot_run(t, cfg, Ch.step(cfg, s, e), LA.pc.K_step(cfg, s, e, k)), pc.le_add_mono(Ch.cuts(t), pc.pot(Ch.step(cfg, s, e)), Nat.add(Ch.Ev.cut(e), pc.pot(s)), pc.pot_step(cfg, s, e, k)))

def pc.resubmits_per_abort(+cfg: Ch.Cfg, +evs: List<&2, Ch.Ev>) -> {Nat.is_le(List.length(&2, Ch.Sub, Ch.St.inbox(Ch.run(evs, cfg, Ch.St.init(cfg)))), Nat.add(Ch.cuts(evs), 1n)) == True{} : Bool}:
  LNat.child.pc.le_trans(List.length(&2, Ch.Sub, Ch.St.inbox(Ch.run(evs, cfg, Ch.St.init(cfg)))), pc.pot(Ch.run(evs, cfg, Ch.St.init(cfg))), Nat.add(Ch.cuts(evs), 1n), pc.len_le(Ch.St.inbox(Ch.run(evs, cfg, Ch.St.init(cfg))), LA.pc.Kin_of(Ch.run(evs, cfg, Ch.St.init(cfg)), LA.pc.K_run(evs, cfg, Ch.St.init(cfg), {==}))), pc.pot_run(evs, cfg, Ch.St.init(cfg), {==}))

def Child.child_resubmits_per_abort(cfg, evs):
  pc.resubmits_per_abort(cfg, evs)
