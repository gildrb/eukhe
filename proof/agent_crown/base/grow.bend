# eukhe: lemmas of area agent_crown for the tree's steps (T14): a taken
# step adds the nodes its op may add (no invariant needed) and only grows
# the tree: every node stays where it was, its spend never drops

import Base
import ../../../bend/agent_tree.bend as T
import ../../../spec/agents/agent_tree.bend as S
import ../../agent_tree/base/reach.bend as AR

# Growth
# ------

# b grew from a: every node of a is in b, its spend no lower
def ac_grow.gr(a: T.Node, b: T.Node) -> Bool:
  match a b:
    case T.Leaf{i} T.Leaf{j}:
      Nat.is_le(T.spent_of(i), T.spent_of(j))
    case T.Leaf{i} T.Split{j, o, l, r}:
      Nat.is_le(T.spent_of(i), T.spent_of(j))
    case T.Split{i, o, l, r} T.Leaf{j}:
      False{}
    case T.Split{i, o, l, r} T.Split{j, o2, l2, r2}:
      Bool.and(Nat.is_le(T.spent_of(i), T.spent_of(j)), Bool.and(ac_grow.gr(l, l2), ac_grow.gr(r, r2)))

# a taken step from t: the new tree has e more nodes and grew from t
def ac_grow.G(s: T.Step, +t: T.Node, +e: Nat) -> Data:
  match s:
    case T.Took{n}:
      AR.at_reach.And({T.size(n) == Nat.add(e, T.size(t)) : Nat}, {ac_grow.gr(t, n) == True{} : Bool})
    case T.Refused{why}:
      Unit

def ac_grow.gr_refl(+t: T.Node) -> {ac_grow.gr(t, t) == True{} : Bool}:
  match t:
    case T.Leaf{i}:
      AR.at_reach.le_refl(T.spent_of(i))
    case T.Split{i, own, l, r}:
      AR.at_reach.and_t(Nat.is_le(T.spent_of(i), T.spent_of(i)), Bool.and(ac_grow.gr(l, l), ac_grow.gr(r, r)), AR.at_reach.le_refl(T.spent_of(i)), AR.at_reach.and_t(ac_grow.gr(l, l), ac_grow.gr(r, r), ac_grow.gr_refl(l), ac_grow.gr_refl(r)))

def ac_grow.gr_cancel(+t: T.Node) -> {ac_grow.gr(t, T.cancel_all(t)) == True{} : Bool}:
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          AR.at_reach.le_refl(sp)
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, +sp, dl, p}:
          AR.at_reach.and_t(Nat.is_le(sp, sp), Bool.and(ac_grow.gr(l, T.cancel_all(l)), ac_grow.gr(r, T.cancel_all(r))), AR.at_reach.le_refl(sp), AR.at_reach.and_t(ac_grow.gr(l, T.cancel_all(l)), ac_grow.gr(r, T.cancel_all(r)), ac_grow.gr_cancel(l), ac_grow.gr_cancel(r)))

def ac_grow.tick_size(+t: T.Node, +now: Nat, +cut: Bool) -> {T.size(T.tick(t, now, cut)) == T.size(t) : Nat}:
  match t:
    case T.Leaf{i}:
      {==}
    case T.Split{+i, own, l, r}:
      AR.at_reach.size_kids(T.size(T.tick(l, now, Bool.or(cut, T.expired(i, now)))), T.size(l), T.size(T.tick(r, now, Bool.or(cut, T.expired(i, now)))), T.size(r), ac_grow.tick_size(l, now, Bool.or(cut, T.expired(i, now))), ac_grow.tick_size(r, now, Bool.or(cut, T.expired(i, now))))

def ac_grow.gr_ti(u: Bool, +st: T.Status, +s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +p: List<&2, Maybe<&2, Nat>>) -> {Nat.is_le(sp, T.spent_of(T.tick_info(u, T.Info{st, s, lim, sp, dl, p}))) == True{} : Bool}:
  match u:
    case True{}:
      AR.at_reach.le_refl(sp)
    case False{}:
      AR.at_reach.le_refl(sp)

def ac_grow.gr_tick(+t: T.Node, +now: Nat, +cut: Bool) -> {ac_grow.gr(t, T.tick(t, now, cut)) == True{} : Bool}:
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          ac_grow.gr_ti(Bool.or(cut, T.expired(T.Info{st, s, lim, sp, dl, p}, now)), st, s, lim, sp, dl, p)
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{+st, +s, +lim, +sp, +dl, +p}:
          +u = Bool.or(cut, T.expired(T.Info{st, s, lim, sp, dl, p}, now))
          AR.at_reach.and_t(Nat.is_le(sp, T.spent_of(T.tick_info(u, T.Info{st, s, lim, sp, dl, p}))), Bool.and(ac_grow.gr(l, T.tick(l, now, u)), ac_grow.gr(r, T.tick(r, now, u))), ac_grow.gr_ti(u, st, s, lim, sp, dl, p), AR.at_reach.and_t(ac_grow.gr(l, T.tick(l, now, u)), ac_grow.gr(r, T.tick(r, now, u)), ac_grow.gr_tick(l, now, u), ac_grow.gr_tick(r, now, u)))

# Local ops
# ---------

def ac_grow.sp_budget(ok: Bool, +i: T.Info, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>, +hold: Nat, +margin: Nat) -> ac_grow.G(T.split_budget(ok, i, own, ls, rs, hold, margin), T.Leaf{i}, 2n):
  match ok:
    case True{}:
      ({==}, AR.at_reach.le_refl(T.spent_of(i)))
    case False{}:
      Unit{}

def ac_grow.sp_scopes(ok: Bool, +i: T.Info, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>, +hold: Nat, +margin: Nat) -> ac_grow.G(T.split_scopes(ok, i, own, ls, rs, hold, margin), T.Leaf{i}, 2n):
  match ok:
    case True{}:
      ac_grow.sp_budget(T.lim_fits(Nat.add(hold, 2n), T.lim_less(T.limit_of(i), T.spent_of(i))), i, own, ls, rs, hold, margin)
    case False{}:
      Unit{}

def ac_grow.sp_room(room: Bool, +i: T.Info, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>, +hold: Nat, +margin: Nat) -> ac_grow.G(T.split_room(room, i, own, ls, rs, hold, margin), T.Leaf{i}, AR.at_reach.xroom(room)):
  match room:
    case True{}:
      ac_grow.sp_scopes(Bool.and(T.tiles(T.scope_of(i), own, ls, rs), Bool.and(T.any(ls), T.any(rs))), i, own, ls, rs, hold, margin)
    case False{}:
      Unit{}

def ac_grow.sp_depth(k: Nat, +i: T.Info, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>, +hold: Nat, +room: Bool, +margin: Nat) -> ac_grow.G(T.split_depth(k, i, own, ls, rs, hold, room, margin), T.Leaf{i}, AR.at_reach.xroom(room)):
  match k:
    case 0n:
      Unit{}
    case 1n+q:
      ac_grow.sp_room(room, i, own, ls, rs, hold, margin)

def ac_grow.local_split(+t: T.Node, +k: Nat, +room: Bool, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>, +hold: Nat, +margin: Nat) -> ac_grow.G(T.local(T.OpSplit{own, ls, rs, hold, room, margin}, t, k), t, AR.at_reach.xroom(room)):
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              ac_grow.sp_depth(k, T.Info{T.Running{}, s, lim, sp, dl, p}, own, ls, rs, hold, room, margin)
            case T.Finished{}:
              Unit{}
            case T.Failed{}:
              Unit{}
            case T.Cancelled{}:
              Unit{}
    case T.Split{i, o2, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              Unit{}
            case T.Finished{}:
              Unit{}
            case T.Failed{}:
              Unit{}
            case T.Cancelled{}:
              Unit{}

def ac_grow.spend_g(ok: Bool, +t: T.Node, +n: Nat) -> ac_grow.G(T.spend_fits(ok, t, n), t, 0n):
  match ok:
    case True{}:
      match t:
        case T.Leaf{i}:
          match i:
            case T.Info{st, s, lim, sp, dl, p}:
              ({==}, AR.at_reach.le_add_r(sp, n))
        case T.Split{i, own, l, r}:
          match i:
            case T.Info{st, s, lim, +sp, dl, p}:
              ({==}, AR.at_reach.and_t(Nat.is_le(sp, Nat.add(sp, n)), Bool.and(ac_grow.gr(l, l), ac_grow.gr(r, r)), AR.at_reach.le_add_r(sp, n), AR.at_reach.and_t(ac_grow.gr(l, l), ac_grow.gr(r, r), ac_grow.gr_refl(l), ac_grow.gr_refl(r))))
    case False{}:
      Unit{}

def ac_grow.local_spend(+t: T.Node, +n: Nat, -k: Nat) -> ac_grow.G(T.local(T.OpSpend{n}, t, k), t, 0n):
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              ac_grow.spend_g(T.lim_fits(n, T.free(T.Leaf{T.Info{T.Running{}, s, lim, sp, dl, p}})), T.Leaf{T.Info{T.Running{}, s, lim, sp, dl, p}}, n)
            case T.Finished{}:
              Unit{}
            case T.Failed{}:
              Unit{}
            case T.Cancelled{}:
              Unit{}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              ac_grow.spend_g(T.lim_fits(n, T.free(T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, r})), T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, r}, n)
            case T.Finished{}:
              Unit{}
            case T.Failed{}:
              Unit{}
            case T.Cancelled{}:
              Unit{}

def ac_grow.fin_split(ok: Bool, +s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +p: List<&2, Maybe<&2, Nat>>, +own: List<&2, Bool>, +l: T.Node, +r: T.Node, +pq: List<&2, Maybe<&2, Nat>>) -> ac_grow.G(T.finish_settled(ok, T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, r, pq), T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, r}, 0n):
  match ok:
    case True{}:
      ({==}, AR.at_reach.and_t(Nat.is_le(sp, sp), Bool.and(ac_grow.gr(l, l), ac_grow.gr(r, r)), AR.at_reach.le_refl(sp), AR.at_reach.and_t(ac_grow.gr(l, l), ac_grow.gr(r, r), ac_grow.gr_refl(l), ac_grow.gr_refl(r))))
    case False{}:
      Unit{}

def ac_grow.local_finish(+t: T.Node, +pq: List<&2, Maybe<&2, Nat>>, -k: Nat) -> ac_grow.G(T.local(T.OpFinish{pq}, t, k), t, 0n):
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              ({==}, AR.at_reach.le_refl(sp))
            case T.Finished{}:
              Unit{}
            case T.Failed{}:
              Unit{}
            case T.Cancelled{}:
              Unit{}
    case T.Split{i, own, +l, +r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              ac_grow.fin_split(Bool.and(Bool.not(T.running(T.st_of(T.info(l)))), Bool.not(T.running(T.st_of(T.info(r))))), s, lim, sp, dl, p, own, l, r, pq)
            case T.Finished{}:
              Unit{}
            case T.Failed{}:
              Unit{}
            case T.Cancelled{}:
              Unit{}

def ac_grow.local_fail(+t: T.Node, +pq: List<&2, Maybe<&2, Nat>>, -k: Nat) -> ac_grow.G(T.local(T.OpFail{pq}, t, k), t, 0n):
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              ({==}, AR.at_reach.le_refl(sp))
            case T.Finished{}:
              Unit{}
            case T.Failed{}:
              Unit{}
            case T.Cancelled{}:
              Unit{}
    case T.Split{i, own, +l, +r}:
      match i:
        case T.Info{st, s, lim, +sp, dl, p}:
          match st:
            case T.Running{}:
              (AR.at_reach.size_kids(T.size(T.cancel_all(l)), T.size(l), T.size(T.cancel_all(r)), T.size(r), AR.at_reach.ca_size(l), AR.at_reach.ca_size(r)), AR.at_reach.and_t(Nat.is_le(sp, sp), Bool.and(ac_grow.gr(l, T.cancel_all(l)), ac_grow.gr(r, T.cancel_all(r))), AR.at_reach.le_refl(sp), AR.at_reach.and_t(ac_grow.gr(l, T.cancel_all(l)), ac_grow.gr(r, T.cancel_all(r)), ac_grow.gr_cancel(l), ac_grow.gr_cancel(r))))
            case T.Finished{}:
              Unit{}
            case T.Failed{}:
              Unit{}
            case T.Cancelled{}:
              Unit{}

def ac_grow.redone_size(-f: T.Lim, -x: Nat, +c: T.Node) -> {T.size(T.redone(f, x, c)) == T.size(c) : Nat}:
  match c:
    case T.Leaf{i}:
      {==}
    case T.Split{i, own, l, r}:
      {==}

def ac_grow.gr_redone(+f: T.Lim, +x: Nat, +c: T.Node) -> {ac_grow.gr(c, T.redone(f, x, c)) == True{} : Bool}:
  match c:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          AR.at_reach.le_refl(sp)
    case T.Split{i, own, l, r}:
      ac_grow.gr_refl(T.Split{i, own, l, r})

def ac_grow.redo_budget(ok: Bool, +f: T.Lim, +i: T.Info, +own: List<&2, Bool>, +side: T.Dir, +x: Nat, +l: T.Node, +r: T.Node) -> ac_grow.G(T.redo_budget(ok, f, i, own, side, x, l, r), T.Split{i, own, l, r}, 0n):
  match ok:
    case True{}:
      match side:
        case T.GoL{}:
          (AR.at_reach.size_kids(T.size(T.redone(f, x, l)), T.size(l), T.size(r), T.size(r), ac_grow.redone_size(f, x, l), {==}), AR.at_reach.and_t(Nat.is_le(T.spent_of(i), T.spent_of(i)), Bool.and(ac_grow.gr(l, T.redone(f, x, l)), ac_grow.gr(r, r)), AR.at_reach.le_refl(T.spent_of(i)), AR.at_reach.and_t(ac_grow.gr(l, T.redone(f, x, l)), ac_grow.gr(r, r), ac_grow.gr_redone(f, x, l), ac_grow.gr_refl(r))))
        case T.GoR{}:
          (AR.at_reach.size_kids(T.size(l), T.size(l), T.size(T.redone(f, x, r)), T.size(r), {==}, ac_grow.redone_size(f, x, r)), AR.at_reach.and_t(Nat.is_le(T.spent_of(i), T.spent_of(i)), Bool.and(ac_grow.gr(l, l), ac_grow.gr(r, T.redone(f, x, r))), AR.at_reach.le_refl(T.spent_of(i)), AR.at_reach.and_t(ac_grow.gr(l, l), ac_grow.gr(r, T.redone(f, x, r)), ac_grow.gr_refl(l), ac_grow.gr_redone(f, x, r))))
    case False{}:
      Unit{}

def ac_grow.redo_child(ok: Bool, +f: T.Lim, +i: T.Info, +own: List<&2, Bool>, +side: T.Dir, +x: Nat, +l: T.Node, +r: T.Node) -> ac_grow.G(T.redo_child(ok, f, i, own, side, x, l, r), T.Split{i, own, l, r}, 0n):
  match ok:
    case True{}:
      ac_grow.redo_budget(T.lim_fits(x, f), f, i, own, side, x, l, r)
    case False{}:
      Unit{}

def ac_grow.local_redo(+side: T.Dir, +t: T.Node, +x: Nat, -k: Nat) -> ac_grow.G(T.local(T.OpRedo{side, x}, t, k), t, 0n):
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              Unit{}
            case T.Finished{}:
              Unit{}
            case T.Failed{}:
              Unit{}
            case T.Cancelled{}:
              Unit{}
    case T.Split{i, own, +l, +r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              ac_grow.redo_child(T.redoable(T.side_child(side, l, r)), T.free(T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, r}), T.Info{T.Running{}, s, lim, sp, dl, p}, own, side, x, l, r)
            case T.Finished{}:
              Unit{}
            case T.Failed{}:
              Unit{}
            case T.Cancelled{}:
              Unit{}

def ac_grow.local_g(+op: T.Op, +t: T.Node, +k: Nat) -> ac_grow.G(T.local(op, t, k), t, AR.at_reach.extra(op)):
  match op:
    case T.OpSplit{own, ls, rs, hold, room, margin}:
      ac_grow.local_split(t, k, room, own, ls, rs, hold, margin)
    case T.OpSpend{n}:
      ac_grow.local_spend(t, n, k)
    case T.OpFinish{pq}:
      ac_grow.local_finish(t, pq, k)
    case T.OpFail{pq}:
      ac_grow.local_fail(t, pq, k)
    case T.OpCancel{}:
      (AR.at_reach.ca_size(t), ac_grow.gr_cancel(t))
    case T.OpRedo{side, x}:
      ac_grow.local_redo(side, t, x, k)

# Edit, step
# ----------

def ac_grow.wrap_l(+s: T.Step, +i: T.Info, +own: List<&2, Bool>, +l: T.Node, +r: T.Node, +e: Nat, +g: ac_grow.G(s, l, e)) -> ac_grow.G(T.wrap_l(i, own, s, r), T.Split{i, own, l, r}, e):
  match s:
    case T.Took{n}:
      (sz, gg) = g
      (AR.at_reach.size_l(e, T.size(l), T.size(n), T.size(r), sz), AR.at_reach.and_t(Nat.is_le(T.spent_of(i), T.spent_of(i)), Bool.and(ac_grow.gr(l, n), ac_grow.gr(r, r)), AR.at_reach.le_refl(T.spent_of(i)), AR.at_reach.and_t(ac_grow.gr(l, n), ac_grow.gr(r, r), gg, ac_grow.gr_refl(r))))
    case T.Refused{why}:
      Unit{}

def ac_grow.wrap_r(+s: T.Step, +i: T.Info, +own: List<&2, Bool>, +l: T.Node, +r: T.Node, +e: Nat, +g: ac_grow.G(s, r, e)) -> ac_grow.G(T.wrap_r(i, own, l, s), T.Split{i, own, l, r}, e):
  match s:
    case T.Took{n}:
      (sz, gg) = g
      (AR.at_reach.size_r(e, T.size(l), T.size(n), T.size(r), sz), AR.at_reach.and_t(Nat.is_le(T.spent_of(i), T.spent_of(i)), Bool.and(ac_grow.gr(l, l), ac_grow.gr(r, n)), AR.at_reach.le_refl(T.spent_of(i)), AR.at_reach.and_t(ac_grow.gr(l, l), ac_grow.gr(r, n), ac_grow.gr_refl(l), gg)))
    case T.Refused{why}:
      Unit{}

def ac_grow.edit_g(+pa: List<&2, T.Dir>, +t: T.Node, +op: T.Op, +k: Nat) -> ac_grow.G(T.edit(pa, t, op, k), t, AR.at_reach.extra(op)):
  match pa:
    case Nil{}:
      ac_grow.local_g(op, t, k)
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match t:
            case T.Leaf{i}:
              Unit{}
            case T.Split{i, own, l, r}:
              ac_grow.wrap_l(T.edit(rest, l, op, T.pred(k)), i, own, l, r, AR.at_reach.extra(op), ac_grow.edit_g(rest, l, op, T.pred(k)))
        case T.GoR{}:
          match t:
            case T.Leaf{i}:
              Unit{}
            case T.Split{i, own, l, r}:
              ac_grow.wrap_r(T.edit(rest, r, op, T.pred(k)), i, own, l, r, AR.at_reach.extra(op), ac_grow.edit_g(rest, r, op, T.pred(k)))

# a taken step grew the tree
def ac_grow.Gr(s: T.Step, +t: T.Node) -> Data:
  match s:
    case T.Took{n}:
      {ac_grow.gr(t, n) == True{} : Bool}
    case T.Refused{why}:
      Unit

def ac_grow.g_gr(+s: T.Step, +t: T.Node, +e: Nat, +g: ac_grow.G(s, t, e)) -> ac_grow.Gr(s, t):
  match s:
    case T.Took{n}:
      (sz, gg) = g
      gg
    case T.Refused{why}:
      Unit{}

def ac_grow.step_gr(+b: T.Bounds, +t: T.Node, +ev: T.Ev) -> ac_grow.Gr(T.step(b, t, ev), t):
  match ev:
    case T.EvSplit{at, own, ls, rs, hold}:
      ac_grow.g_gr(T.edit(at, t, T.OpSplit{own, ls, rs, hold, Nat.is_le(Nat.add(T.size(t), 2n), T.bound_nodes(b)), T.bound_margin(b)}, T.bound_depth(b)), t, AR.at_reach.extra(T.OpSplit{own, ls, rs, hold, Nat.is_le(Nat.add(T.size(t), 2n), T.bound_nodes(b)), T.bound_margin(b)}), ac_grow.edit_g(at, t, T.OpSplit{own, ls, rs, hold, Nat.is_le(Nat.add(T.size(t), 2n), T.bound_nodes(b)), T.bound_margin(b)}, T.bound_depth(b)))
    case T.EvSpend{at, n}:
      ac_grow.g_gr(T.edit(at, t, T.OpSpend{n}, T.bound_depth(b)), t, 0n, ac_grow.edit_g(at, t, T.OpSpend{n}, T.bound_depth(b)))
    case T.EvFinish{at, pq}:
      ac_grow.g_gr(T.edit(at, t, T.OpFinish{pq}, T.bound_depth(b)), t, 0n, ac_grow.edit_g(at, t, T.OpFinish{pq}, T.bound_depth(b)))
    case T.EvFail{at, pq}:
      ac_grow.g_gr(T.edit(at, t, T.OpFail{pq}, T.bound_depth(b)), t, 0n, ac_grow.edit_g(at, t, T.OpFail{pq}, T.bound_depth(b)))
    case T.EvCancel{at}:
      ac_grow.g_gr(T.edit(at, t, T.OpCancel{}, T.bound_depth(b)), t, 0n, ac_grow.edit_g(at, t, T.OpCancel{}, T.bound_depth(b)))
    case T.EvRedo{at, side, x}:
      ac_grow.g_gr(T.edit(at, t, T.OpRedo{side, x}, T.bound_depth(b)), t, 0n, ac_grow.edit_g(at, t, T.OpRedo{side, x}, T.bound_depth(b)))
    case T.EvTick{now}:
      ac_grow.gr_tick(t, now, False{})

def ac_grow.after_size(+sr: T.Step, +t: T.Node, +e: Nat, +mx: Nat, +h: {Nat.is_le(T.size(t), mx) == True{} : Bool}, +he: {Nat.is_le(Nat.add(e, T.size(t)), mx) == True{} : Bool}, +g: ac_grow.G(sr, t, e)) -> {Nat.is_le(T.size(T.after(sr, t)), mx) == True{} : Bool}:
  match sr:
    case T.Took{n}:
      (sz, gg) = g
      AR.at_reach.tr(Nat, Nat.add(e, T.size(t)), T.size(n), z => {Nat.is_le(z, mx) == True{} : Bool}, Equal.sym(Nat, T.size(n), Nat.add(e, T.size(t)), sz), he)
    case T.Refused{why}:
      h

# every tree event keeps the node count within max_nodes (no invariant)
def ac_grow.size_step(+b: T.Bounds, +t: T.Node, +ev: T.Ev, +h: {Nat.is_le(T.size(t), T.bound_nodes(b)) == True{} : Bool}) -> {Nat.is_le(T.size(T.after(T.step(b, t, ev), t)), T.bound_nodes(b)) == True{} : Bool}:
  match ev:
    case T.EvSplit{at, own, ls, rs, hold}:
      ac_grow.after_size(T.edit(at, t, T.OpSplit{own, ls, rs, hold, Nat.is_le(Nat.add(T.size(t), 2n), T.bound_nodes(b)), T.bound_margin(b)}, T.bound_depth(b)), t, AR.at_reach.xroom(Nat.is_le(Nat.add(T.size(t), 2n), T.bound_nodes(b))), T.bound_nodes(b), h, AR.at_reach.room_ok(Nat.is_le(Nat.add(T.size(t), 2n), T.bound_nodes(b)), T.size(t), T.bound_nodes(b), {==}, h), ac_grow.edit_g(at, t, T.OpSplit{own, ls, rs, hold, Nat.is_le(Nat.add(T.size(t), 2n), T.bound_nodes(b)), T.bound_margin(b)}, T.bound_depth(b)))
    case T.EvSpend{at, n}:
      ac_grow.after_size(T.edit(at, t, T.OpSpend{n}, T.bound_depth(b)), t, 0n, T.bound_nodes(b), h, h, ac_grow.edit_g(at, t, T.OpSpend{n}, T.bound_depth(b)))
    case T.EvFinish{at, pq}:
      ac_grow.after_size(T.edit(at, t, T.OpFinish{pq}, T.bound_depth(b)), t, 0n, T.bound_nodes(b), h, h, ac_grow.edit_g(at, t, T.OpFinish{pq}, T.bound_depth(b)))
    case T.EvFail{at, pq}:
      ac_grow.after_size(T.edit(at, t, T.OpFail{pq}, T.bound_depth(b)), t, 0n, T.bound_nodes(b), h, h, ac_grow.edit_g(at, t, T.OpFail{pq}, T.bound_depth(b)))
    case T.EvCancel{at}:
      ac_grow.after_size(T.edit(at, t, T.OpCancel{}, T.bound_depth(b)), t, 0n, T.bound_nodes(b), h, h, ac_grow.edit_g(at, t, T.OpCancel{}, T.bound_depth(b)))
    case T.EvRedo{at, side, x}:
      ac_grow.after_size(T.edit(at, t, T.OpRedo{side, x}, T.bound_depth(b)), t, 0n, T.bound_nodes(b), h, h, ac_grow.edit_g(at, t, T.OpRedo{side, x}, T.bound_depth(b)))
    case T.EvTick{now}:
      AR.at_reach.tr(Nat, T.size(t), T.size(T.tick(t, now, False{})), z => {Nat.is_le(z, T.bound_nodes(b)) == True{} : Bool}, Equal.sym(Nat, T.size(T.tick(t, now, False{})), T.size(t), ac_grow.tick_size(t, now, False{})), h)
