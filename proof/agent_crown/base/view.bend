# eukhe: lemmas of area agent_crown for the view (T14): the code's
# structural shift is the spec's fold of bumps, and keeps every node's
# shape and status

import Base
import ../../../bend/agent_tree.bend as T
import ../../../bend/agent_crown.bend as A
import ../../../spec/agents/agent_tree.bend as S
import ../../../spec/agents/agent_crown.bend as CS
import ../../agent_tree/base/reach.bend as AR

# Numbers
# -------

def ac_view.sub_zero(n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def ac_view.bump0(up: Bool, +sp: Nat) -> {A.bump_by(up, sp, 0n) == sp : Nat}:
  match up:
    case True{}:
      AR.at_reach.add_zero(sp)
    case False{}:
      ac_view.sub_zero(sp)

# sp + (n + h) = (sp + h) + n
def ac_view.add_swap(+sp: Nat, +n: Nat, +h: Nat) -> {Nat.add(sp, Nat.add(n, h)) == Nat.add(Nat.add(sp, h), n) : Nat}:
  %AR.at_reach.add_comm(h, n) : {Nat.add(sp, _) == Nat.add(Nat.add(sp, h), n) : Nat}
  Equal.sym(Nat, Nat.add(Nat.add(sp, h), n), Nat.add(sp, Nat.add(h, n)), AR.at_reach.add_assoc(sp, h, n))

# sp - (n + h) = (sp - h) - n
def ac_view.sub_swap(+sp: Nat, +n: Nat, +h: Nat) -> {Nat.sub(sp, Nat.add(n, h)) == Nat.sub(Nat.sub(sp, h), n) : Nat}:
  %AR.at_reach.add_comm(h, n) : {Nat.sub(sp, _) == Nat.sub(Nat.sub(sp, h), n) : Nat}
  Equal.sym(Nat, Nat.sub(Nat.sub(sp, h), n), Nat.sub(sp, Nat.add(h, n)), AR.at_reach.sub_sub(sp, h, n))

# Shift
# -----

# no charge changes nothing
def ac_view.shift_nil(+t: T.Node, +up: Bool) -> {A.shift(t, [], up) == t : T.Node}:
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, q}:
          Equal.cong(Nat, T.Node, x => T.Leaf{T.Info{st, s, lim, x, dl, q}}, A.bump_by(up, sp, 0n), sp, ac_view.bump0(up, sp))
    case T.Split{i, +own, +l, +r}:
      match i:
        case T.Info{+st, +s, +lim, +sp, +dl, +q}:
          %ac_view.shift_nil(l, up) : {A.shift(T.Split{T.Info{st, s, lim, sp, dl, q}, own, l, r}, [], up) == T.Split{T.Info{st, s, lim, sp, dl, q}, own, _, r} : T.Node}
          %ac_view.shift_nil(r, up) : {A.shift(T.Split{T.Info{st, s, lim, sp, dl, q}, own, l, r}, [], up) == T.Split{T.Info{st, s, lim, sp, dl, q}, own, A.shift(l, [], up), _} : T.Node}
          Equal.cong(Nat, T.Node, x => T.Split{T.Info{st, s, lim, x, dl, q}, own, A.shift(l, [], up), A.shift(r, [], up)}, A.bump_by(up, sp, 0n), sp, ac_view.bump0(up, sp))

# the code's node lookup is the spec's
def ac_view.node_at_eq(+p: List<&2, T.Dir>, +t: T.Node) -> {A.node_at(p, t) == S.node_at(p, t) : Maybe<&2, T.Node>}:
  match p:
    case Nil{}:
      {==}
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match t:
            case T.Leaf{i}:
              {==}
            case T.Split{i, own, l, r}:
              ac_view.node_at_eq(rest, l)
        case T.GoR{}:
          match t:
            case T.Leaf{i}:
              {==}
            case T.Split{i, own, l, r}:
              ac_view.node_at_eq(rest, r)

# the code's charge is the spec's
def ac_view.charge_eq(st: T.Status, lim: T.Lim, -sp: Nat) -> {A.charge_if(T.running(st), lim, sp) == CS.charge_st(st, lim, sp) : Nat}:
  match st:
    case T.Running{}:
      match lim:
        case T.Unlimited{}:
          {==}
        case T.Value{n}:
          {==}
    case T.Finished{}:
      {==}
    case T.Failed{}:
      {==}
    case T.Cancelled{}:
      {==}

# a charge in front raises the node at its path
def ac_view.bump_shift(+p: List<&2, T.Dir>, +t: T.Node, +n: Nat, +ls: List<&2, A.Load>) -> {A.shift(t, A.Load{p, n} <> ls, True{}) == CS.bump(p, A.shift(t, ls, True{}), n) : T.Node}:
  match p:
    case Nil{}:
      match t:
        case T.Leaf{i}:
          match i:
            case T.Info{st, s, lim, sp, dl, q}:
              Equal.cong(Nat, T.Node, x => T.Leaf{T.Info{st, s, lim, x, dl, q}}, Nat.add(sp, Nat.add(n, A.here(ls))), Nat.add(Nat.add(sp, A.here(ls)), n), ac_view.add_swap(sp, n, A.here(ls)))
        case T.Split{i, own, l, r}:
          match i:
            case T.Info{st, s, lim, sp, dl, q}:
              Equal.cong(Nat, T.Node, x => T.Split{T.Info{st, s, lim, x, dl, q}, own, A.shift(l, A.down(ls, T.GoL{}), True{}), A.shift(r, A.down(ls, T.GoR{}), True{})}, Nat.add(sp, Nat.add(n, A.here(ls))), Nat.add(Nat.add(sp, A.here(ls)), n), ac_view.add_swap(sp, n, A.here(ls)))
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match t:
            case T.Leaf{i}:
              {==}
            case T.Split{+i, +own, +l, +r}:
              Equal.cong(T.Node, T.Node, x => T.Split{A.shift_info(i, True{}, A.here(ls)), own, x, A.shift(r, A.down(ls, T.GoR{}), True{})}, A.shift(l, A.Load{rest, n} <> A.down(ls, T.GoL{}), True{}), CS.bump(rest, A.shift(l, A.down(ls, T.GoL{}), True{}), n), ac_view.bump_shift(rest, l, n, A.down(ls, T.GoL{})))
        case T.GoR{}:
          match t:
            case T.Leaf{i}:
              {==}
            case T.Split{+i, +own, +l, +r}:
              Equal.cong(T.Node, T.Node, x => T.Split{A.shift_info(i, True{}, A.here(ls)), own, A.shift(l, A.down(ls, T.GoL{}), True{}), x}, A.shift(r, A.Load{rest, n} <> A.down(ls, T.GoR{}), True{}), CS.bump(rest, A.shift(r, A.down(ls, T.GoR{}), True{}), n), ac_view.bump_shift(rest, r, n, A.down(ls, T.GoR{})))

# a charge in front lowers the node at its path
def ac_view.unbump_shift(+p: List<&2, T.Dir>, +t: T.Node, +n: Nat, +ls: List<&2, A.Load>) -> {A.shift(t, A.Load{p, n} <> ls, False{}) == CS.unbump(p, A.shift(t, ls, False{}), n) : T.Node}:
  match p:
    case Nil{}:
      match t:
        case T.Leaf{i}:
          match i:
            case T.Info{st, s, lim, sp, dl, q}:
              Equal.cong(Nat, T.Node, x => T.Leaf{T.Info{st, s, lim, x, dl, q}}, Nat.sub(sp, Nat.add(n, A.here(ls))), Nat.sub(Nat.sub(sp, A.here(ls)), n), ac_view.sub_swap(sp, n, A.here(ls)))
        case T.Split{i, own, l, r}:
          match i:
            case T.Info{st, s, lim, sp, dl, q}:
              Equal.cong(Nat, T.Node, x => T.Split{T.Info{st, s, lim, x, dl, q}, own, A.shift(l, A.down(ls, T.GoL{}), False{}), A.shift(r, A.down(ls, T.GoR{}), False{})}, Nat.sub(sp, Nat.add(n, A.here(ls))), Nat.sub(Nat.sub(sp, A.here(ls)), n), ac_view.sub_swap(sp, n, A.here(ls)))
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match t:
            case T.Leaf{i}:
              {==}
            case T.Split{+i, +own, +l, +r}:
              Equal.cong(T.Node, T.Node, x => T.Split{A.shift_info(i, False{}, A.here(ls)), own, x, A.shift(r, A.down(ls, T.GoR{}), False{})}, A.shift(l, A.Load{rest, n} <> A.down(ls, T.GoL{}), False{}), CS.unbump(rest, A.shift(l, A.down(ls, T.GoL{}), False{}), n), ac_view.unbump_shift(rest, l, n, A.down(ls, T.GoL{})))
        case T.GoR{}:
          match t:
            case T.Leaf{i}:
              {==}
            case T.Split{+i, +own, +l, +r}:
              Equal.cong(T.Node, T.Node, x => T.Split{A.shift_info(i, False{}, A.here(ls)), own, A.shift(l, A.down(ls, T.GoL{}), False{}), x}, A.shift(r, A.Load{rest, n} <> A.down(ls, T.GoR{}), False{}), CS.unbump(rest, A.shift(r, A.down(ls, T.GoR{}), False{}), n), ac_view.unbump_shift(rest, r, n, A.down(ls, T.GoR{})))

# the code's view is the spec's
def ac_view.view_eq(+t: T.Node, +hs: List<&2, A.Help>) -> {A.view(t, hs) == CS.view_of(t, hs) : T.Node}:
  match hs:
    case Nil{}:
      ac_view.shift_nil(t, True{})
    case Con{h, rest}:
      match h:
        case A.Help{+p, +st, +lim, +sp, dl}:
          %ac_view.view_eq(t, rest) : {A.shift(t, A.Load{p, A.charge_if(T.running(st), lim, sp)} <> A.loads(rest), True{}) == CS.bump(p, _, CS.charge_st(st, lim, sp)) : T.Node}
          %ac_view.charge_eq(st, lim, sp) : {A.shift(t, A.Load{p, A.charge_if(T.running(st), lim, sp)} <> A.loads(rest), True{}) == CS.bump(p, A.shift(t, A.loads(rest), True{}), _) : T.Node}
          ac_view.bump_shift(p, t, A.charge_if(T.running(st), lim, sp), A.loads(rest))

# the code's undoing of the view is the spec's
def ac_view.unview_eq(+t: T.Node, +hs: List<&2, A.Help>) -> {A.shift(t, A.loads(hs), False{}) == CS.unview_of(t, hs) : T.Node}:
  match hs:
    case Nil{}:
      ac_view.shift_nil(t, False{})
    case Con{h, rest}:
      match h:
        case A.Help{+p, +st, +lim, +sp, dl}:
          %ac_view.unview_eq(t, rest) : {A.shift(t, A.Load{p, A.charge_if(T.running(st), lim, sp)} <> A.loads(rest), False{}) == CS.unbump(p, _, CS.charge_st(st, lim, sp)) : T.Node}
          %ac_view.charge_eq(st, lim, sp) : {A.shift(t, A.Load{p, A.charge_if(T.running(st), lim, sp)} <> A.loads(rest), False{}) == CS.unbump(p, A.shift(t, A.loads(rest), False{}), _) : T.Node}
          ac_view.unbump_shift(p, t, A.charge_if(T.running(st), lim, sp), A.loads(rest))

# The node at a path of a shifted tree
# ------------------------------------

# the charges below the path p
def ac_view.downs(p: List<&2, T.Dir>, ls: List<&2, A.Load>) -> List<&2, A.Load>:
  match p:
    case Nil{}:
      ls
    case Con{d, rest}:
      ac_view.downs(rest, A.down(ls, d))

def ac_view.shift_m(m: Maybe<&2, T.Node>, +ls: List<&2, A.Load>, +up: Bool) -> Maybe<&2, T.Node>:
  match m:
    case None{}:
      None{}
    case Some{n}:
      Some{A.shift(n, ls, up)}

# the node at p of a shifted tree is the shifted node at p
def ac_view.node_shift(+p: List<&2, T.Dir>, +t: T.Node, +ls: List<&2, A.Load>, +up: Bool) -> {A.node_at(p, A.shift(t, ls, up)) == ac_view.shift_m(A.node_at(p, t), ac_view.downs(p, ls), up) : Maybe<&2, T.Node>}:
  match p:
    case Nil{}:
      {==}
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match t:
            case T.Leaf{i}:
              {==}
            case T.Split{i, own, l, r}:
              ac_view.node_shift(rest, l, A.down(ls, T.GoL{}), up)
        case T.GoR{}:
          match t:
            case T.Leaf{i}:
              {==}
            case T.Split{i, own, l, r}:
              ac_view.node_shift(rest, r, A.down(ls, T.GoR{}), up)

# a shift keeps whether the node is there and runs
def ac_view.runs_m(+m: Maybe<&2, T.Node>, +ls: List<&2, A.Load>, +up: Bool) -> {A.runs(ac_view.shift_m(m, ls, up)) == A.runs(m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      match n:
        case T.Leaf{i}:
          match i:
            case T.Info{st, s, lim, sp, dl, q}:
              {==}
        case T.Split{i, own, l, r}:
          match i:
            case T.Info{st, s, lim, sp, dl, q}:
              {==}

def ac_view.runs_shift(+p: List<&2, T.Dir>, +t: T.Node, +ls: List<&2, A.Load>, +up: Bool) -> {A.runs(A.node_at(p, A.shift(t, ls, up))) == A.runs(A.node_at(p, t)) : Bool}:
  Equal.trans(Bool, A.runs(A.node_at(p, A.shift(t, ls, up))), A.runs(ac_view.shift_m(A.node_at(p, t), ac_view.downs(p, ls), up)), A.runs(A.node_at(p, t)), Equal.cong(Maybe<&2, T.Node>, Bool, m => A.runs(m), A.node_at(p, A.shift(t, ls, up)), ac_view.shift_m(A.node_at(p, t), ac_view.downs(p, ls), up), ac_view.node_shift(p, t, ls, up)), ac_view.runs_m(A.node_at(p, t), ac_view.downs(p, ls), up))

# the spec's runs_at is the code's runs
def ac_view.runs_eq(+m: Maybe<&2, T.Node>) -> {CS.runs_at(m) == A.runs(m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      {==}

# Paths
# -----

def ac_view.dir_eq(+x: T.Dir, +y: T.Dir, e: {CS.dir_is(x, y) == True{} : Bool}) -> {x == y : T.Dir}:
  match x y:
    case T.GoL{} T.GoL{}:
      {==}
    case T.GoL{} T.GoR{}:
      AR.at_reach.absurd({T.GoL{} == T.GoR{} : T.Dir}, e)
    case T.GoR{} T.GoL{}:
      AR.at_reach.absurd({T.GoR{} == T.GoL{} : T.Dir}, e)
    case T.GoR{} T.GoR{}:
      {==}

def ac_view.path_eq(+a: List<&2, T.Dir>, +b: List<&2, T.Dir>, +e: {CS.path_is(a, b) == True{} : Bool}) -> {a == b : List<&2, T.Dir>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, yt}:
      AR.at_reach.absurd({Nil{} == y <> yt : List<&2, T.Dir>}, e)
    case Con{x, xt} Nil{}:
      AR.at_reach.absurd({x <> xt == Nil{} : List<&2, T.Dir>}, e)
    case Con{+x, +xt} Con{+y, +yt}:
      +ed = ac_view.dir_eq(x, y, AR.at_reach.and_l(CS.dir_is(x, y), CS.path_is(xt, yt), e))
      +et = ac_view.path_eq(xt, yt, AR.at_reach.and_r(CS.dir_is(x, y), CS.path_is(xt, yt), e))
      %ed : {x <> xt == _ <> yt : List<&2, T.Dir>}
      %et : {x <> xt == x <> _ : List<&2, T.Dir>}
      {==}

def ac_view.path_refl(+a: List<&2, T.Dir>) -> {CS.path_is(a, a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{x, xt}:
      match x:
        case T.GoL{}:
          ac_view.path_refl(xt)
        case T.GoR{}:
          ac_view.path_refl(xt)
