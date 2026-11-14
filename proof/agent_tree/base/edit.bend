# eukhe: lemmas of the edit proofs of area agent_tree: the code's edit at
# a path is the node at the path (S.node_at) handed to T.local with the
# depth left after the path (at_edit.npred) and put back (at_edit.via,
# at_edit.edit_at); the code's checks are the spec's (tiles = splits, any
# = owns_some, size = nodes, free = room); put and node_at agree (frame);
# cancel and fail quiet a subtree; a tick leaves no late node

import Base
import ../../../bend/agent_tree.bend as T
import ../../../spec/agents/agent_tree.bend as S
import ../../../laws/agent_tree.bend as AgentTree

# Logic
# -----

def at_edit.If(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

def at_edit.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : at_edit.If(_, G)
  Unit{}

def at_edit.MIf(m: Maybe<&2, T.Node>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

def at_edit.absurd_none(-G: Type, -n: T.Node, e: {None{} == Some{n} : Maybe<&2, T.Node>}) -> G:
  %e : at_edit.MIf(_, G)
  Unit{}

def at_edit.some_inj(-a: T.Node, -b: T.Node, e: {Some{a} == Some{b} : Maybe<&2, T.Node>}) -> {b == a : T.Node}:
  %e : {AgentTree.or_same(_, a) == a : T.Node}
  {==}

def at_edit.and_tt(+a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      at_edit.absurd({False{} == True{} : Bool}, ea)

def at_edit.and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      at_edit.absurd({False{} == True{} : Bool}, e)

def at_edit.and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      at_edit.absurd({b == True{} : Bool}, e)

def at_edit.and_f2(+a: Bool, -z: Bool) -> {Bool.and(Bool.and(a, False{}), z) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def at_edit.and_f3(+a: Bool, +c: Bool, -z: Bool) -> {Bool.and(Bool.and(a, Bool.and(c, False{})), z) == False{} : Bool}:
  match a:
    case True{}:
      match c:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

def at_edit.and_swap(+a: Bool, +c: Bool, -z: Bool) -> {Bool.and(a, Bool.and(c, z)) == Bool.and(c, Bool.and(a, z)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      match c:
        case True{}:
          {==}
        case False{}:
          {==}

def at_edit.nf(+u: Bool, h: {Bool.not(u) == True{} : Bool}) -> {False{} == u : Bool}:
  match u:
    case True{}:
      at_edit.absurd({False{} == True{} : Bool}, h)
    case False{}:
      {==}

def at_edit.eq_refl(+v: Nat) -> {Nat.is_eq(v, v) == True{} : Bool}:
  match v:
    case 0n:
      {==}
    case 1n+w:
      at_edit.eq_refl(w)

def at_edit.add_succ(+a: Nat, +b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+w:
      %at_edit.add_succ(w, b) : {2n+Nat.add(w, b) == 1n+_ : Nat}
      {==}

# The edit at a path
# ------------------

# k after one pred per step of p: the depth left at the node p names
def at_edit.npred(p: List<&2, T.Dir>, k: Nat) -> Nat:
  match p:
    case Nil{}:
      k
    case Con{d, rest}:
      at_edit.npred(rest, T.pred(k))

def at_edit.gate(k: Nat) -> Bool:
  match k:
    case 0n:
      False{}
    case 1n+q:
      True{}

# the node's step put back at p
def at_edit.lift(s: T.Step, +p: List<&2, T.Dir>, +t: T.Node) -> T.Step:
  match s:
    case T.Took{m}:
      T.Took{S.put(p, t, m)}
    case T.Refused{why}:
      T.Refused{why}

# the edit through the spec's node at p
def at_edit.via(m: Maybe<&2, T.Node>, +p: List<&2, T.Dir>, +t: T.Node, op: T.Op, k: Nat) -> T.Step:
  match m:
    case None{}:
      T.Refused{T.NoNode{}}
    case Some{+n}:
      at_edit.lift(T.local(op, n, at_edit.npred(p, k)), p, t)

def at_edit.lift_nil(+s: T.Step, +t: T.Node) -> {at_edit.lift(s, [], t) == s : T.Step}:
  match s:
    case T.Took{m}:
      {==}
    case T.Refused{why}:
      {==}

def at_edit.lift_l(+s: T.Step, +i: T.Info, +own: List<&2, Bool>, +rest: List<&2, T.Dir>, +l: T.Node, +r: T.Node) -> {at_edit.lift(s, T.GoL{} <> rest, T.Split{i, own, l, r}) == T.wrap_l(i, own, at_edit.lift(s, rest, l), r) : T.Step}:
  match s:
    case T.Took{m}:
      {==}
    case T.Refused{why}:
      {==}

def at_edit.lift_r(+s: T.Step, +i: T.Info, +own: List<&2, Bool>, +rest: List<&2, T.Dir>, +l: T.Node, +r: T.Node) -> {at_edit.lift(s, T.GoR{} <> rest, T.Split{i, own, l, r}) == T.wrap_r(i, own, l, at_edit.lift(s, rest, r)) : T.Step}:
  match s:
    case T.Took{m}:
      {==}
    case T.Refused{why}:
      {==}

def at_edit.via_l(+m: Maybe<&2, T.Node>, +i: T.Info, +own: List<&2, Bool>, +rest: List<&2, T.Dir>, +l: T.Node, +r: T.Node, +op: T.Op, +k: Nat) -> {at_edit.via(m, T.GoL{} <> rest, T.Split{i, own, l, r}, op, k) == T.wrap_l(i, own, at_edit.via(m, rest, l, op, T.pred(k)), r) : T.Step}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      at_edit.lift_l(T.local(op, n, at_edit.npred(rest, T.pred(k))), i, own, rest, l, r)

def at_edit.via_r(+m: Maybe<&2, T.Node>, +i: T.Info, +own: List<&2, Bool>, +rest: List<&2, T.Dir>, +l: T.Node, +r: T.Node, +op: T.Op, +k: Nat) -> {at_edit.via(m, T.GoR{} <> rest, T.Split{i, own, l, r}, op, k) == T.wrap_r(i, own, l, at_edit.via(m, rest, r, op, T.pred(k))) : T.Step}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      at_edit.lift_r(T.local(op, n, at_edit.npred(rest, T.pred(k))), i, own, rest, l, r)

# the code's edit is the spec's node handed to local and put back
def at_edit.edit_at(+p: List<&2, T.Dir>, +t: T.Node, +op: T.Op, +k: Nat) -> {at_edit.via(S.node_at(p, t), p, t, op, k) == T.edit(p, t, op, k) : T.Step}:
  match p:
    case Nil{}:
      at_edit.lift_nil(T.local(op, t, k), t)
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match t:
            case T.Leaf{i}:
              {==}
            case T.Split{i, own, l, r}:
              %at_edit.edit_at(rest, l, op, T.pred(k)) : {at_edit.via(S.node_at(rest, l), T.GoL{} <> rest, T.Split{i, own, l, r}, op, k) == T.wrap_l(i, own, _, r) : T.Step}
              at_edit.via_l(S.node_at(rest, l), i, own, rest, l, r, op, k)
        case T.GoR{}:
          match t:
            case T.Leaf{i}:
              {==}
            case T.Split{i, own, l, r}:
              %at_edit.edit_at(rest, r, op, T.pred(k)) : {at_edit.via(S.node_at(rest, r), T.GoR{} <> rest, T.Split{i, own, l, r}, op, k) == T.wrap_r(i, own, l, _) : T.Step}
              at_edit.via_r(S.node_at(rest, r), i, own, rest, l, r, op, k)

def at_edit.npred_zero(+p: List<&2, T.Dir>) -> {0n == at_edit.npred(p, 0n) : Nat}:
  match p:
    case Nil{}:
      {==}
    case Con{d, rest}:
      at_edit.npred_zero(rest)

# depth left at p is positive exactly when 1 + length(p) <= depth
def at_edit.depth(+p: List<&2, T.Dir>, +k: Nat) -> {Nat.is_le(1n+S.length(p), k) == at_edit.gate(at_edit.npred(p, k)) : Bool}:
  match p:
    case Nil{}:
      match k:
        case 0n:
          {==}
        case 1n+q:
          match q:
            case 0n:
              {==}
            case 1n+w:
              {==}
    case Con{d, rest}:
      match k:
        case 0n:
          %at_edit.npred_zero(rest) : {Nat.is_le(1n+S.length(d <> rest), 0n) == at_edit.gate(_) : Bool}
          {==}
        case 1n+q:
          at_edit.depth(rest, q)

# Put and node_at
# ---------------

def at_edit.node_at_put(+p: List<&2, T.Dir>, +t: T.Node, -n: T.Node, +m: T.Node, e: {S.node_at(p, t) == Some{n} : Maybe<&2, T.Node>}) -> {Some{m} == S.node_at(p, S.put(p, t, m)) : Maybe<&2, T.Node>}:
  match p:
    case Nil{}:
      {==}
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match t:
            case T.Leaf{i}:
              at_edit.absurd_none({Some{m} == None{} : Maybe<&2, T.Node>}, n, e)
            case T.Split{i, own, l, r}:
              at_edit.node_at_put(rest, l, n, m, e)
        case T.GoR{}:
          match t:
            case T.Leaf{i}:
              at_edit.absurd_none({Some{m} == None{} : Maybe<&2, T.Node>}, n, e)
            case T.Split{i, own, l, r}:
              at_edit.node_at_put(rest, r, n, m, e)

def at_edit.put_same(+p: List<&2, T.Dir>, +t: T.Node, +n: T.Node, e: {S.node_at(p, t) == Some{n} : Maybe<&2, T.Node>}) -> {S.put(p, t, n) == t : T.Node}:
  match p:
    case Nil{}:
      at_edit.some_inj(t, n, e)
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match t:
            case T.Leaf{i}:
              {==}
            case T.Split{+i, +own, +l, +r}:
              %at_edit.put_same(rest, l, n, e) : {T.Split{i, own, S.put(rest, l, n), r} == T.Split{i, own, _, r} : T.Node}
              {==}
        case T.GoR{}:
          match t:
            case T.Leaf{i}:
              {==}
            case T.Split{+i, +own, +l, +r}:
              %at_edit.put_same(rest, r, n, e) : {T.Split{i, own, l, S.put(rest, r, n)} == T.Split{i, own, l, _} : T.Node}
              {==}

def at_edit.put_back(+p: List<&2, T.Dir>, +t: T.Node, +n: T.Node, +m: T.Node, e: {S.node_at(p, t) == Some{n} : Maybe<&2, T.Node>}) -> {S.put(p, S.put(p, t, m), n) == t : T.Node}:
  match p:
    case Nil{}:
      at_edit.some_inj(t, n, e)
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match t:
            case T.Leaf{i}:
              {==}
            case T.Split{+i, +own, +l, +r}:
              %at_edit.put_back(rest, l, n, m, e) : {T.Split{i, own, S.put(rest, S.put(rest, l, m), n), r} == T.Split{i, own, _, r} : T.Node}
              {==}
        case T.GoR{}:
          match t:
            case T.Leaf{i}:
              {==}
            case T.Split{+i, +own, +l, +r}:
              %at_edit.put_back(rest, r, n, m, e) : {T.Split{i, own, l, S.put(rest, S.put(rest, r, m), n)} == T.Split{i, own, l, _} : T.Node}
              {==}

def at_edit.frame_lift(+s: T.Step, +p: List<&2, T.Dir>, +t: T.Node, +n: T.Node, e: {S.node_at(p, t) == Some{n} : Maybe<&2, T.Node>}) -> {S.put(p, AgentTree.landed(at_edit.lift(s, p, t), t), n) == t : T.Node}:
  match s:
    case T.Took{m}:
      at_edit.put_back(p, t, n, m, e)
    case T.Refused{why}:
      at_edit.put_same(p, t, n, e)

# an edit at the node n at p changes nothing outside p's subtree
def at_edit.frame(+op: T.Op, +p: List<&2, T.Dir>, +t: T.Node, +n: T.Node, +k: Nat, +e: {S.node_at(p, t) == Some{n} : Maybe<&2, T.Node>}) -> {S.put(p, AgentTree.landed(at_edit.via(S.node_at(p, t), p, t, op, k), t), n) == t : T.Node}:
  %Equal.sym(Maybe<&2, T.Node>, S.node_at(p, t), Some{n}, e) : {S.put(p, AgentTree.landed(at_edit.via(_, p, t, op, k), t), n) == t : T.Node}
  at_edit.frame_lift(T.local(op, n, at_edit.npred(p, k)), p, t, n, e)

# Cancel, fail
# ------------

def at_edit.nrc(+i: T.Info) -> {Bool.not(T.running(T.st_of(T.cancel_info(i)))) == True{} : Bool}:
  match i:
    case T.Info{st, s, lim, sp, dl, pa}:
      match st:
        case T.Running{}:
          {==}
        case T.Finished{}:
          {==}
        case T.Failed{}:
          {==}
        case T.Cancelled{}:
          {==}

def at_edit.quiet_cancel(+n: T.Node) -> {S.quiet(T.cancel_all(n)) == True{} : Bool}:
  match n:
    case T.Leaf{i}:
      at_edit.nrc(i)
    case T.Split{+i, own, +l, +r}:
      at_edit.and_tt(Bool.not(T.running(T.st_of(T.cancel_info(i)))), Bool.and(S.quiet(T.cancel_all(l)), S.quiet(T.cancel_all(r))), at_edit.nrc(i), at_edit.and_tt(S.quiet(T.cancel_all(l)), S.quiet(T.cancel_all(r)), at_edit.quiet_cancel(l), at_edit.quiet_cancel(r)))

def at_edit.cancel_q(+p: List<&2, T.Dir>, +t: T.Node, +n: T.Node, +k: Nat, +e: {S.node_at(p, t) == Some{n} : Maybe<&2, T.Node>}) -> {AgentTree.quiet_at(p, AgentTree.landed(at_edit.via(S.node_at(p, t), p, t, T.OpCancel{}, k), t)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, T.Node>, S.node_at(p, t), Some{n}, e) : {AgentTree.quiet_at(p, AgentTree.landed(at_edit.via(_, p, t, T.OpCancel{}, k), t)) == True{} : Bool}
  %at_edit.node_at_put(p, t, n, T.cancel_all(n), e) : {AgentTree.quiet_of(_) == True{} : Bool}
  at_edit.quiet_cancel(n)

def at_edit.patch_refl(+q: List<&2, Maybe<&2, Nat>>) -> {AgentTree.patch_is(q, q) == True{} : Bool}:
  match q:
    case Nil{}:
      {==}
    case Con{x, xt}:
      match x:
        case None{}:
          at_edit.patch_refl(xt)
        case Some{v}:
          at_edit.and_tt(Nat.is_eq(v, v), AgentTree.patch_is(xt, xt), at_edit.eq_refl(v), at_edit.patch_refl(xt))

def at_edit.failed_node(+n: T.Node, +q: List<&2, Maybe<&2, Nat>>) -> {AgentTree.failed_with(Some{T.fail_node(n, q)}, q) == True{} : Bool}:
  match n:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, pa}:
          at_edit.patch_refl(q)
    case T.Split{i, own, +l, +r}:
      match i:
        case T.Info{st, s, lim, sp, dl, pa}:
          at_edit.and_tt(AgentTree.patch_is(q, q), Bool.and(S.quiet(T.cancel_all(l)), S.quiet(T.cancel_all(r))), at_edit.patch_refl(q), at_edit.and_tt(S.quiet(T.cancel_all(l)), S.quiet(T.cancel_all(r)), at_edit.quiet_cancel(l), at_edit.quiet_cancel(r)))

# a fail as the node's running flag decides it
def at_edit.fail_if(c: Bool, n: T.Node, q: List<&2, Maybe<&2, Nat>>) -> T.Step:
  match c:
    case True{}:
      T.Took{T.fail_node(n, q)}
    case False{}:
      T.Refused{T.NotRunning{}}

def at_edit.fail_run(+n: T.Node, +q: List<&2, Maybe<&2, Nat>>) -> {at_edit.fail_if(S.is_running(n), n, q) == T.fail_st(T.st_of(T.info(n)), n, q) : T.Step}:
  match n:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, pa}:
          match st:
            case T.Running{}:
              {==}
            case T.Finished{}:
              {==}
            case T.Failed{}:
              {==}
            case T.Cancelled{}:
              {==}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, pa}:
          match st:
            case T.Running{}:
              {==}
            case T.Finished{}:
              {==}
            case T.Failed{}:
              {==}
            case T.Cancelled{}:
              {==}

def at_edit.fail_q(+p: List<&2, T.Dir>, +t: T.Node, +q: List<&2, Maybe<&2, Nat>>, +n: T.Node, +k: Nat, +e: {S.node_at(p, t) == Some{n} : Maybe<&2, T.Node>}, r: {S.is_running(n) == True{} : Bool}) -> {AgentTree.failed_with(S.node_at(p, AgentTree.landed(at_edit.via(S.node_at(p, t), p, t, T.OpFail{q}, k), t)), q) == True{} : Bool}:
  %Equal.sym(Maybe<&2, T.Node>, S.node_at(p, t), Some{n}, e) : {AgentTree.failed_with(S.node_at(p, AgentTree.landed(at_edit.via(_, p, t, T.OpFail{q}, k), t)), q) == True{} : Bool}
  %at_edit.fail_run(n, q) : {AgentTree.failed_with(S.node_at(p, AgentTree.landed(at_edit.lift(_, p, t), t)), q) == True{} : Bool}
  %Equal.sym(Bool, S.is_running(n), True{}, r) : {AgentTree.failed_with(S.node_at(p, AgentTree.landed(at_edit.lift(at_edit.fail_if(_, n, q), p, t), t)), q) == True{} : Bool}
  %at_edit.node_at_put(p, t, n, T.fail_node(n, q), e) : {AgentTree.failed_with(_, q) == True{} : Bool}
  at_edit.failed_node(n, q)

def at_edit.fail_nr(+p: List<&2, T.Dir>, +t: T.Node, +q: List<&2, Maybe<&2, Nat>>, +n: T.Node, +k: Nat, e: {S.node_at(p, t) == Some{n} : Maybe<&2, T.Node>}, r: {S.is_running(n) == False{} : Bool}) -> {at_edit.via(S.node_at(p, t), p, t, T.OpFail{q}, k) == T.Refused{T.NotRunning{}} : T.Step}:
  %Equal.sym(Maybe<&2, T.Node>, S.node_at(p, t), Some{n}, e) : {at_edit.via(_, p, t, T.OpFail{q}, k) == T.Refused{T.NotRunning{}} : T.Step}
  %at_edit.fail_run(n, q) : {at_edit.lift(_, p, t) == T.Refused{T.NotRunning{}} : T.Step}
  %Equal.sym(Bool, S.is_running(n), False{}, r) : {at_edit.lift(at_edit.fail_if(_, n, q), p, t) == T.Refused{T.NotRunning{}} : T.Step}
  {==}

# Tick
# ----

# the info j is not running late at now
def at_edit.ok_info(+j: T.Info, +now: Nat) -> Bool:
  Bool.not(Bool.and(T.running(T.st_of(j)), S.up(T.deadline_of(j), now)))

def at_edit.late_gen(+u: Bool, +s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +d: Nat, +pa: List<&2, Maybe<&2, Nat>>, +now: Nat, eu: {Nat.is_le(d, now) == u : Bool}) -> {at_edit.ok_info(T.tick_info(u, T.Info{T.Running{}, s, lim, sp, T.Value{d}, pa}), now) == True{} : Bool}:
  match u:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Nat.is_le(d, now), False{}, eu) : {Bool.not(_) == True{} : Bool}
      {==}

# the ticked info of a node is never late
def at_edit.head(+c: Bool, +i: T.Info, +now: Nat) -> {at_edit.ok_info(T.tick_info(Bool.or(c, T.expired(i, now)), i), now) == True{} : Bool}:
  match c:
    case True{}:
      match i:
        case T.Info{st, s, lim, sp, dl, pa}:
          match st:
            case T.Running{}:
              {==}
            case T.Finished{}:
              {==}
            case T.Failed{}:
              {==}
            case T.Cancelled{}:
              {==}
    case False{}:
      match i:
        case T.Info{st, s, lim, sp, dl, pa}:
          match st:
            case T.Running{}:
              match dl:
                case T.Unlimited{}:
                  {==}
                case T.Value{d}:
                  at_edit.late_gen(Nat.is_le(d, now), s, lim, sp, d, pa, now, {==})
            case T.Finished{}:
              {==}
            case T.Failed{}:
              {==}
            case T.Cancelled{}:
              {==}

def at_edit.tick_late(+t: T.Node, +now: Nat, +c: Bool) -> {S.none_late(T.tick(t, now, c), now) == True{} : Bool}:
  match t:
    case T.Leaf{i}:
      at_edit.head(c, i, now)
    case T.Split{+i, own, +l, +r}:
      +u = Bool.or(c, T.expired(i, now))
      at_edit.and_tt(at_edit.ok_info(T.tick_info(u, i), now), Bool.and(S.none_late(T.tick(l, now, u), now), S.none_late(T.tick(r, now, u), now)), at_edit.head(c, i, now), at_edit.and_tt(S.none_late(T.tick(l, now, u), now), S.none_late(T.tick(r, now, u), now), at_edit.tick_late(l, now, u), at_edit.tick_late(r, now, u)))

# a node not late at now has not expired
def at_edit.expired_false(+i: T.Info, +now: Nat, h: {at_edit.ok_info(i, now) == True{} : Bool}) -> {False{} == T.expired(i, now) : Bool}:
  match i:
    case T.Info{st, s, lim, sp, dl, pa}:
      match st:
        case T.Running{}:
          match dl:
            case T.Unlimited{}:
              {==}
            case T.Value{d}:
              at_edit.nf(Nat.is_le(d, now), h)
        case T.Finished{}:
          {==}
        case T.Failed{}:
          {==}
        case T.Cancelled{}:
          {==}

def at_edit.tick_keep(+t: T.Node, +now: Nat, +e: {S.none_late(t, now) == True{} : Bool}) -> {T.tick(t, now, False{}) == t : T.Node}:
  match t:
    case T.Leaf{+i}:
      %at_edit.expired_false(i, now, e) : {T.Leaf{T.tick_info(_, i)} == T.Leaf{i} : T.Node}
      {==}
    case T.Split{+i, +own, +l, +r}:
      +hr = at_edit.and_r(at_edit.ok_info(i, now), Bool.and(S.none_late(l, now), S.none_late(r, now)), e)
      +hx = at_edit.expired_false(i, now, at_edit.and_l(at_edit.ok_info(i, now), Bool.and(S.none_late(l, now), S.none_late(r, now)), e))
      %hx : {T.Split{T.tick_info(_, i), own, T.tick(l, now, T.expired(i, now)), T.tick(r, now, T.expired(i, now))} == T.Split{i, own, l, r} : T.Node}
      %hx : {T.Split{i, own, T.tick(l, now, _), T.tick(r, now, T.expired(i, now))} == T.Split{i, own, l, r} : T.Node}
      %hx : {T.Split{i, own, T.tick(l, now, False{}), T.tick(r, now, _)} == T.Split{i, own, l, r} : T.Node}
      %at_edit.tick_keep(l, now, at_edit.and_l(S.none_late(l, now), S.none_late(r, now), hr)) : {T.Split{i, own, T.tick(l, now, False{}), T.tick(r, now, False{})} == T.Split{i, own, _, r} : T.Node}
      %at_edit.tick_keep(r, now, at_edit.and_r(S.none_late(l, now), S.none_late(r, now), hr)) : {T.Split{i, own, T.tick(l, now, False{}), T.tick(r, now, False{})} == T.Split{i, own, T.tick(l, now, False{}), _} : T.Node}
      {==}

# Budget: free is room
# --------------------

def at_edit.minus_less(+l: T.Lim, +n: Nat) -> {S.minus(l, n) == T.lim_less(l, n) : T.Lim}:
  match l:
    case T.Unlimited{}:
      {==}
    case T.Value{m}:
      {==}

def at_edit.ml_drop(+x: T.Lim, +y: T.Lim) -> {S.minus_lim(x, y) == T.lim_drop(x, y) : T.Lim}:
  match x y:
    case T.Unlimited{} T.Unlimited{}:
      {==}
    case T.Unlimited{} T.Value{b}:
      {==}
    case T.Value{a} T.Unlimited{}:
      {==}
    case T.Value{a} T.Value{b}:
      {==}

def at_edit.has_fits(+l: T.Lim, +n: Nat) -> {S.has(n, l) == T.lim_fits(n, l) : Bool}:
  match l:
    case T.Unlimited{}:
      {==}
    case T.Value{m}:
      {==}

def at_edit.spent_total(+n: T.Node) -> {S.spent_all(n) == T.total(n) : Nat}:
  match n:
    case T.Leaf{i}:
      {==}
    case T.Split{+i, own, +l, +r}:
      %at_edit.spent_total(l) : {S.spent_all(T.Split{i, own, l, r}) == Nat.add(T.spent_of(i), Nat.add(_, T.total(r))) : Nat}
      %at_edit.spent_total(r) : {S.spent_all(T.Split{i, own, l, r}) == Nat.add(T.spent_of(i), Nat.add(S.spent_all(l), _)) : Nat}
      {==}

def at_edit.held_st(+st: T.Status, +l: T.Lim, +x: Nat) -> {S.held_if(T.running(st), l, x) == T.charge_st(st, l, x) : T.Lim}:
  match st:
    case T.Running{}:
      {==}
    case T.Finished{}:
      {==}
    case T.Failed{}:
      {==}
    case T.Cancelled{}:
      {==}

def at_edit.held_charge(+c: T.Node) -> {S.held(c) == T.charge(c) : T.Lim}:
  %at_edit.spent_total(c) : {S.held(c) == T.charge_st(T.st_of(T.info(c)), T.limit_of(T.info(c)), _) : T.Lim}
  at_edit.held_st(T.st_of(T.info(c)), T.limit_of(T.info(c)), S.spent_all(c))

def at_edit.room_free(+n: T.Node) -> {S.room(n) == T.free(n) : T.Lim}:
  match n:
    case T.Leaf{+i}:
      at_edit.minus_less(T.limit_of(i), T.spent_of(i))
    case T.Split{+i, +own, +l, +r}:
      %at_edit.held_charge(r) : {S.room(T.Split{i, own, l, r}) == T.lim_drop(T.lim_drop(T.lim_less(T.limit_of(i), T.spent_of(i)), T.charge(l)), _) : T.Lim}
      %at_edit.held_charge(l) : {S.room(T.Split{i, own, l, r}) == T.lim_drop(T.lim_drop(T.lim_less(T.limit_of(i), T.spent_of(i)), _), S.held(r)) : T.Lim}
      %at_edit.minus_less(T.limit_of(i), T.spent_of(i)) : {S.room(T.Split{i, own, l, r}) == T.lim_drop(T.lim_drop(_, S.held(l)), S.held(r)) : T.Lim}
      %at_edit.ml_drop(S.minus(T.limit_of(i), T.spent_of(i)), S.held(l)) : {S.room(T.Split{i, own, l, r}) == T.lim_drop(_, S.held(r)) : T.Lim}
      at_edit.ml_drop(S.minus_lim(S.minus(T.limit_of(i), T.spent_of(i)), S.held(l)), S.held(r))

# the code's budget check is the spec's
def at_edit.fits(+a: Nat, +n: T.Node) -> {S.has(a, S.room(n)) == T.lim_fits(a, T.free(n)) : Bool}:
  %at_edit.room_free(n) : {S.has(a, S.room(n)) == T.lim_fits(a, _) : Bool}
  at_edit.has_fits(S.room(n), a)

# Split: the code's checks are the spec's
# ---------------------------------------

def at_edit.nodes_size(+t: T.Node) -> {S.nodes(t) == T.size(t) : Nat}:
  match t:
    case T.Leaf{i}:
      {==}
    case T.Split{i, own, +l, +r}:
      %at_edit.add_succ(S.nodes(l), S.nodes(r)) : {_ == 1n+Nat.add(T.size(l), T.size(r)) : Nat}
      %at_edit.nodes_size(l) : {1n+Nat.add(S.nodes(l), S.nodes(r)) == 1n+Nat.add(_, T.size(r)) : Nat}
      %at_edit.nodes_size(r) : {1n+Nat.add(S.nodes(l), S.nodes(r)) == 1n+Nat.add(S.nodes(l), _) : Nat}
      {==}

def at_edit.nodes_room(+t: T.Node, +m: Nat) -> {Nat.is_le(Nat.add(S.nodes(t), 2n), m) == Nat.is_le(Nat.add(T.size(t), 2n), m) : Bool}:
  %at_edit.nodes_size(t) : {Nat.is_le(Nat.add(S.nodes(t), 2n), m) == Nat.is_le(Nat.add(_, 2n), m) : Bool}
  {==}

def at_edit.owns_any(+xs: List<&2, Bool>) -> {S.owns_some(xs) == T.any(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      match x:
        case True{}:
          {==}
        case False{}:
          at_edit.owns_any(t)

def at_edit.cell_eq(+x: Bool, +a: Bool, +b: Bool, +c: Bool) -> {Nat.is_eq(Nat.add(S.b2n(a), Nat.add(S.b2n(b), S.b2n(c))), S.b2n(x)) == T.cell(x, a, b, c) : Bool}:
  match x:
    case True{}:
      match a:
        case True{}:
          match b:
            case True{}:
              match c:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match c:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case False{}:
          match b:
            case True{}:
              match c:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match c:
                case True{}:
                  {==}
                case False{}:
                  {==}
    case False{}:
      match a:
        case True{}:
          match b:
            case True{}:
              match c:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match c:
                case True{}:
                  {==}
                case False{}:
                  {==}
        case False{}:
          match b:
            case True{}:
              match c:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              match c:
                case True{}:
                  {==}
                case False{}:
                  {==}

def at_edit.splits_tiles(+s: List<&2, Bool>, +o: List<&2, Bool>, +l: List<&2, Bool>, +r: List<&2, Bool>) -> {S.splits(s, o, l, r) == T.tiles(s, o, l, r) : Bool}:
  match s o l r:
    case Nil{} Nil{} Nil{} Nil{}:
      {==}
    case Nil{} Nil{} Nil{} Con{c, ct}:
      {==}
    case Nil{} Nil{} Con{b, bt} Nil{}:
      {==}
    case Nil{} Nil{} Con{b, bt} Con{c, ct}:
      {==}
    case Nil{} Con{a, at} Nil{} Nil{}:
      {==}
    case Nil{} Con{a, at} Nil{} Con{c, ct}:
      {==}
    case Nil{} Con{a, at} Con{b, bt} Nil{}:
      {==}
    case Nil{} Con{a, at} Con{b, bt} Con{c, ct}:
      {==}
    case Con{x, xt} Nil{} Nil{} Nil{}:
      {==}
    case Con{x, xt} Nil{} Nil{} Con{c, ct}:
      {==}
    case Con{x, xt} Nil{} Con{b, bt} Nil{}:
      {==}
    case Con{x, xt} Nil{} Con{b, bt} Con{c, ct}:
      {==}
    case Con{x, xt} Con{a, at} Nil{} Nil{}:
      at_edit.and_f2(Nat.is_eq(List.length(&2, Bool, at), List.length(&2, Bool, xt)), S.nats_eq(S.addv(S.counts(a <> at), S.addv(S.counts([]), S.counts([]))), S.counts(x <> xt)))
    case Con{x, xt} Con{a, at} Nil{} Con{c, ct}:
      at_edit.and_f2(Nat.is_eq(List.length(&2, Bool, at), List.length(&2, Bool, xt)), S.nats_eq(S.addv(S.counts(a <> at), S.addv(S.counts([]), S.counts(c <> ct))), S.counts(x <> xt)))
    case Con{x, xt} Con{a, at} Con{b, bt} Nil{}:
      at_edit.and_f3(Nat.is_eq(List.length(&2, Bool, at), List.length(&2, Bool, xt)), Nat.is_eq(List.length(&2, Bool, bt), List.length(&2, Bool, xt)), S.nats_eq(S.addv(S.counts(a <> at), S.addv(S.counts(b <> bt), S.counts([]))), S.counts(x <> xt)))
    case Con{x, xt} Con{a, at} Con{b, bt} Con{c, ct}:
      %at_edit.splits_tiles(xt, at, bt, ct) : {S.splits(x <> xt, a <> at, b <> bt, c <> ct) == Bool.and(T.cell(x, a, b, c), _) : Bool}
      %at_edit.cell_eq(x, a, b, c) : {S.splits(x <> xt, a <> at, b <> bt, c <> ct) == Bool.and(_, S.splits(xt, at, bt, ct)) : Bool}
      at_edit.and_swap(S.same_lengths(xt, at, bt, ct), Nat.is_eq(Nat.add(S.b2n(a), Nat.add(S.b2n(b), S.b2n(c))), S.b2n(x)), S.nats_eq(S.addv(S.counts(at), S.addv(S.counts(bt), S.counts(ct))), S.counts(xt)))

def at_edit.scopes_eq(+s: List<&2, Bool>, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>) -> {Bool.and(S.splits(s, own, ls, rs), Bool.and(S.owns_some(ls), S.owns_some(rs))) == Bool.and(T.tiles(s, own, ls, rs), Bool.and(T.any(ls), T.any(rs))) : Bool}:
  %at_edit.splits_tiles(s, own, ls, rs) : {Bool.and(S.splits(s, own, ls, rs), Bool.and(S.owns_some(ls), S.owns_some(rs))) == Bool.and(_, Bool.and(T.any(ls), T.any(rs))) : Bool}
  %at_edit.owns_any(ls) : {Bool.and(S.splits(s, own, ls, rs), Bool.and(S.owns_some(ls), S.owns_some(rs))) == Bool.and(S.splits(s, own, ls, rs), Bool.and(_, T.any(rs))) : Bool}
  %at_edit.owns_any(rs) : {Bool.and(S.splits(s, own, ls, rs), Bool.and(S.owns_some(ls), S.owns_some(rs))) == Bool.and(S.splits(s, own, ls, rs), Bool.and(S.owns_some(ls), _)) : Bool}
  {==}

# the split's four late checks as Bools, then the node
def at_edit.split_code(c3: Bool, c4: Bool, c5: Bool, c6: Bool, x: T.Node) -> T.Step:
  match c3:
    case True{}:
      match c4:
        case True{}:
          match c5:
            case True{}:
              match c6:
                case True{}:
                  T.Took{x}
                case False{}:
                  T.Refused{T.NoBudget{}}
            case False{}:
              T.Refused{T.BadScopes{}}
        case False{}:
          T.Refused{T.TooMany{}}
    case False{}:
      T.Refused{T.TooDeep{}}

def at_edit.split_lhs(c3: Bool, c4: Bool, c5: Bool, c6: Bool, x: T.Node, +p: List<&2, T.Dir>, +t: T.Node) -> T.Step:
  at_edit.lift(at_edit.split_code(c3, c4, c5, c6, x), p, t)

def at_edit.split_rhs(c3: Bool, c4: Bool, c5: Bool, c6: Bool, x: T.Node, +p: List<&2, T.Dir>, +t: T.Node) -> T.Step:
  AgentTree.decided(AgentTree.first_failed([AgentTree.Check{c3, T.TooDeep{}}, AgentTree.Check{c4, T.TooMany{}}, AgentTree.Check{c5, T.BadScopes{}}, AgentTree.Check{c6, T.NoBudget{}}]), S.put(p, t, x))

def at_edit.split_dec(+c3: Bool, +c4: Bool, +c5: Bool, +c6: Bool, +x: T.Node, +p: List<&2, T.Dir>, +t: T.Node) -> {at_edit.split_lhs(c3, c4, c5, c6, x, p, t) == at_edit.split_rhs(c3, c4, c5, c6, x, p, t) : T.Step}:
  match c3:
    case True{}:
      match c4:
        case True{}:
          match c5:
            case True{}:
              match c6:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              {==}
        case False{}:
          {==}
    case False{}:
      {==}

def at_edit.split_cong(-c3: Bool, -c4: Bool, -c5: Bool, -c6: Bool, +d3: Bool, +d4: Bool, +d5: Bool, +d6: Bool, +x: T.Node, +p: List<&2, T.Dir>, +t: T.Node, e3: {d3 == c3 : Bool}, e4: {d4 == c4 : Bool}, e5: {d5 == c5 : Bool}, e6: {d6 == c6 : Bool}) -> {at_edit.split_lhs(c3, c4, c5, c6, x, p, t) == at_edit.split_rhs(d3, d4, d5, d6, x, p, t) : T.Step}:
  %e3 : {at_edit.split_lhs(_, c4, c5, c6, x, p, t) == at_edit.split_rhs(d3, d4, d5, d6, x, p, t) : T.Step}
  %e4 : {at_edit.split_lhs(d3, _, c5, c6, x, p, t) == at_edit.split_rhs(d3, d4, d5, d6, x, p, t) : T.Step}
  %e5 : {at_edit.split_lhs(d3, d4, _, c6, x, p, t) == at_edit.split_rhs(d3, d4, d5, d6, x, p, t) : T.Step}
  %e6 : {at_edit.split_lhs(d3, d4, d5, _, x, p, t) == at_edit.split_rhs(d3, d4, d5, d6, x, p, t) : T.Step}
  at_edit.split_dec(d3, d4, d5, d6, x, p, t)

def at_edit.sc_budget(+c6: Bool, +i: T.Info, +b: T.Bounds, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>, +hold: Nat) -> {at_edit.split_code(True{}, True{}, True{}, c6, AgentTree.split_node(b, T.Leaf{i}, own, ls, rs, hold)) == T.split_budget(c6, i, own, ls, rs, hold, T.bound_margin(b)) : T.Step}:
  match c6:
    case True{}:
      match i:
        case T.Info{st, s, lim, sp, dl, pa}:
          match lim:
            case T.Unlimited{}:
              match dl:
                case T.Unlimited{}:
                  {==}
                case T.Value{v}:
                  {==}
            case T.Value{m}:
              match dl:
                case T.Unlimited{}:
                  {==}
                case T.Value{v}:
                  {==}
    case False{}:
      {==}

def at_edit.sc_scopes(+c5: Bool, +i: T.Info, +b: T.Bounds, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>, +hold: Nat) -> {at_edit.split_code(True{}, True{}, c5, T.lim_fits(Nat.add(hold, 2n), T.lim_less(T.limit_of(i), T.spent_of(i))), AgentTree.split_node(b, T.Leaf{i}, own, ls, rs, hold)) == T.split_scopes(c5, i, own, ls, rs, hold, T.bound_margin(b)) : T.Step}:
  match c5:
    case True{}:
      at_edit.sc_budget(T.lim_fits(Nat.add(hold, 2n), T.lim_less(T.limit_of(i), T.spent_of(i))), i, b, own, ls, rs, hold)
    case False{}:
      {==}

def at_edit.sc_room(+c4: Bool, +i: T.Info, +b: T.Bounds, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>, +hold: Nat) -> {at_edit.split_code(True{}, c4, Bool.and(T.tiles(T.scope_of(i), own, ls, rs), Bool.and(T.any(ls), T.any(rs))), T.lim_fits(Nat.add(hold, 2n), T.lim_less(T.limit_of(i), T.spent_of(i))), AgentTree.split_node(b, T.Leaf{i}, own, ls, rs, hold)) == T.split_room(c4, i, own, ls, rs, hold, T.bound_margin(b)) : T.Step}:
  match c4:
    case True{}:
      at_edit.sc_scopes(Bool.and(T.tiles(T.scope_of(i), own, ls, rs), Bool.and(T.any(ls), T.any(rs))), i, b, own, ls, rs, hold)
    case False{}:
      {==}

def at_edit.sc_depth(+k: Nat, +c4: Bool, +i: T.Info, +b: T.Bounds, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>, +hold: Nat) -> {at_edit.split_code(at_edit.gate(k), c4, Bool.and(T.tiles(T.scope_of(i), own, ls, rs), Bool.and(T.any(ls), T.any(rs))), T.lim_fits(Nat.add(hold, 2n), T.lim_less(T.limit_of(i), T.spent_of(i))), AgentTree.split_node(b, T.Leaf{i}, own, ls, rs, hold)) == T.split_depth(k, i, own, ls, rs, hold, c4, T.bound_margin(b)) : T.Step}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      at_edit.sc_room(c4, i, b, own, ls, rs, hold)

def at_edit.ri(s: List<&2, Bool>, lim: T.Lim, sp: Nat, dl: T.Lim, pa: List<&2, Maybe<&2, Nat>>) -> T.Info:
  T.Info{T.Running{}, s, lim, sp, dl, pa}

def at_edit.split_op(+b: T.Bounds, +t: T.Node, own: List<&2, Bool>, ls: List<&2, Bool>, rs: List<&2, Bool>, hold: Nat) -> T.Op:
  T.OpSplit{own, ls, rs, hold, Nat.is_le(Nat.add(T.size(t), 2n), T.bound_nodes(b)), T.bound_margin(b)}

def at_edit.split_leaf(+s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +pa: List<&2, Maybe<&2, Nat>>, +b: T.Bounds, +t: T.Node, +p: List<&2, T.Dir>, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>, +hold: Nat) -> {at_edit.lift(T.local(at_edit.split_op(b, t, own, ls, rs, hold), T.Leaf{at_edit.ri(s, lim, sp, dl, pa)}, at_edit.npred(p, T.bound_depth(b))), p, t) == AgentTree.split_spec_at(Some{T.Leaf{at_edit.ri(s, lim, sp, dl, pa)}}, b, t, p, own, ls, rs, hold) : T.Step}:
  +i = at_edit.ri(s, lim, sp, dl, pa)
  %at_edit.sc_depth(at_edit.npred(p, T.bound_depth(b)), Nat.is_le(Nat.add(T.size(t), 2n), T.bound_nodes(b)), i, b, own, ls, rs, hold) : {at_edit.lift(_, p, t) == AgentTree.split_spec_at(Some{T.Leaf{i}}, b, t, p, own, ls, rs, hold) : T.Step}
  at_edit.split_cong(at_edit.gate(at_edit.npred(p, T.bound_depth(b))), Nat.is_le(Nat.add(T.size(t), 2n), T.bound_nodes(b)), Bool.and(T.tiles(s, own, ls, rs), Bool.and(T.any(ls), T.any(rs))), T.lim_fits(Nat.add(hold, 2n), T.lim_less(lim, sp)), Nat.is_le(1n+S.length(p), T.bound_depth(b)), Nat.is_le(Nat.add(S.nodes(t), 2n), T.bound_nodes(b)), Bool.and(S.splits(s, own, ls, rs), Bool.and(S.owns_some(ls), S.owns_some(rs))), S.has(Nat.add(hold, 2n), S.room(T.Leaf{i})), AgentTree.split_node(b, T.Leaf{i}, own, ls, rs, hold), p, t, at_edit.depth(p, T.bound_depth(b)), at_edit.nodes_room(t, T.bound_nodes(b)), at_edit.scopes_eq(s, own, ls, rs), at_edit.fits(Nat.add(hold, 2n), T.Leaf{i}))

def at_edit.split_n(+n: T.Node, +b: T.Bounds, +t: T.Node, +p: List<&2, T.Dir>, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>, +hold: Nat) -> {at_edit.lift(T.local(at_edit.split_op(b, t, own, ls, rs, hold), n, at_edit.npred(p, T.bound_depth(b))), p, t) == AgentTree.split_spec_at(Some{n}, b, t, p, own, ls, rs, hold) : T.Step}:
  match n:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, pa}:
          match st:
            case T.Running{}:
              at_edit.split_leaf(s, lim, sp, dl, pa, b, t, p, own, ls, rs, hold)
            case T.Finished{}:
              {==}
            case T.Failed{}:
              {==}
            case T.Cancelled{}:
              {==}
    case T.Split{i, o, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, pa}:
          match st:
            case T.Running{}:
              {==}
            case T.Finished{}:
              {==}
            case T.Failed{}:
              {==}
            case T.Cancelled{}:
              {==}

def at_edit.split_m(+m: Maybe<&2, T.Node>, +b: T.Bounds, +t: T.Node, +p: List<&2, T.Dir>, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>, +hold: Nat) -> {at_edit.via(m, p, t, at_edit.split_op(b, t, own, ls, rs, hold), T.bound_depth(b)) == AgentTree.split_spec_at(m, b, t, p, own, ls, rs, hold) : T.Step}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      at_edit.split_n(n, b, t, p, own, ls, rs, hold)

# Finish
# ------

def at_edit.finish_dec(+c: Bool, +i: T.Info, +own: List<&2, Bool>, +l: T.Node, +r: T.Node, +q: List<&2, Maybe<&2, Nat>>, +p: List<&2, T.Dir>, +t: T.Node) -> {at_edit.lift(T.finish_settled(c, i, own, l, r, q), p, t) == AgentTree.decided(AgentTree.first_failed([AgentTree.Check{c, T.Unsettled{}}]), S.put(p, t, T.Split{T.settle_info(i, T.Finished{}, q), own, l, r})) : T.Step}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def at_edit.finish_n(+n: T.Node, +t: T.Node, +p: List<&2, T.Dir>, +q: List<&2, Maybe<&2, Nat>>, +k: Nat) -> {at_edit.lift(T.local(T.OpFinish{q}, n, k), p, t) == AgentTree.finish_spec_at(Some{n}, t, p, q) : T.Step}:
  match n:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, pa}:
          match st:
            case T.Running{}:
              {==}
            case T.Finished{}:
              {==}
            case T.Failed{}:
              {==}
            case T.Cancelled{}:
              {==}
    case T.Split{i, own, +l, +r}:
      match i:
        case T.Info{st, s, lim, sp, dl, pa}:
          match st:
            case T.Running{}:
              at_edit.finish_dec(Bool.and(Bool.not(T.running(T.st_of(T.info(l)))), Bool.not(T.running(T.st_of(T.info(r))))), at_edit.ri(s, lim, sp, dl, pa), own, l, r, q, p, t)
            case T.Finished{}:
              {==}
            case T.Failed{}:
              {==}
            case T.Cancelled{}:
              {==}

def at_edit.finish_m(+m: Maybe<&2, T.Node>, +t: T.Node, +p: List<&2, T.Dir>, +q: List<&2, Maybe<&2, Nat>>, +k: Nat) -> {at_edit.via(m, p, t, T.OpFinish{q}, k) == AgentTree.finish_spec_at(m, t, p, q) : T.Step}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      at_edit.finish_n(n, t, p, q, at_edit.npred(p, k))

# Spend
# -----

def at_edit.spend_dec(+c: Bool, +n: T.Node, +a: Nat, +p: List<&2, T.Dir>, +t: T.Node) -> {at_edit.lift(T.spend_fits(c, n, a), p, t) == AgentTree.decided(AgentTree.first_failed([AgentTree.Check{c, T.NoBudget{}}]), S.put(p, t, T.add_spent(n, a))) : T.Step}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def at_edit.spend_n(+n: T.Node, +t: T.Node, +p: List<&2, T.Dir>, +a: Nat, +k: Nat) -> {at_edit.lift(T.local(T.OpSpend{a}, n, k), p, t) == AgentTree.spend_spec_at(Some{n}, t, p, a) : T.Step}:
  match n:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, pa}:
          match st:
            case T.Running{}:
              %at_edit.fits(a, T.Leaf{at_edit.ri(s, lim, sp, dl, pa)}) : {at_edit.lift(T.spend_fits(_, T.Leaf{at_edit.ri(s, lim, sp, dl, pa)}, a), p, t) == AgentTree.spend_spec_at(Some{T.Leaf{at_edit.ri(s, lim, sp, dl, pa)}}, t, p, a) : T.Step}
              at_edit.spend_dec(S.has(a, S.room(T.Leaf{at_edit.ri(s, lim, sp, dl, pa)})), T.Leaf{at_edit.ri(s, lim, sp, dl, pa)}, a, p, t)
            case T.Finished{}:
              {==}
            case T.Failed{}:
              {==}
            case T.Cancelled{}:
              {==}
    case T.Split{i, +own, +l, +r}:
      match i:
        case T.Info{st, s, lim, sp, dl, pa}:
          match st:
            case T.Running{}:
              %at_edit.fits(a, T.Split{at_edit.ri(s, lim, sp, dl, pa), own, l, r}) : {at_edit.lift(T.spend_fits(_, T.Split{at_edit.ri(s, lim, sp, dl, pa), own, l, r}, a), p, t) == AgentTree.spend_spec_at(Some{T.Split{at_edit.ri(s, lim, sp, dl, pa), own, l, r}}, t, p, a) : T.Step}
              at_edit.spend_dec(S.has(a, S.room(T.Split{at_edit.ri(s, lim, sp, dl, pa), own, l, r})), T.Split{at_edit.ri(s, lim, sp, dl, pa), own, l, r}, a, p, t)
            case T.Finished{}:
              {==}
            case T.Failed{}:
              {==}
            case T.Cancelled{}:
              {==}

def at_edit.spend_m(+m: Maybe<&2, T.Node>, +t: T.Node, +p: List<&2, T.Dir>, +a: Nat, +k: Nat) -> {at_edit.via(m, p, t, T.OpSpend{a}, k) == AgentTree.spend_spec_at(m, t, p, a) : T.Step}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      at_edit.spend_n(n, t, p, a, at_edit.npred(p, k))

# Redo
# ----

def at_edit.redoable_fcl(+c: T.Node) -> {AgentTree.failed_or_cancelled_leaf(c) == T.redoable(c) : Bool}:
  match c:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, pa}:
          match st:
            case T.Running{}:
              {==}
            case T.Finished{}:
              {==}
            case T.Failed{}:
              {==}
            case T.Cancelled{}:
              {==}
    case T.Split{i, own, l, r}:
      {==}

def at_edit.regrant_eq(+f: T.Lim, +c: T.Node, +x: Nat) -> {AgentTree.regranted(f, c, x) == T.redone(f, x, c) : T.Node}:
  match f:
    case T.Unlimited{}:
      match c:
        case T.Leaf{i}:
          match i:
            case T.Info{st, s, lim, sp, dl, pa}:
              {==}
        case T.Split{i, own, l, r}:
          {==}
    case T.Value{m}:
      match c:
        case T.Leaf{i}:
          match i:
            case T.Info{st, s, lim, sp, dl, pa}:
              {==}
        case T.Split{i, own, l, r}:
          {==}

def at_edit.redo_b_l(+c2: Bool, +f: T.Lim, +i: T.Info, +own: List<&2, Bool>, +x: Nat, +l: T.Node, +r: T.Node, +p: List<&2, T.Dir>, +t: T.Node) -> {at_edit.lift(T.redo_budget(c2, f, i, own, T.GoL{}, x, l, r), p, t) == AgentTree.decided(AgentTree.first_failed([AgentTree.Check{c2, T.NoBudget{}}]), S.put(p, t, T.Split{i, own, AgentTree.regranted(f, l, x), r})) : T.Step}:
  match c2:
    case True{}:
      %at_edit.regrant_eq(f, l, x) : {T.Took{S.put(p, t, T.Split{i, own, _, r})} == T.Took{S.put(p, t, T.Split{i, own, AgentTree.regranted(f, l, x), r})} : T.Step}
      {==}
    case False{}:
      {==}

def at_edit.redo_b_r(+c2: Bool, +f: T.Lim, +i: T.Info, +own: List<&2, Bool>, +x: Nat, +l: T.Node, +r: T.Node, +p: List<&2, T.Dir>, +t: T.Node) -> {at_edit.lift(T.redo_budget(c2, f, i, own, T.GoR{}, x, l, r), p, t) == AgentTree.decided(AgentTree.first_failed([AgentTree.Check{c2, T.NoBudget{}}]), S.put(p, t, T.Split{i, own, l, AgentTree.regranted(f, r, x)})) : T.Step}:
  match c2:
    case True{}:
      %at_edit.regrant_eq(f, r, x) : {T.Took{S.put(p, t, T.Split{i, own, l, _})} == T.Took{S.put(p, t, T.Split{i, own, l, AgentTree.regranted(f, r, x)})} : T.Step}
      {==}
    case False{}:
      {==}

def at_edit.redo_dec_l(+c1: Bool, +f: T.Lim, +i: T.Info, +own: List<&2, Bool>, +x: Nat, +l: T.Node, +r: T.Node, +p: List<&2, T.Dir>, +t: T.Node) -> {at_edit.lift(T.redo_child(c1, f, i, own, T.GoL{}, x, l, r), p, t) == AgentTree.decided(AgentTree.first_failed([AgentTree.Check{c1, T.NotRedoable{}}, AgentTree.Check{S.has(x, f), T.NoBudget{}}]), S.put(p, t, T.Split{i, own, AgentTree.regranted(f, l, x), r})) : T.Step}:
  match c1:
    case True{}:
      %at_edit.has_fits(f, x) : {at_edit.lift(T.redo_budget(_, f, i, own, T.GoL{}, x, l, r), p, t) == AgentTree.decided(AgentTree.first_failed([AgentTree.Check{S.has(x, f), T.NoBudget{}}]), S.put(p, t, T.Split{i, own, AgentTree.regranted(f, l, x), r})) : T.Step}
      at_edit.redo_b_l(S.has(x, f), f, i, own, x, l, r, p, t)
    case False{}:
      {==}

def at_edit.redo_dec_r(+c1: Bool, +f: T.Lim, +i: T.Info, +own: List<&2, Bool>, +x: Nat, +l: T.Node, +r: T.Node, +p: List<&2, T.Dir>, +t: T.Node) -> {at_edit.lift(T.redo_child(c1, f, i, own, T.GoR{}, x, l, r), p, t) == AgentTree.decided(AgentTree.first_failed([AgentTree.Check{c1, T.NotRedoable{}}, AgentTree.Check{S.has(x, f), T.NoBudget{}}]), S.put(p, t, T.Split{i, own, l, AgentTree.regranted(f, r, x)})) : T.Step}:
  match c1:
    case True{}:
      %at_edit.has_fits(f, x) : {at_edit.lift(T.redo_budget(_, f, i, own, T.GoR{}, x, l, r), p, t) == AgentTree.decided(AgentTree.first_failed([AgentTree.Check{S.has(x, f), T.NoBudget{}}]), S.put(p, t, T.Split{i, own, l, AgentTree.regranted(f, r, x)})) : T.Step}
      at_edit.redo_b_r(S.has(x, f), f, i, own, x, l, r, p, t)
    case False{}:
      {==}

def at_edit.redo_go(+d: T.Dir, +s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +pa: List<&2, Maybe<&2, Nat>>, +own: List<&2, Bool>, +l: T.Node, +r: T.Node, +x: Nat, +p: List<&2, T.Dir>, +t: T.Node, +k: Nat) -> {at_edit.lift(T.local(T.OpRedo{d, x}, T.Split{at_edit.ri(s, lim, sp, dl, pa), own, l, r}, k), p, t) == AgentTree.redo_spec_at(Some{T.Split{at_edit.ri(s, lim, sp, dl, pa), own, l, r}}, t, p, d, x) : T.Step}:
  match d:
    case T.GoL{}:
      +i = at_edit.ri(s, lim, sp, dl, pa)
      +n = {T.Split{i, own, l, r} : T.Node}
      %at_edit.redoable_fcl(l) : {at_edit.lift(T.redo_child(_, T.free(n), i, own, T.GoL{}, x, l, r), p, t) == AgentTree.redo_spec_at(Some{n}, t, p, T.GoL{}, x) : T.Step}
      %at_edit.room_free(n) : {at_edit.lift(T.redo_child(AgentTree.failed_or_cancelled_leaf(l), _, i, own, T.GoL{}, x, l, r), p, t) == AgentTree.redo_spec_at(Some{n}, t, p, T.GoL{}, x) : T.Step}
      at_edit.redo_dec_l(AgentTree.failed_or_cancelled_leaf(l), S.room(n), i, own, x, l, r, p, t)
    case T.GoR{}:
      +i = at_edit.ri(s, lim, sp, dl, pa)
      +n = {T.Split{i, own, l, r} : T.Node}
      %at_edit.redoable_fcl(r) : {at_edit.lift(T.redo_child(_, T.free(n), i, own, T.GoR{}, x, l, r), p, t) == AgentTree.redo_spec_at(Some{n}, t, p, T.GoR{}, x) : T.Step}
      %at_edit.room_free(n) : {at_edit.lift(T.redo_child(AgentTree.failed_or_cancelled_leaf(r), _, i, own, T.GoR{}, x, l, r), p, t) == AgentTree.redo_spec_at(Some{n}, t, p, T.GoR{}, x) : T.Step}
      at_edit.redo_dec_r(AgentTree.failed_or_cancelled_leaf(r), S.room(n), i, own, x, l, r, p, t)

def at_edit.redo_n(+n: T.Node, +t: T.Node, +p: List<&2, T.Dir>, +d: T.Dir, +x: Nat, +k: Nat) -> {at_edit.lift(T.local(T.OpRedo{d, x}, n, k), p, t) == AgentTree.redo_spec_at(Some{n}, t, p, d, x) : T.Step}:
  match n:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, pa}:
          match st:
            case T.Running{}:
              {==}
            case T.Finished{}:
              {==}
            case T.Failed{}:
              {==}
            case T.Cancelled{}:
              {==}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, pa}:
          match st:
            case T.Running{}:
              at_edit.redo_go(d, s, lim, sp, dl, pa, own, l, r, x, p, t, k)
            case T.Finished{}:
              {==}
            case T.Failed{}:
              {==}
            case T.Cancelled{}:
              {==}

def at_edit.redo_m(+m: Maybe<&2, T.Node>, +t: T.Node, +p: List<&2, T.Dir>, +d: T.Dir, +x: Nat, +k: Nat) -> {at_edit.via(m, p, t, T.OpRedo{d, x}, k) == AgentTree.redo_spec_at(m, t, p, d, x) : T.Step}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      at_edit.redo_n(n, t, p, d, x, at_edit.npred(p, k))
