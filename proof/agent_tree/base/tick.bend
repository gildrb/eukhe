# eukhe: lemmas of area agent_tree for the tick (T8)

import Base
import ../../../bend/agent_tree.bend as T
import ../../../spec/agents/agent_tree.bend as S
import ../../../laws/agent_tree.bend as AgentTree
import ./patch.bend as LP

# the node a Maybe holds, d when none
def at_tick.unwrap(m: Maybe<&2, T.Node>, d: T.Node) -> T.Node:
  match m:
    case None{}:
      d
    case Some{x}:
      x

# G when some, Unit when none
def at_tick.IfSome(m: Maybe<&2, T.Node>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# no node is some node
def at_tick.none_some(-n: T.Node, -G: Type, e: {None{} == Some{n} : Maybe<&2, T.Node>}) -> G:
  %e : at_tick.IfSome(_, G)
  Unit{}

def at_tick.notb(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {False{} == b : Bool}:
  match b:
    case True{}:
      LP.at_patch.absurd({False{} == True{} : Bool}, h)
    case False{}:
      {==}

# a node not late is not expired
def at_tick.exp_false(i: T.Info, +now: Nat, h: {Bool.not(Bool.and(T.running(T.st_of(i)), S.up(T.deadline_of(i), now))) == True{} : Bool}) -> {False{} == T.expired(i, now) : Bool}:
  match i:
    case T.Info{st, s, lim, sp, dl, q}:
      match st:
        case T.Running{}:
          match dl:
            case T.Unlimited{}:
              {==}
            case T.Value{d}:
              at_tick.notb(Nat.is_le(d, now), h)
        case T.Finished{}:
          {==}
        case T.Failed{}:
          {==}
        case T.Cancelled{}:
          {==}

def at_tick.tb(b: Bool, -s: List<&2, Bool>, -lim: T.Lim, -sp: Nat, -dl: T.Lim, -q: List<&2, Maybe<&2, Nat>>, o: {Bool.not(b) == True{} : Bool}) -> {T.running(T.st_of(T.tick_info(b, T.Info{T.Running{}, s, lim, sp, dl, q}))) == True{} : Bool}:
  match b:
    case True{}:
      LP.at_patch.absurd({T.running(T.st_of(T.tick_info(True{}, T.Info{T.Running{}, s, lim, sp, dl, q}))) == True{} : Bool}, o)
    case False{}:
      {==}

# a running node not late still runs after its tick
def at_tick.tinfo(i: T.Info, +now: Nat, hr: {T.running(T.st_of(i)) == True{} : Bool}, o: {Bool.not(Bool.and(T.running(T.st_of(i)), S.up(T.deadline_of(i), now))) == True{} : Bool}) -> {T.running(T.st_of(T.tick_info(T.expired(i, now), i))) == True{} : Bool}:
  match i:
    case T.Info{st, s, lim, sp, dl, q}:
      match st:
        case T.Running{}:
          match dl:
            case T.Unlimited{}:
              {==}
            case T.Value{d}:
              at_tick.tb(Nat.is_le(d, now), s, lim, sp, T.Value{d}, q, o)
        case T.Finished{}:
          hr
        case T.Failed{}:
          hr
        case T.Cancelled{}:
          hr

def at_tick.base(t: T.Node, +now: Nat, hr: {S.is_running(t) == True{} : Bool}, o: {Bool.not(AgentTree.late(t, now)) == True{} : Bool}) -> {S.is_running(T.tick(t, now, False{})) == True{} : Bool}:
  match t:
    case T.Leaf{i}:
      at_tick.tinfo(i, now, hr, o)
    case T.Split{i, own, l, r}:
      at_tick.tinfo(i, now, hr, o)

# T8: on an on-time path the running node at its end still runs after a tick
def at_tick.run_eq(-t: T.Node, -n: T.Node, tn: {t == n : T.Node}, hr: {S.is_running(n) == True{} : Bool}) -> {S.is_running(t) == True{} : Bool}:
  %Equal.sym(T.Node, t, n, tn) : {S.is_running(_) == True{} : Bool}
  hr

def at_tick.keeps(p: List<&2, T.Dir>, +t: T.Node, +now: Nat, -n: T.Node, e: {S.node_at(p, t) == Some{n} : Maybe<&2, T.Node>}, hr: {S.is_running(n) == True{} : Bool}, +o: {AgentTree.on_time_path(p, t, now) == True{} : Bool}) -> {AgentTree.runs_at(S.node_at(p, T.tick(t, now, False{}))) == True{} : Bool}:
  match p:
    case Nil{}:
      at_tick.base(t, now, at_tick.run_eq(t, n, Equal.cong(Maybe<&2, T.Node>, T.Node, m => at_tick.unwrap(m, t), Some{t}, Some{n}, e), hr), o)
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match t:
            case T.Leaf{i}:
              at_tick.none_some(n, {AgentTree.runs_at(S.node_at(T.GoL{} <> rest, T.tick(T.Leaf{i}, now, False{}))) == True{} : Bool}, e)
            case T.Split{i, own, l, r}:
              %at_tick.exp_false(i, now, LP.at_patch.and_l(Bool.not(AgentTree.late(T.Split{i, own, l, r}, now)), AgentTree.on_time_path(rest, l, now), o)) : {AgentTree.runs_at(S.node_at(rest, T.tick(l, now, _))) == True{} : Bool}
              at_tick.keeps(rest, l, now, n, e, hr, LP.at_patch.and_r(Bool.not(AgentTree.late(T.Split{i, own, l, r}, now)), AgentTree.on_time_path(rest, l, now), o))
        case T.GoR{}:
          match t:
            case T.Leaf{i}:
              at_tick.none_some(n, {AgentTree.runs_at(S.node_at(T.GoR{} <> rest, T.tick(T.Leaf{i}, now, False{}))) == True{} : Bool}, e)
            case T.Split{i, own, l, r}:
              %at_tick.exp_false(i, now, LP.at_patch.and_l(Bool.not(AgentTree.late(T.Split{i, own, l, r}, now)), AgentTree.on_time_path(rest, r, now), o)) : {AgentTree.runs_at(S.node_at(rest, T.tick(r, now, _))) == True{} : Bool}
              at_tick.keeps(rest, r, now, n, e, hr, LP.at_patch.and_r(Bool.not(AgentTree.late(T.Split{i, own, l, r}, now)), AgentTree.on_time_path(rest, r, now), o))

# a cancelled node never runs
def at_tick.cancel_stops(i: T.Info) -> {T.running(T.st_of(T.cancel_info(i))) == False{} : Bool}:
  match i:
    case T.Info{st, s, lim, sp, dl, q}:
      match st:
        case T.Running{}:
          {==}
        case T.Finished{}:
          {==}
        case T.Failed{}:
          {==}
        case T.Cancelled{}:
          {==}

# T8: a tick with the cut flag set leaves no running node at any path
def at_tick.cut_stops(p: List<&2, T.Dir>, +t: T.Node, +now: Nat) -> {AgentTree.runs_at(S.node_at(p, T.tick(t, now, True{}))) == False{} : Bool}:
  match p:
    case Nil{}:
      match t:
        case T.Leaf{i}:
          at_tick.cancel_stops(i)
        case T.Split{i, own, l, r}:
          at_tick.cancel_stops(i)
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match t:
            case T.Leaf{i}:
              {==}
            case T.Split{i, own, l, r}:
              at_tick.cut_stops(rest, l, now)
        case T.GoR{}:
          match t:
            case T.Leaf{i}:
              {==}
            case T.Split{i, own, l, r}:
              at_tick.cut_stops(rest, r, now)

# a node is late exactly when it is expired
def at_tick.late_eq(i: T.Info, +now: Nat) -> {Bool.and(T.running(T.st_of(i)), S.up(T.deadline_of(i), now)) == T.expired(i, now) : Bool}:
  match i:
    case T.Info{st, s, lim, sp, dl, q}:
      match dl:
        case T.Unlimited{}:
          {==}
        case T.Value{d}:
          {==}

# a node whose tick flag is not False does not run after its tick
def at_tick.cut_base(a: Bool, i: T.Info, o: {Bool.not(a) == False{} : Bool}) -> {T.running(T.st_of(T.tick_info(a, i))) == False{} : Bool}:
  match a:
    case True{}:
      at_tick.cancel_stops(i)
    case False{}:
      LP.at_patch.absurd({T.running(T.st_of(T.tick_info(False{}, i))) == False{} : Bool}, Equal.sym(Bool, True{}, False{}, o))

# T8: under the cut flag c, a node with a late node on its path from the
# root (itself included) does not run after a tick
def at_tick.late_below(p: List<&2, T.Dir>, c: Bool, +t: T.Node, +now: Nat, o: {Bool.and(Bool.not(c), AgentTree.on_time_path(p, t, now)) == False{} : Bool}) -> {AgentTree.runs_at(S.node_at(p, T.tick(t, now, c))) == False{} : Bool}:
  match p:
    case Nil{}:
      match c:
        case True{}:
          at_tick.cut_stops(Nil{}, t, now)
        case False{}:
          match t:
            case T.Leaf{i}:
              %at_tick.late_eq(i, now) : {T.running(T.st_of(T.tick_info(_, i))) == False{} : Bool}
              at_tick.cut_base(Bool.and(T.running(T.st_of(i)), S.up(T.deadline_of(i), now)), i, o)
            case T.Split{i, own, l, r}:
              %at_tick.late_eq(i, now) : {T.running(T.st_of(T.tick_info(_, i))) == False{} : Bool}
              at_tick.cut_base(Bool.and(T.running(T.st_of(i)), S.up(T.deadline_of(i), now)), i, o)
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match c:
            case True{}:
              at_tick.cut_stops(T.GoL{} <> rest, t, now)
            case False{}:
              match t:
                case T.Leaf{i}:
                  {==}
                case T.Split{i, own, l, r}:
                  %at_tick.late_eq(i, now) : {AgentTree.runs_at(S.node_at(rest, T.tick(l, now, _))) == False{} : Bool}
                  at_tick.late_below(rest, Bool.and(T.running(T.st_of(i)), S.up(T.deadline_of(i), now)), l, now, o)
        case T.GoR{}:
          match c:
            case True{}:
              at_tick.cut_stops(T.GoR{} <> rest, t, now)
            case False{}:
              match t:
                case T.Leaf{i}:
                  {==}
                case T.Split{i, own, l, r}:
                  %at_tick.late_eq(i, now) : {AgentTree.runs_at(S.node_at(rest, T.tick(r, now, _))) == False{} : Bool}
                  at_tick.late_below(rest, Bool.and(T.running(T.st_of(i)), S.up(T.deadline_of(i), now)), r, now, o)
