# eukhe: lemmas of area agent_crown for reachable crowns (T14): every
# event keeps the running help leaves at running nodes, and the nodes plus
# the help leaves within max_nodes

import Base
import ../../../bend/agent_tree.bend as T
import ../../../bend/agent_crown.bend as A
import ../../../spec/agents/agent_tree.bend as S
import ../../../spec/agents/agent_crown.bend as CS
import ../../agent_tree/base/reach.bend as AR
import ../../agent_tree/base/edit.bend as E
import ./view.bend as V
import ./step.bend as St
import ./grow.bend as Gw

# Help leaf edits
# ---------------

# a change of the help leaves keeps a Bool property of them
def ac_reach.HR(r: A.HRes, P: List<&2, A.Help> -> Bool) -> Data:
  match r:
    case A.HOk{xs}:
      {P(xs) == True{} : Bool}
    case A.HNo{why}:
      Unit

def ac_reach.or_cancel(st: T.Status, -x: Bool) -> {Bool.or(Bool.not(T.running(T.cancel_st(st))), x) == True{} : Bool}:
  match st:
    case T.Running{}:
      {==}
    case T.Finished{}:
      {==}
    case T.Failed{}:
      {==}
    case T.Cancelled{}:
      {==}

def ac_reach.or_end(ok: Bool, -x: Bool) -> {Bool.or(Bool.not(T.running(A.end_st(ok))), x) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# No orphan
# ---------

# a swept help leaf runs only at a node that runs
def ac_reach.one_placed(r: Bool, +st: T.Status, +late: Bool) -> {Bool.or(Bool.not(T.running(A.sweep_st(Bool.or(Bool.not(r), late), st))), r) == True{} : Bool}:
  match r:
    case True{}:
      AR.at_reach.or_r(Bool.not(T.running(A.sweep_st(late, st))), True{}, {==})
    case False{}:
      ac_reach.or_cancel(st, False{})

def ac_reach.sweep_placed(hs: List<&2, A.Help>, +y: T.Node, +e: T.Ev) -> {CS.placed_in(y, A.sweep(hs, y, e)) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, rest}:
      match h:
        case A.Help{+p, +st, lim, sp, +dl}:
          %St.ac_step.runs_node(p, y) : {Bool.and(Bool.or(Bool.not(T.running(A.sweep_st(Bool.or(Bool.not(A.runs(A.node_at(p, y))), A.help_late(dl, e)), st))), _), CS.placed_in(y, A.sweep(rest, y, e))) == True{} : Bool}
          AR.at_reach.and_t(Bool.or(Bool.not(T.running(A.sweep_st(Bool.or(Bool.not(A.runs(A.node_at(p, y))), A.help_late(dl, e)), st))), A.runs(A.node_at(p, y))), CS.placed_in(y, A.sweep(rest, y, e)), ac_reach.one_placed(A.runs(A.node_at(p, y)), st, A.help_late(dl, e)), ac_reach.sweep_placed(rest, y, e))

def ac_reach.on_placed(+s: T.Step, +t: T.Node, +hs: List<&2, A.Help>, +e: T.Ev, h: {CS.placed_in(t, hs) == True{} : Bool}) -> {CS.helps_placed(A.cafter(A.on_tree(s, hs, e), A.Crown{t, hs})) == True{} : Bool}:
  match s:
    case T.Took{x}:
      ac_reach.sweep_placed(hs, A.shift(x, A.loads(hs), False{}), e)
    case T.Refused{why}:
      h

def ac_reach.placed_app(+t: T.Node, hs: List<&2, A.Help>, +x: A.Help, +h: {CS.placed_in(t, hs) == True{} : Bool}, +h2: {CS.placed_in(t, [x]) == True{} : Bool}) -> {CS.placed_in(t, List.append(&2, A.Help, hs, [x])) == True{} : Bool}:
  match hs:
    case Nil{}:
      h2
    case Con{y, rest}:
      match y:
        case A.Help{+p, +st, lim, sp, dl}:
          AR.at_reach.and_t(Bool.or(Bool.not(T.running(st)), CS.runs_at(S.node_at(p, t))), CS.placed_in(t, List.append(&2, A.Help, rest, [x])), AR.at_reach.and_l(Bool.or(Bool.not(T.running(st)), CS.runs_at(S.node_at(p, t))), CS.placed_in(t, rest), h), ac_reach.placed_app(t, rest, x, AR.at_reach.and_r(Bool.or(Bool.not(T.running(st)), CS.runs_at(S.node_at(p, t))), CS.placed_in(t, rest), h), h2))

# the node at p of the view runs: so does the node at p of the tree
def ac_reach.runs_tree(+p: List<&2, T.Dir>, +t: T.Node, +hs: List<&2, A.Help>, -n: T.Node, em: {A.node_at(p, A.view(t, hs)) == Some{n} : Maybe<&2, T.Node>}, er: {T.running(T.st_of(T.info(n))) == True{} : Bool}) -> {CS.runs_at(S.node_at(p, t)) == True{} : Bool}:
  %St.ac_step.runs_node(p, t) : {_ == True{} : Bool}
  %V.ac_view.runs_shift(p, t, A.loads(hs), True{}) : {_ == True{} : Bool}
  %Equal.sym(Maybe<&2, T.Node>, A.node_at(p, A.view(t, hs)), Some{n}, em) : {A.runs(_) == True{} : Bool}
  er

def ac_reach.fit_placed(ok: Bool, +n: T.Node, +t: T.Node, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>, +a: Nat, +margin: Nat, +h: {CS.placed_in(t, hs) == True{} : Bool}, +hr: {CS.runs_at(S.node_at(p, t)) == True{} : Bool}) -> {CS.helps_placed(A.cafter(A.help_fit(ok, n, t, hs, p, a, margin), A.Crown{t, hs})) == True{} : Bool}:
  match ok:
    case True{}:
      ac_reach.placed_app(t, hs, A.Help{p, T.Running{}, A.grant(T.free(n), a), 0n, T.lim_less(T.deadline_of(T.info(n)), margin)}, h, AR.at_reach.and_t(CS.runs_at(S.node_at(p, t)), True{}, hr, {==}))
    case False{}:
      h

def ac_reach.room_placed(room: Bool, +n: T.Node, +t: T.Node, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>, +a: Nat, +margin: Nat, +h: {CS.placed_in(t, hs) == True{} : Bool}, +hr: {CS.runs_at(S.node_at(p, t)) == True{} : Bool}) -> {CS.helps_placed(A.cafter(A.help_room(room, n, t, hs, p, a, margin), A.Crown{t, hs})) == True{} : Bool}:
  match room:
    case True{}:
      ac_reach.fit_placed(T.lim_fits(a, T.free(n)), n, t, hs, p, a, margin, h, hr)
    case False{}:
      h

def ac_reach.run_placed(run: Bool, +n: T.Node, +t: T.Node, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>, +a: Nat, +room: Bool, +margin: Nat, +h: {CS.placed_in(t, hs) == True{} : Bool}, em: {A.node_at(p, A.view(t, hs)) == Some{n} : Maybe<&2, T.Node>}, er: {T.running(T.st_of(T.info(n))) == run : Bool}) -> {CS.helps_placed(A.cafter(A.help_run(run, n, t, hs, p, a, room, margin), A.Crown{t, hs})) == True{} : Bool}:
  match run:
    case True{}:
      ac_reach.room_placed(room, n, t, hs, p, a, margin, h, ac_reach.runs_tree(p, t, hs, n, em, er))
    case False{}:
      h

def ac_reach.help_placed(+m: Maybe<&2, T.Node>, +t: T.Node, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>, +a: Nat, +room: Bool, +margin: Nat, +h: {CS.placed_in(t, hs) == True{} : Bool}, em: {A.node_at(p, A.view(t, hs)) == m : Maybe<&2, T.Node>}) -> {CS.helps_placed(A.cafter(A.help_node(m, t, hs, p, a, room, margin), A.Crown{t, hs})) == True{} : Bool}:
  match m:
    case None{}:
      h
    case Some{+n}:
      ac_reach.run_placed(T.running(T.st_of(T.info(n))), n, t, hs, p, a, room, margin, h, em, {==})

def ac_reach.cons_placed(+h: A.Help, +r: A.HRes, +t: T.Node, +hc: {CS.placed_in(t, [h]) == True{} : Bool}, +hr: ac_reach.HR(r, xs => CS.placed_in(t, xs))) -> ac_reach.HR(A.hres_cons(h, r), xs => CS.placed_in(t, xs)):
  match h:
    case A.Help{+p, +st, lim, sp, dl}:
      match r:
        case A.HOk{xs}:
          AR.at_reach.and_t(Bool.or(Bool.not(T.running(st)), CS.runs_at(S.node_at(p, t))), CS.placed_in(t, xs), AR.at_reach.and_l(Bool.or(Bool.not(T.running(st)), CS.runs_at(S.node_at(p, t))), True{}, hc), hr)
        case A.HNo{why}:
          Unit{}

def ac_reach.head_placed(+h: A.Help, +rest: List<&2, A.Help>, +t: T.Node, +hh: {CS.placed_in(t, h <> rest) == True{} : Bool}) -> {CS.placed_in(t, [h]) == True{} : Bool}:
  match h:
    case A.Help{+p, +st, lim, sp, dl}:
      AR.at_reach.and_t(Bool.or(Bool.not(T.running(st)), CS.runs_at(S.node_at(p, t))), True{}, AR.at_reach.and_l(Bool.or(Bool.not(T.running(st)), CS.runs_at(S.node_at(p, t))), CS.placed_in(t, rest), hh), {==})

def ac_reach.tail_placed(+h: A.Help, +rest: List<&2, A.Help>, +t: T.Node, +hh: {CS.placed_in(t, h <> rest) == True{} : Bool}) -> {CS.placed_in(t, rest) == True{} : Bool}:
  match h:
    case A.Help{+p, +st, lim, sp, dl}:
      AR.at_reach.and_r(Bool.or(Bool.not(T.running(st)), CS.runs_at(S.node_at(p, t))), CS.placed_in(t, rest), hh)

def ac_reach.sfit_placed(ok: Bool, +p: List<&2, T.Dir>, +st: T.Status, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +a: Nat, +rest: List<&2, A.Help>, +t: T.Node, +hh: {CS.placed_in(t, A.Help{p, st, lim, sp, dl} <> rest) == True{} : Bool}) -> ac_reach.HR(A.spend_fit(ok, A.Help{p, st, lim, sp, dl}, a, rest), xs => CS.placed_in(t, xs)):
  match ok:
    case True{}:
      hh
    case False{}:
      Unit{}

def ac_reach.spend_placed(k: Nat, hs: List<&2, A.Help>, +a: Nat, +t: T.Node, +hh: {CS.placed_in(t, hs) == True{} : Bool}) -> ac_reach.HR(A.spend_k(k, hs, a), xs => CS.placed_in(t, xs)):
  match k:
    case 0n:
      match hs:
        case Nil{}:
          Unit{}
        case Con{h, rest}:
          match h:
            case A.Help{p, st, +lim, +sp, dl}:
              match st:
                case T.Running{}:
                  ac_reach.sfit_placed(T.lim_fits(a, T.lim_less(lim, sp)), p, T.Running{}, lim, sp, dl, a, rest, t, hh)
                case T.Finished{}:
                  Unit{}
                case T.Failed{}:
                  Unit{}
                case T.Cancelled{}:
                  Unit{}
    case 1n++j:
      match hs:
        case Nil{}:
          Unit{}
        case Con{+h, +rest}:
          ac_reach.cons_placed(h, A.spend_k(j, rest, a), t, ac_reach.head_placed(h, rest, t, hh), ac_reach.spend_placed(j, rest, a, t, ac_reach.tail_placed(h, rest, t, hh)))

def ac_reach.end_placed(k: Nat, hs: List<&2, A.Help>, +ok: Bool, +t: T.Node, +hh: {CS.placed_in(t, hs) == True{} : Bool}) -> ac_reach.HR(A.end_k(k, hs, ok), xs => CS.placed_in(t, xs)):
  match k:
    case 0n:
      match hs:
        case Nil{}:
          Unit{}
        case Con{h, rest}:
          match h:
            case A.Help{+p, st, lim, sp, dl}:
              match st:
                case T.Running{}:
                  AR.at_reach.and_t(Bool.or(Bool.not(T.running(A.end_st(ok))), CS.runs_at(S.node_at(p, t))), CS.placed_in(t, rest), ac_reach.or_end(ok, CS.runs_at(S.node_at(p, t))), AR.at_reach.and_r(Bool.or(Bool.not(True{}), CS.runs_at(S.node_at(p, t))), CS.placed_in(t, rest), hh))
                case T.Finished{}:
                  Unit{}
                case T.Failed{}:
                  Unit{}
                case T.Cancelled{}:
                  Unit{}
    case 1n++j:
      match hs:
        case Nil{}:
          Unit{}
        case Con{+h, +rest}:
          ac_reach.cons_placed(h, A.end_k(j, rest, ok), t, ac_reach.head_placed(h, rest, t, hh), ac_reach.end_placed(j, rest, ok, t, ac_reach.tail_placed(h, rest, t, hh)))

def ac_reach.hres_placed(+r: A.HRes, +t: T.Node, +hs: List<&2, A.Help>, +h: {CS.placed_in(t, hs) == True{} : Bool}, +hr: ac_reach.HR(r, xs => CS.placed_in(t, xs))) -> {CS.helps_placed(A.cafter(A.hres_crown(r, t), A.Crown{t, hs})) == True{} : Bool}:
  match r:
    case A.HOk{xs}:
      hr
    case A.HNo{why}:
      h

# every event keeps every running help leaf at a running node
def ac_reach.step_placed(+b: T.Bounds, +c: A.Crown, +e: A.CEv, +h: {CS.helps_placed(c) == True{} : Bool}) -> {CS.helps_placed(A.cafter(A.hstep(b, c, e), c)) == True{} : Bool}:
  match c:
    case A.Crown{+t, +hs}:
      match e:
        case A.OnTree{+ev}:
          ac_reach.on_placed(T.step(A.cbounds(b, hs), A.view(t, hs), ev), t, hs, ev, h)
        case A.EvHelp{+p, +a}:
          ac_reach.help_placed(A.node_at(p, A.view(t, hs)), t, hs, p, a, Nat.is_le(Nat.add(Nat.add(T.size(t), A.hcount(hs)), 1n), T.bound_nodes(b)), T.bound_margin(b), h, {==})
        case A.EvHelpSpend{k, a}:
          ac_reach.hres_placed(A.spend_k(k, hs, a), t, hs, h, ac_reach.spend_placed(k, hs, a, t, h))
        case A.EvHelpEnd{k, ok}:
          ac_reach.hres_placed(A.end_k(k, hs, ok), t, hs, h, ac_reach.end_placed(k, hs, ok, t, h))

def ac_reach.run_placed_all(evs: List<&2, A.CEv>, +b: T.Bounds, +c: A.Crown, +h: {CS.helps_placed(c) == True{} : Bool}) -> {CS.helps_placed(A.crun(evs, b, c)) == True{} : Bool}:
  match evs:
    case Nil{}:
      h
    case Con{+e, es}:
      ac_reach.run_placed_all(es, b, A.cafter(A.hstep(b, c, e), c), ac_reach.step_placed(b, c, e, h))

# Nodes bound
# -----------

# l <= x + l
def ac_reach.le_add_l(+x: Nat, +l: Nat) -> {Nat.is_le(l, Nat.add(x, l)) == True{} : Bool}:
  %AR.at_reach.add_comm(l, x) : {Nat.is_le(l, _) == True{} : Bool}
  AR.at_reach.le_add_r(l, x)

# x + l <= n: x <= n - l
def ac_reach.le_sub(+x: Nat, l: Nat, n: Nat, h: {Nat.is_le(Nat.add(x, l), n) == True{} : Bool}) -> {Nat.is_le(x, Nat.sub(n, l)) == True{} : Bool}:
  match l:
    case 0n:
      AR.at_reach.tr(Nat, n, Nat.sub(n, 0n), z => {Nat.is_le(x, z) == True{} : Bool}, Equal.sym(Nat, Nat.sub(n, 0n), n, V.ac_view.sub_zero(n)), AR.at_reach.tr(Nat, Nat.add(x, 0n), x, z => {Nat.is_le(z, n) == True{} : Bool}, AR.at_reach.add_zero(x), h))
    case 1n+q:
      match n:
        case 0n:
          AR.at_reach.absurd({Nat.is_le(x, 0n) == True{} : Bool}, AR.at_reach.tr(Nat, Nat.add(x, 1n+q), 1n+Nat.add(x, q), z => {Nat.is_le(z, 0n) == True{} : Bool}, AR.at_reach.add_succ(x, q), h))
        case 1n+m:
          ac_reach.le_sub(x, q, m, AR.at_reach.tr(Nat, Nat.add(x, 1n+q), 1n+Nat.add(x, q), z => {Nat.is_le(z, 1n+m) == True{} : Bool}, AR.at_reach.add_succ(x, q), h))

# x <= n - l and l <= n: x + l <= n
def ac_reach.sub_back(+x: Nat, +l: Nat, +n: Nat, hx: {Nat.is_le(x, Nat.sub(n, l)) == True{} : Bool}, hl: {Nat.is_le(l, n) == True{} : Bool}) -> {Nat.is_le(Nat.add(x, l), n) == True{} : Bool}:
  %AR.at_reach.add_comm(l, x) : {Nat.is_le(_, n) == True{} : Bool}
  AR.at_reach.fit_sub(l, x, n, hl, hx)

def ac_reach.size_shift(+t: T.Node, +ls: List<&2, A.Load>, +up: Bool) -> {T.size(A.shift(t, ls, up)) == T.size(t) : Nat}:
  match t:
    case T.Leaf{i}:
      {==}
    case T.Split{i, own, l, r}:
      AR.at_reach.size_kids(T.size(A.shift(l, A.down(ls, T.GoL{}), up)), T.size(l), T.size(A.shift(r, A.down(ls, T.GoR{}), up)), T.size(r), ac_reach.size_shift(l, A.down(ls, T.GoL{}), up), ac_reach.size_shift(r, A.down(ls, T.GoR{}), up))

def ac_reach.sweep_count(hs: List<&2, A.Help>, -t: T.Node, -e: T.Ev) -> {A.hcount(A.sweep(hs, t, e)) == A.hcount(hs) : Nat}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, rest}:
      match h:
        case A.Help{p, st, lim, sp, dl}:
          Equal.cong(Nat, Nat, z => 1n+z, A.hcount(A.sweep(rest, t, e)), A.hcount(rest), ac_reach.sweep_count(rest, t, e))

def ac_reach.count_app(hs: List<&2, A.Help>, -x: A.Help) -> {A.hcount(List.append(&2, A.Help, hs, [x])) == Nat.add(A.hcount(hs), 1n) : Nat}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, rest}:
      Equal.cong(Nat, Nat, z => 1n+z, A.hcount(List.append(&2, A.Help, rest, [x])), Nat.add(A.hcount(rest), 1n), ac_reach.count_app(rest, x))

def ac_reach.nodes_cb(b: T.Bounds, -hs: List<&2, A.Help>) -> {T.bound_nodes(A.cbounds(b, hs)) == Nat.sub(T.bound_nodes(b), A.hcount(hs)) : Nat}:
  match b:
    case T.Bounds{d, n, m}:
      {==}

def ac_reach.depth_cb(b: T.Bounds, -hs: List<&2, A.Help>) -> {T.bound_depth(A.cbounds(b, hs)) == T.bound_depth(b) : Nat}:
  match b:
    case T.Bounds{d, n, m}:
      {==}

# the code's count of the crown within n
def ac_reach.nb(c: A.Crown, n: Nat) -> Bool:
  match c:
    case A.Crown{t, hs}:
      Nat.is_le(Nat.add(T.size(t), A.hcount(hs)), n)

def ac_reach.on_nb(+s: T.Step, +t: T.Node, +hs: List<&2, A.Help>, +e: T.Ev, +n: Nat, +h: {ac_reach.nb(A.Crown{t, hs}, n) == True{} : Bool}, hx: {Nat.is_le(T.size(T.after(s, A.view(t, hs))), Nat.sub(n, A.hcount(hs))) == True{} : Bool}) -> {ac_reach.nb(A.cafter(A.on_tree(s, hs, e), A.Crown{t, hs}), n) == True{} : Bool}:
  match s:
    case T.Took{x}:
      +hl = AR.at_reach.le_trans(A.hcount(hs), Nat.add(T.size(t), A.hcount(hs)), n, ac_reach.le_add_l(T.size(t), A.hcount(hs)), h)
      %Equal.sym(Nat, T.size(A.shift(x, A.loads(hs), False{})), T.size(x), ac_reach.size_shift(x, A.loads(hs), False{})) : {Nat.is_le(Nat.add(_, A.hcount(A.sweep(hs, A.shift(x, A.loads(hs), False{}), e))), n) == True{} : Bool}
      %Equal.sym(Nat, A.hcount(A.sweep(hs, A.shift(x, A.loads(hs), False{}), e)), A.hcount(hs), ac_reach.sweep_count(hs, A.shift(x, A.loads(hs), False{}), e)) : {Nat.is_le(Nat.add(T.size(x), _), n) == True{} : Bool}
      ac_reach.sub_back(T.size(x), A.hcount(hs), n, hx, hl)
    case T.Refused{why}:
      h

def ac_reach.fit_nb(ok: Bool, +nd: T.Node, +t: T.Node, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>, +a: Nat, +margin: Nat, +n: Nat, +h: {ac_reach.nb(A.Crown{t, hs}, n) == True{} : Bool}, +hr: {Nat.is_le(Nat.add(Nat.add(T.size(t), A.hcount(hs)), 1n), n) == True{} : Bool}) -> {ac_reach.nb(A.cafter(A.help_fit(ok, nd, t, hs, p, a, margin), A.Crown{t, hs}), n) == True{} : Bool}:
  match ok:
    case True{}:
      %Equal.sym(Nat, A.hcount(List.append(&2, A.Help, hs, [A.Help{p, T.Running{}, A.grant(T.free(nd), a), 0n, T.lim_less(T.deadline_of(T.info(nd)), margin)}])), Nat.add(A.hcount(hs), 1n), ac_reach.count_app(hs, A.Help{p, T.Running{}, A.grant(T.free(nd), a), 0n, T.lim_less(T.deadline_of(T.info(nd)), margin)})) : {Nat.is_le(Nat.add(T.size(t), _), n) == True{} : Bool}
      %AR.at_reach.add_assoc(T.size(t), A.hcount(hs), 1n) : {Nat.is_le(_, n) == True{} : Bool}
      hr
    case False{}:
      h

def ac_reach.room_nb(room: Bool, +nd: T.Node, +t: T.Node, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>, +a: Nat, +margin: Nat, +n: Nat, +h: {ac_reach.nb(A.Crown{t, hs}, n) == True{} : Bool}, er: {Nat.is_le(Nat.add(Nat.add(T.size(t), A.hcount(hs)), 1n), n) == room : Bool}) -> {ac_reach.nb(A.cafter(A.help_room(room, nd, t, hs, p, a, margin), A.Crown{t, hs}), n) == True{} : Bool}:
  match room:
    case True{}:
      ac_reach.fit_nb(T.lim_fits(a, T.free(nd)), nd, t, hs, p, a, margin, n, h, er)
    case False{}:
      h

def ac_reach.run_nb(run: Bool, +nd: T.Node, +t: T.Node, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>, +a: Nat, +room: Bool, +margin: Nat, +n: Nat, +h: {ac_reach.nb(A.Crown{t, hs}, n) == True{} : Bool}, er: {Nat.is_le(Nat.add(Nat.add(T.size(t), A.hcount(hs)), 1n), n) == room : Bool}) -> {ac_reach.nb(A.cafter(A.help_run(run, nd, t, hs, p, a, room, margin), A.Crown{t, hs}), n) == True{} : Bool}:
  match run:
    case True{}:
      ac_reach.room_nb(room, nd, t, hs, p, a, margin, n, h, er)
    case False{}:
      h

def ac_reach.help_nb(+m: Maybe<&2, T.Node>, +t: T.Node, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>, +a: Nat, +margin: Nat, +n: Nat, +h: {ac_reach.nb(A.Crown{t, hs}, n) == True{} : Bool}) -> {ac_reach.nb(A.cafter(A.help_node(m, t, hs, p, a, Nat.is_le(Nat.add(Nat.add(T.size(t), A.hcount(hs)), 1n), n), margin), A.Crown{t, hs}), n) == True{} : Bool}:
  match m:
    case None{}:
      h
    case Some{+nd}:
      ac_reach.run_nb(T.running(T.st_of(T.info(nd))), nd, t, hs, p, a, Nat.is_le(Nat.add(Nat.add(T.size(t), A.hcount(hs)), 1n), n), margin, n, h, {==})

def ac_reach.cons_count(+h: A.Help, +r: A.HRes, +m: Nat, hr: ac_reach.HR(r, xs => Nat.is_eq(A.hcount(xs), m))) -> ac_reach.HR(A.hres_cons(h, r), xs => Nat.is_eq(A.hcount(xs), 1n+m)):
  match r:
    case A.HOk{xs}:
      hr
    case A.HNo{why}:
      Unit{}

def ac_reach.sfit_count(ok: Bool, +x: A.Help, +a: Nat, +rest: List<&2, A.Help>) -> ac_reach.HR(A.spend_fit(ok, x, a, rest), xs => Nat.is_eq(A.hcount(xs), 1n+A.hcount(rest))):
  match ok:
    case True{}:
      match x:
        case A.Help{p, st, lim, sp, dl}:
          E.at_edit.eq_refl(1n+A.hcount(rest))
    case False{}:
      Unit{}

def ac_reach.spend_count(k: Nat, hs: List<&2, A.Help>, +a: Nat) -> ac_reach.HR(A.spend_k(k, hs, a), xs => Nat.is_eq(A.hcount(xs), A.hcount(hs))):
  match k:
    case 0n:
      match hs:
        case Nil{}:
          Unit{}
        case Con{h, +rest}:
          match h:
            case A.Help{p, st, +lim, +sp, dl}:
              match st:
                case T.Running{}:
                  ac_reach.sfit_count(T.lim_fits(a, T.lim_less(lim, sp)), A.Help{p, T.Running{}, lim, sp, dl}, a, rest)
                case T.Finished{}:
                  Unit{}
                case T.Failed{}:
                  Unit{}
                case T.Cancelled{}:
                  Unit{}
    case 1n++j:
      match hs:
        case Nil{}:
          Unit{}
        case Con{+h, +rest}:
          ac_reach.cons_count(h, A.spend_k(j, rest, a), A.hcount(rest), ac_reach.spend_count(j, rest, a))

def ac_reach.end_count(k: Nat, hs: List<&2, A.Help>, +ok: Bool) -> ac_reach.HR(A.end_k(k, hs, ok), xs => Nat.is_eq(A.hcount(xs), A.hcount(hs))):
  match k:
    case 0n:
      match hs:
        case Nil{}:
          Unit{}
        case Con{h, +rest}:
          match h:
            case A.Help{p, st, lim, sp, dl}:
              match st:
                case T.Running{}:
                  E.at_edit.eq_refl(1n+A.hcount(rest))
                case T.Finished{}:
                  Unit{}
                case T.Failed{}:
                  Unit{}
                case T.Cancelled{}:
                  Unit{}
    case 1n++j:
      match hs:
        case Nil{}:
          Unit{}
        case Con{+h, +rest}:
          ac_reach.cons_count(h, A.end_k(j, rest, ok), A.hcount(rest), ac_reach.end_count(j, rest, ok))

def ac_reach.eq_nat(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      AR.at_reach.absurd({0n == 1n+y : Nat}, h)
    case 1n+x 0n:
      AR.at_reach.absurd({1n+x == 0n : Nat}, h)
    case 1n+x 1n+y:
      Equal.cong(Nat, Nat, z => 1n+z, x, y, ac_reach.eq_nat(x, y, h))

def ac_reach.hres_nb(+r: A.HRes, +t: T.Node, +hs: List<&2, A.Help>, +n: Nat, +h: {ac_reach.nb(A.Crown{t, hs}, n) == True{} : Bool}, hr: ac_reach.HR(r, xs => Nat.is_eq(A.hcount(xs), A.hcount(hs)))) -> {ac_reach.nb(A.cafter(A.hres_crown(r, t), A.Crown{t, hs}), n) == True{} : Bool}:
  match r:
    case A.HOk{xs}:
      %Equal.sym(Nat, A.hcount(xs), A.hcount(hs), ac_reach.eq_nat(A.hcount(xs), A.hcount(hs), hr)) : {Nat.is_le(Nat.add(T.size(t), _), n) == True{} : Bool}
      h
    case A.HNo{why}:
      h

# every event keeps the nodes plus the help leaves within max_nodes
def ac_reach.step_nb(+b: T.Bounds, +c: A.Crown, +e: A.CEv, +h: {ac_reach.nb(c, T.bound_nodes(b)) == True{} : Bool}) -> {ac_reach.nb(A.cafter(A.hstep(b, c, e), c), T.bound_nodes(b)) == True{} : Bool}:
  match c:
    case A.Crown{+t, +hs}:
      match e:
        case A.OnTree{+ev}:
          +hv = AR.at_reach.tr(Nat, T.size(t), T.size(A.view(t, hs)), z => {Nat.is_le(z, T.bound_nodes(A.cbounds(b, hs))) == True{} : Bool}, Equal.sym(Nat, T.size(A.view(t, hs)), T.size(t), ac_reach.size_shift(t, A.loads(hs), True{})), AR.at_reach.tr(Nat, Nat.sub(T.bound_nodes(b), A.hcount(hs)), T.bound_nodes(A.cbounds(b, hs)), z => {Nat.is_le(T.size(t), z) == True{} : Bool}, Equal.sym(Nat, T.bound_nodes(A.cbounds(b, hs)), Nat.sub(T.bound_nodes(b), A.hcount(hs)), ac_reach.nodes_cb(b, hs)), ac_reach.le_sub(T.size(t), A.hcount(hs), T.bound_nodes(b), h)))
          +hx = AR.at_reach.tr(Nat, T.bound_nodes(A.cbounds(b, hs)), Nat.sub(T.bound_nodes(b), A.hcount(hs)), z => {Nat.is_le(T.size(T.after(T.step(A.cbounds(b, hs), A.view(t, hs), ev), A.view(t, hs))), z) == True{} : Bool}, ac_reach.nodes_cb(b, hs), Gw.ac_grow.size_step(A.cbounds(b, hs), A.view(t, hs), ev, hv))
          ac_reach.on_nb(T.step(A.cbounds(b, hs), A.view(t, hs), ev), t, hs, ev, T.bound_nodes(b), h, hx)
        case A.EvHelp{+p, +a}:
          ac_reach.help_nb(A.node_at(p, A.view(t, hs)), t, hs, p, a, T.bound_margin(b), T.bound_nodes(b), h)
        case A.EvHelpSpend{k, a}:
          ac_reach.hres_nb(A.spend_k(k, hs, a), t, hs, T.bound_nodes(b), h, ac_reach.spend_count(k, hs, a))
        case A.EvHelpEnd{k, ok}:
          ac_reach.hres_nb(A.end_k(k, hs, ok), t, hs, T.bound_nodes(b), h, ac_reach.end_count(k, hs, ok))

def ac_reach.run_nb_all(evs: List<&2, A.CEv>, +b: T.Bounds, +c: A.Crown, +h: {ac_reach.nb(c, T.bound_nodes(b)) == True{} : Bool}) -> {ac_reach.nb(A.crun(evs, b, c), T.bound_nodes(b)) == True{} : Bool}:
  match evs:
    case Nil{}:
      h
    case Con{+e, es}:
      ac_reach.run_nb_all(es, b, A.cafter(A.hstep(b, c, e), c), ac_reach.step_nb(b, c, e, h))

# the spec's count is the code's
def ac_reach.nodes_eq(c: A.Crown, +n: Nat) -> {Nat.is_le(CS.crown_nodes(c), n) == ac_reach.nb(c, n) : Bool}:
  match c:
    case A.Crown{+t, +hs}:
      %E.at_edit.nodes_size(t) : {Nat.is_le(Nat.add(S.nodes(t), CS.count(hs)), n) == Nat.is_le(Nat.add(_, A.hcount(hs)), n) : Bool}
      %Equal.sym(Nat, A.hcount(hs), CS.count(hs), St.ac_step.count_eq(hs)) : {Nat.is_le(Nat.add(S.nodes(t), CS.count(hs)), n) == Nat.is_le(Nat.add(S.nodes(t), _), n) : Bool}
      {==}
