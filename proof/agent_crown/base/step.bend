# eukhe: lemmas of area agent_crown for the decisions (T14): the code's
# bounds, sweep and help-leaf edits are the spec's

import Base
import ../../../bend/agent_tree.bend as T
import ../../../bend/agent_crown.bend as A
import ../../../spec/agents/agent_tree.bend as S
import ../../../spec/agents/agent_crown.bend as CS
import ../../../laws/agent_tree.bend as AgentTree
import ../../../laws/agent_crown.bend as AgentCrown
import ../../agent_tree/base/edit.bend as E
import ./view.bend as V

# Tree events
# -----------

def ac_step.count_eq(hs: List<&2, A.Help>) -> {A.hcount(hs) == CS.count(hs) : Nat}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, rest}:
      Equal.cong(Nat, Nat, x => 1n+x, A.hcount(rest), CS.count(rest), ac_step.count_eq(rest))

def ac_step.bounds_eq(b: T.Bounds, +t: T.Node, +hs: List<&2, A.Help>) -> {A.cbounds(b, hs) == CS.bounds(b, A.Crown{t, hs}) : T.Bounds}:
  match b:
    case T.Bounds{d, n, m}:
      Equal.cong(Nat, T.Bounds, x => T.Bounds{d, Nat.sub(n, x), m}, A.hcount(hs), CS.count(hs), ac_step.count_eq(hs))

def ac_step.late_eq(e: T.Ev, dl: T.Lim) -> {A.help_late(dl, e) == AgentCrown.tick_up(dl, e) : Bool}:
  match e:
    case T.EvSplit{at, own, ls, rs, hold}:
      {==}
    case T.EvSpend{at, n}:
      {==}
    case T.EvFinish{at, q}:
      {==}
    case T.EvFail{at, q}:
      {==}
    case T.EvCancel{at}:
      {==}
    case T.EvRedo{at, side, extra}:
      {==}
    case T.EvTick{now}:
      match dl:
        case T.Unlimited{}:
          {==}
        case T.Value{d}:
          {==}

def ac_step.stop_eq(x: Bool, st: T.Status) -> {A.sweep_st(x, st) == AgentCrown.stopped(Bool.and(T.running(st), x), st) : T.Status}:
  match x:
    case True{}:
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
      match st:
        case T.Running{}:
          {==}
        case T.Finished{}:
          {==}
        case T.Failed{}:
          {==}
        case T.Cancelled{}:
          {==}

# the code's runs is the spec's runs_at of the spec's node
def ac_step.runs_node(+p: List<&2, T.Dir>, +t: T.Node) -> {A.runs(A.node_at(p, t)) == CS.runs_at(S.node_at(p, t)) : Bool}:
  %V.ac_view.node_at_eq(p, t) : {A.runs(A.node_at(p, t)) == CS.runs_at(_) : Bool}
  Equal.sym(Bool, CS.runs_at(A.node_at(p, t)), A.runs(A.node_at(p, t)), V.ac_view.runs_eq(A.node_at(p, t)))

# the code's sweep is the spec's
def ac_step.sweep_eq(hs: List<&2, A.Help>, +t: T.Node, +e: T.Ev) -> {A.sweep(hs, t, e) == AgentCrown.swept(t, e, hs) : List<&2, A.Help>}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, rest}:
      match h:
        case A.Help{+p, +st, +lim, +sp, +dl}:
          %ac_step.sweep_eq(rest, t, e) : {A.sweep(A.Help{p, st, lim, sp, dl} <> rest, t, e) == A.Help{p, AgentCrown.stopped(Bool.and(T.running(st), Bool.or(Bool.not(CS.runs_at(S.node_at(p, t))), AgentCrown.tick_up(dl, e))), st), lim, sp, dl} <> _ : List<&2, A.Help>}
          %ac_step.runs_node(p, t) : {A.sweep(A.Help{p, st, lim, sp, dl} <> rest, t, e) == A.Help{p, AgentCrown.stopped(Bool.and(T.running(st), Bool.or(Bool.not(_), AgentCrown.tick_up(dl, e))), st), lim, sp, dl} <> A.sweep(rest, t, e) : List<&2, A.Help>}
          %ac_step.late_eq(e, dl) : {A.sweep(A.Help{p, st, lim, sp, dl} <> rest, t, e) == A.Help{p, AgentCrown.stopped(Bool.and(T.running(st), Bool.or(Bool.not(A.runs(A.node_at(p, t))), _)), st), lim, sp, dl} <> A.sweep(rest, t, e) : List<&2, A.Help>}
          %ac_step.stop_eq(Bool.or(Bool.not(A.runs(A.node_at(p, t))), A.help_late(dl, e)), st) : {A.sweep(A.Help{p, st, lim, sp, dl} <> rest, t, e) == A.Help{p, _, lim, sp, dl} <> A.sweep(rest, t, e) : List<&2, A.Help>}
          {==}

# a tree step on the view lands as the spec says
def ac_step.on_tree_eq(+s: T.Step, +hs: List<&2, A.Help>, +e: T.Ev) -> {A.on_tree(s, hs, e) == AgentCrown.tree_spec_of(s, hs, e) : A.CStep}:
  match s:
    case T.Took{x}:
      %V.ac_view.unview_eq(x, hs) : {A.on_tree(T.Took{x}, hs, e) == A.CTook{A.Crown{_, AgentCrown.swept(_, e, hs)}} : A.CStep}
      %ac_step.sweep_eq(hs, A.shift(x, A.loads(hs), False{}), e) : {A.on_tree(T.Took{x}, hs, e) == A.CTook{A.Crown{A.shift(x, A.loads(hs), False{}), _}} : A.CStep}
      {==}
    case T.Refused{why}:
      {==}

# a tree event is the tree's step on the view, as the spec says
def ac_step.tree_eq(+b: T.Bounds, +t: T.Node, +hs: List<&2, A.Help>, +e: T.Ev) -> {A.hstep(b, A.Crown{t, hs}, A.OnTree{e}) == AgentCrown.tree_spec(b, A.Crown{t, hs}, e) : A.CStep}:
  %ac_step.bounds_eq(b, t, hs) : {A.on_tree(T.step(A.cbounds(b, hs), A.view(t, hs), e), hs, e) == AgentCrown.tree_spec_of(T.step(_, CS.view_of(t, hs), e), hs, e) : A.CStep}
  %V.ac_view.view_eq(t, hs) : {A.on_tree(T.step(A.cbounds(b, hs), A.view(t, hs), e), hs, e) == AgentCrown.tree_spec_of(T.step(A.cbounds(b, hs), _, e), hs, e) : A.CStep}
  ac_step.on_tree_eq(T.step(A.cbounds(b, hs), A.view(t, hs), e), hs, e)

# Help leaf edits
# ---------------

# a crown step with h put in front of the help leaves
def ac_step.cons_step(h: A.Help, s: A.CStep) -> A.CStep:
  match s:
    case A.CTook{c}:
      match c:
        case A.Crown{t, xs}:
          A.CTook{A.Crown{t, h <> xs}}
    case A.CRefused{why}:
      A.CRefused{why}

def ac_step.cons_hres(+h: A.Help, +r: A.HRes, +t: T.Node) -> {A.hres_crown(A.hres_cons(h, r), t) == ac_step.cons_step(h, A.hres_crown(r, t)) : A.CStep}:
  match r:
    case A.HOk{xs}:
      {==}
    case A.HNo{why}:
      {==}

def ac_step.cons_dec(+h: A.Help, +m: Maybe<&2, T.Refusal>, +t: T.Node, +xs: List<&2, A.Help>) -> {ac_step.cons_step(h, AgentCrown.cdecided(m, A.Crown{t, xs})) == AgentCrown.cdecided(m, A.Crown{t, h <> xs}) : A.CStep}:
  match m:
    case None{}:
      {==}
    case Some{why}:
      {==}

def ac_step.cons_spend(+h: A.Help, +m: Maybe<&2, A.Help>, +t: T.Node, +rest: List<&2, A.Help>, +j: Nat, +a: Nat) -> {ac_step.cons_step(h, AgentCrown.spend_spec_at(m, t, rest, j, a)) == AgentCrown.spend_spec_at(m, t, h <> rest, 1n+j, a) : A.CStep}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case A.Help{p, +st, +lim, +sp, dl}:
          ac_step.cons_dec(h, AgentTree.first_failed([AgentTree.Check{T.running(st), T.NotRunning{}}, AgentTree.Check{S.has(a, S.minus(lim, sp)), T.NoBudget{}}]), t, CS.set(rest, j, A.Help{p, st, lim, Nat.add(sp, a), dl}))

def ac_step.spend_fit_eq(c: Bool, +p: List<&2, T.Dir>, +st: T.Status, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +a: Nat, +rest: List<&2, A.Help>, +t: T.Node) -> {A.hres_crown(A.spend_fit(c, A.Help{p, st, lim, sp, dl}, a, rest), t) == AgentCrown.cdecided(AgentTree.first_failed([AgentTree.Check{c, T.NoBudget{}}]), A.Crown{t, A.Help{p, st, lim, Nat.add(sp, a), dl} <> rest}) : A.CStep}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def ac_step.spend_head(+h: A.Help, +rest: List<&2, A.Help>, +t: T.Node, +a: Nat) -> {A.hres_crown(A.spend_one(A.hrunning(h), h, a, rest), t) == AgentCrown.spend_spec_at(Some{h}, t, h <> rest, 0n, a) : A.CStep}:
  match h:
    case A.Help{p, st, lim, sp, dl}:
      match st:
        case T.Running{}:
          match lim:
            case T.Unlimited{}:
              {==}
            case T.Value{+m}:
              ac_step.spend_fit_eq(Nat.is_le(a, Nat.sub(m, sp)), p, T.Running{}, T.Value{m}, sp, dl, a, rest, t)
        case T.Finished{}:
          {==}
        case T.Failed{}:
          {==}
        case T.Cancelled{}:
          {==}

# the code's spend of help leaf k is the spec's
def ac_step.spend_eq(k: Nat, hs: List<&2, A.Help>, +t: T.Node, +a: Nat) -> {A.hres_crown(A.spend_k(k, hs, a), t) == AgentCrown.spend_spec_at(CS.nth(hs, k), t, hs, k, a) : A.CStep}:
  match k:
    case 0n:
      match hs:
        case Nil{}:
          {==}
        case Con{+h, +rest}:
          ac_step.spend_head(h, rest, t, a)
    case 1n++j:
      match hs:
        case Nil{}:
          {==}
        case Con{+h, +rest}:
          %ac_step.cons_spend(h, CS.nth(rest, j), t, rest, j, a) : {A.hres_crown(A.hres_cons(h, A.spend_k(j, rest, a)), t) == _ : A.CStep}
          %ac_step.spend_eq(j, rest, t, a) : {A.hres_crown(A.hres_cons(h, A.spend_k(j, rest, a)), t) == ac_step.cons_step(h, _) : A.CStep}
          ac_step.cons_hres(h, A.spend_k(j, rest, a), t)

def ac_step.cons_end(+h: A.Help, +m: Maybe<&2, A.Help>, +t: T.Node, +rest: List<&2, A.Help>, +j: Nat, +ok: Bool) -> {ac_step.cons_step(h, AgentCrown.end_spec_at(m, t, rest, j, ok)) == AgentCrown.end_spec_at(m, t, h <> rest, 1n+j, ok) : A.CStep}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case A.Help{p, st, lim, sp, dl}:
          ac_step.cons_dec(h, AgentTree.first_failed([AgentTree.Check{T.running(st), T.NotRunning{}}]), t, CS.set(rest, j, A.Help{p, AgentCrown.settled(ok), lim, sp, dl}))

def ac_step.end_settled(ok: Bool) -> {A.end_st(ok) == AgentCrown.settled(ok) : T.Status}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def ac_step.end_head(+h: A.Help, +rest: List<&2, A.Help>, +t: T.Node, +ok: Bool) -> {A.hres_crown(A.end_one(A.hrunning(h), h, ok, rest), t) == AgentCrown.end_spec_at(Some{h}, t, h <> rest, 0n, ok) : A.CStep}:
  match h:
    case A.Help{p, st, lim, sp, dl}:
      match st:
        case T.Running{}:
          Equal.cong(T.Status, A.CStep, x => A.CTook{A.Crown{t, A.Help{p, x, lim, sp, dl} <> rest}}, A.end_st(ok), AgentCrown.settled(ok), ac_step.end_settled(ok))
        case T.Finished{}:
          {==}
        case T.Failed{}:
          {==}
        case T.Cancelled{}:
          {==}

# the code's settling of help leaf k is the spec's
def ac_step.end_eq(k: Nat, hs: List<&2, A.Help>, +t: T.Node, +ok: Bool) -> {A.hres_crown(A.end_k(k, hs, ok), t) == AgentCrown.end_spec_at(CS.nth(hs, k), t, hs, k, ok) : A.CStep}:
  match k:
    case 0n:
      match hs:
        case Nil{}:
          {==}
        case Con{+h, +rest}:
          ac_step.end_head(h, rest, t, ok)
    case 1n++j:
      match hs:
        case Nil{}:
          {==}
        case Con{+h, +rest}:
          %ac_step.cons_end(h, CS.nth(rest, j), t, rest, j, ok) : {A.hres_crown(A.hres_cons(h, A.end_k(j, rest, ok)), t) == _ : A.CStep}
          %ac_step.end_eq(j, rest, t, ok) : {A.hres_crown(A.hres_cons(h, A.end_k(j, rest, ok)), t) == ac_step.cons_step(h, _) : A.CStep}
          ac_step.cons_hres(h, A.end_k(j, rest, ok), t)

# Help
# ----

# a help decision by its checks c1-c3, the granted limit g and deadline d
def ac_step.hf(+t: T.Node, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>, c1: Bool, c2: Bool, c3: Bool, g: T.Lim, d: T.Lim) -> A.CStep:
  AgentCrown.cdecided(AgentTree.first_failed([AgentTree.Check{c1, T.NotRunning{}}, AgentTree.Check{c2, T.TooMany{}}, AgentTree.Check{c3, T.NoBudget{}}]), A.Crown{t, List.append(&2, A.Help, hs, [A.Help{p, T.Running{}, g, 0n, d}])})

def ac_step.hf_cong(+t: T.Node, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>, +c1: Bool, -c2: Bool, -c3: Bool, -g: T.Lim, -d: T.Lim, +x2: Bool, +x3: Bool, +h: T.Lim, +y: T.Lim, e2: {c2 == x2 : Bool}, e3: {c3 == x3 : Bool}, eg: {g == h : T.Lim}, ed: {d == y : T.Lim}) -> {ac_step.hf(t, hs, p, c1, c2, c3, g, d) == ac_step.hf(t, hs, p, c1, x2, x3, h, y) : A.CStep}:
  %e2 : {ac_step.hf(t, hs, p, c1, c2, c3, g, d) == ac_step.hf(t, hs, p, c1, _, x3, h, y) : A.CStep}
  %e3 : {ac_step.hf(t, hs, p, c1, c2, c3, g, d) == ac_step.hf(t, hs, p, c1, c2, _, h, y) : A.CStep}
  %eg : {ac_step.hf(t, hs, p, c1, c2, c3, g, d) == ac_step.hf(t, hs, p, c1, c2, c3, _, y) : A.CStep}
  %ed : {ac_step.hf(t, hs, p, c1, c2, c3, g, d) == ac_step.hf(t, hs, p, c1, c2, c3, g, _) : A.CStep}
  {==}

def ac_step.fit_hf(ok: Bool, +n: T.Node, +t: T.Node, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>, +a: Nat, +margin: Nat) -> {A.help_fit(ok, n, t, hs, p, a, margin) == ac_step.hf(t, hs, p, True{}, True{}, ok, A.grant(T.free(n), a), T.lim_less(T.deadline_of(T.info(n)), margin)) : A.CStep}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def ac_step.room_hf(room: Bool, +n: T.Node, +t: T.Node, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>, +a: Nat, +margin: Nat) -> {A.help_room(room, n, t, hs, p, a, margin) == ac_step.hf(t, hs, p, True{}, room, T.lim_fits(a, T.free(n)), A.grant(T.free(n), a), T.lim_less(T.deadline_of(T.info(n)), margin)) : A.CStep}:
  match room:
    case True{}:
      ac_step.fit_hf(T.lim_fits(a, T.free(n)), n, t, hs, p, a, margin)
    case False{}:
      {==}

def ac_step.run_hf(run: Bool, +n: T.Node, +t: T.Node, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>, +a: Nat, +room: Bool, +margin: Nat) -> {A.help_run(run, n, t, hs, p, a, room, margin) == ac_step.hf(t, hs, p, run, room, T.lim_fits(a, T.free(n)), A.grant(T.free(n), a), T.lim_less(T.deadline_of(T.info(n)), margin)) : A.CStep}:
  match run:
    case True{}:
      ac_step.room_hf(room, n, t, hs, p, a, margin)
    case False{}:
      {==}

def ac_step.grant_gen(f: T.Lim, -a: Nat) -> {A.grant(f, a) == AgentCrown.granted(f, a) : T.Lim}:
  match f:
    case T.Unlimited{}:
      {==}
    case T.Value{m}:
      {==}

def ac_step.grant_eq(+n: T.Node, +a: Nat) -> {A.grant(T.free(n), a) == AgentCrown.granted(S.room(n), a) : T.Lim}:
  %E.at_edit.room_free(n) : {A.grant(_, a) == AgentCrown.granted(S.room(n), a) : T.Lim}
  ac_step.grant_gen(S.room(n), a)

def ac_step.room_eq(+t: T.Node, +hs: List<&2, A.Help>, +m: Nat) -> {Nat.is_le(Nat.add(Nat.add(T.size(t), A.hcount(hs)), 1n), m) == Nat.is_le(Nat.add(Nat.add(S.nodes(t), CS.count(hs)), 1n), m) : Bool}:
  %E.at_edit.nodes_size(t) : {Nat.is_le(Nat.add(Nat.add(_, A.hcount(hs)), 1n), m) == Nat.is_le(Nat.add(Nat.add(S.nodes(t), CS.count(hs)), 1n), m) : Bool}
  Equal.cong(Nat, Bool, x => Nat.is_le(Nat.add(Nat.add(S.nodes(t), x), 1n), m), A.hcount(hs), CS.count(hs), ac_step.count_eq(hs))

def ac_step.help_m(+m: Maybe<&2, T.Node>, +b: T.Bounds, +t: T.Node, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>, +a: Nat) -> {A.help_node(m, t, hs, p, a, Nat.is_le(Nat.add(Nat.add(T.size(t), A.hcount(hs)), 1n), T.bound_nodes(b)), T.bound_margin(b)) == AgentCrown.help_spec_at(m, b, t, hs, p, a) : A.CStep}:
  match m:
    case None{}:
      {==}
    case Some{+n}:
      Equal.trans(A.CStep, A.help_run(T.running(T.st_of(T.info(n))), n, t, hs, p, a, Nat.is_le(Nat.add(Nat.add(T.size(t), A.hcount(hs)), 1n), T.bound_nodes(b)), T.bound_margin(b)), ac_step.hf(t, hs, p, T.running(T.st_of(T.info(n))), Nat.is_le(Nat.add(Nat.add(T.size(t), A.hcount(hs)), 1n), T.bound_nodes(b)), T.lim_fits(a, T.free(n)), A.grant(T.free(n), a), T.lim_less(T.deadline_of(T.info(n)), T.bound_margin(b))), AgentCrown.help_spec_at(Some{n}, b, t, hs, p, a), ac_step.run_hf(T.running(T.st_of(T.info(n))), n, t, hs, p, a, Nat.is_le(Nat.add(Nat.add(T.size(t), A.hcount(hs)), 1n), T.bound_nodes(b)), T.bound_margin(b)), ac_step.hf_cong(t, hs, p, T.running(T.st_of(T.info(n))), Nat.is_le(Nat.add(Nat.add(T.size(t), A.hcount(hs)), 1n), T.bound_nodes(b)), T.lim_fits(a, T.free(n)), A.grant(T.free(n), a), T.lim_less(T.deadline_of(T.info(n)), T.bound_margin(b)), Nat.is_le(Nat.add(Nat.add(S.nodes(t), CS.count(hs)), 1n), T.bound_nodes(b)), S.has(a, S.room(n)), AgentCrown.granted(S.room(n), a), S.minus(T.deadline_of(T.info(n)), T.bound_margin(b)), ac_step.room_eq(t, hs, T.bound_nodes(b)), Equal.sym(Bool, S.has(a, S.room(n)), T.lim_fits(a, T.free(n)), E.at_edit.fits(a, n)), ac_step.grant_eq(n, a), Equal.sym(T.Lim, S.minus(T.deadline_of(T.info(n)), T.bound_margin(b)), T.lim_less(T.deadline_of(T.info(n)), T.bound_margin(b)), E.at_edit.minus_less(T.deadline_of(T.info(n)), T.bound_margin(b)))))

# a help is decided as the spec says
def ac_step.help_eq(+b: T.Bounds, +t: T.Node, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>, +a: Nat) -> {A.hstep(b, A.Crown{t, hs}, A.EvHelp{p, a}) == AgentCrown.help_spec(b, A.Crown{t, hs}, p, a) : A.CStep}:
  %V.ac_view.view_eq(t, hs) : {A.help_node(A.node_at(p, A.view(t, hs)), t, hs, p, a, Nat.is_le(Nat.add(Nat.add(T.size(t), A.hcount(hs)), 1n), T.bound_nodes(b)), T.bound_margin(b)) == AgentCrown.help_spec_at(S.node_at(p, _), b, t, hs, p, a) : A.CStep}
  %V.ac_view.node_at_eq(p, A.view(t, hs)) : {A.help_node(A.node_at(p, A.view(t, hs)), t, hs, p, a, Nat.is_le(Nat.add(Nat.add(T.size(t), A.hcount(hs)), 1n), T.bound_nodes(b)), T.bound_margin(b)) == AgentCrown.help_spec_at(_, b, t, hs, p, a) : A.CStep}
  ac_step.help_m(A.node_at(p, A.view(t, hs)), b, t, hs, p, a)
