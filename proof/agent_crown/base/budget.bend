# eukhe: lemmas of area agent_crown for the budget (T14): under a Value
# root limit the view of every reachable crown keeps the tree's invariant
# (agent_tree's Good), so the tree's spend plus the help leaves' fits

import Base
import ../../../bend/agent_tree.bend as T
import ../../../bend/agent_crown.bend as A
import ../../../spec/agents/agent_tree.bend as S
import ../../../spec/agents/agent_crown.bend as CS
import ../../agent_tree/base/reach.bend as AR
import ../../agent_tree/base/edit.bend as E
import ./view.bend as V
import ./grow.bend as Gw
import ./reach.bend as R

# Loads
# -----

# la charges no more than lb, load by load, at the same paths
def ac_bud.lle1(x: A.Load, y: A.Load) -> Bool:
  match x y:
    case A.Load{p, n} A.Load{q, m}:
      Bool.and(CS.path_is(p, q), Nat.is_le(n, m))

def ac_bud.lle(a: List<&2, A.Load>, b: List<&2, A.Load>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, yt}:
      False{}
    case Con{x, xt} Nil{}:
      False{}
    case Con{x, xt} Con{y, yt}:
      Bool.and(ac_bud.lle1(x, y), ac_bud.lle(xt, yt))

# every load is at the path []
def ac_bud.all_nil(ls: List<&2, A.Load>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{x, rest}:
      match x:
        case A.Load{p, n}:
          match p:
            case Nil{}:
              ac_bud.all_nil(rest)
            case Con{d, q}:
              False{}

# every load's path names a node of t
def ac_bud.placed(t: T.Node, +ls: List<&2, A.Load>) -> Bool:
  match t:
    case T.Leaf{i}:
      ac_bud.all_nil(ls)
    case T.Split{i, own, l, r}:
      Bool.and(ac_bud.placed(l, A.down(ls, T.GoL{})), ac_bud.placed(r, A.down(ls, T.GoR{})))

# every node of t spent at least the charges at its path
def ac_bud.cov(t: T.Node, +ls: List<&2, A.Load>) -> Bool:
  match t:
    case T.Leaf{i}:
      Nat.is_le(A.here(ls), T.spent_of(i))
    case T.Split{i, own, l, r}:
      Bool.and(Nat.is_le(A.here(ls), T.spent_of(i)), Bool.and(ac_bud.cov(l, A.down(ls, T.GoL{})), ac_bud.cov(r, A.down(ls, T.GoR{}))))

def ac_bud.add_le2(+a: Nat, +b: Nat, +c: Nat, +d: Nat, hab: {Nat.is_le(a, b) == True{} : Bool}, hcd: {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  AR.at_reach.le_trans(Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), AR.at_reach.add_mono_r(a, b, c, hab), AR.at_reach.add_mono_l(b, c, d, hcd))

def ac_bud.here_le1(p: List<&2, T.Dir>, +n: Nat, +m: Nat, +xt: List<&2, A.Load>, +yt: List<&2, A.Load>, nm: {Nat.is_le(n, m) == True{} : Bool}, ih: {Nat.is_le(A.here(xt), A.here(yt)) == True{} : Bool}) -> {Nat.is_le(A.here(A.Load{p, n} <> xt), A.here(A.Load{p, m} <> yt)) == True{} : Bool}:
  match p:
    case Nil{}:
      ac_bud.add_le2(n, m, A.here(xt), A.here(yt), nm, ih)
    case Con{d, q}:
      ih

def ac_bud.here_le_c(x: A.Load, y: A.Load, +xt: List<&2, A.Load>, +yt: List<&2, A.Load>, +h: {ac_bud.lle1(x, y) == True{} : Bool}, ih: {Nat.is_le(A.here(xt), A.here(yt)) == True{} : Bool}) -> {Nat.is_le(A.here(x <> xt), A.here(y <> yt)) == True{} : Bool}:
  match x:
    case A.Load{+p, +n}:
      match y:
        case A.Load{+q, +m}:
          +epq = V.ac_view.path_eq(p, q, AR.at_reach.and_l(CS.path_is(p, q), Nat.is_le(n, m), h))
          %epq : {Nat.is_le(A.here(A.Load{p, n} <> xt), A.here(A.Load{_, m} <> yt)) == True{} : Bool}
          ac_bud.here_le1(p, n, m, xt, yt, AR.at_reach.and_r(CS.path_is(p, q), Nat.is_le(n, m), h), ih)

def ac_bud.here_le(a: List<&2, A.Load>, b: List<&2, A.Load>, +h: {ac_bud.lle(a, b) == True{} : Bool}) -> {Nat.is_le(A.here(a), A.here(b)) == True{} : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, yt}:
      AR.at_reach.absurd({Nat.is_le(0n, A.here(y <> yt)) == True{} : Bool}, h)
    case Con{x, xt} Nil{}:
      AR.at_reach.absurd({Nat.is_le(A.here(x <> xt), 0n) == True{} : Bool}, h)
    case Con{+x, +xt} Con{+y, +yt}:
      ac_bud.here_le_c(x, y, xt, yt, AR.at_reach.and_l(ac_bud.lle1(x, y), ac_bud.lle(xt, yt), h), ac_bud.here_le(xt, yt, AR.at_reach.and_r(ac_bud.lle1(x, y), ac_bud.lle(xt, yt), h)))

def ac_bud.down_c(d: T.Dir, p: List<&2, T.Dir>, +n: Nat, +m: Nat, +xt: List<&2, A.Load>, +yt: List<&2, A.Load>, +nm: {Nat.is_le(n, m) == True{} : Bool}, +ih: {ac_bud.lle(A.down(xt, d), A.down(yt, d)) == True{} : Bool}) -> {ac_bud.lle(A.down(A.Load{p, n} <> xt, d), A.down(A.Load{p, m} <> yt, d)) == True{} : Bool}:
  match d:
    case T.GoL{}:
      match p:
        case Nil{}:
          ih
        case Con{e, q}:
          match e:
            case T.GoL{}:
              AR.at_reach.and_t(Bool.and(CS.path_is(q, q), Nat.is_le(n, m)), ac_bud.lle(A.down(xt, T.GoL{}), A.down(yt, T.GoL{})), AR.at_reach.and_t(CS.path_is(q, q), Nat.is_le(n, m), V.ac_view.path_refl(q), nm), ih)
            case T.GoR{}:
              ih
    case T.GoR{}:
      match p:
        case Nil{}:
          ih
        case Con{e, q}:
          match e:
            case T.GoL{}:
              ih
            case T.GoR{}:
              AR.at_reach.and_t(Bool.and(CS.path_is(q, q), Nat.is_le(n, m)), ac_bud.lle(A.down(xt, T.GoR{}), A.down(yt, T.GoR{})), AR.at_reach.and_t(CS.path_is(q, q), Nat.is_le(n, m), V.ac_view.path_refl(q), nm), ih)

def ac_bud.down_x(+d: T.Dir, x: A.Load, y: A.Load, +xt: List<&2, A.Load>, +yt: List<&2, A.Load>, +h: {ac_bud.lle1(x, y) == True{} : Bool}, +ih: {ac_bud.lle(A.down(xt, d), A.down(yt, d)) == True{} : Bool}) -> {ac_bud.lle(A.down(x <> xt, d), A.down(y <> yt, d)) == True{} : Bool}:
  match x:
    case A.Load{+p, +n}:
      match y:
        case A.Load{+q, +m}:
          +epq = V.ac_view.path_eq(p, q, AR.at_reach.and_l(CS.path_is(p, q), Nat.is_le(n, m), h))
          %epq : {ac_bud.lle(A.down(A.Load{p, n} <> xt, d), A.down(A.Load{_, m} <> yt, d)) == True{} : Bool}
          ac_bud.down_c(d, p, n, m, xt, yt, AR.at_reach.and_r(CS.path_is(p, q), Nat.is_le(n, m), h), ih)

# loads charging no more stay so below a child
def ac_bud.lle_down(+d: T.Dir, a: List<&2, A.Load>, b: List<&2, A.Load>, +h: {ac_bud.lle(a, b) == True{} : Bool}) -> {ac_bud.lle(A.down(a, d), A.down(b, d)) == True{} : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, yt}:
      AR.at_reach.absurd({ac_bud.lle(A.down([], d), A.down(y <> yt, d)) == True{} : Bool}, h)
    case Con{x, xt} Nil{}:
      AR.at_reach.absurd({ac_bud.lle(A.down(x <> xt, d), A.down([], d)) == True{} : Bool}, h)
    case Con{+x, +xt} Con{+y, +yt}:
      ac_bud.down_x(d, x, y, xt, yt, AR.at_reach.and_l(ac_bud.lle1(x, y), ac_bud.lle(xt, yt), h), ac_bud.lle_down(d, xt, yt, AR.at_reach.and_r(ac_bud.lle1(x, y), ac_bud.lle(xt, yt), h)))

def ac_bud.all_nil_c(p: List<&2, T.Dir>, -n: Nat, -m: Nat, -xt: List<&2, A.Load>, -yt: List<&2, A.Load>, ih: {ac_bud.all_nil(xt) == ac_bud.all_nil(yt) : Bool}) -> {ac_bud.all_nil(A.Load{p, n} <> xt) == ac_bud.all_nil(A.Load{p, m} <> yt) : Bool}:
  match p:
    case Nil{}:
      ih
    case Con{d, q}:
      {==}

def ac_bud.all_nil_x(x: A.Load, y: A.Load, +xt: List<&2, A.Load>, +yt: List<&2, A.Load>, +h: {ac_bud.lle1(x, y) == True{} : Bool}, ih: {ac_bud.all_nil(xt) == ac_bud.all_nil(yt) : Bool}) -> {ac_bud.all_nil(x <> xt) == ac_bud.all_nil(y <> yt) : Bool}:
  match x:
    case A.Load{+p, +n}:
      match y:
        case A.Load{+q, +m}:
          +epq = V.ac_view.path_eq(p, q, AR.at_reach.and_l(CS.path_is(p, q), Nat.is_le(n, m), h))
          %epq : {ac_bud.all_nil(A.Load{p, n} <> xt) == ac_bud.all_nil(A.Load{_, m} <> yt) : Bool}
          ac_bud.all_nil_c(p, n, m, xt, yt, ih)

def ac_bud.all_nil_lle(a: List<&2, A.Load>, b: List<&2, A.Load>, +h: {ac_bud.lle(a, b) == True{} : Bool}) -> {ac_bud.all_nil(a) == ac_bud.all_nil(b) : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, yt}:
      AR.at_reach.absurd({ac_bud.all_nil([]) == ac_bud.all_nil(y <> yt) : Bool}, h)
    case Con{x, xt} Nil{}:
      AR.at_reach.absurd({ac_bud.all_nil(x <> xt) == ac_bud.all_nil([]) : Bool}, h)
    case Con{+x, +xt} Con{+y, +yt}:
      ac_bud.all_nil_x(x, y, xt, yt, AR.at_reach.and_l(ac_bud.lle1(x, y), ac_bud.lle(xt, yt), h), ac_bud.all_nil_lle(xt, yt, AR.at_reach.and_r(ac_bud.lle1(x, y), ac_bud.lle(xt, yt), h)))

# placed reads only the paths
def ac_bud.placed_lle(+t: T.Node, +a: List<&2, A.Load>, +b: List<&2, A.Load>, +h: {ac_bud.lle(a, b) == True{} : Bool}) -> {ac_bud.placed(t, a) == ac_bud.placed(t, b) : Bool}:
  match t:
    case T.Leaf{i}:
      ac_bud.all_nil_lle(a, b, h)
    case T.Split{i, own, l, r}:
      %ac_bud.placed_lle(l, A.down(a, T.GoL{}), A.down(b, T.GoL{}), ac_bud.lle_down(T.GoL{}, a, b, h)) : {Bool.and(ac_bud.placed(l, A.down(a, T.GoL{})), ac_bud.placed(r, A.down(a, T.GoR{}))) == Bool.and(_, ac_bud.placed(r, A.down(b, T.GoR{}))) : Bool}
      %ac_bud.placed_lle(r, A.down(a, T.GoR{}), A.down(b, T.GoR{}), ac_bud.lle_down(T.GoR{}, a, b, h)) : {Bool.and(ac_bud.placed(l, A.down(a, T.GoL{})), ac_bud.placed(r, A.down(a, T.GoR{}))) == Bool.and(ac_bud.placed(l, A.down(a, T.GoL{})), _) : Bool}
      {==}

# The view kept Good when charges drop
# ------------------------------------

def ac_bud.sc_same(+t: T.Node, -a: List<&2, A.Load>, -b: List<&2, A.Load>, -up: Bool) -> {T.scope_of(T.info(A.shift(t, b, up))) == T.scope_of(T.info(A.shift(t, a, up))) : List<&2, Bool>}:
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, q}:
          {==}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, q}:
          {==}

def ac_bud.dl_same(+t: T.Node, -a: List<&2, A.Load>, -b: List<&2, A.Load>, -up: Bool) -> {T.deadline_of(T.info(A.shift(t, b, up))) == T.deadline_of(T.info(A.shift(t, a, up))) : T.Lim}:
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, q}:
          {==}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, q}:
          {==}

def ac_bud.lim_same(+t: T.Node, -a: List<&2, A.Load>, -b: List<&2, A.Load>, -up: Bool) -> {T.limit_of(T.info(A.shift(t, b, up))) == T.limit_of(T.info(A.shift(t, a, up))) : T.Lim}:
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, q}:
          {==}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, q}:
          {==}

def ac_bud.run_same(+t: T.Node, -a: List<&2, A.Load>, -b: List<&2, A.Load>, -up: Bool) -> {S.is_running(A.shift(t, b, up)) == S.is_running(A.shift(t, a, up)) : Bool}:
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, q}:
          {==}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, q}:
          {==}

def ac_bud.sa_mono(+t: T.Node, +a: List<&2, A.Load>, +b: List<&2, A.Load>, +h: {ac_bud.lle(a, b) == True{} : Bool}) -> {Nat.is_le(S.spent_all(A.shift(t, a, True{})), S.spent_all(A.shift(t, b, True{}))) == True{} : Bool}:
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, q}:
          AR.at_reach.add_mono_l(sp, A.here(a), A.here(b), ac_bud.here_le(a, b, h))
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, +sp, dl, q}:
          ac_bud.add_le2(Nat.add(sp, A.here(a)), Nat.add(sp, A.here(b)), Nat.add(S.spent_all(A.shift(l, A.down(a, T.GoL{}), True{})), S.spent_all(A.shift(r, A.down(a, T.GoR{}), True{}))), Nat.add(S.spent_all(A.shift(l, A.down(b, T.GoL{}), True{})), S.spent_all(A.shift(r, A.down(b, T.GoR{}), True{}))), AR.at_reach.add_mono_l(sp, A.here(a), A.here(b), ac_bud.here_le(a, b, h)), ac_bud.add_le2(S.spent_all(A.shift(l, A.down(a, T.GoL{}), True{})), S.spent_all(A.shift(l, A.down(b, T.GoL{}), True{})), S.spent_all(A.shift(r, A.down(a, T.GoR{}), True{})), S.spent_all(A.shift(r, A.down(b, T.GoR{}), True{})), ac_bud.sa_mono(l, A.down(a, T.GoL{}), A.down(b, T.GoL{}), ac_bud.lle_down(T.GoL{}, a, b, h)), ac_bud.sa_mono(r, A.down(a, T.GoR{}), A.down(b, T.GoR{}), ac_bud.lle_down(T.GoR{}, a, b, h))))

def ac_bud.held_if_le(r: Bool, +l: T.Lim, -x: Nat, -y: Nat, h: {Nat.is_le(x, y) == True{} : Bool}) -> {S.lim_le(S.held_if(r, l, x), S.held_if(r, l, y)) == True{} : Bool}:
  match r:
    case True{}:
      AR.at_reach.lim_le_refl(l)
    case False{}:
      h

def ac_bud.held_mono(+t: T.Node, +a: List<&2, A.Load>, +b: List<&2, A.Load>, +h: {ac_bud.lle(a, b) == True{} : Bool}) -> {S.lim_le(S.held(A.shift(t, a, True{})), S.held(A.shift(t, b, True{}))) == True{} : Bool}:
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{+st, +s, +lim, +sp, +dl, +q}:
          ac_bud.held_if_le(T.running(st), lim, S.spent_all(A.shift(T.Leaf{T.Info{st, s, lim, sp, dl, q}}, a, True{})), S.spent_all(A.shift(T.Leaf{T.Info{st, s, lim, sp, dl, q}}, b, True{})), ac_bud.sa_mono(T.Leaf{T.Info{st, s, lim, sp, dl, q}}, a, b, h))
    case T.Split{i, +own, +l, +r}:
      match i:
        case T.Info{+st, +s, +lim, +sp, +dl, +q}:
          ac_bud.held_if_le(T.running(st), lim, S.spent_all(A.shift(T.Split{T.Info{st, s, lim, sp, dl, q}, own, l, r}, a, True{})), S.spent_all(A.shift(T.Split{T.Info{st, s, lim, sp, dl, q}, own, l, r}, b, True{})), ac_bud.sa_mono(T.Split{T.Info{st, s, lim, sp, dl, q}, own, l, r}, a, b, h))

def ac_bud.rc_same(+st: T.Status, +l: T.Node, +r: T.Node, +la: List<&2, A.Load>, +lb: List<&2, A.Load>, +ra: List<&2, A.Load>, +rb: List<&2, A.Load>, rc: AR.at_reach.RunCond(st, A.shift(l, lb, True{}), A.shift(r, rb, True{}))) -> AR.at_reach.RunCond(st, A.shift(l, la, True{}), A.shift(r, ra, True{})):
  match st:
    case T.Running{}:
      Unit{}
    case T.Finished{}:
      (el, er) = rc
      (AR.at_reach.tr(Bool, S.is_running(A.shift(l, lb, True{})), S.is_running(A.shift(l, la, True{})), z => {z == False{} : Bool}, ac_bud.run_same(l, la, lb, True{}), el), AR.at_reach.tr(Bool, S.is_running(A.shift(r, rb, True{})), S.is_running(A.shift(r, ra, True{})), z => {z == False{} : Bool}, ac_bud.run_same(r, ra, rb, True{}), er))
    case T.Failed{}:
      (el, er) = rc
      (AR.at_reach.tr(Bool, S.is_running(A.shift(l, lb, True{})), S.is_running(A.shift(l, la, True{})), z => {z == False{} : Bool}, ac_bud.run_same(l, la, lb, True{}), el), AR.at_reach.tr(Bool, S.is_running(A.shift(r, rb, True{})), S.is_running(A.shift(r, ra, True{})), z => {z == False{} : Bool}, ac_bud.run_same(r, ra, rb, True{}), er))
    case T.Cancelled{}:
      (el, er) = rc
      (AR.at_reach.tr(Bool, S.is_running(A.shift(l, lb, True{})), S.is_running(A.shift(l, la, True{})), z => {z == False{} : Bool}, ac_bud.run_same(l, la, lb, True{}), el), AR.at_reach.tr(Bool, S.is_running(A.shift(r, rb, True{})), S.is_running(A.shift(r, ra, True{})), z => {z == False{} : Bool}, ac_bud.run_same(r, ra, rb, True{}), er))

# the view with charges no higher stays Good
def ac_bud.good_lle(+t: T.Node, +a: List<&2, A.Load>, +b: List<&2, A.Load>, +k: Nat, +h: {ac_bud.lle(a, b) == True{} : Bool}, +g: AR.at_reach.Good(A.shift(t, b, True{}), k)) -> AR.at_reach.Good(A.shift(t, a, True{}), k):
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, +lim, +sp, dl, q}:
          AR.at_reach.le_has(Nat.add(sp, A.here(a)), lim, AR.at_reach.lim_le_trans(T.Value{Nat.add(sp, A.here(a))}, T.Value{Nat.add(sp, A.here(b))}, lim, AR.at_reach.add_mono_l(sp, A.here(a), A.here(b), ac_bud.here_le(a, b, h)), AR.at_reach.has_le(Nat.add(sp, A.here(b)), lim, g)))
    case T.Split{i, +own, +l, +r}:
      match i:
        case T.Info{+st, +s, +lim, +sp, +dl, +q}:
          match k:
            case 0n:
              match g:
            case 1n+kq:
              (tl, g1) = g
              (rc, g2) = g1
              (bu, g3) = g2
              (dl1, g4) = g3
              (dr1, g5) = g4
              (gl, gr) = g5
              +la = A.down(a, T.GoL{})
              +lb = A.down(b, T.GoL{})
              +ra = A.down(a, T.GoR{})
              +rb = A.down(b, T.GoR{})
              +hl = ac_bud.lle_down(T.GoL{}, a, b, h)
              +hr = ac_bud.lle_down(T.GoR{}, a, b, h)
              +tl2 = AR.at_reach.tr(List<&2, Bool>, T.scope_of(T.info(A.shift(r, rb, True{}))), T.scope_of(T.info(A.shift(r, ra, True{}))), z => {S.addv(S.counts(own), S.addv(S.counts(T.scope_of(T.info(A.shift(l, la, True{})))), S.counts(z))) == S.counts(s) : List<&2, Nat>}, ac_bud.sc_same(r, ra, rb, True{}), AR.at_reach.tr(List<&2, Bool>, T.scope_of(T.info(A.shift(l, lb, True{}))), T.scope_of(T.info(A.shift(l, la, True{}))), z => {S.addv(S.counts(own), S.addv(S.counts(z), S.counts(T.scope_of(T.info(A.shift(r, rb, True{})))))) == S.counts(s) : List<&2, Nat>}, ac_bud.sc_same(l, la, lb, True{}), tl))
              +bu1 = AR.at_reach.bu_mono(Nat.add(sp, A.here(b)), lim, S.held(A.shift(l, la, True{})), S.held(A.shift(l, lb, True{})), S.held(A.shift(r, ra, True{})), S.held(A.shift(r, rb, True{})), ac_bud.held_mono(l, la, lb, hl), ac_bud.held_mono(r, ra, rb, hr), bu)
              +bu2 = AR.at_reach.lim_le_trans(AR.at_reach.lplus(T.Value{Nat.add(sp, A.here(a))}, AR.at_reach.lplus(S.held(A.shift(l, la, True{})), S.held(A.shift(r, ra, True{})))), AR.at_reach.lplus(T.Value{Nat.add(sp, A.here(b))}, AR.at_reach.lplus(S.held(A.shift(l, la, True{})), S.held(A.shift(r, ra, True{})))), lim, AR.at_reach.lplus_mono_l(T.Value{Nat.add(sp, A.here(a))}, T.Value{Nat.add(sp, A.here(b))}, AR.at_reach.lplus(S.held(A.shift(l, la, True{})), S.held(A.shift(r, ra, True{}))), AR.at_reach.add_mono_l(sp, A.here(a), A.here(b), ac_bud.here_le(a, b, h))), bu1)
              +dl2 = AR.at_reach.tr(T.Lim, T.deadline_of(T.info(A.shift(l, lb, True{}))), T.deadline_of(T.info(A.shift(l, la, True{}))), z => {S.lim_le(z, dl) == True{} : Bool}, ac_bud.dl_same(l, la, lb, True{}), dl1)
              +dr2 = AR.at_reach.tr(T.Lim, T.deadline_of(T.info(A.shift(r, rb, True{}))), T.deadline_of(T.info(A.shift(r, ra, True{}))), z => {S.lim_le(z, dl) == True{} : Bool}, ac_bud.dl_same(r, ra, rb, True{}), dr1)
              (tl2, (ac_bud.rc_same(st, l, r, la, lb, ra, rb, rc), (bu2, (dl2, (dr2, (ac_bud.good_lle(l, la, lb, kq, hl, gl), ac_bud.good_lle(r, ra, rb, kq, hr, gr)))))))

# The charges taken off and put back
# ----------------------------------

# (y - h) + h = y when h <= y
def ac_bud.sub_add_r(+h: Nat, +y: Nat, e: {Nat.is_le(h, y) == True{} : Bool}) -> {Nat.add(Nat.sub(y, h), h) == y : Nat}:
  Equal.trans(Nat, Nat.add(Nat.sub(y, h), h), Nat.add(h, Nat.sub(y, h)), y, AR.at_reach.add_comm(Nat.sub(y, h), h), AR.at_reach.sub_add(h, y, e))

# where every node covers its charges, lowering then raising is the tree
def ac_bud.roundtrip(+x: T.Node, +ls: List<&2, A.Load>, +h: {ac_bud.cov(x, ls) == True{} : Bool}) -> {A.shift(A.shift(x, ls, False{}), ls, True{}) == x : T.Node}:
  match x:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, +sp, dl, q}:
          Equal.cong(Nat, T.Node, z => T.Leaf{T.Info{st, s, lim, z, dl, q}}, Nat.add(Nat.sub(sp, A.here(ls)), A.here(ls)), sp, ac_bud.sub_add_r(A.here(ls), sp, h))
    case T.Split{i, +own, +l, +r}:
      match i:
        case T.Info{+st, +s, +lim, +sp, +dl, +q}:
          +h1 = AR.at_reach.and_l(Nat.is_le(A.here(ls), sp), Bool.and(ac_bud.cov(l, A.down(ls, T.GoL{})), ac_bud.cov(r, A.down(ls, T.GoR{}))), h)
          +h2 = AR.at_reach.and_r(Nat.is_le(A.here(ls), sp), Bool.and(ac_bud.cov(l, A.down(ls, T.GoL{})), ac_bud.cov(r, A.down(ls, T.GoR{}))), h)
          %ac_bud.roundtrip(l, A.down(ls, T.GoL{}), AR.at_reach.and_l(ac_bud.cov(l, A.down(ls, T.GoL{})), ac_bud.cov(r, A.down(ls, T.GoR{})), h2)) : {A.shift(A.shift(T.Split{T.Info{st, s, lim, sp, dl, q}, own, l, r}, ls, False{}), ls, True{}) == T.Split{T.Info{st, s, lim, sp, dl, q}, own, _, r} : T.Node}
          %ac_bud.roundtrip(r, A.down(ls, T.GoR{}), AR.at_reach.and_r(ac_bud.cov(l, A.down(ls, T.GoL{})), ac_bud.cov(r, A.down(ls, T.GoR{})), h2)) : {A.shift(A.shift(T.Split{T.Info{st, s, lim, sp, dl, q}, own, l, r}, ls, False{}), ls, True{}) == T.Split{T.Info{st, s, lim, sp, dl, q}, own, A.shift(A.shift(l, A.down(ls, T.GoL{}), False{}), A.down(ls, T.GoL{}), True{}), _} : T.Node}
          Equal.cong(Nat, T.Node, z => T.Split{T.Info{st, s, lim, z, dl, q}, own, A.shift(A.shift(l, A.down(ls, T.GoL{}), False{}), A.down(ls, T.GoL{}), True{}), A.shift(A.shift(r, A.down(ls, T.GoR{}), False{}), A.down(ls, T.GoR{}), True{})}, Nat.add(Nat.sub(sp, A.here(ls)), A.here(ls)), sp, ac_bud.sub_add_r(A.here(ls), sp, h1))

# l <= x + l
def ac_bud.le_add_l(+x: Nat, +l: Nat) -> {Nat.is_le(l, Nat.add(x, l)) == True{} : Bool}:
  %AR.at_reach.add_comm(l, x) : {Nat.is_le(l, _) == True{} : Bool}
  AR.at_reach.le_add_r(l, x)

# the view covers its charges
def ac_bud.cov_shift(+t: T.Node, +ls: List<&2, A.Load>) -> {ac_bud.cov(A.shift(t, ls, True{}), ls) == True{} : Bool}:
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, q}:
          ac_bud.le_add_l(sp, A.here(ls))
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, +sp, dl, q}:
          AR.at_reach.and_t(Nat.is_le(A.here(ls), Nat.add(sp, A.here(ls))), Bool.and(ac_bud.cov(A.shift(l, A.down(ls, T.GoL{}), True{}), A.down(ls, T.GoL{})), ac_bud.cov(A.shift(r, A.down(ls, T.GoR{}), True{}), A.down(ls, T.GoR{}))), ac_bud.le_add_l(sp, A.here(ls)), AR.at_reach.and_t(ac_bud.cov(A.shift(l, A.down(ls, T.GoL{}), True{}), A.down(ls, T.GoL{})), ac_bud.cov(A.shift(r, A.down(ls, T.GoR{}), True{}), A.down(ls, T.GoR{})), ac_bud.cov_shift(l, A.down(ls, T.GoL{})), ac_bud.cov_shift(r, A.down(ls, T.GoR{}))))

def ac_bud.cov_nil(+t: T.Node) -> {ac_bud.cov(t, []) == True{} : Bool}:
  match t:
    case T.Leaf{i}:
      AR.at_reach.le0(T.spent_of(i))
    case T.Split{i, own, l, r}:
      AR.at_reach.and_t(Nat.is_le(0n, T.spent_of(i)), Bool.and(ac_bud.cov(l, []), ac_bud.cov(r, [])), AR.at_reach.le0(T.spent_of(i)), AR.at_reach.and_t(ac_bud.cov(l, []), ac_bud.cov(r, []), ac_bud.cov_nil(l), ac_bud.cov_nil(r)))

def ac_bud.placed_nil(+t: T.Node) -> {ac_bud.placed(t, []) == True{} : Bool}:
  match t:
    case T.Leaf{i}:
      {==}
    case T.Split{i, own, l, r}:
      AR.at_reach.and_t(ac_bud.placed(l, []), ac_bud.placed(r, []), ac_bud.placed_nil(l), ac_bud.placed_nil(r))

# loads all at [] have none below a child
def ac_bud.down_nil(+d: T.Dir, ls: List<&2, A.Load>, h: {ac_bud.all_nil(ls) == True{} : Bool}) -> {A.down(ls, d) == [] : List<&2, A.Load>}:
  match ls:
    case Nil{}:
      {==}
    case Con{x, rest}:
      match x:
        case A.Load{p, n}:
          match p:
            case Nil{}:
              ac_bud.down_nil(d, rest, h)
            case Con{e, q}:
              AR.at_reach.absurd({A.down(A.Load{e <> q, n} <> rest, d) == [] : List<&2, A.Load>}, h)

# a tree that grew from a covering, placed one covers the same charges
def ac_bud.cov_gr(+a: T.Node, +b: T.Node, +ls: List<&2, A.Load>, +hg: {Gw.ac_grow.gr(a, b) == True{} : Bool}, +hc: {ac_bud.cov(a, ls) == True{} : Bool}, +hp: {ac_bud.placed(a, ls) == True{} : Bool}) -> {ac_bud.cov(b, ls) == True{} : Bool}:
  match a b:
    case T.Leaf{i} T.Leaf{j}:
      AR.at_reach.le_trans(A.here(ls), T.spent_of(i), T.spent_of(j), hc, hg)
    case T.Leaf{i} T.Split{j, o, l, r}:
      AR.at_reach.and_t(Nat.is_le(A.here(ls), T.spent_of(j)), Bool.and(ac_bud.cov(l, A.down(ls, T.GoL{})), ac_bud.cov(r, A.down(ls, T.GoR{}))), AR.at_reach.le_trans(A.here(ls), T.spent_of(i), T.spent_of(j), hc, hg), AR.at_reach.and_t(ac_bud.cov(l, A.down(ls, T.GoL{})), ac_bud.cov(r, A.down(ls, T.GoR{})), AR.at_reach.tr(List<&2, A.Load>, [], A.down(ls, T.GoL{}), z => {ac_bud.cov(l, z) == True{} : Bool}, Equal.sym(List<&2, A.Load>, A.down(ls, T.GoL{}), [], ac_bud.down_nil(T.GoL{}, ls, hp)), ac_bud.cov_nil(l)), AR.at_reach.tr(List<&2, A.Load>, [], A.down(ls, T.GoR{}), z => {ac_bud.cov(r, z) == True{} : Bool}, Equal.sym(List<&2, A.Load>, A.down(ls, T.GoR{}), [], ac_bud.down_nil(T.GoR{}, ls, hp)), ac_bud.cov_nil(r))))
    case T.Split{i, o, l, r} T.Leaf{j}:
      AR.at_reach.absurd({ac_bud.cov(T.Leaf{j}, ls) == True{} : Bool}, hg)
    case T.Split{i, o, l, r} T.Split{j, o2, l2, r2}:
      +g1 = AR.at_reach.and_r(Nat.is_le(T.spent_of(i), T.spent_of(j)), Bool.and(Gw.ac_grow.gr(l, l2), Gw.ac_grow.gr(r, r2)), hg)
      +c1 = AR.at_reach.and_r(Nat.is_le(A.here(ls), T.spent_of(i)), Bool.and(ac_bud.cov(l, A.down(ls, T.GoL{})), ac_bud.cov(r, A.down(ls, T.GoR{}))), hc)
      AR.at_reach.and_t(Nat.is_le(A.here(ls), T.spent_of(j)), Bool.and(ac_bud.cov(l2, A.down(ls, T.GoL{})), ac_bud.cov(r2, A.down(ls, T.GoR{}))), AR.at_reach.le_trans(A.here(ls), T.spent_of(i), T.spent_of(j), AR.at_reach.and_l(Nat.is_le(A.here(ls), T.spent_of(i)), Bool.and(ac_bud.cov(l, A.down(ls, T.GoL{})), ac_bud.cov(r, A.down(ls, T.GoR{}))), hc), AR.at_reach.and_l(Nat.is_le(T.spent_of(i), T.spent_of(j)), Bool.and(Gw.ac_grow.gr(l, l2), Gw.ac_grow.gr(r, r2)), hg)), AR.at_reach.and_t(ac_bud.cov(l2, A.down(ls, T.GoL{})), ac_bud.cov(r2, A.down(ls, T.GoR{})), ac_bud.cov_gr(l, l2, A.down(ls, T.GoL{}), AR.at_reach.and_l(Gw.ac_grow.gr(l, l2), Gw.ac_grow.gr(r, r2), g1), AR.at_reach.and_l(ac_bud.cov(l, A.down(ls, T.GoL{})), ac_bud.cov(r, A.down(ls, T.GoR{})), c1), AR.at_reach.and_l(ac_bud.placed(l, A.down(ls, T.GoL{})), ac_bud.placed(r, A.down(ls, T.GoR{})), hp)), ac_bud.cov_gr(r, r2, A.down(ls, T.GoR{}), AR.at_reach.and_r(Gw.ac_grow.gr(l, l2), Gw.ac_grow.gr(r, r2), g1), AR.at_reach.and_r(ac_bud.cov(l, A.down(ls, T.GoL{})), ac_bud.cov(r, A.down(ls, T.GoR{})), c1), AR.at_reach.and_r(ac_bud.placed(l, A.down(ls, T.GoL{})), ac_bud.placed(r, A.down(ls, T.GoR{})), hp))))

# a tree that grew from a placed one is placed
def ac_bud.placed_gr(+a: T.Node, +b: T.Node, +ls: List<&2, A.Load>, +hg: {Gw.ac_grow.gr(a, b) == True{} : Bool}, +hp: {ac_bud.placed(a, ls) == True{} : Bool}) -> {ac_bud.placed(b, ls) == True{} : Bool}:
  match a b:
    case T.Leaf{i} T.Leaf{j}:
      hp
    case T.Leaf{i} T.Split{j, o, l, r}:
      AR.at_reach.and_t(ac_bud.placed(l, A.down(ls, T.GoL{})), ac_bud.placed(r, A.down(ls, T.GoR{})), AR.at_reach.tr(List<&2, A.Load>, [], A.down(ls, T.GoL{}), z => {ac_bud.placed(l, z) == True{} : Bool}, Equal.sym(List<&2, A.Load>, A.down(ls, T.GoL{}), [], ac_bud.down_nil(T.GoL{}, ls, hp)), ac_bud.placed_nil(l)), AR.at_reach.tr(List<&2, A.Load>, [], A.down(ls, T.GoR{}), z => {ac_bud.placed(r, z) == True{} : Bool}, Equal.sym(List<&2, A.Load>, A.down(ls, T.GoR{}), [], ac_bud.down_nil(T.GoR{}, ls, hp)), ac_bud.placed_nil(r)))
    case T.Split{i, o, l, r} T.Leaf{j}:
      AR.at_reach.absurd({ac_bud.placed(T.Leaf{j}, ls) == True{} : Bool}, hg)
    case T.Split{i, o, l, r} T.Split{j, o2, l2, r2}:
      +g1 = AR.at_reach.and_r(Nat.is_le(T.spent_of(i), T.spent_of(j)), Bool.and(Gw.ac_grow.gr(l, l2), Gw.ac_grow.gr(r, r2)), hg)
      AR.at_reach.and_t(ac_bud.placed(l2, A.down(ls, T.GoL{})), ac_bud.placed(r2, A.down(ls, T.GoR{})), ac_bud.placed_gr(l, l2, A.down(ls, T.GoL{}), AR.at_reach.and_l(Gw.ac_grow.gr(l, l2), Gw.ac_grow.gr(r, r2), g1), AR.at_reach.and_l(ac_bud.placed(l, A.down(ls, T.GoL{})), ac_bud.placed(r, A.down(ls, T.GoR{})), hp)), ac_bud.placed_gr(r, r2, A.down(ls, T.GoR{}), AR.at_reach.and_r(Gw.ac_grow.gr(l, l2), Gw.ac_grow.gr(r, r2), g1), AR.at_reach.and_r(ac_bud.placed(l, A.down(ls, T.GoL{})), ac_bud.placed(r, A.down(ls, T.GoR{})), hp)))

# a shift keeps the tree's shape
def ac_bud.placed_shift(+t: T.Node, +ls: List<&2, A.Load>, +k: List<&2, A.Load>, +up: Bool) -> {ac_bud.placed(A.shift(t, k, up), ls) == ac_bud.placed(t, ls) : Bool}:
  match t:
    case T.Leaf{i}:
      {==}
    case T.Split{i, own, l, r}:
      %ac_bud.placed_shift(l, A.down(ls, T.GoL{}), A.down(k, T.GoL{}), up) : {Bool.and(ac_bud.placed(A.shift(l, A.down(k, T.GoL{}), up), A.down(ls, T.GoL{})), ac_bud.placed(A.shift(r, A.down(k, T.GoR{}), up), A.down(ls, T.GoR{}))) == Bool.and(_, ac_bud.placed(r, A.down(ls, T.GoR{}))) : Bool}
      %ac_bud.placed_shift(r, A.down(ls, T.GoR{}), A.down(k, T.GoR{}), up) : {Bool.and(ac_bud.placed(A.shift(l, A.down(k, T.GoL{}), up), A.down(ls, T.GoL{})), ac_bud.placed(A.shift(r, A.down(k, T.GoR{}), up), A.down(ls, T.GoR{}))) == Bool.and(ac_bud.placed(A.shift(l, A.down(k, T.GoL{}), up), A.down(ls, T.GoL{})), _) : Bool}
      {==}

# Sums
# ----

# every load's charge
def ac_bud.lsum(ls: List<&2, A.Load>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case Con{x, rest}:
      match x:
        case A.Load{p, n}:
          Nat.add(n, ac_bud.lsum(rest))

# (a + b) + (c + d) = (a + c) + (b + d)
def ac_bud.interchange(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  %Equal.sym(Nat, Nat.add(Nat.add(a, b), Nat.add(c, d)), Nat.add(a, Nat.add(b, Nat.add(c, d))), AR.at_reach.add_assoc(a, b, Nat.add(c, d))) : {_ == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}
  %Equal.sym(Nat, Nat.add(b, Nat.add(c, d)), Nat.add(c, Nat.add(b, d)), AR.at_reach.add_lcomm(b, c, d)) : {Nat.add(a, _) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}
  Equal.sym(Nat, Nat.add(Nat.add(a, c), Nat.add(b, d)), Nat.add(a, Nat.add(c, Nat.add(b, d))), AR.at_reach.add_assoc(a, c, Nat.add(b, d)))

def ac_bud.split_c(p: List<&2, T.Dir>, +n: Nat, +rest: List<&2, A.Load>, +ih: {ac_bud.lsum(rest) == Nat.add(A.here(rest), Nat.add(ac_bud.lsum(A.down(rest, T.GoL{})), ac_bud.lsum(A.down(rest, T.GoR{})))) : Nat}) -> {ac_bud.lsum(A.Load{p, n} <> rest) == Nat.add(A.here(A.Load{p, n} <> rest), Nat.add(ac_bud.lsum(A.down(A.Load{p, n} <> rest, T.GoL{})), ac_bud.lsum(A.down(A.Load{p, n} <> rest, T.GoR{})))) : Nat}:
  match p:
    case Nil{}:
      %Equal.sym(Nat, ac_bud.lsum(rest), Nat.add(A.here(rest), Nat.add(ac_bud.lsum(A.down(rest, T.GoL{})), ac_bud.lsum(A.down(rest, T.GoR{})))), ih) : {Nat.add(n, _) == Nat.add(Nat.add(n, A.here(rest)), Nat.add(ac_bud.lsum(A.down(rest, T.GoL{})), ac_bud.lsum(A.down(rest, T.GoR{})))) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(n, A.here(rest)), Nat.add(ac_bud.lsum(A.down(rest, T.GoL{})), ac_bud.lsum(A.down(rest, T.GoR{})))), Nat.add(n, Nat.add(A.here(rest), Nat.add(ac_bud.lsum(A.down(rest, T.GoL{})), ac_bud.lsum(A.down(rest, T.GoR{}))))), AR.at_reach.add_assoc(n, A.here(rest), Nat.add(ac_bud.lsum(A.down(rest, T.GoL{})), ac_bud.lsum(A.down(rest, T.GoR{})))))
    case Con{e, q}:
      match e:
        case T.GoL{}:
          %Equal.sym(Nat, ac_bud.lsum(rest), Nat.add(A.here(rest), Nat.add(ac_bud.lsum(A.down(rest, T.GoL{})), ac_bud.lsum(A.down(rest, T.GoR{})))), ih) : {Nat.add(n, _) == Nat.add(A.here(rest), Nat.add(Nat.add(n, ac_bud.lsum(A.down(rest, T.GoL{}))), ac_bud.lsum(A.down(rest, T.GoR{})))) : Nat}
          %AR.at_reach.add_lcomm(A.here(rest), n, Nat.add(ac_bud.lsum(A.down(rest, T.GoL{})), ac_bud.lsum(A.down(rest, T.GoR{})))) : {_ == Nat.add(A.here(rest), Nat.add(Nat.add(n, ac_bud.lsum(A.down(rest, T.GoL{}))), ac_bud.lsum(A.down(rest, T.GoR{})))) : Nat}
          Equal.cong(Nat, Nat, z => Nat.add(A.here(rest), z), Nat.add(n, Nat.add(ac_bud.lsum(A.down(rest, T.GoL{})), ac_bud.lsum(A.down(rest, T.GoR{})))), Nat.add(Nat.add(n, ac_bud.lsum(A.down(rest, T.GoL{}))), ac_bud.lsum(A.down(rest, T.GoR{}))), Equal.sym(Nat, Nat.add(Nat.add(n, ac_bud.lsum(A.down(rest, T.GoL{}))), ac_bud.lsum(A.down(rest, T.GoR{}))), Nat.add(n, Nat.add(ac_bud.lsum(A.down(rest, T.GoL{})), ac_bud.lsum(A.down(rest, T.GoR{})))), AR.at_reach.add_assoc(n, ac_bud.lsum(A.down(rest, T.GoL{})), ac_bud.lsum(A.down(rest, T.GoR{})))))
        case T.GoR{}:
          %Equal.sym(Nat, ac_bud.lsum(rest), Nat.add(A.here(rest), Nat.add(ac_bud.lsum(A.down(rest, T.GoL{})), ac_bud.lsum(A.down(rest, T.GoR{})))), ih) : {Nat.add(n, _) == Nat.add(A.here(rest), Nat.add(ac_bud.lsum(A.down(rest, T.GoL{})), Nat.add(n, ac_bud.lsum(A.down(rest, T.GoR{}))))) : Nat}
          %AR.at_reach.add_lcomm(A.here(rest), n, Nat.add(ac_bud.lsum(A.down(rest, T.GoL{})), ac_bud.lsum(A.down(rest, T.GoR{})))) : {_ == Nat.add(A.here(rest), Nat.add(ac_bud.lsum(A.down(rest, T.GoL{})), Nat.add(n, ac_bud.lsum(A.down(rest, T.GoR{}))))) : Nat}
          Equal.cong(Nat, Nat, z => Nat.add(A.here(rest), z), Nat.add(n, Nat.add(ac_bud.lsum(A.down(rest, T.GoL{})), ac_bud.lsum(A.down(rest, T.GoR{})))), Nat.add(ac_bud.lsum(A.down(rest, T.GoL{})), Nat.add(n, ac_bud.lsum(A.down(rest, T.GoR{})))), AR.at_reach.add_lcomm(n, ac_bud.lsum(A.down(rest, T.GoL{})), ac_bud.lsum(A.down(rest, T.GoR{}))))

# the charges add up: here, then below each child
def ac_bud.lsum_split(ls: List<&2, A.Load>) -> {ac_bud.lsum(ls) == Nat.add(A.here(ls), Nat.add(ac_bud.lsum(A.down(ls, T.GoL{})), ac_bud.lsum(A.down(ls, T.GoR{})))) : Nat}:
  match ls:
    case Nil{}:
      {==}
    case Con{x, +rest}:
      match x:
        case A.Load{p, n}:
          ac_bud.split_c(p, n, rest, ac_bud.lsum_split(rest))

def ac_bud.here_all(ls: List<&2, A.Load>, h: {ac_bud.all_nil(ls) == True{} : Bool}) -> {A.here(ls) == ac_bud.lsum(ls) : Nat}:
  match ls:
    case Nil{}:
      {==}
    case Con{x, rest}:
      match x:
        case A.Load{p, +n}:
          match p:
            case Nil{}:
              Equal.cong(Nat, Nat, z => Nat.add(n, z), A.here(rest), ac_bud.lsum(rest), ac_bud.here_all(rest, h))
            case Con{e, q}:
              AR.at_reach.absurd({A.here(A.Load{e <> q, n} <> rest) == ac_bud.lsum(A.Load{e <> q, n} <> rest) : Nat}, h)

# the view of a placed tree spent the tree's spend plus every charge
def ac_bud.spent_shift(+t: T.Node, +ls: List<&2, A.Load>, +hp: {ac_bud.placed(t, ls) == True{} : Bool}) -> {S.spent_all(A.shift(t, ls, True{})) == Nat.add(S.spent_all(t), ac_bud.lsum(ls)) : Nat}:
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, +sp, dl, q}:
          Equal.cong(Nat, Nat, z => Nat.add(sp, z), A.here(ls), ac_bud.lsum(ls), ac_bud.here_all(ls, hp))
    case T.Split{i, own, +l, +r}:
      match i:
        case T.Info{st, s, lim, +sp, dl, q}:
          %Equal.sym(Nat, S.spent_all(A.shift(l, A.down(ls, T.GoL{}), True{})), Nat.add(S.spent_all(l), ac_bud.lsum(A.down(ls, T.GoL{}))), ac_bud.spent_shift(l, A.down(ls, T.GoL{}), AR.at_reach.and_l(ac_bud.placed(l, A.down(ls, T.GoL{})), ac_bud.placed(r, A.down(ls, T.GoR{})), hp))) : {Nat.add(Nat.add(sp, A.here(ls)), Nat.add(_, S.spent_all(A.shift(r, A.down(ls, T.GoR{}), True{})))) == Nat.add(Nat.add(sp, Nat.add(S.spent_all(l), S.spent_all(r))), ac_bud.lsum(ls)) : Nat}
          %Equal.sym(Nat, S.spent_all(A.shift(r, A.down(ls, T.GoR{}), True{})), Nat.add(S.spent_all(r), ac_bud.lsum(A.down(ls, T.GoR{}))), ac_bud.spent_shift(r, A.down(ls, T.GoR{}), AR.at_reach.and_r(ac_bud.placed(l, A.down(ls, T.GoL{})), ac_bud.placed(r, A.down(ls, T.GoR{})), hp))) : {Nat.add(Nat.add(sp, A.here(ls)), Nat.add(Nat.add(S.spent_all(l), ac_bud.lsum(A.down(ls, T.GoL{}))), _)) == Nat.add(Nat.add(sp, Nat.add(S.spent_all(l), S.spent_all(r))), ac_bud.lsum(ls)) : Nat}
          %Equal.sym(Nat, ac_bud.lsum(ls), Nat.add(A.here(ls), Nat.add(ac_bud.lsum(A.down(ls, T.GoL{})), ac_bud.lsum(A.down(ls, T.GoR{})))), ac_bud.lsum_split(ls)) : {Nat.add(Nat.add(sp, A.here(ls)), Nat.add(Nat.add(S.spent_all(l), ac_bud.lsum(A.down(ls, T.GoL{}))), Nat.add(S.spent_all(r), ac_bud.lsum(A.down(ls, T.GoR{}))))) == Nat.add(Nat.add(sp, Nat.add(S.spent_all(l), S.spent_all(r))), _) : Nat}
          %Equal.sym(Nat, Nat.add(Nat.add(S.spent_all(l), ac_bud.lsum(A.down(ls, T.GoL{}))), Nat.add(S.spent_all(r), ac_bud.lsum(A.down(ls, T.GoR{})))), Nat.add(Nat.add(S.spent_all(l), S.spent_all(r)), Nat.add(ac_bud.lsum(A.down(ls, T.GoL{})), ac_bud.lsum(A.down(ls, T.GoR{})))), ac_bud.interchange(S.spent_all(l), ac_bud.lsum(A.down(ls, T.GoL{})), S.spent_all(r), ac_bud.lsum(A.down(ls, T.GoR{})))) : {Nat.add(Nat.add(sp, A.here(ls)), _) == Nat.add(Nat.add(sp, Nat.add(S.spent_all(l), S.spent_all(r))), Nat.add(A.here(ls), Nat.add(ac_bud.lsum(A.down(ls, T.GoL{})), ac_bud.lsum(A.down(ls, T.GoR{}))))) : Nat}
          ac_bud.interchange(sp, A.here(ls), Nat.add(S.spent_all(l), S.spent_all(r)), Nat.add(ac_bud.lsum(A.down(ls, T.GoL{})), ac_bud.lsum(A.down(ls, T.GoR{}))))

# Value limits
# ------------

def ac_bud.lv(l: T.Lim) -> Bool:
  match l:
    case T.Unlimited{}:
      False{}
    case T.Value{x}:
      True{}

def ac_bud.quiet_root(+t: T.Node, h: {S.quiet(t) == True{} : Bool}) -> {S.is_running(t) == False{} : Bool}:
  match t:
    case T.Leaf{i}:
      AR.at_reach.not_t(T.running(T.st_of(i)), h)
    case T.Split{+i, own, l, r}:
      AR.at_reach.not_t(T.running(T.st_of(i)), AR.at_reach.and_l(Bool.not(T.running(T.st_of(i))), Bool.and(S.quiet(l), S.quiet(r)), h))

# under a quiet tree no node runs
def ac_bud.quiet_node(p: List<&2, T.Dir>, +t: T.Node, -n: T.Node, e: {S.node_at(p, t) == Some{n} : Maybe<&2, T.Node>}, h: {S.quiet(t) == True{} : Bool}) -> {S.is_running(n) == False{} : Bool}:
  match p:
    case Nil{}:
      AR.at_reach.tr(T.Node, t, n, z => {S.is_running(z) == False{} : Bool}, Equal.sym(T.Node, n, t, E.at_edit.some_inj(t, n, e)), ac_bud.quiet_root(t, h))
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match t:
            case T.Leaf{i}:
              E.at_edit.absurd_none({S.is_running(n) == False{} : Bool}, n, e)
            case T.Split{+i, own, +l, +r}:
              ac_bud.quiet_node(rest, l, n, e, AR.at_reach.and_l(S.quiet(l), S.quiet(r), AR.at_reach.and_r(Bool.not(T.running(T.st_of(i))), Bool.and(S.quiet(l), S.quiet(r)), h)))
        case T.GoR{}:
          match t:
            case T.Leaf{i}:
              E.at_edit.absurd_none({S.is_running(n) == False{} : Bool}, n, e)
            case T.Split{+i, own, +l, +r}:
              ac_bud.quiet_node(rest, r, n, e, AR.at_reach.and_r(S.quiet(l), S.quiet(r), AR.at_reach.and_r(Bool.not(T.running(T.st_of(i))), Bool.and(S.quiet(l), S.quiet(r)), h)))

# a running node's ancestors run
def ac_bud.run_kid(c: Bool, +l: T.Node, +k: Nat, +g: AR.at_reach.Good(l, k), ec: {S.is_running(l) == c : Bool}, +rest: List<&2, T.Dir>, -n: T.Node, e: {S.node_at(rest, l) == Some{n} : Maybe<&2, T.Node>}, r: {S.is_running(n) == True{} : Bool}) -> {S.is_running(l) == True{} : Bool}:
  match c:
    case True{}:
      ec
    case False{}:
      AR.at_reach.absurd_t({S.is_running(l) == True{} : Bool}, Equal.trans(Bool, True{}, S.is_running(n), False{}, Equal.sym(Bool, S.is_running(n), True{}, r), ac_bud.quiet_node(rest, l, n, e, AR.at_reach.quiet_of(l, k, g, ec))))

# a child that holds part of a Value limit holds a Value
def ac_bud.lplus_val(+sp: Nat, x: T.Lim, -y: T.Lim, lim: T.Lim, hl: {ac_bud.lv(lim) == True{} : Bool}, bu: {S.lim_le(AR.at_reach.lplus(T.Value{sp}, AR.at_reach.lplus(x, y)), lim) == True{} : Bool}) -> {ac_bud.lv(x) == True{} : Bool}:
  match x:
    case T.Unlimited{}:
      match lim:
        case T.Unlimited{}:
          AR.at_reach.absurd({ac_bud.lv(T.Unlimited{}) == True{} : Bool}, hl)
        case T.Value{m}:
          AR.at_reach.absurd({ac_bud.lv(T.Unlimited{}) == True{} : Bool}, bu)
    case T.Value{v}:
      {==}

def ac_bud.held_run(+l: T.Node, er: {S.is_running(l) == True{} : Bool}) -> {S.held(l) == T.limit_of(T.info(l)) : T.Lim}:
  %Equal.sym(Bool, S.is_running(l), True{}, er) : {S.held_if(_, T.limit_of(T.info(l)), S.spent_all(l)) == T.limit_of(T.info(l)) : T.Lim}
  {==}

def ac_bud.lplus_comm(x: T.Lim, y: T.Lim) -> {AR.at_reach.lplus(x, y) == AR.at_reach.lplus(y, x) : T.Lim}:
  match x:
    case T.Unlimited{}:
      match y:
        case T.Unlimited{}:
          {==}
        case T.Value{b}:
          {==}
    case T.Value{+a}:
      match y:
        case T.Unlimited{}:
          {==}
        case T.Value{+b}:
          Equal.cong(Nat, T.Lim, z => T.Value{z}, Nat.add(a, b), Nat.add(b, a), AR.at_reach.add_comm(a, b))

# under a Value root every running node has a Value limit
def ac_bud.run_value(p: List<&2, T.Dir>, +t: T.Node, +k: Nat, +g: AR.at_reach.Good(t, k), -n: T.Node, +e: {S.node_at(p, t) == Some{n} : Maybe<&2, T.Node>}, +r: {S.is_running(n) == True{} : Bool}, hv: {ac_bud.lv(T.limit_of(T.info(t))) == True{} : Bool}) -> {ac_bud.lv(T.limit_of(T.info(n))) == True{} : Bool}:
  match p:
    case Nil{}:
      AR.at_reach.tr(T.Node, t, n, z => {ac_bud.lv(T.limit_of(T.info(z))) == True{} : Bool}, Equal.sym(T.Node, n, t, E.at_edit.some_inj(t, n, e)), hv)
    case Con{d, +rest}:
      match d:
        case T.GoL{}:
          match t:
            case T.Leaf{i}:
              E.at_edit.absurd_none({ac_bud.lv(T.limit_of(T.info(n))) == True{} : Bool}, n, e)
            case T.Split{i, +own, +l, +r2}:
              match i:
                case T.Info{+st, +s, +lim, +sp, +dl, +q}:
                  match k:
                    case 0n:
                      match g:
                    case 1n+kq:
                      (tl, g1) = g
                      (rc, g2) = g1
                      (bu, g3) = g2
                      (dl1, g4) = g3
                      (dr1, g5) = g4
                      (gl, gr) = g5
                      +rl = ac_bud.run_kid(S.is_running(l), l, kq, gl, {==}, rest, n, e, r)
                      +hx = ac_bud.lplus_val(sp, S.held(l), S.held(r2), lim, hv, bu)
                      ac_bud.run_value(rest, l, kq, gl, n, e, r, AR.at_reach.tr(T.Lim, S.held(l), T.limit_of(T.info(l)), z => {ac_bud.lv(z) == True{} : Bool}, ac_bud.held_run(l, rl), hx))
        case T.GoR{}:
          match t:
            case T.Leaf{i}:
              E.at_edit.absurd_none({ac_bud.lv(T.limit_of(T.info(n))) == True{} : Bool}, n, e)
            case T.Split{i, +own, +l, +r2}:
              match i:
                case T.Info{+st, +s, +lim, +sp, +dl, +q}:
                  match k:
                    case 0n:
                      match g:
                    case 1n+kq:
                      (tl, g1) = g
                      (rc, g2) = g1
                      (bu, g3) = g2
                      (dl1, g4) = g3
                      (dr1, g5) = g4
                      (gl, gr) = g5
                      +rr = ac_bud.run_kid(S.is_running(r2), r2, kq, gr, {==}, rest, n, e, r)
                      +bu2 = AR.at_reach.tr(T.Lim, AR.at_reach.lplus(S.held(l), S.held(r2)), AR.at_reach.lplus(S.held(r2), S.held(l)), z => {S.lim_le(AR.at_reach.lplus(T.Value{sp}, z), lim) == True{} : Bool}, ac_bud.lplus_comm(S.held(l), S.held(r2)), bu)
                      +hx = ac_bud.lplus_val(sp, S.held(r2), S.held(l), lim, hv, bu2)
                      ac_bud.run_value(rest, r2, kq, gr, n, e, r, AR.at_reach.tr(T.Lim, S.held(r2), T.limit_of(T.info(r2)), z => {ac_bud.lv(z) == True{} : Bool}, ac_bud.held_run(r2, rr), hx))

def ac_bud.less_value(lim: T.Lim, -sp: Nat, h: {ac_bud.lv(lim) == True{} : Bool}) -> {ac_bud.lv(T.lim_less(lim, sp)) == True{} : Bool}:
  match lim:
    case T.Unlimited{}:
      AR.at_reach.absurd({ac_bud.lv(T.lim_less(T.Unlimited{}, sp)) == True{} : Bool}, h)
    case T.Value{x}:
      {==}

def ac_bud.drop_value(a: T.Lim, b: T.Lim, h: {ac_bud.lv(a) == True{} : Bool}) -> {ac_bud.lv(T.lim_drop(a, b)) == True{} : Bool}:
  match a:
    case T.Unlimited{}:
      AR.at_reach.absurd({ac_bud.lv(T.lim_drop(T.Unlimited{}, b)) == True{} : Bool}, h)
    case T.Value{x}:
      match b:
        case T.Unlimited{}:
          {==}
        case T.Value{y}:
          {==}

# a node with a Value limit has a Value free
def ac_bud.free_value(+n: T.Node, h: {ac_bud.lv(T.limit_of(T.info(n))) == True{} : Bool}) -> {ac_bud.lv(T.free(n)) == True{} : Bool}:
  match n:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, q}:
          ac_bud.less_value(lim, sp, h)
    case T.Split{i, own, +l, +r}:
      match i:
        case T.Info{st, s, +lim, +sp, dl, q}:
          ac_bud.drop_value(T.lim_drop(T.lim_less(lim, sp), T.charge(l)), T.charge(r), ac_bud.drop_value(T.lim_less(lim, sp), T.charge(l), ac_bud.less_value(lim, sp, h)))

def ac_bud.grant_n(f: T.Lim, -a: Nat, h: {ac_bud.lv(f) == True{} : Bool}) -> {A.lim_n(A.grant(f, a)) == a : Nat}:
  match f:
    case T.Unlimited{}:
      AR.at_reach.absurd({A.lim_n(A.grant(T.Unlimited{}, a)) == a : Nat}, h)
    case T.Value{m}:
      {==}

# The view after a help: the help's charge spent at its node
# ---------------------------------------------------------

def ac_bud.app_nil(xs: List<&2, A.Load>) -> {List.append(&2, A.Load, xs, []) == xs : List<&2, A.Load>}:
  match xs:
    case Nil{}:
      {==}
    case Con{y, rest}:
      Equal.cong(List<&2, A.Load>, List<&2, A.Load>, z => y <> z, List.append(&2, A.Load, rest, []), rest, ac_bud.app_nil(rest))

def ac_bud.here_snoc(ls: List<&2, A.Load>, +x: A.Load) -> {A.here(List.append(&2, A.Load, ls, [x])) == Nat.add(A.here(ls), A.here([x])) : Nat}:
  match ls:
    case Nil{}:
      {==}
    case Con{y, rest}:
      match y:
        case A.Load{p, +n}:
          match p:
            case Nil{}:
              %Equal.sym(Nat, A.here(List.append(&2, A.Load, rest, [x])), Nat.add(A.here(rest), A.here([x])), ac_bud.here_snoc(rest, x)) : {Nat.add(n, _) == Nat.add(Nat.add(n, A.here(rest)), A.here([x])) : Nat}
              Equal.sym(Nat, Nat.add(Nat.add(n, A.here(rest)), A.here([x])), Nat.add(n, Nat.add(A.here(rest), A.here([x]))), AR.at_reach.add_assoc(n, A.here(rest), A.here([x])))
            case Con{e, q}:
              ac_bud.here_snoc(rest, x)

def ac_bud.down_snoc_l(ls: List<&2, A.Load>, +x: A.Load) -> {A.down(List.append(&2, A.Load, ls, [x]), T.GoL{}) == List.append(&2, A.Load, A.down(ls, T.GoL{}), A.down([x], T.GoL{})) : List<&2, A.Load>}:
  match ls:
    case Nil{}:
      {==}
    case Con{y, rest}:
      match y:
        case A.Load{p, +n}:
          match p:
            case Nil{}:
              ac_bud.down_snoc_l(rest, x)
            case Con{e, +q}:
              match e:
                case T.GoL{}:
                  Equal.cong(List<&2, A.Load>, List<&2, A.Load>, z => A.Load{q, n} <> z, A.down(List.append(&2, A.Load, rest, [x]), T.GoL{}), List.append(&2, A.Load, A.down(rest, T.GoL{}), A.down([x], T.GoL{})), ac_bud.down_snoc_l(rest, x))
                case T.GoR{}:
                  ac_bud.down_snoc_l(rest, x)

def ac_bud.down_snoc_r(ls: List<&2, A.Load>, +x: A.Load) -> {A.down(List.append(&2, A.Load, ls, [x]), T.GoR{}) == List.append(&2, A.Load, A.down(ls, T.GoR{}), A.down([x], T.GoR{})) : List<&2, A.Load>}:
  match ls:
    case Nil{}:
      {==}
    case Con{y, rest}:
      match y:
        case A.Load{p, +n}:
          match p:
            case Nil{}:
              ac_bud.down_snoc_r(rest, x)
            case Con{e, +q}:
              match e:
                case T.GoL{}:
                  ac_bud.down_snoc_r(rest, x)
                case T.GoR{}:
                  Equal.cong(List<&2, A.Load>, List<&2, A.Load>, z => A.Load{q, n} <> z, A.down(List.append(&2, A.Load, rest, [x]), T.GoR{}), List.append(&2, A.Load, A.down(rest, T.GoR{}), A.down([x], T.GoR{})), ac_bud.down_snoc_r(rest, x))

def ac_bud.down_snoc(+ls: List<&2, A.Load>, d: T.Dir, +x: A.Load) -> {A.down(List.append(&2, A.Load, ls, [x]), d) == List.append(&2, A.Load, A.down(ls, d), A.down([x], d)) : List<&2, A.Load>}:
  match d:
    case T.GoL{}:
      ac_bud.down_snoc_l(ls, x)
    case T.GoR{}:
      ac_bud.down_snoc_r(ls, x)

# a charge appended at another child, or at [], adds nothing below d
def ac_bud.kid_none(+ls: List<&2, A.Load>, +d: T.Dir, +x: A.Load, e: {A.down([x], d) == [] : List<&2, A.Load>}) -> {A.down(List.append(&2, A.Load, ls, [x]), d) == A.down(ls, d) : List<&2, A.Load>}:
  %Equal.sym(List<&2, A.Load>, A.down(List.append(&2, A.Load, ls, [x]), d), List.append(&2, A.Load, A.down(ls, d), A.down([x], d)), ac_bud.down_snoc(ls, d, x)) : {_ == A.down(ls, d) : List<&2, A.Load>}
  %Equal.sym(List<&2, A.Load>, A.down([x], d), [], e) : {List.append(&2, A.Load, A.down(ls, d), _) == A.down(ls, d) : List<&2, A.Load>}
  ac_bud.app_nil(A.down(ls, d))

# a charge appended below a child adds nothing here
def ac_bud.here_none(+ls: List<&2, A.Load>, +d: T.Dir, +q: List<&2, T.Dir>, +a: Nat) -> {A.here(List.append(&2, A.Load, ls, [A.Load{d <> q, a}])) == A.here(ls) : Nat}:
  Equal.trans(Nat, A.here(List.append(&2, A.Load, ls, [A.Load{d <> q, a}])), Nat.add(A.here(ls), 0n), A.here(ls), ac_bud.here_snoc(ls, A.Load{d <> q, a}), AR.at_reach.add_zero(A.here(ls)))

# sp + (h + (a + 0)) = (sp + h) + a
def ac_bud.snoc_arith(+sp: Nat, +h: Nat, +a: Nat) -> {Nat.add(sp, Nat.add(h, Nat.add(a, 0n))) == Nat.add(Nat.add(sp, h), a) : Nat}:
  %Equal.sym(Nat, Nat.add(a, 0n), a, AR.at_reach.add_zero(a)) : {Nat.add(sp, Nat.add(h, _)) == Nat.add(Nat.add(sp, h), a) : Nat}
  Equal.sym(Nat, Nat.add(Nat.add(sp, h), a), Nat.add(sp, Nat.add(h, a)), AR.at_reach.add_assoc(sp, h, a))

def ac_bud.here_root(+ls: List<&2, A.Load>, +sp: Nat, +a: Nat) -> {Nat.add(sp, A.here(List.append(&2, A.Load, ls, [A.Load{[], a}]))) == Nat.add(Nat.add(sp, A.here(ls)), a) : Nat}:
  %Equal.sym(Nat, A.here(List.append(&2, A.Load, ls, [A.Load{[], a}])), Nat.add(A.here(ls), Nat.add(a, 0n)), ac_bud.here_snoc(ls, A.Load{[], a})) : {Nat.add(sp, _) == Nat.add(Nat.add(sp, A.here(ls)), a) : Nat}
  ac_bud.snoc_arith(sp, A.here(ls), a)

# a charge appended raises the node at its path
def ac_bud.shift_snoc(p: List<&2, T.Dir>, +t: T.Node, +ls: List<&2, A.Load>, +a: Nat) -> {A.shift(t, List.append(&2, A.Load, ls, [A.Load{p, a}]), True{}) == CS.bump(p, A.shift(t, ls, True{}), a) : T.Node}:
  match p:
    case Nil{}:
      match t:
        case T.Leaf{i}:
          match i:
            case T.Info{st, s, lim, +sp, dl, q}:
              Equal.cong(Nat, T.Node, z => T.Leaf{T.Info{st, s, lim, z, dl, q}}, Nat.add(sp, A.here(List.append(&2, A.Load, ls, [A.Load{[], a}]))), Nat.add(Nat.add(sp, A.here(ls)), a), ac_bud.here_root(ls, sp, a))
        case T.Split{i, +own, +l, +r}:
          match i:
            case T.Info{+st, +s, +lim, +sp, +dl, +q}:
              %Equal.sym(List<&2, A.Load>, A.down(List.append(&2, A.Load, ls, [A.Load{[], a}]), T.GoL{}), A.down(ls, T.GoL{}), ac_bud.kid_none(ls, T.GoL{}, A.Load{[], a}, {==})) : {T.Split{T.Info{st, s, lim, Nat.add(sp, A.here(List.append(&2, A.Load, ls, [A.Load{[], a}]))), dl, q}, own, A.shift(l, _, True{}), A.shift(r, A.down(List.append(&2, A.Load, ls, [A.Load{[], a}]), T.GoR{}), True{})} == CS.bump([], A.shift(T.Split{T.Info{st, s, lim, sp, dl, q}, own, l, r}, ls, True{}), a) : T.Node}
              %Equal.sym(List<&2, A.Load>, A.down(List.append(&2, A.Load, ls, [A.Load{[], a}]), T.GoR{}), A.down(ls, T.GoR{}), ac_bud.kid_none(ls, T.GoR{}, A.Load{[], a}, {==})) : {T.Split{T.Info{st, s, lim, Nat.add(sp, A.here(List.append(&2, A.Load, ls, [A.Load{[], a}]))), dl, q}, own, A.shift(l, A.down(ls, T.GoL{}), True{}), A.shift(r, _, True{})} == CS.bump([], A.shift(T.Split{T.Info{st, s, lim, sp, dl, q}, own, l, r}, ls, True{}), a) : T.Node}
              Equal.cong(Nat, T.Node, z => T.Split{T.Info{st, s, lim, z, dl, q}, own, A.shift(l, A.down(ls, T.GoL{}), True{}), A.shift(r, A.down(ls, T.GoR{}), True{})}, Nat.add(sp, A.here(List.append(&2, A.Load, ls, [A.Load{[], a}]))), Nat.add(Nat.add(sp, A.here(ls)), a), ac_bud.here_root(ls, sp, a))
    case Con{d, +rest}:
      match d:
        case T.GoL{}:
          match t:
            case T.Leaf{+i}:
              Equal.cong(Nat, T.Node, z => T.Leaf{A.shift_info(i, True{}, z)}, A.here(List.append(&2, A.Load, ls, [A.Load{T.GoL{} <> rest, a}])), A.here(ls), ac_bud.here_none(ls, T.GoL{}, rest, a))
            case T.Split{+i, +own, +l, +r}:
              %Equal.sym(Nat, A.here(List.append(&2, A.Load, ls, [A.Load{T.GoL{} <> rest, a}])), A.here(ls), ac_bud.here_none(ls, T.GoL{}, rest, a)) : {T.Split{A.shift_info(i, True{}, _), own, A.shift(l, A.down(List.append(&2, A.Load, ls, [A.Load{T.GoL{} <> rest, a}]), T.GoL{}), True{}), A.shift(r, A.down(List.append(&2, A.Load, ls, [A.Load{T.GoL{} <> rest, a}]), T.GoR{}), True{})} == T.Split{A.shift_info(i, True{}, A.here(ls)), own, CS.bump(rest, A.shift(l, A.down(ls, T.GoL{}), True{}), a), A.shift(r, A.down(ls, T.GoR{}), True{})} : T.Node}
              %Equal.sym(List<&2, A.Load>, A.down(List.append(&2, A.Load, ls, [A.Load{T.GoL{} <> rest, a}]), T.GoR{}), A.down(ls, T.GoR{}), ac_bud.kid_none(ls, T.GoR{}, A.Load{T.GoL{} <> rest, a}, {==})) : {T.Split{A.shift_info(i, True{}, A.here(ls)), own, A.shift(l, A.down(List.append(&2, A.Load, ls, [A.Load{T.GoL{} <> rest, a}]), T.GoL{}), True{}), A.shift(r, _, True{})} == T.Split{A.shift_info(i, True{}, A.here(ls)), own, CS.bump(rest, A.shift(l, A.down(ls, T.GoL{}), True{}), a), A.shift(r, A.down(ls, T.GoR{}), True{})} : T.Node}
              %Equal.sym(List<&2, A.Load>, A.down(List.append(&2, A.Load, ls, [A.Load{T.GoL{} <> rest, a}]), T.GoL{}), List.append(&2, A.Load, A.down(ls, T.GoL{}), [A.Load{rest, a}]), ac_bud.down_snoc(ls, T.GoL{}, A.Load{T.GoL{} <> rest, a})) : {T.Split{A.shift_info(i, True{}, A.here(ls)), own, A.shift(l, _, True{}), A.shift(r, A.down(ls, T.GoR{}), True{})} == T.Split{A.shift_info(i, True{}, A.here(ls)), own, CS.bump(rest, A.shift(l, A.down(ls, T.GoL{}), True{}), a), A.shift(r, A.down(ls, T.GoR{}), True{})} : T.Node}
              Equal.cong(T.Node, T.Node, z => T.Split{A.shift_info(i, True{}, A.here(ls)), own, z, A.shift(r, A.down(ls, T.GoR{}), True{})}, A.shift(l, List.append(&2, A.Load, A.down(ls, T.GoL{}), [A.Load{rest, a}]), True{}), CS.bump(rest, A.shift(l, A.down(ls, T.GoL{}), True{}), a), ac_bud.shift_snoc(rest, l, A.down(ls, T.GoL{}), a))
        case T.GoR{}:
          match t:
            case T.Leaf{+i}:
              Equal.cong(Nat, T.Node, z => T.Leaf{A.shift_info(i, True{}, z)}, A.here(List.append(&2, A.Load, ls, [A.Load{T.GoR{} <> rest, a}])), A.here(ls), ac_bud.here_none(ls, T.GoR{}, rest, a))
            case T.Split{+i, +own, +l, +r}:
              %Equal.sym(Nat, A.here(List.append(&2, A.Load, ls, [A.Load{T.GoR{} <> rest, a}])), A.here(ls), ac_bud.here_none(ls, T.GoR{}, rest, a)) : {T.Split{A.shift_info(i, True{}, _), own, A.shift(l, A.down(List.append(&2, A.Load, ls, [A.Load{T.GoR{} <> rest, a}]), T.GoL{}), True{}), A.shift(r, A.down(List.append(&2, A.Load, ls, [A.Load{T.GoR{} <> rest, a}]), T.GoR{}), True{})} == T.Split{A.shift_info(i, True{}, A.here(ls)), own, A.shift(l, A.down(ls, T.GoL{}), True{}), CS.bump(rest, A.shift(r, A.down(ls, T.GoR{}), True{}), a)} : T.Node}
              %Equal.sym(List<&2, A.Load>, A.down(List.append(&2, A.Load, ls, [A.Load{T.GoR{} <> rest, a}]), T.GoL{}), A.down(ls, T.GoL{}), ac_bud.kid_none(ls, T.GoL{}, A.Load{T.GoR{} <> rest, a}, {==})) : {T.Split{A.shift_info(i, True{}, A.here(ls)), own, A.shift(l, _, True{}), A.shift(r, A.down(List.append(&2, A.Load, ls, [A.Load{T.GoR{} <> rest, a}]), T.GoR{}), True{})} == T.Split{A.shift_info(i, True{}, A.here(ls)), own, A.shift(l, A.down(ls, T.GoL{}), True{}), CS.bump(rest, A.shift(r, A.down(ls, T.GoR{}), True{}), a)} : T.Node}
              %Equal.sym(List<&2, A.Load>, A.down(List.append(&2, A.Load, ls, [A.Load{T.GoR{} <> rest, a}]), T.GoR{}), List.append(&2, A.Load, A.down(ls, T.GoR{}), [A.Load{rest, a}]), ac_bud.down_snoc(ls, T.GoR{}, A.Load{T.GoR{} <> rest, a})) : {T.Split{A.shift_info(i, True{}, A.here(ls)), own, A.shift(l, A.down(ls, T.GoL{}), True{}), A.shift(r, _, True{})} == T.Split{A.shift_info(i, True{}, A.here(ls)), own, A.shift(l, A.down(ls, T.GoL{}), True{}), CS.bump(rest, A.shift(r, A.down(ls, T.GoR{}), True{}), a)} : T.Node}
              Equal.cong(T.Node, T.Node, z => T.Split{A.shift_info(i, True{}, A.here(ls)), own, A.shift(l, A.down(ls, T.GoL{}), True{}), z}, A.shift(r, List.append(&2, A.Load, A.down(ls, T.GoR{}), [A.Load{rest, a}]), True{}), CS.bump(rest, A.shift(r, A.down(ls, T.GoR{}), True{}), a), ac_bud.shift_snoc(rest, r, A.down(ls, T.GoR{}), a))

def ac_bud.raise_add(+u: T.Node, -a: Nat) -> {CS.raise_root(u, a) == T.add_spent(u, a) : T.Node}:
  match u:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, q}:
          {==}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, q}:
          {==}

# bumping the node n at p is spending at it
def ac_bud.bump_put(p: List<&2, T.Dir>, +u: T.Node, -n: T.Node, +a: Nat, e: {S.node_at(p, u) == Some{n} : Maybe<&2, T.Node>}) -> {CS.bump(p, u, a) == S.put(p, u, T.add_spent(n, a)) : T.Node}:
  match p:
    case Nil{}:
      %Equal.sym(T.Node, n, u, E.at_edit.some_inj(u, n, e)) : {CS.raise_root(u, a) == T.add_spent(_, a) : T.Node}
      ac_bud.raise_add(u, a)
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match u:
            case T.Leaf{i}:
              E.at_edit.absurd_none({CS.bump(T.GoL{} <> rest, T.Leaf{i}, a) == S.put(T.GoL{} <> rest, T.Leaf{i}, T.add_spent(n, a)) : T.Node}, n, e)
            case T.Split{+i, +own, +l, +r}:
              Equal.cong(T.Node, T.Node, z => T.Split{i, own, z, r}, CS.bump(rest, l, a), S.put(rest, l, T.add_spent(n, a)), ac_bud.bump_put(rest, l, n, a, e))
        case T.GoR{}:
          match u:
            case T.Leaf{i}:
              E.at_edit.absurd_none({CS.bump(T.GoR{} <> rest, T.Leaf{i}, a) == S.put(T.GoR{} <> rest, T.Leaf{i}, T.add_spent(n, a)) : T.Node}, n, e)
            case T.Split{+i, +own, +l, +r}:
              Equal.cong(T.Node, T.Node, z => T.Split{i, own, l, z}, CS.bump(rest, r, a), S.put(rest, r, T.add_spent(n, a)), ac_bud.bump_put(rest, r, n, a, e))

# a spend that fits a running node is taken
def ac_bud.spend_took(+n: T.Node, +a: Nat, -k: Nat, er: {T.running(T.st_of(T.info(n))) == True{} : Bool}, ef: {T.lim_fits(a, T.free(n)) == True{} : Bool}) -> {T.local(T.OpSpend{a}, n, k) == T.Took{T.add_spent(n, a)} : T.Step}:
  match n:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, q}:
          match st:
            case T.Running{}:
              %Equal.sym(Bool, T.lim_fits(a, T.free(T.Leaf{T.Info{T.Running{}, s, lim, sp, dl, q}})), True{}, ef) : {T.spend_fits(_, T.Leaf{T.Info{T.Running{}, s, lim, sp, dl, q}}, a) == T.Took{T.add_spent(T.Leaf{T.Info{T.Running{}, s, lim, sp, dl, q}}, a)} : T.Step}
              {==}
            case T.Finished{}:
              AR.at_reach.absurd({T.local(T.OpSpend{a}, T.Leaf{T.Info{T.Finished{}, s, lim, sp, dl, q}}, k) == T.Took{T.add_spent(T.Leaf{T.Info{T.Finished{}, s, lim, sp, dl, q}}, a)} : T.Step}, er)
            case T.Failed{}:
              AR.at_reach.absurd({T.local(T.OpSpend{a}, T.Leaf{T.Info{T.Failed{}, s, lim, sp, dl, q}}, k) == T.Took{T.add_spent(T.Leaf{T.Info{T.Failed{}, s, lim, sp, dl, q}}, a)} : T.Step}, er)
            case T.Cancelled{}:
              AR.at_reach.absurd({T.local(T.OpSpend{a}, T.Leaf{T.Info{T.Cancelled{}, s, lim, sp, dl, q}}, k) == T.Took{T.add_spent(T.Leaf{T.Info{T.Cancelled{}, s, lim, sp, dl, q}}, a)} : T.Step}, er)
    case T.Split{i, +own, +l, +r}:
      match i:
        case T.Info{st, s, lim, sp, dl, q}:
          match st:
            case T.Running{}:
              %Equal.sym(Bool, T.lim_fits(a, T.free(T.Split{T.Info{T.Running{}, s, lim, sp, dl, q}, own, l, r})), True{}, ef) : {T.spend_fits(_, T.Split{T.Info{T.Running{}, s, lim, sp, dl, q}, own, l, r}, a) == T.Took{T.add_spent(T.Split{T.Info{T.Running{}, s, lim, sp, dl, q}, own, l, r}, a)} : T.Step}
              {==}
            case T.Finished{}:
              AR.at_reach.absurd({T.local(T.OpSpend{a}, T.Split{T.Info{T.Finished{}, s, lim, sp, dl, q}, own, l, r}, k) == T.Took{T.add_spent(T.Split{T.Info{T.Finished{}, s, lim, sp, dl, q}, own, l, r}, a)} : T.Step}, er)
            case T.Failed{}:
              AR.at_reach.absurd({T.local(T.OpSpend{a}, T.Split{T.Info{T.Failed{}, s, lim, sp, dl, q}, own, l, r}, k) == T.Took{T.add_spent(T.Split{T.Info{T.Failed{}, s, lim, sp, dl, q}, own, l, r}, a)} : T.Step}, er)
            case T.Cancelled{}:
              AR.at_reach.absurd({T.local(T.OpSpend{a}, T.Split{T.Info{T.Cancelled{}, s, lim, sp, dl, q}, own, l, r}, k) == T.Took{T.add_spent(T.Split{T.Info{T.Cancelled{}, s, lim, sp, dl, q}, own, l, r}, a)} : T.Step}, er)

# the tree's step for the help's charge at p
def ac_bud.edit_spend(+p: List<&2, T.Dir>, +u: T.Node, +n: T.Node, +a: Nat, +k: Nat, e: {S.node_at(p, u) == Some{n} : Maybe<&2, T.Node>}, er: {T.running(T.st_of(T.info(n))) == True{} : Bool}, ef: {T.lim_fits(a, T.free(n)) == True{} : Bool}) -> {T.edit(p, u, T.OpSpend{a}, k) == T.Took{S.put(p, u, T.add_spent(n, a))} : T.Step}:
  %E.at_edit.edit_at(p, u, T.OpSpend{a}, k) : {_ == T.Took{S.put(p, u, T.add_spent(n, a))} : T.Step}
  %Equal.sym(Maybe<&2, T.Node>, S.node_at(p, u), Some{n}, e) : {E.at_edit.via(_, p, u, T.OpSpend{a}, k) == T.Took{S.put(p, u, T.add_spent(n, a))} : T.Step}
  %Equal.sym(T.Step, T.local(T.OpSpend{a}, n, E.at_edit.npred(p, k)), T.Took{T.add_spent(n, a)}, ac_bud.spend_took(n, a, E.at_edit.npred(p, k), er, ef)) : {E.at_edit.lift(_, p, u) == T.Took{S.put(p, u, T.add_spent(n, a))} : T.Step}
  {==}

# Help leaves
# -----------

# a spend sp fits the Value limit lim (an Unlimited limit: no)
def ac_bud.vfit(sp: Nat, lim: T.Lim) -> Bool:
  match lim:
    case T.Unlimited{}:
      False{}
    case T.Value{x}:
      Nat.is_le(sp, x)

# every running help leaf has a Value limit its spend fits
def ac_bud.hv(hs: List<&2, A.Help>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{h, rest}:
      match h:
        case A.Help{p, st, lim, sp, dl}:
          Bool.and(Bool.or(Bool.not(T.running(st)), ac_bud.vfit(sp, lim)), ac_bud.hv(rest))

def ac_bud.lle1_refl(x: A.Load) -> {ac_bud.lle1(x, x) == True{} : Bool}:
  match x:
    case A.Load{+p, +n}:
      AR.at_reach.and_t(CS.path_is(p, p), Nat.is_le(n, n), V.ac_view.path_refl(p), AR.at_reach.le_refl(n))

def ac_bud.lle_refl(ls: List<&2, A.Load>) -> {ac_bud.lle(ls, ls) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      AR.at_reach.and_t(ac_bud.lle1(x, x), ac_bud.lle(rest, rest), ac_bud.lle1_refl(x), ac_bud.lle_refl(rest))

def ac_bud.loads_app(hs: List<&2, A.Help>, +x: A.Help) -> {A.loads(List.append(&2, A.Help, hs, [x])) == List.append(&2, A.Load, A.loads(hs), [A.load_of(x)]) : List<&2, A.Load>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, rest}:
      Equal.cong(List<&2, A.Load>, List<&2, A.Load>, z => A.load_of(h) <> z, A.loads(List.append(&2, A.Help, rest, [x])), List.append(&2, A.Load, A.loads(rest), [A.load_of(x)]), ac_bud.loads_app(rest, x))

def ac_bud.hv_app(hs: List<&2, A.Help>, +x: A.Help, +h1: {ac_bud.hv(hs) == True{} : Bool}, +h2: {ac_bud.hv([x]) == True{} : Bool}) -> {ac_bud.hv(List.append(&2, A.Help, hs, [x])) == True{} : Bool}:
  match hs:
    case Nil{}:
      h2
    case Con{h, +rest}:
      match h:
        case A.Help{p, +st, +lim, +sp, dl}:
          AR.at_reach.and_t(Bool.or(Bool.not(T.running(st)), ac_bud.vfit(sp, lim)), ac_bud.hv(List.append(&2, A.Help, rest, [x])), AR.at_reach.and_l(Bool.or(Bool.not(T.running(st)), ac_bud.vfit(sp, lim)), ac_bud.hv(rest), h1), ac_bud.hv_app(rest, x, AR.at_reach.and_r(Bool.or(Bool.not(T.running(st)), ac_bud.vfit(sp, lim)), ac_bud.hv(rest), h1), h2))

def ac_bud.vfit_grant(f: T.Lim, +a: Nat, h: {ac_bud.lv(f) == True{} : Bool}) -> {ac_bud.vfit(0n, A.grant(f, a)) == True{} : Bool}:
  match f:
    case T.Unlimited{}:
      AR.at_reach.absurd({ac_bud.vfit(0n, A.grant(T.Unlimited{}, a)) == True{} : Bool}, h)
    case T.Value{m}:
      AR.at_reach.le0(a)

def ac_bud.all_nil_snoc(ls: List<&2, A.Load>, -a: Nat, h: {ac_bud.all_nil(ls) == True{} : Bool}) -> {ac_bud.all_nil(List.append(&2, A.Load, ls, [A.Load{[], a}])) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{y, rest}:
      match y:
        case A.Load{p, n}:
          match p:
            case Nil{}:
              ac_bud.all_nil_snoc(rest, a, h)
            case Con{d, q}:
              AR.at_reach.absurd({ac_bud.all_nil(List.append(&2, A.Load, A.Load{d <> q, n} <> rest, [A.Load{[], a}])) == True{} : Bool}, h)

# a charge appended at a node of t keeps the loads placed
def ac_bud.placed_snoc(+t: T.Node, +ls: List<&2, A.Load>, p: List<&2, T.Dir>, +a: Nat, +hp: {ac_bud.placed(t, ls) == True{} : Bool}, +hx: {Maybe.is_some(&2, T.Node, A.node_at(p, t)) == True{} : Bool}) -> {ac_bud.placed(t, List.append(&2, A.Load, ls, [A.Load{p, a}])) == True{} : Bool}:
  match t:
    case T.Leaf{i}:
      match p:
        case Nil{}:
          ac_bud.all_nil_snoc(ls, a, hp)
        case Con{d, q}:
          match d:
            case T.GoL{}:
              AR.at_reach.absurd({ac_bud.placed(T.Leaf{i}, List.append(&2, A.Load, ls, [A.Load{T.GoL{} <> q, a}])) == True{} : Bool}, hx)
            case T.GoR{}:
              AR.at_reach.absurd({ac_bud.placed(T.Leaf{i}, List.append(&2, A.Load, ls, [A.Load{T.GoR{} <> q, a}])) == True{} : Bool}, hx)
    case T.Split{i, own, +l, +r}:
      match p:
        case Nil{}:
          +pl = AR.at_reach.and_l(ac_bud.placed(l, A.down(ls, T.GoL{})), ac_bud.placed(r, A.down(ls, T.GoR{})), hp)
          +pr = AR.at_reach.and_r(ac_bud.placed(l, A.down(ls, T.GoL{})), ac_bud.placed(r, A.down(ls, T.GoR{})), hp)
          AR.at_reach.and_t(ac_bud.placed(l, A.down(List.append(&2, A.Load, ls, [A.Load{[], a}]), T.GoL{})), ac_bud.placed(r, A.down(List.append(&2, A.Load, ls, [A.Load{[], a}]), T.GoR{})), AR.at_reach.tr(List<&2, A.Load>, A.down(ls, T.GoL{}), A.down(List.append(&2, A.Load, ls, [A.Load{[], a}]), T.GoL{}), z => {ac_bud.placed(l, z) == True{} : Bool}, Equal.sym(List<&2, A.Load>, A.down(List.append(&2, A.Load, ls, [A.Load{[], a}]), T.GoL{}), A.down(ls, T.GoL{}), ac_bud.kid_none(ls, T.GoL{}, A.Load{[], a}, {==})), pl), AR.at_reach.tr(List<&2, A.Load>, A.down(ls, T.GoR{}), A.down(List.append(&2, A.Load, ls, [A.Load{[], a}]), T.GoR{}), z => {ac_bud.placed(r, z) == True{} : Bool}, Equal.sym(List<&2, A.Load>, A.down(List.append(&2, A.Load, ls, [A.Load{[], a}]), T.GoR{}), A.down(ls, T.GoR{}), ac_bud.kid_none(ls, T.GoR{}, A.Load{[], a}, {==})), pr))
        case Con{d, +q}:
          match d:
            case T.GoL{}:
              +pl = AR.at_reach.and_l(ac_bud.placed(l, A.down(ls, T.GoL{})), ac_bud.placed(r, A.down(ls, T.GoR{})), hp)
              +pr = AR.at_reach.and_r(ac_bud.placed(l, A.down(ls, T.GoL{})), ac_bud.placed(r, A.down(ls, T.GoR{})), hp)
              AR.at_reach.and_t(ac_bud.placed(l, A.down(List.append(&2, A.Load, ls, [A.Load{T.GoL{} <> q, a}]), T.GoL{})), ac_bud.placed(r, A.down(List.append(&2, A.Load, ls, [A.Load{T.GoL{} <> q, a}]), T.GoR{})), AR.at_reach.tr(List<&2, A.Load>, List.append(&2, A.Load, A.down(ls, T.GoL{}), [A.Load{q, a}]), A.down(List.append(&2, A.Load, ls, [A.Load{T.GoL{} <> q, a}]), T.GoL{}), z => {ac_bud.placed(l, z) == True{} : Bool}, Equal.sym(List<&2, A.Load>, A.down(List.append(&2, A.Load, ls, [A.Load{T.GoL{} <> q, a}]), T.GoL{}), List.append(&2, A.Load, A.down(ls, T.GoL{}), [A.Load{q, a}]), ac_bud.down_snoc(ls, T.GoL{}, A.Load{T.GoL{} <> q, a})), ac_bud.placed_snoc(l, A.down(ls, T.GoL{}), q, a, pl, hx)), AR.at_reach.tr(List<&2, A.Load>, A.down(ls, T.GoR{}), A.down(List.append(&2, A.Load, ls, [A.Load{T.GoL{} <> q, a}]), T.GoR{}), z => {ac_bud.placed(r, z) == True{} : Bool}, Equal.sym(List<&2, A.Load>, A.down(List.append(&2, A.Load, ls, [A.Load{T.GoL{} <> q, a}]), T.GoR{}), A.down(ls, T.GoR{}), ac_bud.kid_none(ls, T.GoR{}, A.Load{T.GoL{} <> q, a}, {==})), pr))
            case T.GoR{}:
              +pl = AR.at_reach.and_l(ac_bud.placed(l, A.down(ls, T.GoL{})), ac_bud.placed(r, A.down(ls, T.GoR{})), hp)
              +pr = AR.at_reach.and_r(ac_bud.placed(l, A.down(ls, T.GoL{})), ac_bud.placed(r, A.down(ls, T.GoR{})), hp)
              AR.at_reach.and_t(ac_bud.placed(l, A.down(List.append(&2, A.Load, ls, [A.Load{T.GoR{} <> q, a}]), T.GoL{})), ac_bud.placed(r, A.down(List.append(&2, A.Load, ls, [A.Load{T.GoR{} <> q, a}]), T.GoR{})), AR.at_reach.tr(List<&2, A.Load>, A.down(ls, T.GoL{}), A.down(List.append(&2, A.Load, ls, [A.Load{T.GoR{} <> q, a}]), T.GoL{}), z => {ac_bud.placed(l, z) == True{} : Bool}, Equal.sym(List<&2, A.Load>, A.down(List.append(&2, A.Load, ls, [A.Load{T.GoR{} <> q, a}]), T.GoL{}), A.down(ls, T.GoL{}), ac_bud.kid_none(ls, T.GoL{}, A.Load{T.GoR{} <> q, a}, {==})), pl), AR.at_reach.tr(List<&2, A.Load>, List.append(&2, A.Load, A.down(ls, T.GoR{}), [A.Load{q, a}]), A.down(List.append(&2, A.Load, ls, [A.Load{T.GoR{} <> q, a}]), T.GoR{}), z => {ac_bud.placed(r, z) == True{} : Bool}, Equal.sym(List<&2, A.Load>, A.down(List.append(&2, A.Load, ls, [A.Load{T.GoR{} <> q, a}]), T.GoR{}), List.append(&2, A.Load, A.down(ls, T.GoR{}), [A.Load{q, a}]), ac_bud.down_snoc(ls, T.GoR{}, A.Load{T.GoR{} <> q, a})), ac_bud.placed_snoc(r, A.down(ls, T.GoR{}), q, a, pr, hx)))

def ac_bud.some_shift(m: Maybe<&2, T.Node>, -ls: List<&2, A.Load>, -up: Bool, -n: T.Node, e: {V.ac_view.shift_m(m, ls, up) == Some{n} : Maybe<&2, T.Node>}) -> {Maybe.is_some(&2, T.Node, m) == True{} : Bool}:
  match m:
    case None{}:
      E.at_edit.absurd_none({Maybe.is_some(&2, T.Node, None{}) == True{} : Bool}, n, e)
    case Some{x}:
      {==}

# The invariant
# -------------

# a crown reachable from a root with the limit Value m: its view is Good
# with the root's scope and limit, its loads are placed, its help leaves fit
def ac_bud.CB(c: A.Crown, +b: T.Bounds, +s: List<&2, Bool>, +m: Nat) -> Data:
  match c:
    case A.Crown{+t, +hs}:
      AR.at_reach.And(AR.at_reach.Inv(A.view(t, hs), b, s, T.Value{m}), AR.at_reach.And({ac_bud.placed(t, A.loads(hs)) == True{} : Bool}, {ac_bud.hv(hs) == True{} : Bool}))

def ac_bud.inv_cb(+v: T.Node, +b: T.Bounds, +hs: List<&2, A.Help>, -s: List<&2, Bool>, -lim: T.Lim, +iv: AR.at_reach.Inv(v, b, s, lim)) -> AR.at_reach.Inv(v, A.cbounds(b, hs), s, lim):
  (g, rest) = iv
  (AR.at_reach.tr(Nat, T.bound_depth(b), T.bound_depth(A.cbounds(b, hs)), z => AR.at_reach.Good(v, z), Equal.sym(Nat, T.bound_depth(A.cbounds(b, hs)), T.bound_depth(b), R.ac_reach.depth_cb(b, hs)), g), rest)

def ac_bud.inv_uncb(+v: T.Node, +b: T.Bounds, +hs: List<&2, A.Help>, -s: List<&2, Bool>, -lim: T.Lim, +iv: AR.at_reach.Inv(v, A.cbounds(b, hs), s, lim)) -> AR.at_reach.Inv(v, b, s, lim):
  (g, rest) = iv
  (AR.at_reach.tr(Nat, T.bound_depth(A.cbounds(b, hs)), T.bound_depth(b), z => AR.at_reach.Good(v, z), R.ac_reach.depth_cb(b, hs), g), rest)

# Tree events
# -----------

def ac_bud.one_lle(f: Bool, st: T.Status, lim: T.Lim, +sp: Nat, h1: {Bool.or(Bool.not(T.running(st)), ac_bud.vfit(sp, lim)) == True{} : Bool}) -> {Nat.is_le(A.charge_if(T.running(A.sweep_st(f, st)), lim, sp), A.charge_if(T.running(st), lim, sp)) == True{} : Bool}:
  match f:
    case True{}:
      match st:
        case T.Running{}:
          match lim:
            case T.Unlimited{}:
              AR.at_reach.absurd({Nat.is_le(sp, 0n) == True{} : Bool}, h1)
            case T.Value{x}:
              h1
        case T.Finished{}:
          AR.at_reach.le_refl(sp)
        case T.Failed{}:
          AR.at_reach.le_refl(sp)
        case T.Cancelled{}:
          AR.at_reach.le_refl(sp)
    case False{}:
      AR.at_reach.le_refl(A.charge_if(T.running(st), lim, sp))

def ac_bud.one_hv(f: Bool, st: T.Status, -lim: T.Lim, -sp: Nat, h1: {Bool.or(Bool.not(T.running(st)), ac_bud.vfit(sp, lim)) == True{} : Bool}) -> {Bool.or(Bool.not(T.running(A.sweep_st(f, st))), ac_bud.vfit(sp, lim)) == True{} : Bool}:
  match f:
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
      h1

# the sweep only lowers charges
def ac_bud.sweep_lle(hs: List<&2, A.Help>, +y: T.Node, +e: T.Ev, +hh: {ac_bud.hv(hs) == True{} : Bool}) -> {ac_bud.lle(A.loads(A.sweep(hs, y, e)), A.loads(hs)) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, +rest}:
      match h:
        case A.Help{+p, +st, +lim, +sp, +dl}:
          +f = Bool.or(Bool.not(A.runs(A.node_at(p, y))), A.help_late(dl, e))
          AR.at_reach.and_t(Bool.and(CS.path_is(p, p), Nat.is_le(A.charge_if(T.running(A.sweep_st(f, st)), lim, sp), A.charge_if(T.running(st), lim, sp))), ac_bud.lle(A.loads(A.sweep(rest, y, e)), A.loads(rest)), AR.at_reach.and_t(CS.path_is(p, p), Nat.is_le(A.charge_if(T.running(A.sweep_st(f, st)), lim, sp), A.charge_if(T.running(st), lim, sp)), V.ac_view.path_refl(p), ac_bud.one_lle(f, st, lim, sp, AR.at_reach.and_l(Bool.or(Bool.not(T.running(st)), ac_bud.vfit(sp, lim)), ac_bud.hv(rest), hh))), ac_bud.sweep_lle(rest, y, e, AR.at_reach.and_r(Bool.or(Bool.not(T.running(st)), ac_bud.vfit(sp, lim)), ac_bud.hv(rest), hh)))

def ac_bud.sweep_hv(hs: List<&2, A.Help>, +y: T.Node, +e: T.Ev, +hh: {ac_bud.hv(hs) == True{} : Bool}) -> {ac_bud.hv(A.sweep(hs, y, e)) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, +rest}:
      match h:
        case A.Help{+p, +st, +lim, +sp, +dl}:
          +f = Bool.or(Bool.not(A.runs(A.node_at(p, y))), A.help_late(dl, e))
          AR.at_reach.and_t(Bool.or(Bool.not(T.running(A.sweep_st(f, st))), ac_bud.vfit(sp, lim)), ac_bud.hv(A.sweep(rest, y, e)), ac_bud.one_hv(f, st, lim, sp, AR.at_reach.and_l(Bool.or(Bool.not(T.running(st)), ac_bud.vfit(sp, lim)), ac_bud.hv(rest), hh)), ac_bud.sweep_hv(rest, y, e, AR.at_reach.and_r(Bool.or(Bool.not(T.running(st)), ac_bud.vfit(sp, lim)), ac_bud.hv(rest), hh)))

def ac_bud.on_took(+x: T.Node, +t: T.Node, +hs: List<&2, A.Help>, +b: T.Bounds, +s0: List<&2, Bool>, +m: Nat, +e: T.Ev, +hh: {ac_bud.hv(hs) == True{} : Bool}, +gro: {Gw.ac_grow.gr(A.view(t, hs), x) == True{} : Bool}, +pv: {ac_bud.placed(A.view(t, hs), A.loads(hs)) == True{} : Bool}, +ivy: AR.at_reach.Inv(A.shift(A.shift(x, A.loads(hs), False{}), A.loads(hs), True{}), b, s0, T.Value{m})) -> ac_bud.CB(A.Crown{A.shift(x, A.loads(hs), False{}), A.sweep(hs, A.shift(x, A.loads(hs), False{}), e)}, b, s0, m):
  (gy, ivy1) = ivy
  (scy, liy) = ivy1
  +y = A.shift(x, A.loads(hs), False{})
  +hl = ac_bud.sweep_lle(hs, y, e, hh)
  +g2 = ac_bud.good_lle(y, A.loads(A.sweep(hs, y, e)), A.loads(hs), T.bound_depth(b), hl, gy)
  +sc2 = Equal.trans(List<&2, Bool>, T.scope_of(T.info(A.shift(y, A.loads(A.sweep(hs, y, e)), True{}))), T.scope_of(T.info(A.shift(y, A.loads(hs), True{}))), s0, Equal.sym(List<&2, Bool>, T.scope_of(T.info(A.shift(y, A.loads(hs), True{}))), T.scope_of(T.info(A.shift(y, A.loads(A.sweep(hs, y, e)), True{}))), ac_bud.sc_same(y, A.loads(A.sweep(hs, y, e)), A.loads(hs), True{})), scy)
  +li2 = Equal.trans(T.Lim, T.limit_of(T.info(A.shift(y, A.loads(A.sweep(hs, y, e)), True{}))), T.limit_of(T.info(A.shift(y, A.loads(hs), True{}))), T.Value{m}, Equal.sym(T.Lim, T.limit_of(T.info(A.shift(y, A.loads(hs), True{}))), T.limit_of(T.info(A.shift(y, A.loads(A.sweep(hs, y, e)), True{}))), ac_bud.lim_same(y, A.loads(A.sweep(hs, y, e)), A.loads(hs), True{})), liy)
  +py = Equal.trans(Bool, ac_bud.placed(y, A.loads(A.sweep(hs, y, e))), ac_bud.placed(y, A.loads(hs)), True{}, ac_bud.placed_lle(y, A.loads(A.sweep(hs, y, e)), A.loads(hs), hl), Equal.trans(Bool, ac_bud.placed(A.shift(x, A.loads(hs), False{}), A.loads(hs)), ac_bud.placed(x, A.loads(hs)), True{}, ac_bud.placed_shift(x, A.loads(hs), A.loads(hs), False{}), ac_bud.placed_gr(A.view(t, hs), x, A.loads(hs), gro, pv)))
  ((g2, (sc2, li2)), (py, ac_bud.sweep_hv(hs, y, e, hh)))

def ac_bud.on_cb(+s: T.Step, +t: T.Node, +hs: List<&2, A.Help>, +b: T.Bounds, +s0: List<&2, Bool>, +m: Nat, +e: T.Ev, +cb: ac_bud.CB(A.Crown{t, hs}, b, s0, m), +gro: Gw.ac_grow.Gr(s, A.view(t, hs)), +ivx: AR.at_reach.Inv(T.after(s, A.view(t, hs)), b, s0, T.Value{m})) -> ac_bud.CB(A.cafter(A.on_tree(s, hs, e), A.Crown{t, hs}), b, s0, m):
  match s:
    case T.Took{x}:
      (iv, cb1) = cb
      (hp, hh) = cb1
      +pv = AR.at_reach.tr(Bool, ac_bud.placed(t, A.loads(hs)), ac_bud.placed(A.view(t, hs), A.loads(hs)), z => {z == True{} : Bool}, Equal.sym(Bool, ac_bud.placed(A.shift(t, A.loads(hs), True{}), A.loads(hs)), ac_bud.placed(t, A.loads(hs)), ac_bud.placed_shift(t, A.loads(hs), A.loads(hs), True{})), hp)
      +cx = ac_bud.cov_gr(A.view(t, hs), x, A.loads(hs), gro, ac_bud.cov_shift(t, A.loads(hs)), pv)
      ac_bud.on_took(x, t, hs, b, s0, m, e, hh, gro, pv, AR.at_reach.tr(T.Node, x, A.shift(A.shift(x, A.loads(hs), False{}), A.loads(hs), True{}), z => AR.at_reach.Inv(z, b, s0, T.Value{m}), Equal.sym(T.Node, A.shift(A.shift(x, A.loads(hs), False{}), A.loads(hs), True{}), x, ac_bud.roundtrip(x, A.loads(hs), cx)), ivx))
    case T.Refused{why}:
      cb

# Help
# ----

def ac_bud.fit_cb(ok: Bool, +n: T.Node, +t: T.Node, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>, +a: Nat, +margin: Nat, +b: T.Bounds, +s0: List<&2, Bool>, +m: Nat, +cb: ac_bud.CB(A.Crown{t, hs}, b, s0, m), +em: {A.node_at(p, A.view(t, hs)) == Some{n} : Maybe<&2, T.Node>}, +er: {T.running(T.st_of(T.info(n))) == True{} : Bool}, +eok: {T.lim_fits(a, T.free(n)) == ok : Bool}) -> ac_bud.CB(A.cafter(A.help_fit(ok, n, t, hs, p, a, margin), A.Crown{t, hs}), b, s0, m):
  match ok:
    case True{}:
      (iv, cb1) = cb
      (g, iv1) = iv
      (sc, li) = iv1
      (hp, hh) = cb1
      +h = {A.Help{p, T.Running{}, A.grant(T.free(n), a), 0n, T.lim_less(T.deadline_of(T.info(n)), margin)} : A.Help}
      +en = Equal.trans(Maybe<&2, T.Node>, S.node_at(p, A.view(t, hs)), A.node_at(p, A.view(t, hs)), Some{n}, Equal.sym(Maybe<&2, T.Node>, A.node_at(p, A.view(t, hs)), S.node_at(p, A.view(t, hs)), V.ac_view.node_at_eq(p, A.view(t, hs))), em)
      +lvv = AR.at_reach.tr(T.Lim, T.Value{m}, T.limit_of(T.info(A.view(t, hs))), z => {ac_bud.lv(z) == True{} : Bool}, Equal.sym(T.Lim, T.limit_of(T.info(A.view(t, hs))), T.Value{m}, li), {==})
      +lvf = ac_bud.free_value(n, ac_bud.run_value(p, A.view(t, hs), T.bound_depth(b), g, n, en, er, lvv))
      +el = Equal.trans(List<&2, A.Load>, A.loads(List.append(&2, A.Help, hs, [h])), List.append(&2, A.Load, A.loads(hs), [A.load_of(h)]), List.append(&2, A.Load, A.loads(hs), [A.Load{p, a}]), ac_bud.loads_app(hs, h), Equal.cong(Nat, List<&2, A.Load>, z => List.append(&2, A.Load, A.loads(hs), [A.Load{p, z}]), A.lim_n(A.grant(T.free(n), a)), a, ac_bud.grant_n(T.free(n), a, lvf)))
      +x2 = S.put(p, A.view(t, hs), T.add_spent(n, a))
      +ev = Equal.trans(T.Node, A.shift(t, A.loads(List.append(&2, A.Help, hs, [h])), True{}), A.shift(t, List.append(&2, A.Load, A.loads(hs), [A.Load{p, a}]), True{}), x2, Equal.cong(List<&2, A.Load>, T.Node, z => A.shift(t, z, True{}), A.loads(List.append(&2, A.Help, hs, [h])), List.append(&2, A.Load, A.loads(hs), [A.Load{p, a}]), el), Equal.trans(T.Node, A.shift(t, List.append(&2, A.Load, A.loads(hs), [A.Load{p, a}]), True{}), CS.bump(p, A.view(t, hs), a), x2, ac_bud.shift_snoc(p, t, A.loads(hs), a), ac_bud.bump_put(p, A.view(t, hs), n, a, en)))
      +post = AR.at_reach.tr(T.Step, T.edit(p, A.view(t, hs), T.OpSpend{a}, T.bound_depth(b)), T.Took{x2}, z => AR.at_reach.Post(z, A.view(t, hs), T.bound_depth(b), 0n), ac_bud.edit_spend(p, A.view(t, hs), n, a, T.bound_depth(b), en, er, eok), AR.at_reach.edit_post(p, A.view(t, hs), T.OpSpend{a}, T.bound_depth(b), g))
      +iv2 = AR.at_reach.after_inv(T.Took{x2}, A.view(t, hs), b, s0, T.Value{m}, 0n, (g, (sc, li)), post)
      +iv3 = AR.at_reach.tr(T.Node, x2, A.view(t, List.append(&2, A.Help, hs, [h])), z => AR.at_reach.Inv(z, b, s0, T.Value{m}), Equal.sym(T.Node, A.shift(t, A.loads(List.append(&2, A.Help, hs, [h])), True{}), x2, ev), iv2)
      +hx = ac_bud.some_shift(A.node_at(p, t), V.ac_view.downs(p, A.loads(hs)), True{}, n, Equal.trans(Maybe<&2, T.Node>, V.ac_view.shift_m(A.node_at(p, t), V.ac_view.downs(p, A.loads(hs)), True{}), A.node_at(p, A.view(t, hs)), Some{n}, Equal.sym(Maybe<&2, T.Node>, A.node_at(p, A.shift(t, A.loads(hs), True{})), V.ac_view.shift_m(A.node_at(p, t), V.ac_view.downs(p, A.loads(hs)), True{}), V.ac_view.node_shift(p, t, A.loads(hs), True{})), em))
      +pl2 = AR.at_reach.tr(List<&2, A.Load>, List.append(&2, A.Load, A.loads(hs), [A.Load{p, a}]), A.loads(List.append(&2, A.Help, hs, [h])), z => {ac_bud.placed(t, z) == True{} : Bool}, Equal.sym(List<&2, A.Load>, A.loads(List.append(&2, A.Help, hs, [h])), List.append(&2, A.Load, A.loads(hs), [A.Load{p, a}]), el), ac_bud.placed_snoc(t, A.loads(hs), p, a, hp, hx))
      +hv2 = ac_bud.hv_app(hs, h, hh, AR.at_reach.and_t(ac_bud.vfit(0n, A.grant(T.free(n), a)), True{}, ac_bud.vfit_grant(T.free(n), a, lvf), {==}))
      (iv3, (pl2, hv2))
    case False{}:
      cb

def ac_bud.room_cb(room: Bool, +n: T.Node, +t: T.Node, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>, +a: Nat, +margin: Nat, +b: T.Bounds, +s0: List<&2, Bool>, +m: Nat, +cb: ac_bud.CB(A.Crown{t, hs}, b, s0, m), +em: {A.node_at(p, A.view(t, hs)) == Some{n} : Maybe<&2, T.Node>}, +er: {T.running(T.st_of(T.info(n))) == True{} : Bool}) -> ac_bud.CB(A.cafter(A.help_room(room, n, t, hs, p, a, margin), A.Crown{t, hs}), b, s0, m):
  match room:
    case True{}:
      ac_bud.fit_cb(T.lim_fits(a, T.free(n)), n, t, hs, p, a, margin, b, s0, m, cb, em, er, {==})
    case False{}:
      cb

def ac_bud.run_cb(run: Bool, +n: T.Node, +t: T.Node, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>, +a: Nat, +room: Bool, +margin: Nat, +b: T.Bounds, +s0: List<&2, Bool>, +m: Nat, +cb: ac_bud.CB(A.Crown{t, hs}, b, s0, m), +em: {A.node_at(p, A.view(t, hs)) == Some{n} : Maybe<&2, T.Node>}, er: {T.running(T.st_of(T.info(n))) == run : Bool}) -> ac_bud.CB(A.cafter(A.help_run(run, n, t, hs, p, a, room, margin), A.Crown{t, hs}), b, s0, m):
  match run:
    case True{}:
      ac_bud.room_cb(room, n, t, hs, p, a, margin, b, s0, m, cb, em, er)
    case False{}:
      cb

def ac_bud.help_cb(+mm: Maybe<&2, T.Node>, +t: T.Node, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>, +a: Nat, +room: Bool, +margin: Nat, +b: T.Bounds, +s0: List<&2, Bool>, +m: Nat, +cb: ac_bud.CB(A.Crown{t, hs}, b, s0, m), em: {A.node_at(p, A.view(t, hs)) == mm : Maybe<&2, T.Node>}) -> ac_bud.CB(A.cafter(A.help_node(mm, t, hs, p, a, room, margin), A.Crown{t, hs}), b, s0, m):
  match mm:
    case None{}:
      cb
    case Some{+n}:
      ac_bud.run_cb(T.running(T.st_of(T.info(n))), n, t, hs, p, a, room, margin, b, s0, m, cb, em, {==})

# Help leaf spend and end
# -----------------------

# a spend keeps the loads; the help leaves still fit
def ac_bud.HB(r: A.HRes, +hs: List<&2, A.Help>) -> Data:
  match r:
    case A.HOk{xs}:
      AR.at_reach.And({A.loads(xs) == A.loads(hs) : List<&2, A.Load>}, {ac_bud.hv(xs) == True{} : Bool})
    case A.HNo{why}:
      Unit

def ac_bud.vfit_add(lim: T.Lim, +sp: Nat, +a: Nat, h1: {ac_bud.vfit(sp, lim) == True{} : Bool}, h2: {T.lim_fits(a, T.lim_less(lim, sp)) == True{} : Bool}) -> {ac_bud.vfit(Nat.add(sp, a), lim) == True{} : Bool}:
  match lim:
    case T.Unlimited{}:
      AR.at_reach.absurd({ac_bud.vfit(Nat.add(sp, a), T.Unlimited{}) == True{} : Bool}, h1)
    case T.Value{x}:
      AR.at_reach.fit_sub(sp, a, x, h1, h2)

def ac_bud.sfit_hb(ok: Bool, +p: List<&2, T.Dir>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +a: Nat, +rest: List<&2, A.Help>, +h1: {ac_bud.vfit(sp, lim) == True{} : Bool}, +hr: {ac_bud.hv(rest) == True{} : Bool}, +eok: {T.lim_fits(a, T.lim_less(lim, sp)) == ok : Bool}) -> ac_bud.HB(A.spend_fit(ok, A.Help{p, T.Running{}, lim, sp, dl}, a, rest), A.Help{p, T.Running{}, lim, sp, dl} <> rest):
  match ok:
    case True{}:
      ({==}, AR.at_reach.and_t(ac_bud.vfit(Nat.add(sp, a), lim), ac_bud.hv(rest), ac_bud.vfit_add(lim, sp, a, h1, eok), hr))
    case False{}:
      Unit{}

def ac_bud.cons_hb(+h: A.Help, +r: A.HRes, +rest: List<&2, A.Help>, +hh: {ac_bud.hv(h <> rest) == True{} : Bool}, +ih: ac_bud.HB(r, rest)) -> ac_bud.HB(A.hres_cons(h, r), h <> rest):
  match h:
    case A.Help{+p, +st, +lim, +sp, +dl}:
      match r:
        case A.HOk{xs}:
          (el, hvx) = ih
          (Equal.cong(List<&2, A.Load>, List<&2, A.Load>, z => A.Load{p, A.charge_if(T.running(st), lim, sp)} <> z, A.loads(xs), A.loads(rest), el), AR.at_reach.and_t(Bool.or(Bool.not(T.running(st)), ac_bud.vfit(sp, lim)), ac_bud.hv(xs), AR.at_reach.and_l(Bool.or(Bool.not(T.running(st)), ac_bud.vfit(sp, lim)), ac_bud.hv(rest), hh), hvx))
        case A.HNo{why}:
          Unit{}

def ac_bud.tail_hv(+h: A.Help, +rest: List<&2, A.Help>, +hh: {ac_bud.hv(h <> rest) == True{} : Bool}) -> {ac_bud.hv(rest) == True{} : Bool}:
  match h:
    case A.Help{p, +st, +lim, +sp, dl}:
      AR.at_reach.and_r(Bool.or(Bool.not(T.running(st)), ac_bud.vfit(sp, lim)), ac_bud.hv(rest), hh)

def ac_bud.spend_hb(k: Nat, hs: List<&2, A.Help>, +a: Nat, +hh: {ac_bud.hv(hs) == True{} : Bool}) -> ac_bud.HB(A.spend_k(k, hs, a), hs):
  match k:
    case 0n:
      match hs:
        case Nil{}:
          Unit{}
        case Con{h, +rest}:
          match h:
            case A.Help{+p, st, +lim, +sp, +dl}:
              match st:
                case T.Running{}:
                  ac_bud.sfit_hb(T.lim_fits(a, T.lim_less(lim, sp)), p, lim, sp, dl, a, rest, AR.at_reach.and_l(ac_bud.vfit(sp, lim), ac_bud.hv(rest), hh), AR.at_reach.and_r(ac_bud.vfit(sp, lim), ac_bud.hv(rest), hh), {==})
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
          ac_bud.cons_hb(h, A.spend_k(j, rest, a), rest, hh, ac_bud.spend_hb(j, rest, a, ac_bud.tail_hv(h, rest, hh)))

def ac_bud.hres_cb(+r: A.HRes, +t: T.Node, +hs: List<&2, A.Help>, +b: T.Bounds, +s0: List<&2, Bool>, +m: Nat, +cb: ac_bud.CB(A.Crown{t, hs}, b, s0, m), +hb: ac_bud.HB(r, hs)) -> ac_bud.CB(A.cafter(A.hres_crown(r, t), A.Crown{t, hs}), b, s0, m):
  match r:
    case A.HOk{xs}:
      (iv, cb1) = cb
      (hp, hh) = cb1
      (el, hvx) = hb
      (AR.at_reach.tr(List<&2, A.Load>, A.loads(hs), A.loads(xs), z => AR.at_reach.Inv(A.shift(t, z, True{}), b, s0, T.Value{m}), Equal.sym(List<&2, A.Load>, A.loads(xs), A.loads(hs), el), iv), (AR.at_reach.tr(List<&2, A.Load>, A.loads(hs), A.loads(xs), z => {ac_bud.placed(t, z) == True{} : Bool}, Equal.sym(List<&2, A.Load>, A.loads(xs), A.loads(hs), el), hp), hvx))
    case A.HNo{why}:
      cb

# an end lowers the loads; the help leaves still fit
def ac_bud.HE(r: A.HRes, +hs: List<&2, A.Help>) -> Data:
  match r:
    case A.HOk{xs}:
      AR.at_reach.And({ac_bud.lle(A.loads(xs), A.loads(hs)) == True{} : Bool}, {ac_bud.hv(xs) == True{} : Bool})
    case A.HNo{why}:
      Unit

def ac_bud.end_ch(ok: Bool, lim: T.Lim, +sp: Nat, h1: {ac_bud.vfit(sp, lim) == True{} : Bool}) -> {Nat.is_le(A.charge_if(T.running(A.end_st(ok)), lim, sp), A.lim_n(lim)) == True{} : Bool}:
  match ok:
    case True{}:
      match lim:
        case T.Unlimited{}:
          AR.at_reach.absurd({Nat.is_le(sp, 0n) == True{} : Bool}, h1)
        case T.Value{x}:
          h1
    case False{}:
      match lim:
        case T.Unlimited{}:
          AR.at_reach.absurd({Nat.is_le(sp, 0n) == True{} : Bool}, h1)
        case T.Value{x}:
          h1

def ac_bud.cons_he(+h: A.Help, +r: A.HRes, +rest: List<&2, A.Help>, +hh: {ac_bud.hv(h <> rest) == True{} : Bool}, +ih: ac_bud.HE(r, rest)) -> ac_bud.HE(A.hres_cons(h, r), h <> rest):
  match h:
    case A.Help{+p, +st, +lim, +sp, +dl}:
      match r:
        case A.HOk{xs}:
          (hl, hvx) = ih
          (AR.at_reach.and_t(ac_bud.lle1(A.Load{p, A.charge_if(T.running(st), lim, sp)}, A.Load{p, A.charge_if(T.running(st), lim, sp)}), ac_bud.lle(A.loads(xs), A.loads(rest)), ac_bud.lle1_refl(A.Load{p, A.charge_if(T.running(st), lim, sp)}), hl), AR.at_reach.and_t(Bool.or(Bool.not(T.running(st)), ac_bud.vfit(sp, lim)), ac_bud.hv(xs), AR.at_reach.and_l(Bool.or(Bool.not(T.running(st)), ac_bud.vfit(sp, lim)), ac_bud.hv(rest), hh), hvx))
        case A.HNo{why}:
          Unit{}

def ac_bud.end_he(k: Nat, hs: List<&2, A.Help>, +ok: Bool, +hh: {ac_bud.hv(hs) == True{} : Bool}) -> ac_bud.HE(A.end_k(k, hs, ok), hs):
  match k:
    case 0n:
      match hs:
        case Nil{}:
          Unit{}
        case Con{h, +rest}:
          match h:
            case A.Help{+p, st, +lim, +sp, +dl}:
              match st:
                case T.Running{}:
                  +h1 = AR.at_reach.and_l(ac_bud.vfit(sp, lim), ac_bud.hv(rest), hh)
                  +hr = AR.at_reach.and_r(ac_bud.vfit(sp, lim), ac_bud.hv(rest), hh)
                  (AR.at_reach.and_t(Bool.and(CS.path_is(p, p), Nat.is_le(A.charge_if(T.running(A.end_st(ok)), lim, sp), A.lim_n(lim))), ac_bud.lle(A.loads(rest), A.loads(rest)), AR.at_reach.and_t(CS.path_is(p, p), Nat.is_le(A.charge_if(T.running(A.end_st(ok)), lim, sp), A.lim_n(lim)), V.ac_view.path_refl(p), ac_bud.end_ch(ok, lim, sp, h1)), ac_bud.lle_refl(A.loads(rest))), AR.at_reach.and_t(Bool.or(Bool.not(T.running(A.end_st(ok))), ac_bud.vfit(sp, lim)), ac_bud.hv(rest), R.ac_reach.or_end(ok, ac_bud.vfit(sp, lim)), hr))
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
          ac_bud.cons_he(h, A.end_k(j, rest, ok), rest, hh, ac_bud.end_he(j, rest, ok, ac_bud.tail_hv(h, rest, hh)))

def ac_bud.hres_cb_end(+r: A.HRes, +t: T.Node, +hs: List<&2, A.Help>, +b: T.Bounds, +s0: List<&2, Bool>, +m: Nat, +cb: ac_bud.CB(A.Crown{t, hs}, b, s0, m), +he: ac_bud.HE(r, hs)) -> ac_bud.CB(A.cafter(A.hres_crown(r, t), A.Crown{t, hs}), b, s0, m):
  match r:
    case A.HOk{xs}:
      (iv, cb1) = cb
      (g, iv1) = iv
      (sc, li) = iv1
      (hp, hh) = cb1
      (hl, hvx) = he
      +sc2 = Equal.trans(List<&2, Bool>, T.scope_of(T.info(A.shift(t, A.loads(xs), True{}))), T.scope_of(T.info(A.shift(t, A.loads(hs), True{}))), s0, Equal.sym(List<&2, Bool>, T.scope_of(T.info(A.shift(t, A.loads(hs), True{}))), T.scope_of(T.info(A.shift(t, A.loads(xs), True{}))), ac_bud.sc_same(t, A.loads(xs), A.loads(hs), True{})), sc)
      +li2 = Equal.trans(T.Lim, T.limit_of(T.info(A.shift(t, A.loads(xs), True{}))), T.limit_of(T.info(A.shift(t, A.loads(hs), True{}))), T.Value{m}, Equal.sym(T.Lim, T.limit_of(T.info(A.shift(t, A.loads(hs), True{}))), T.limit_of(T.info(A.shift(t, A.loads(xs), True{}))), ac_bud.lim_same(t, A.loads(xs), A.loads(hs), True{})), li)
      ((ac_bud.good_lle(t, A.loads(xs), A.loads(hs), T.bound_depth(b), hl, g), (sc2, li2)), (Equal.trans(Bool, ac_bud.placed(t, A.loads(xs)), ac_bud.placed(t, A.loads(hs)), True{}, ac_bud.placed_lle(t, A.loads(xs), A.loads(hs), hl), hp), hvx))
    case A.HNo{why}:
      cb

# The step and the run
# --------------------

def ac_bud.cb_iv(+t: T.Node, +hs: List<&2, A.Help>, +b: T.Bounds, +s0: List<&2, Bool>, +m: Nat, +cb: ac_bud.CB(A.Crown{t, hs}, b, s0, m)) -> AR.at_reach.Inv(A.view(t, hs), b, s0, T.Value{m}):
  (iv, cb1) = cb
  iv

def ac_bud.cb_hv(+t: T.Node, +hs: List<&2, A.Help>, +b: T.Bounds, +s0: List<&2, Bool>, +m: Nat, +cb: ac_bud.CB(A.Crown{t, hs}, b, s0, m)) -> {ac_bud.hv(hs) == True{} : Bool}:
  (iv, cb1) = cb
  (hp, hh) = cb1
  hh

def ac_bud.step_cb(+b: T.Bounds, +c: A.Crown, +e: A.CEv, +s0: List<&2, Bool>, +m: Nat, +cb: ac_bud.CB(c, b, s0, m)) -> ac_bud.CB(A.cafter(A.hstep(b, c, e), c), b, s0, m):
  match c:
    case A.Crown{+t, +hs}:
      match e:
        case A.OnTree{+ev}:
          ac_bud.on_cb(T.step(A.cbounds(b, hs), A.view(t, hs), ev), t, hs, b, s0, m, ev, cb, Gw.ac_grow.step_gr(A.cbounds(b, hs), A.view(t, hs), ev), ac_bud.inv_uncb(T.after(T.step(A.cbounds(b, hs), A.view(t, hs), ev), A.view(t, hs)), b, hs, s0, T.Value{m}, AR.at_reach.inv_step(A.cbounds(b, hs), A.view(t, hs), ev, s0, T.Value{m}, ac_bud.inv_cb(A.view(t, hs), b, hs, s0, T.Value{m}, ac_bud.cb_iv(t, hs, b, s0, m, cb)))))
        case A.EvHelp{+p, +a}:
          ac_bud.help_cb(A.node_at(p, A.view(t, hs)), t, hs, p, a, Nat.is_le(Nat.add(Nat.add(T.size(t), A.hcount(hs)), 1n), T.bound_nodes(b)), T.bound_margin(b), b, s0, m, cb, {==})
        case A.EvHelpSpend{k, a}:
          ac_bud.hres_cb(A.spend_k(k, hs, a), t, hs, b, s0, m, cb, ac_bud.spend_hb(k, hs, a, ac_bud.cb_hv(t, hs, b, s0, m, cb)))
        case A.EvHelpEnd{k, ok}:
          ac_bud.hres_cb_end(A.end_k(k, hs, ok), t, hs, b, s0, m, cb, ac_bud.end_he(k, hs, ok, ac_bud.cb_hv(t, hs, b, s0, m, cb)))

def ac_bud.run_cb_all(evs: List<&2, A.CEv>, +b: T.Bounds, +c: A.Crown, +s0: List<&2, Bool>, +m: Nat, +cb: ac_bud.CB(c, b, s0, m)) -> ac_bud.CB(A.crun(evs, b, c), b, s0, m):
  match evs:
    case Nil{}:
      cb
    case Con{+e, es}:
      ac_bud.run_cb_all(es, b, A.cafter(A.hstep(b, c, e), c), s0, m, ac_bud.step_cb(b, c, e, s0, m, cb))

# The bound
# ---------

def ac_bud.one_ch(st: T.Status, lim: T.Lim, +sp: Nat, h1: {Bool.or(Bool.not(T.running(st)), ac_bud.vfit(sp, lim)) == True{} : Bool}) -> {Nat.is_le(sp, A.charge_if(T.running(st), lim, sp)) == True{} : Bool}:
  match st:
    case T.Running{}:
      match lim:
        case T.Unlimited{}:
          AR.at_reach.absurd({Nat.is_le(sp, 0n) == True{} : Bool}, h1)
        case T.Value{x}:
          h1
    case T.Finished{}:
      AR.at_reach.le_refl(sp)
    case T.Failed{}:
      AR.at_reach.le_refl(sp)
    case T.Cancelled{}:
      AR.at_reach.le_refl(sp)

# what the help leaves spent is at most what they charge
def ac_bud.hspent_le(hs: List<&2, A.Help>, +hh: {ac_bud.hv(hs) == True{} : Bool}) -> {Nat.is_le(CS.helps_spent(hs), ac_bud.lsum(A.loads(hs))) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, +rest}:
      match h:
        case A.Help{p, +st, +lim, +sp, dl}:
          ac_bud.add_le2(sp, A.charge_if(T.running(st), lim, sp), CS.helps_spent(rest), ac_bud.lsum(A.loads(rest)), ac_bud.one_ch(st, lim, sp, AR.at_reach.and_l(Bool.or(Bool.not(T.running(st)), ac_bud.vfit(sp, lim)), ac_bud.hv(rest), hh)), ac_bud.hspent_le(rest, AR.at_reach.and_r(Bool.or(Bool.not(T.running(st)), ac_bud.vfit(sp, lim)), ac_bud.hv(rest), hh)))

def ac_bud.fin(+c: A.Crown, +b: T.Bounds, +s0: List<&2, Bool>, +m: Nat, +cb: ac_bud.CB(c, b, s0, m)) -> {Nat.is_le(CS.crown_spent(c), m) == True{} : Bool}:
  match c:
    case A.Crown{+t, +hs}:
      (iv, cb1) = cb
      (g, iv1) = iv
      (sc, li) = iv1
      (hp, hh) = cb1
      +fa = AR.at_reach.tr(T.Lim, T.limit_of(T.info(A.view(t, hs))), T.Value{m}, z => {S.has(S.spent_all(A.view(t, hs)), z) == True{} : Bool}, li, AR.at_reach.fits_all(A.view(t, hs), T.bound_depth(b), g))
      +fb = AR.at_reach.tr(Nat, S.spent_all(A.shift(t, A.loads(hs), True{})), Nat.add(S.spent_all(t), ac_bud.lsum(A.loads(hs))), z => {Nat.is_le(z, m) == True{} : Bool}, ac_bud.spent_shift(t, A.loads(hs), hp), fa)
      AR.at_reach.le_trans(Nat.add(S.spent_all(t), CS.helps_spent(hs)), Nat.add(S.spent_all(t), ac_bud.lsum(A.loads(hs))), m, AR.at_reach.add_mono_l(S.spent_all(t), CS.helps_spent(hs), ac_bud.lsum(A.loads(hs)), ac_bud.hspent_le(hs, hh)), fb)

# under a Value root limit every reachable crown's spend fits it
def ac_bud.budget(+evs: List<&2, A.CEv>, +b: T.Bounds, +s: List<&2, Bool>, +m: Nat, +dl: T.Lim) -> {Nat.is_le(CS.crown_spent(A.crun(evs, b, A.cinit(s, T.Value{m}, dl))), m) == True{} : Bool}:
  ac_bud.fin(A.crun(evs, b, A.cinit(s, T.Value{m}, dl)), b, s, m, ac_bud.run_cb_all(evs, b, A.cinit(s, T.Value{m}, dl), s, m, (AR.at_reach.init_inv(b, s, T.Value{m}, dl), ({==}, {==}))))
