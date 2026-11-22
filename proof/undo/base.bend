# eukhe: lemmas shared by the proofs of area undo: the backward count of
# undos (laws/undo.bend sp_live) with k undos to go is the list with k
# turns dropped; the state after a history; the code's content equality is
# the spec's; the entry's encoders are the spec's spellings

import Base
import ../../bend/undo.bend as U
import ../../bend/ffi_undo.bend as FU
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/undo.bend as Undo

# Logic
# -----

def unb.IfF(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

def unb.IfT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# a premise False == True proves anything
def unb.absurd_ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : unb.IfF(_, G)
  Unit{}

# a premise True == False proves anything
def unb.absurd_tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : unb.IfT(_, G)
  Unit{}

# Snapshots
# ---------

# xs with its first k items dropped
def unb.drop(k: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match k:
    case 0n:
      xs
    case 1n+j:
      match xs:
        case Nil{}:
          Nil{}
        case Con{x, t}:
          unb.drop(j, t)

def unb.drop_nil(k: Nat) -> {unb.drop(k, Nil{}) == Nil{} : List<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      {==}

# dropping 1 + k is dropping 1, then k
def unb.drop_succ(xs: List<&2, Nat>, +k: Nat) -> {unb.drop(1n+k, xs) == unb.drop(k, unb.drop(1n, xs)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      Equal.sym(List<&2, Nat>, unb.drop(k, Nil{}), Nil{}, unb.drop_nil(k))
    case Con{x, t}:
      {==}

# the backward count with k undos still to take back a turn drops k of
# the turns the count with none keeps
def unb.live_drop(h: List<&2, U.Ev>, +k: Nat) -> {Undo.sp_live(h, k) == unb.drop(k, Undo.sp_live(h, 0n)) : List<&2, Nat>}:
  match h:
    case Nil{}:
      Equal.sym(List<&2, Nat>, unb.drop(k, Nil{}), Nil{}, unb.drop_nil(k))
    case Con{e, +older}:
      match e:
        case U.TurnStart{+t}:
          match k:
            case 0n:
              {==}
            case 1n+j:
              unb.live_drop(older, j)
        case U.Undo{}:
          +a = unb.live_drop(older, 1n+k)
          +b = unb.live_drop(older, 1n)
          +c = unb.drop_succ(Undo.sp_live(older, 0n), k)
          +d = Equal.cong(List<&2, Nat>, List<&2, Nat>, z => unb.drop(k, z), Undo.sp_live(older, 1n), unb.drop(1n, Undo.sp_live(older, 0n)), b)
          Equal.trans(List<&2, Nat>, Undo.sp_live(older, 1n+k), unb.drop(k, unb.drop(1n, Undo.sp_live(older, 0n))), unb.drop(k, Undo.sp_live(older, 1n)), Equal.trans(List<&2, Nat>, Undo.sp_live(older, 1n+k), unb.drop(1n+k, Undo.sp_live(older, 0n)), unb.drop(k, unb.drop(1n, Undo.sp_live(older, 0n))), a, c), Equal.sym(List<&2, Nat>, unb.drop(k, Undo.sp_live(older, 1n)), unb.drop(k, unb.drop(1n, Undo.sp_live(older, 0n))), d))
        case U.Diff{s}:
          unb.live_drop(older, k)

# the state after one more event, from the spec's state
def unb.step_turn(+live: List<&2, Nat>, m: Maybe<&2, Nat>, +t: Nat) -> {Undo.sp_state(U.step(U.St{live, m}, U.TurnStart{t})) == U.St{t <> live, Undo.sp_first.of(m, U.TurnStart{t})} : U.St}:
  match m:
    case None{}:
      {==}
    case Some{b}:
      {==}

def unb.step_undo(+m: Maybe<&2, Nat>, live: List<&2, Nat>) -> {Undo.sp_state(U.step(U.St{live, m}, U.Undo{})) == U.St{unb.drop(1n, live), Undo.sp_first.of(m, U.Undo{})} : U.St}:
  match m:
    case None{}:
      match live:
        case Nil{}:
          {==}
        case Con{x, t}:
          {==}
    case Some{b}:
      match live:
        case Nil{}:
          {==}
        case Con{x, t}:
          {==}

def unb.step_diff(+live: List<&2, Nat>, +m: Maybe<&2, Nat>, s: U.Scope) -> {Undo.sp_state(U.step(U.St{live, m}, U.Diff{s})) == U.St{live, Undo.sp_first.of(m, U.Diff{s})} : U.St}:
  match m:
    case None{}:
      match s:
        case U.Turn{}:
          {==}
        case U.All{}:
          {==}
    case Some{b}:
      match s:
        case U.Turn{}:
          {==}
        case U.All{}:
          {==}

# R1: the state after every history
def unb.state(h: List<&2, U.Ev>) -> {Undo.sp_replay(h) == U.St{Undo.sp_live(h, 0n), Undo.sp_first(h)} : U.St}:
  match h:
    case Nil{}:
      {==}
    case Con{e, +older}:
      match e:
        case U.TurnStart{+t}:
          +l = Undo.sp_live(older, 0n)
          +f = Undo.sp_first(older)
          %Equal.sym(U.St, Undo.sp_replay(older), U.St{l, f}, unb.state(older)) : {Undo.sp_state(U.step(_, U.TurnStart{t})) == U.St{t <> l, Undo.sp_first.of(f, U.TurnStart{t})} : U.St}
          unb.step_turn(l, f, t)
        case U.Undo{}:
          +l = Undo.sp_live(older, 0n)
          +f = Undo.sp_first(older)
          %Equal.sym(U.St, Undo.sp_replay(older), U.St{l, f}, unb.state(older)) : {Undo.sp_state(U.step(_, U.Undo{})) == U.St{Undo.sp_live(older, 1n), Undo.sp_first.of(f, U.Undo{})} : U.St}
          %Equal.sym(List<&2, Nat>, Undo.sp_live(older, 1n), unb.drop(1n, l), unb.live_drop(older, 1n)) : {Undo.sp_state(U.step(U.St{l, f}, U.Undo{})) == U.St{_, Undo.sp_first.of(f, U.Undo{})} : U.St}
          unb.step_undo(f, l)
        case U.Diff{+s}:
          +l = Undo.sp_live(older, 0n)
          +f = Undo.sp_first(older)
          %Equal.sym(U.St, Undo.sp_replay(older), U.St{l, f}, unb.state(older)) : {Undo.sp_state(U.step(_, U.Diff{s})) == U.St{l, Undo.sp_first.of(f, U.Diff{s})} : U.St}
          unb.step_diff(l, f, s)

# Rows
# ----

def unb.nat_eq(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Undo.sp_nat_eq(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+x 0n:
      {==}
    case 1n+x 1n+y:
      unb.nat_eq(x, y)

def unb.nat_eq_true(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      unb.absurd_ft({0n == 1n+y : Nat}, e)
    case 1n+x 0n:
      unb.absurd_ft({1n+x == 0n : Nat}, e)
    case 1n+x 1n+y:
      %unb.nat_eq_true(x, y, e) : {1n+x == 1n+_ : Nat}
      {==}

# Wire
# ----

# a Nat read as a Maybe spells back as that Nat
def unb.wm(n: Nat) -> {Undo.sp_w_maybe(FU.maybe_of(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+t:
      {==}

# a Nat read as an event spells back as that Nat
def unb.we(n: Nat) -> {Undo.sp_w_ev(FU.ev_of(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n+t:
      {==}

# a Maybe spelled as a Nat reads back
def unb.mw(m: Maybe<&2, Nat>) -> {FU.maybe_of(Undo.sp_w_maybe(m)) == m : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      {==}

# an event spelled as a Nat reads back
def unb.ew(e: U.Ev) -> {FU.ev_of(Undo.sp_w_ev(e)) == e : U.Ev}:
  match e:
    case U.Undo{}:
      {==}
    case U.Diff{s}:
      match s:
        case U.Turn{}:
          {==}
        case U.All{}:
          {==}
    case U.TurnStart{t}:
      {==}

def unb.under(-s: String, -s1: String, -y: String, -f: String -> String, e: {s == f(s1) : String}, p: {s1 == y : String}) -> {s == f(y) : String}:
  %p : {s == f(_) : String}
  e

# rows spelled as Nats read back
def unb.rows_back(rows: List<&2, U.Row>) -> {FU.rows_of(Undo.sp_flat(rows)) == Some{rows} : Maybe<&2, List<&2, U.Row>>}:
  match rows:
    case Nil{}:
      {==}
    case Con{r, +t}:
      match r:
        case U.Row{+b, +n, h}:
          match h:
            case False{}:
              %Equal.sym(Maybe<&2, List<&2, U.Row>>, FU.rows_of(Undo.sp_flat(t)), Some{t}, unb.rows_back(t)) : {FU.rows_of.cons(U.Row{FU.maybe_of(Undo.sp_w_maybe(b)), FU.maybe_of(Undo.sp_w_maybe(n)), False{}}, _) == Some{U.Row{b, n, False{}} <> t} : Maybe<&2, List<&2, U.Row>>}
              %Equal.sym(Maybe<&2, Nat>, FU.maybe_of(Undo.sp_w_maybe(b)), b, unb.mw(b)) : {FU.rows_of.cons(U.Row{_, FU.maybe_of(Undo.sp_w_maybe(n)), False{}}, Some{t}) == Some{U.Row{b, n, False{}} <> t} : Maybe<&2, List<&2, U.Row>>}
              %Equal.sym(Maybe<&2, Nat>, FU.maybe_of(Undo.sp_w_maybe(n)), n, unb.mw(n)) : {FU.rows_of.cons(U.Row{b, _, False{}}, Some{t}) == Some{U.Row{b, n, False{}} <> t} : Maybe<&2, List<&2, U.Row>>}
              {==}
            case True{}:
              %Equal.sym(Maybe<&2, List<&2, U.Row>>, FU.rows_of(Undo.sp_flat(t)), Some{t}, unb.rows_back(t)) : {FU.rows_of.cons(U.Row{FU.maybe_of(Undo.sp_w_maybe(b)), FU.maybe_of(Undo.sp_w_maybe(n)), True{}}, _) == Some{U.Row{b, n, True{}} <> t} : Maybe<&2, List<&2, U.Row>>}
              %Equal.sym(Maybe<&2, Nat>, FU.maybe_of(Undo.sp_w_maybe(b)), b, unb.mw(b)) : {FU.rows_of.cons(U.Row{_, FU.maybe_of(Undo.sp_w_maybe(n)), True{}}, Some{t}) == Some{U.Row{b, n, True{}} <> t} : Maybe<&2, List<&2, U.Row>>}
              %Equal.sym(Maybe<&2, Nat>, FU.maybe_of(Undo.sp_w_maybe(n)), n, unb.mw(n)) : {FU.rows_of.cons(U.Row{b, _, True{}}, Some{t}) == Some{U.Row{b, n, True{}} <> t} : Maybe<&2, List<&2, U.Row>>}
              {==}

# what the rows decoder reads: rows whose spelling is the Nats it read
def unb.RX(ns: List<&2, Nat>, m: Maybe<&2, List<&2, U.Row>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{rows}:
      {ns == Undo.sp_flat(rows) : List<&2, Nat>}

def unb.rx_cons(+b: Nat, +n: Nat, hb: Bool, +t: List<&2, Nat>, m: Maybe<&2, List<&2, U.Row>>, ih: unb.RX(t, m)) -> unb.RX(b <> (n <> (Undo.sp_w_held(hb) <> t)), FU.rows_of.cons(U.Row{FU.maybe_of(b), FU.maybe_of(n), hb}, m)):
  match m:
    case None{}:
      Unit{}
    case Some{rows}:
      %Equal.sym(Nat, Undo.sp_w_maybe(FU.maybe_of(b)), b, unb.wm(b)) : {b <> (n <> (Undo.sp_w_held(hb) <> t)) == _ <> (Undo.sp_w_maybe(FU.maybe_of(n)) <> (Undo.sp_w_held(hb) <> Undo.sp_flat(rows))) : List<&2, Nat>}
      %Equal.sym(Nat, Undo.sp_w_maybe(FU.maybe_of(n)), n, unb.wm(n)) : {b <> (n <> (Undo.sp_w_held(hb) <> t)) == b <> (_ <> (Undo.sp_w_held(hb) <> Undo.sp_flat(rows))) : List<&2, Nat>}
      %ih : {b <> (n <> (Undo.sp_w_held(hb) <> t)) == b <> (n <> (Undo.sp_w_held(hb) <> _)) : List<&2, Nat>}
      {==}

def unb.rx(ns: List<&2, Nat>) -> unb.RX(ns, FU.rows_of(ns)):
  match ns:
    case Nil{}:
      {==}
    case Con{+b, t1}:
      match t1:
        case Nil{}:
          Unit{}
        case Con{+n, t2}:
          match t2:
            case Nil{}:
              Unit{}
            case Con{h, +t3}:
              match h:
                case 0n:
                  unb.rx_cons(b, n, False{}, t3, FU.rows_of(t3), unb.rx(t3))
                case 1n:
                  unb.rx_cons(b, n, True{}, t3, FU.rows_of(t3), unb.rx(t3))
                case 2n+x:
                  Unit{}
