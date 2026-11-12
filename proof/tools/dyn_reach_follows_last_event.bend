# eukhe: the proof of LAW dyn_reach_follows_last_event
# One event (prd.one): a join of u reaches u and keeps every other tool's
# reach (prd.join); a quit of u reaches u no more (dyn_drops_quit) and
# keeps every other tool's reach (prd.keep, by induction on the dynamic
# tools); a request keeps the dynamic tools. Then by induction on the
# events: a later event's word wins (prd.later).

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./base.bend as LA
import ./dyn_drops_quit.bend as PDynDropsQuit

# a later word wins over an earlier one
def prd.later(m: Maybe<&2, Bool>, -h: Maybe<&2, Bool>, -b: Bool) -> {Tools.tr_or(m, Tools.tr_or(h, b)) == Tools.tr_or(Tools.tr_later(m, h), b) : Bool}:
  match m:
    case Some{v}:
      {==}
    case None{}:
      {==}

# a join, with the test b of the joined tool against t
def prd.join(b: Bool, -e: Bool) -> {Bool.or(b, e) == Tools.tr_or(Tools.tr_hit(b, True{}), e) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a quit of u (not t) keeps whether t is reached; hit is the head test
def prd.keep(d: List<&2, Nat>, +u: Nat, +t: Nat, hit: Bool, eh: {Tl.is.at(d, u) == hit : Bool}, +ne: {Nat.is_eq(u, t) == False{} : Bool}) -> {Tl.elem(Tl.drop.go(d, u, hit), t) == Tl.elem(d, t) : Bool}:
  match d:
    case Nil{}:
      {==}
    case +y <> +rest:
      match hit:
        case True{}:
          %Equal.sym(Nat, y, u, LA.shell.ps.eq_of_is_eq(y, u, eh)) : {Tl.elem(Tl.drop.go(rest, u, Tl.is.at(rest, u)), t) == Bool.or(Nat.is_eq(_, t), Tl.elem(rest, t)) : Bool}
          %Equal.sym(Bool, Nat.is_eq(u, t), False{}, ne) : {Tl.elem(Tl.drop.go(rest, u, Tl.is.at(rest, u)), t) == Bool.or(_, Tl.elem(rest, t)) : Bool}
          prd.keep(rest, u, t, Tl.is.at(rest, u), {==}, ne)
        case False{}:
          %Equal.sym(Bool, Tl.elem(Tl.drop.go(rest, u, Tl.is.at(rest, u)), t), Tl.elem(rest, t), prd.keep(rest, u, t, Tl.is.at(rest, u), {==}, ne)) : {Bool.or(Nat.is_eq(y, t), _) == Bool.or(Nat.is_eq(y, t), Tl.elem(rest, t)) : Bool}
          {==}

# a quit of u, with the test b of u against t
def prd.quit(b: Bool, +d: List<&2, Nat>, +u: Nat, +t: Nat, e: {Nat.is_eq(u, t) == b : Bool}) -> {Tl.elem(Tl.drop(d, u), t) == Tools.tr_or(Tools.tr_hit(b, False{}), Tl.elem(d, t)) : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, u, t, LA.shell.ps.eq_of_is_eq(u, t, e)) : {Tl.elem(Tl.drop(d, _), t) == False{} : Bool}
      Tools.dyn_drops_quit(Tl.Sess{Nil{}, d, Nil{}}, t)
    case False{}:
      prd.keep(d, u, t, Tl.is.at(d, u), {==}, e)

# one event: t is reached as the event says, else as before
def prd.one(+s: Tl.Sess, +e: Tl.Ev, +t: Nat) -> {Tl.dyn_call(Tl.step(s, e), t) == Tools.tr_or(Tools.tr_says(e, t), Tl.dyn_call(s, t)) : Bool}:
  match s:
    case Tl.Sess{r, +d, x}:
      match e:
        case Tl.Join{u}:
          prd.join(Nat.is_eq(u, t), Tl.elem(d, t))
        case Tl.Quit{+u}:
          prd.quit(Nat.is_eq(u, t), d, u, t, {==})
        case Tl.Turn{}:
          {==}

def prd.run(es: List<&2, Tl.Ev>, +s: Tl.Sess, +t: Nat) -> {Tl.dyn_call(Tl.run(es, s), t) == Tools.tr_or(Tools.tr_last(es, t), Tl.dyn_call(s, t)) : Bool}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      Equal.trans(Bool, Tl.dyn_call(Tl.run(rest, Tl.step(s, e)), t), Tools.tr_or(Tools.tr_last(rest, t), Tl.dyn_call(Tl.step(s, e), t)), Tools.tr_or(Tools.tr_later(Tools.tr_last(rest, t), Tools.tr_says(e, t)), Tl.dyn_call(s, t)), prd.run(rest, Tl.step(s, e), t), Equal.trans(Bool, Tools.tr_or(Tools.tr_last(rest, t), Tl.dyn_call(Tl.step(s, e), t)), Tools.tr_or(Tools.tr_last(rest, t), Tools.tr_or(Tools.tr_says(e, t), Tl.dyn_call(s, t))), Tools.tr_or(Tools.tr_later(Tools.tr_last(rest, t), Tools.tr_says(e, t)), Tl.dyn_call(s, t)), Equal.cong(Bool, Bool, z => Tools.tr_or(Tools.tr_last(rest, t), z), Tl.dyn_call(Tl.step(s, e), t), Tools.tr_or(Tools.tr_says(e, t), Tl.dyn_call(s, t)), prd.one(s, e, t)), prd.later(Tools.tr_last(rest, t), Tools.tr_says(e, t), Tl.dyn_call(s, t))))

def Tools.dyn_reach_follows_last_event(es, s, t):
  prd.run(es, s, t)
