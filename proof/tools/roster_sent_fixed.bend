# eukhe: the proof of LAW roster_sent_fixed

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./base.bend as LA

def pl.and_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

# a turn sends r before rosters that are all r
def pl.all_cons(x: List<&2, List<&2, Nat>>, +r: List<&2, Nat>, h: {Tl.all_eq(x, r) == True{} : Bool}) -> {Tl.all_eq(r <> x, r) == True{} : Bool}:
  pl.and_t(Tl.ids.eq(r, r), Tl.all_eq(x, r), LA.pl.ids_refl(r), h)

def pl.sent_go(es: List<&2, Tl.Ev>, +r: List<&2, Nat>, +d: List<&2, Nat>, +x: List<&2, List<&2, Nat>>, +h: {Tl.all_eq(x, r) == True{} : Bool}) -> {Tl.all_eq(Tl.Sess.sent(Tl.run(es, Tl.Sess{r, d, x})), r) == True{} : Bool}:
  match es:
    case Nil{}:
      h
    case +e <> rest:
      match e:
        case Tl.Join{+t}:
          pl.sent_go(rest, r, t <> d, x, h)
        case Tl.Quit{+t}:
          pl.sent_go(rest, r, Tl.drop(d, t), x, h)
        case Tl.Turn{}:
          pl.sent_go(rest, r, d, r <> x, pl.all_cons(x, r, h))

def pl.roster_sent_fixed(es: List<&2, Tl.Ev>, +r: List<&2, Nat>, d: List<&2, Nat>) -> {Tl.all_eq(Tl.Sess.sent(Tl.run(es, Tl.Sess{r, d, Nil{}})), r) == True{} : Bool}:
  pl.sent_go(es, r, d, Nil{}, {==})

def Tools.roster_sent_fixed(es, r, d):
  pl.roster_sent_fixed(es, r, d)
