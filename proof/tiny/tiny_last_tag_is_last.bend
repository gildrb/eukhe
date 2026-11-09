# eukhe: the proof of LAW tiny_last_tag_is_last
#
# PROOF: by induction on the events before the last one, from any start
# value: each event only sets the value the rest starts from; the last
# event sets the answer.

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny/pick.bend as Tiny

def tll.need(es: List<&2, Tn.Ev>, m: Maybe<&2, Nat>, +p: Nat, +t: Nat) -> {Tn.last_tag(List.append(&2, Tn.Ev, es, [Tn.Need{p, t}]), m) == Some{t} : Maybe<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case Tn.Need{q, u}:
          tll.need(rest, Some{u}, p, t)
        case Tn.Gone{}:
          tll.need(rest, None{}, p, t)

def tll.gone(es: List<&2, Tn.Ev>, m: Maybe<&2, Nat>) -> {Tn.last_tag(List.append(&2, Tn.Ev, es, [Tn.Gone{}]), m) == None{} : Maybe<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case Tn.Need{q, u}:
          tll.gone(rest, Some{u})
        case Tn.Gone{}:
          tll.gone(rest, None{})

def Tiny.tiny_last_tag_is_last(es, m, p, t):
  (tll.need(es, m, p, t), (tll.gone(es, m), {==}))
