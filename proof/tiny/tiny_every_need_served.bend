# eukhe: the proof of LAW tiny_every_need_served

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/tiny.bend as Tiny

def pn.tiny_every_need_served(+es: List<&2, Tn.Ev>, +w: Tn.W) -> {List.length(&2, Tn.Got, Tn.gots(es, w)) == Tn.needs(es) : Nat}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      match e:
        case Tn.Gone{}:
          match w:
            case Tn.NoWorker{}:
              pn.tiny_every_need_served(rest, Tn.NoWorker{})
            case Tn.Worker{o, t}:
              pn.tiny_every_need_served(rest, Tn.NoWorker{})
        case Tn.Need{+p, +tag}:
          match w:
            case Tn.NoWorker{}:
              Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Tn.Got, Tn.gots(rest, Tn.Worker{p, tag})), Tn.needs(rest), pn.tiny_every_need_served(rest, Tn.Worker{p, tag}))
            case Tn.Worker{+o, +t}:
              +s = Tn.need.w(Nat.is_eq(t, tag), p, tag, Tn.Worker{o, t})
              Equal.cong(Nat, Nat, n => 1n+n, List.length(&2, Tn.Got, Tn.gots(rest, s)), Tn.needs(rest), pn.tiny_every_need_served(rest, s))

def Tiny.tiny_every_need_served(es, w):
  pn.tiny_every_need_served(es, w)
