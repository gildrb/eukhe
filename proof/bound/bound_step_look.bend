# eukhe: the proof of LAW bound_step_look: the stored text reads back whole as the body; the reply's Nats are the spec's

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def sl.pair(r: Bd.St & Bd.Seen) -> {FBd.step.look(r) == (FBd.Run{Bound.bd_fst.look(r)}, Bound.bd_spell(Bound.bd_seen.nats(Bound.bd_snd.look(r)))) : FBd.St & String}:
  match r:
    case (s, v):
      match v:
        case Bd.Seen{sp, b, l, c}:
          match sp:
            case Bd.Span{f, t}:
              {==}

def sl.ev(+s: Bd.St, x: Bd.Body) -> {FBd.step.ev(FBd.Run{s}, FBd.ev(2n <> Bound.bd_body(x))) == (FBd.Run{Bound.bd_fst.look(Bd.look(s, x))}, Bound.bd_spell(Bound.bd_seen.nats(Bound.bd_snd.look(Bd.look(s, x))))) : FBd.St & String}:
  match x:
    case Bd.Body{+xs, o, +hc, +tc, +mc}:
      match o:
        case False{}:
          sl.pair(Bd.look(s, Bd.Body{xs, False{}, hc, tc, mc}))
        case True{}:
          sl.pair(Bd.look(s, Bd.Body{xs, True{}, hc, tc, mc}))

def Bound.bound_step_look(s, x, h):
  +xs = {2n <> Bound.bd_body(x) : List<&2, Nat>}
  %LBound.bnd.read(xs, h) : {FBd.step.got(FBd.Run{s}, _) == (FBd.Run{Bound.bd_fst.look(Bd.look(s, x))}, Bound.bd_spell(Bound.bd_seen.nats(Bound.bd_snd.look(Bd.look(s, x))))) : FBd.St & String}
  sl.ev(s, x)
