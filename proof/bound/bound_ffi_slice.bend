# eukhe: the proof of LAW bound_ffi_slice: the request reads back whole, as the cap and the body; the reply's Nats are the spec's

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def fs.nats(v: Bd.Slice) -> {FBd.slice.nats(v) == Bound.bd_slice.nats(v) : List<&2, Nat>}:
  match v:
    case Bd.Slice{sp, b, l}:
      match sp:
        case Bd.Span{f, t}:
          {==}

def fs.ask(c: Bd.Cap, x: Bd.Body) -> {FBd.ffi.ask(FBd.req(0n <> Bound.bd_cap(c, Bound.bd_body(x)))) == Bound.bd_spell(Bound.bd_slice.nats(Bd.slice(c, x))) : String}:
  match c:
    case Bd.Cap{+b, +k, t}:
      match t:
        case False{}:
          match x:
            case Bd.Body{+xs, o, +hc, +tc, +mc}:
              match o:
                case False{}:
                  +v = Bd.slice(Bd.Cap{b, k, False{}}, Bd.Body{xs, False{}, hc, tc, mc})
                  Equal.cong(List<&2, Nat>, String, ys => Wr.put_list(~Nat, ~Wr.put_nat, ys, ""), FBd.slice.nats(v), Bound.bd_slice.nats(v), fs.nats(v))
                case True{}:
                  +v = Bd.slice(Bd.Cap{b, k, False{}}, Bd.Body{xs, True{}, hc, tc, mc})
                  Equal.cong(List<&2, Nat>, String, ys => Wr.put_list(~Nat, ~Wr.put_nat, ys, ""), FBd.slice.nats(v), Bound.bd_slice.nats(v), fs.nats(v))
        case True{}:
          match x:
            case Bd.Body{+xs, o, +hc, +tc, +mc}:
              match o:
                case False{}:
                  +v = Bd.slice(Bd.Cap{b, k, True{}}, Bd.Body{xs, False{}, hc, tc, mc})
                  Equal.cong(List<&2, Nat>, String, ys => Wr.put_list(~Nat, ~Wr.put_nat, ys, ""), FBd.slice.nats(v), Bound.bd_slice.nats(v), fs.nats(v))
                case True{}:
                  +v = Bd.slice(Bd.Cap{b, k, True{}}, Bd.Body{xs, True{}, hc, tc, mc})
                  Equal.cong(List<&2, Nat>, String, ys => Wr.put_list(~Nat, ~Wr.put_nat, ys, ""), FBd.slice.nats(v), Bound.bd_slice.nats(v), fs.nats(v))

def Bound.bound_ffi_slice(c, x, h):
  +xs = {0n <> Bound.bd_cap(c, Bound.bd_body(x)) : List<&2, Nat>}
  %LBound.bnd.read(xs, h) : {FBd.ffi.got(_) == Bound.bd_spell(Bound.bd_slice.nats(Bd.slice(c, x))) : String}
  fs.ask(c, x)
