# eukhe: the proof of LAW bound_ffi_notice: the request reads back whole; both sides compute on every retention, count and holding

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def fn.ask(t: Bool, +d: Nat, s: Bool) -> {FBd.ffi.ask(FBd.req([1n, Bound.bd_bit(t), d, Bound.bd_bit(s)])) == Bound.bd_spell(Bound.bd_notice.nats(Bd.notice(t, d, s))) : String}:
  match t:
    case False{}:
      match d:
        case 0n:
          match s:
            case False{}:
              {==}
            case True{}:
              {==}
        case 1n++p:
          match s:
            case False{}:
              {==}
            case True{}:
              {==}
    case True{}:
      match d:
        case 0n:
          match s:
            case False{}:
              {==}
            case True{}:
              {==}
        case 1n++p:
          match s:
            case False{}:
              {==}
            case True{}:
              {==}

def Bound.bound_ffi_notice(t, d, s, h):
  +xs = {[1n, Bound.bd_bit(t), d, Bound.bd_bit(s)] : List<&2, Nat>}
  %LBound.bnd.read(xs, h) : {FBd.ffi.got(_) == Bound.bd_spell(Bound.bd_notice.nats(Bd.notice(t, d, s))) : String}
  fn.ask(t, d, s)
