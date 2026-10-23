# eukhe: the proof of LAW proto_runs_every_accepted

import Base
import ../../bend/sandbox.bend as Sb
import ../../LAWS.bend as Laws

def px.len_add(g: Bool, +f: Sb.Frame, h: Sb.Host) -> {Nat.add(Sb.one(g), List.length(&2, Sb.Frame, Sb.Host.ran(h))) == List.length(&2, Sb.Frame, Sb.Host.ran(Sb.host.add(g, f, h))) : Nat}:
  match g:
    case True{}:
      match h:
        case Sb.Host{rs, xs}:
          {==}
    case False{}:
      match h:
        case Sb.Host{rs, xs}:
          {==}

def px.proto_runs_every_accepted(+fs: List<&2, Sb.Frame>, +max: Nat, +allowed: List<&2, Nat>) -> {List.length(&2, Sb.Frame, Sb.Host.ran(Sb.serve(fs, max, allowed))) == Sb.oks(fs, max, allowed) : Nat}:
  match fs:
    case Nil{}:
      {==}
    case f <> rest:
      %px.len_add(Sb.accepts(max, allowed, f), f, Sb.serve(rest, max, allowed)) : {_ == Nat.add(Sb.one(Sb.accepts(max, allowed, f)), Sb.oks(rest, max, allowed)) : Nat}
      %px.proto_runs_every_accepted(rest, max, allowed) : {Nat.add(Sb.one(Sb.accepts(max, allowed, f)), List.length(&2, Sb.Frame, Sb.Host.ran(Sb.serve(rest, max, allowed)))) == Nat.add(Sb.one(Sb.accepts(max, allowed, f)), _) : Nat}
      {==}

def Laws.proto_runs_every_accepted(fs, max, allowed):
  px.proto_runs_every_accepted(fs, max, allowed)
