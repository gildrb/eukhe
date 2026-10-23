# eukhe: the proof of LAW proto_runs_only_accepted

import Base
import ../../bend/sandbox.bend as Sb
import ../../laws/sandbox.bend as Sandbox

def px.and_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

# a step keeps every frame run accepted
def px.ok_add(g: Bool, +f: Sb.Frame, h: Sb.Host, +max: Nat, +allowed: List<&2, Nat>, e: {Sb.accepts(max, allowed, f) == g : Bool}, ih: {Sb.all_ok(Sb.Host.ran(h), max, allowed) == True{} : Bool}) -> {Sb.all_ok(Sb.Host.ran(Sb.host.add(g, f, h)), max, allowed) == True{} : Bool}:
  match g:
    case True{}:
      match h:
        case Sb.Host{rs, xs}:
          px.and_t(Sb.accepts(max, allowed, f), Sb.all_ok(xs, max, allowed), e, ih)
    case False{}:
      match h:
        case Sb.Host{rs, xs}:
          ih

def px.proto_runs_only_accepted(+fs: List<&2, Sb.Frame>, +max: Nat, +allowed: List<&2, Nat>) -> {Sb.all_ok(Sb.Host.ran(Sb.serve(fs, max, allowed)), max, allowed) == True{} : Bool}:
  match fs:
    case Nil{}:
      {==}
    case f <> rest:
      px.ok_add(Sb.accepts(max, allowed, f), f, Sb.serve(rest, max, allowed), max, allowed, {==}, px.proto_runs_only_accepted(rest, max, allowed))

def Sandbox.proto_runs_only_accepted(fs, max, allowed):
  px.proto_runs_only_accepted(fs, max, allowed)
