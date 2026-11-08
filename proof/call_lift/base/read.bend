# eukhe: lemmas of area call_lift about the request reader: the entry's
# decoder (bend/ffi_call_lift.bend get_req) is the laws' reader
# (spec/harness/lift_wire.bend r_call), stage by stage

import Base
import ../../../bend/call_lift.bend as Cl
import ../../../bend/ffi_call_lift.bend as FCl
import ../../../bend/wire.bend as Wr
import ../../../spec/harness/lift_wire.bend as SpW

def cle.keys(f: String, r: String, d: Wr.Dec<List<&2, String>>) -> {FCl.get_call.keys(f, r, d) == SpW.r_call.keys(f, r, d) : Wr.Dec<Cl.Call>}:
  match d:
    case Wr.Got{ks, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cle.rev(f: String, d: Wr.Dec<String>) -> {FCl.get_call.rev(f, d) == SpW.r_call.rev(f, d) : Wr.Dec<Cl.Call>}:
  match d:
    case Wr.Got{+r, +s}:
      cle.keys(f, r, Wr.get_list(~String, ~Wr.get_str, s))
    case Wr.Bad{}:
      {==}

def cle.fam(d: Wr.Dec<String>) -> {FCl.get_call.fam(d) == SpW.r_call.fam(d) : Wr.Dec<Cl.Call>}:
  match d:
    case Wr.Got{+f, +s}:
      cle.rev(f, Wr.get_str(s))
    case Wr.Bad{}:
      {==}

# the entry reads a call as the laws' reader does
def cle.call(+s: String) -> {FCl.get_call(s) == SpW.r_call(s) : Wr.Dec<Cl.Call>}:
  cle.fam(Wr.get_str(s))

def cle.calls_go(k: Nat, cur: Wr.Dec<Cl.Call>) -> {Wr.get_list.go(~Cl.Call, ~FCl.get_call, k, cur) == Wr.get_list.go(~Cl.Call, ~SpW.r_call, k, cur) : Wr.Dec<List<&2, Cl.Call>>}:
  match k:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n+m:
      match cur:
        case Wr.Got{+x, +s}:
          %Equal.sym(Wr.Dec<Cl.Call>, FCl.get_call(s), SpW.r_call(s), cle.call(s)) : {Wr.get_list.cons(Cl.Call, x, Wr.get_list.go(~Cl.Call, ~FCl.get_call, m, _)) == Wr.get_list.cons(Cl.Call, x, Wr.get_list.go(~Cl.Call, ~SpW.r_call, m, SpW.r_call(s))) : Wr.Dec<List<&2, Cl.Call>>}
          %cle.calls_go(m, SpW.r_call(s)) : {Wr.get_list.cons(Cl.Call, x, Wr.get_list.go(~Cl.Call, ~FCl.get_call, m, SpW.r_call(s))) == Wr.get_list.cons(Cl.Call, x, _) : Wr.Dec<List<&2, Cl.Call>>}
          {==}
        case Wr.Bad{}:
          {==}

def cle.calls_start(r: Wr.Dec<Nat>) -> {Wr.get_list.start(~Cl.Call, ~FCl.get_call, r) == Wr.get_list.start(~Cl.Call, ~SpW.r_call, r) : Wr.Dec<List<&2, Cl.Call>>}:
  match r:
    case Wr.Got{k, +s}:
      match k:
        case 0n:
          {==}
        case 1n+m:
          %Equal.sym(Wr.Dec<Cl.Call>, FCl.get_call(s), SpW.r_call(s), cle.call(s)) : {Wr.get_list.go(~Cl.Call, ~FCl.get_call, m, _) == Wr.get_list.go(~Cl.Call, ~SpW.r_call, m, SpW.r_call(s)) : Wr.Dec<List<&2, Cl.Call>>}
          cle.calls_go(m, SpW.r_call(s))
    case Wr.Bad{}:
      {==}

# the entry reads a request as the laws' reader does
def cle.req(+s: String) -> {FCl.get_req(s) == Wr.get_list(~Cl.Call, ~SpW.r_call, s) : Wr.Dec<List<&2, Cl.Call>>}:
  cle.calls_start(Wr.get_nat(s))
