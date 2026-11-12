# eukhe: lemmas of area call_lift about the lookups and the walk: a table
# (a step list) whose first rows are named otherwise (leave other revs)
# finds the first row named f (leaving x); one with no such row finds
# none; a chain of revs (CallLift.chain_ok) is what the walk follows, and
# the walk answers its ops (CallLift.chain_ops)

import Base
import ../../../bend/call_lift.bend as Cl
import ../../../laws/call_lift.bend as CallLift
import ../../base/staging.bend as LStg
import ../../base/logic/bool.bend as LLogicBool
import ../../auth_flight/base/logic.bend as LAuthLogic
import ./string.bend as LCallLiftString

# Families
# --------

# a row the premise says is not named f is skipped
def cll.fam_skip(b: Bool, x: Cl.Fam, -m: Maybe<&2, Cl.Fam>, -want: Maybe<&2, Cl.Fam>, -q: Bool, h: {Bool.and(Bool.not(b), q) == True{} : Bool}, ih: {q == True{} : Bool} -> {m == want : Maybe<&2, Cl.Fam>}) -> {Cl.fam_of.pick(b, x, m) == want : Maybe<&2, Cl.Fam>}:
  match b:
    case True{}:
      LStg.stg.absurd({Cl.fam_of.pick(True{}, x, m) == want : Maybe<&2, Cl.Fam>}, Equal.sym(Bool, False{}, True{}, h))
    case False{}:
      ih(h)

# the first family named f, after families named otherwise, is found
def cll.fam_found(+pre: List<&2, Cl.Fam>, post: List<&2, Cl.Fam>, +f: String, +c: String, +s: List<&2, Cl.Step>, first: {CallLift.names_lack(pre, f) == True{} : Bool}) -> {Cl.fam_of(List.append(&2, Cl.Fam, pre, Cl.Fam{f, c, s} <> post), f) == Some{Cl.Fam{f, c, s}} : Maybe<&2, Cl.Fam>}:
  match pre:
    case Nil{}:
      %LCallLiftString.clm.str_refl_sym(f) : {Cl.fam_of.pick(_, Cl.Fam{f, c, s}, Cl.fam_of(post, f)) == Some{Cl.Fam{f, c, s}} : Maybe<&2, Cl.Fam>}
      {==}
    case Con{x, +rest}:
      match x:
        case Cl.Fam{+n, c2, s2}:
          cll.fam_skip(String.eq(n, f), Cl.Fam{n, c2, s2}, Cl.fam_of(List.append(&2, Cl.Fam, rest, Cl.Fam{f, c, s} <> post), f), Some{Cl.Fam{f, c, s}}, CallLift.names_lack(rest, f), first, h => cll.fam_found(rest, post, f, c, s, h))

# no family named f: none is found
def cll.fam_none(+t: List<&2, Cl.Fam>, +f: String, no: {CallLift.names_lack(t, f) == True{} : Bool}) -> {Cl.fam_of(t, f) == None{} : Maybe<&2, Cl.Fam>}:
  match t:
    case Nil{}:
      {==}
    case Con{x, +rest}:
      match x:
        case Cl.Fam{+n, c, s}:
          cll.fam_skip(String.eq(n, f), Cl.Fam{n, c, s}, Cl.fam_of(rest, f), None{}, CallLift.names_lack(rest, f), no, h => cll.fam_none(rest, f, h))

# Steps
# -----

# a step the premise says leaves another rev is skipped
def cll.step_skip(b: Bool, x: Cl.Step, -m: Maybe<&2, Cl.Step>, -want: Maybe<&2, Cl.Step>, -q: Bool, h: {Bool.and(Bool.not(b), q) == True{} : Bool}, ih: {q == True{} : Bool} -> {m == want : Maybe<&2, Cl.Step>}) -> {Cl.step_of.pick(b, x, m) == want : Maybe<&2, Cl.Step>}:
  match b:
    case True{}:
      LStg.stg.absurd({Cl.step_of.pick(True{}, x, m) == want : Maybe<&2, Cl.Step>}, Equal.sym(Bool, False{}, True{}, h))
    case False{}:
      ih(h)

# the first step leaving x, after steps leaving other revs, is found
def cll.step_found(+pre: List<&2, Cl.Step>, post: List<&2, Cl.Step>, +x: String, +b: String, +o: List<&2, Cl.Op>, first: {CallLift.leaves_none(pre, x) == True{} : Bool}) -> {Cl.step_of(List.append(&2, Cl.Step, pre, Cl.Step{x, b, o} <> post), x) == Some{Cl.Step{x, b, o}} : Maybe<&2, Cl.Step>}:
  match pre:
    case Nil{}:
      %LCallLiftString.clm.str_refl_sym(x) : {Cl.step_of.pick(_, Cl.Step{x, b, o}, Cl.step_of(post, x)) == Some{Cl.Step{x, b, o}} : Maybe<&2, Cl.Step>}
      {==}
    case Con{st, +rest}:
      match st:
        case Cl.Step{+a, b2, o2}:
          cll.step_skip(String.eq(a, x), Cl.Step{a, b2, o2}, Cl.step_of(List.append(&2, Cl.Step, rest, Cl.Step{x, b, o} <> post), x), Some{Cl.Step{x, b, o}}, CallLift.leaves_none(rest, x), first, h => cll.step_found(rest, post, x, b, o, h))

# no step leaves x: none is found
def cll.step_none(+ss: List<&2, Cl.Step>, +x: String, no: {CallLift.leaves_none(ss, x) == True{} : Bool}) -> {Cl.step_of(ss, x) == None{} : Maybe<&2, Cl.Step>}:
  match ss:
    case Nil{}:
      {==}
    case Con{st, +rest}:
      match st:
        case Cl.Step{+a, b, o}:
          cll.step_skip(String.eq(a, x), Cl.Step{a, b, o}, Cl.step_of(rest, x), None{}, CallLift.leaves_none(rest, x), no, h => cll.step_none(rest, x, h))

# The walk
# --------

def cll.append_nil(+o: List<&2, Cl.Op>) -> {o == List.append(&2, Cl.Op, o, Nil{}) : List<&2, Cl.Op>}:
  match o:
    case Nil{}:
      {==}
    case Con{z, +rest}:
      %cll.append_nil(rest) : {Con{z, rest} == Con{z, _} : List<&2, Cl.Op>}
      {==}

# a walk with no step found is none, at every fuel
def cll.walk_none(n: Nat, -ss: List<&2, Cl.Step>, -cur: String) -> {Cl.walk(n, ss, cur, None{}) == None{} : Maybe<&2, List<&2, Cl.Op>>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

# after a step that arrives at y: y the current rev ends the chain (its ops
# alone), else the walk goes on from y (ih)
def cll.wc.at(at: Bool, +o: List<&2, Cl.Op>, -f: Nat, -ss: List<&2, Cl.Step>, -cur: String, -y: String, more: List<&2, String>, h: {CallLift.chain_ok.after(at, more, CallLift.chain_ok(more, ss, y, cur)) == True{} : Bool}, ih: {CallLift.chain_ok(more, ss, y, cur) == True{} : Bool} -> {Cl.walk(f, ss, cur, Cl.step_of(ss, y)) == Some{CallLift.chain_ops(more, ss, y)} : Maybe<&2, List<&2, Cl.Op>>}) -> {Cl.walk.join(o, at, Cl.walk(f, ss, cur, Cl.step_of(ss, y))) == Some{List.append(&2, Cl.Op, o, CallLift.chain_ops(more, ss, y))} : Maybe<&2, List<&2, Cl.Op>>}:
  match at:
    case True{}:
      match more:
        case Nil{}:
          %cll.append_nil(o) : {Some{o} == Some{_} : Maybe<&2, List<&2, Cl.Op>>}
          {==}
        case Con{z, rest}:
          LStg.stg.absurd({Cl.walk.join(o, True{}, Cl.walk(f, ss, cur, Cl.step_of(ss, y))) == Some{List.append(&2, Cl.Op, o, CallLift.chain_ops(Con{z, rest}, ss, y))} : Maybe<&2, List<&2, Cl.Op>>}, Equal.sym(Bool, False{}, True{}, h))
    case False{}:
      %Equal.sym(Maybe<&2, List<&2, Cl.Op>>, Cl.walk(f, ss, cur, Cl.step_of(ss, y)), Some{CallLift.chain_ops(more, ss, y)}, ih(h)) : {Cl.walk.join(o, False{}, _) == Some{List.append(&2, Cl.Op, o, CallLift.chain_ops(more, ss, y))} : Maybe<&2, List<&2, Cl.Op>>}
      {==}

# the step the walk found arrives at y (b is y), then cll.wc.at
def cll.wc.step(+a: String, +b: String, +o: List<&2, Cl.Op>, -f: Nat, +ss: List<&2, Cl.Step>, +cur: String, +y: String, +more: List<&2, String>, +h: {Bool.and(String.eq(b, y), CallLift.chain_ok.after(String.eq(y, cur), more, CallLift.chain_ok(more, ss, y, cur))) == True{} : Bool}, ih: {CallLift.chain_ok(more, ss, y, cur) == True{} : Bool} -> {Cl.walk(f, ss, cur, Cl.step_of(ss, y)) == Some{CallLift.chain_ops(more, ss, y)} : Maybe<&2, List<&2, Cl.Op>>}) -> {Cl.walk.join(o, String.eq(b, cur), Cl.walk(f, ss, cur, Cl.step_of(ss, b))) == Some{List.append(&2, Cl.Op, o, CallLift.chain_ops(more, ss, y))} : Maybe<&2, List<&2, Cl.Op>>}:
  +eb = Equal.sym(String, b, y, LAuthLogic.ad.str_sound(b, y, LLogicBool.wr_and_l(String.eq(b, y), CallLift.chain_ok.after(String.eq(y, cur), more, CallLift.chain_ok(more, ss, y, cur)), h)))
  %eb : {Cl.walk.join(o, String.eq(_, cur), Cl.walk(f, ss, cur, Cl.step_of(ss, b))) == Some{List.append(&2, Cl.Op, o, CallLift.chain_ops(more, ss, y))} : Maybe<&2, List<&2, Cl.Op>>}
  %eb : {Cl.walk.join(o, String.eq(y, cur), Cl.walk(f, ss, cur, Cl.step_of(ss, _))) == Some{List.append(&2, Cl.Op, o, CallLift.chain_ops(more, ss, y))} : Maybe<&2, List<&2, Cl.Op>>}
  cll.wc.at(String.eq(y, cur), o, f, ss, cur, y, more, LLogicBool.wr_and_r(String.eq(b, y), CallLift.chain_ok.after(String.eq(y, cur), more, CallLift.chain_ok(more, ss, y, cur)), h), ih)

# the step m the walk takes from the chain's last rev
def cll.wc.m(m: Maybe<&2, Cl.Step>, -f: Nat, +ss: List<&2, Cl.Step>, +cur: String, +y: String, +more: List<&2, String>, h: {Bool.and(CallLift.goes_to(m, y), CallLift.chain_ok.after(String.eq(y, cur), more, CallLift.chain_ok(more, ss, y, cur))) == True{} : Bool}, ih: {CallLift.chain_ok(more, ss, y, cur) == True{} : Bool} -> {Cl.walk(f, ss, cur, Cl.step_of(ss, y)) == Some{CallLift.chain_ops(more, ss, y)} : Maybe<&2, List<&2, Cl.Op>>}) -> {Cl.walk(1n+f, ss, cur, m) == Some{List.append(&2, Cl.Op, CallLift.ops_at(m), CallLift.chain_ops(more, ss, y))} : Maybe<&2, List<&2, Cl.Op>>}:
  match m:
    case None{}:
      LStg.stg.absurd({Cl.walk(1n+f, ss, cur, None{}) == Some{List.append(&2, Cl.Op, CallLift.ops_at(None{}), CallLift.chain_ops(more, ss, y))} : Maybe<&2, List<&2, Cl.Op>>}, Equal.sym(Bool, False{}, True{}, h))
    case Some{st}:
      match st:
        case Cl.Step{+a, +b, +o}:
          cll.wc.step(a, b, o, f, ss, cur, y, more, h, ih)

# a chain of revs ys from x, of at most fuel revs, is what the walk follows
# from the step leaving x: the walk answers the chain's ops
def cll.walk_chain(ys: List<&2, String>, fuel: Nat, +ss: List<&2, Cl.Step>, +cur: String, +x: String, ch: {CallLift.chain_ok(ys, ss, x, cur) == True{} : Bool}, sh: {CallLift.at_most(ys, fuel) == True{} : Bool}) -> {Cl.walk(fuel, ss, cur, Cl.step_of(ss, x)) == Some{CallLift.chain_ops(ys, ss, x)} : Maybe<&2, List<&2, Cl.Op>>}:
  match ys:
    case Nil{}:
      LStg.stg.absurd({Cl.walk(fuel, ss, cur, Cl.step_of(ss, x)) == Some{CallLift.chain_ops(Nil{}, ss, x)} : Maybe<&2, List<&2, Cl.Op>>}, Equal.sym(Bool, False{}, True{}, ch))
    case Con{+y, +more}:
      match fuel:
        case 0n:
          LStg.stg.absurd({Cl.walk(0n, ss, cur, Cl.step_of(ss, x)) == Some{CallLift.chain_ops(Con{y, more}, ss, x)} : Maybe<&2, List<&2, Cl.Op>>}, Equal.sym(Bool, False{}, True{}, sh))
        case 1n+f:
          cll.wc.m(Cl.step_of(ss, x), f, ss, cur, y, more, ch, h => cll.walk_chain(more, f, ss, cur, y, h, sh))

# The stored arguments
# --------------------

def cll.kept_stored(ks: List<&2, String>, +i: Nat) -> {CallLift.stored(ks, i) == Cl.kept(ks, i) : List<&2, Cl.Arg>}:
  match ks:
    case Nil{}:
      {==}
    case Con{k, rest}:
      %cll.kept_stored(rest, 1n+i) : {Con{Cl.Kept{i, k}, CallLift.stored(rest, 1n+i)} == Con{Cl.Kept{i, k}, _} : List<&2, Cl.Arg>}
      {==}

def cll.done_as(-cur: String, st: Cl.St) -> {Cl.lift.done(cur, st) == CallLift.lifted_as(cur, st) : Cl.Lift}:
  match st:
    case Cl.St{a, rs}:
      {==}
