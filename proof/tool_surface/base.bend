# eukhe: lemmas the proofs of area tool_surface share

import Base
import ../../bend/ffi_tool_surface.bend as FTs
import ../../bend/tools.bend as Tl
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tool_surface.bend as ToolSurface
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire

# The entry reads every input as the laws' reader does
# -----------------------------------------------------

def ts.build_version(ps: List<&2, Nat>, r: Wr.Dec<Nat>) -> {ToolSurface.read_build.version(ps, r) == FTs.get_build.version(ps, r) : Wr.Dec<FTs.Req>}:
  match r:
    case Wr.Got{v, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ts.build(r: Wr.Dec<List<&2, Nat>>) -> {ToolSurface.read_build(r) == FTs.get_build(r) : Wr.Dec<FTs.Req>}:
  match r:
    case Wr.Got{ps, s}:
      ts.build_version(ps, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def ts.join_t(d: List<&2, Nat>, r: Wr.Dec<Nat>) -> {ToolSurface.read_join.t(d, r) == FTs.get_join.t(d, r) : Wr.Dec<FTs.Req>}:
  match r:
    case Wr.Got{t, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ts.join(r: Wr.Dec<List<&2, Nat>>) -> {ToolSurface.read_join(r) == FTs.get_join(r) : Wr.Dec<FTs.Req>}:
  match r:
    case Wr.Got{d, s}:
      ts.join_t(d, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def ts.quit_t(d: List<&2, Nat>, r: Wr.Dec<Nat>) -> {ToolSurface.read_quit.t(d, r) == FTs.get_quit.t(d, r) : Wr.Dec<FTs.Req>}:
  match r:
    case Wr.Got{t, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ts.quit(r: Wr.Dec<List<&2, Nat>>) -> {ToolSurface.read_quit(r) == FTs.get_quit(r) : Wr.Dec<FTs.Req>}:
  match r:
    case Wr.Got{d, s}:
      ts.quit_t(d, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def ts.reach_t(d: List<&2, Nat>, r: Wr.Dec<Nat>) -> {ToolSurface.read_reach.t(d, r) == FTs.get_reach.t(d, r) : Wr.Dec<FTs.Req>}:
  match r:
    case Wr.Got{t, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ts.reach(r: Wr.Dec<List<&2, Nat>>) -> {ToolSurface.read_reach(r) == FTs.get_reach(r) : Wr.Dec<FTs.Req>}:
  match r:
    case Wr.Got{d, s}:
      ts.reach_t(d, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def ts.tag(t: Nat, s: String) -> {ToolSurface.read_req.tag(t, s) == FTs.get_req.tag(t, s) : Wr.Dec<FTs.Req>}:
  match t:
    case 0n:
      ts.build(Wr.get_list(~Nat, ~Wr.get_nat, s))
    case 1n:
      ts.join(Wr.get_list(~Nat, ~Wr.get_nat, s))
    case 2n:
      ts.quit(Wr.get_list(~Nat, ~Wr.get_nat, s))
    case 3n:
      ts.reach(Wr.get_list(~Nat, ~Wr.get_nat, s))
    case 4n+u:
      {==}

def ts.go(r: Wr.Dec<Nat>) -> {ToolSurface.read_req.go(r) == FTs.get_req.go(r) : Wr.Dec<FTs.Req>}:
  match r:
    case Wr.Got{t, s}:
      ts.tag(t, s)
    case Wr.Bad{}:
      {==}

def ts.req(s: String) -> {ToolSurface.read_req(s) == FTs.get_req(s) : Wr.Dec<FTs.Req>}:
  ts.go(Wr.get_nat(s))

# The entry answers as the laws spell the model's decision
# --------------------------------------------------------

def ts.schema(x: Tl.Schema) -> {FTs.put_schema(x) == ToolSurface.spell_schema(x) : String}:
  match x:
    case Tl.Schema{ps, v}:
      {==}

def ts.reply(q: FTs.Req) -> {FTs.answer(q) == ToolSurface.spell_answer(q) : String}:
  match q:
    case FTs.QBuild{+ps, +v}:
      ts.schema(Tl.build(Tl.Schema{ps, v}))
    case FTs.QJoin{d, t}:
      {==}
    case FTs.QQuit{d, t}:
      {==}
    case FTs.QReach{d, t}:
      {==}

def ts.end(b: Bool, q: FTs.Req) -> {FTs.run.end(b, q) == ToolSurface.spec.end(b, q) : String}:
  match b:
    case True{}:
      ts.reply(q)
    case False{}:
      {==}

def ts.run(r: Wr.Dec<FTs.Req>) -> {FTs.run(r) == ToolSurface.spec.run(r) : String}:
  match r:
    case Wr.Got{q, s}:
      ts.end(Wr.end(s), q)
    case Wr.Bad{}:
      {==}

def ts.exact(+s: String) -> {FTs.ffi(s) == ToolSurface.spec(s) : String}:
  %ts.req(s) : {FTs.run(_) == ToolSurface.spec(s) : String}
  ts.run(ToolSurface.read_req(s))

# The reader reads back what Rust writes
# --------------------------------------

def ts.rt_build(+ps: List<&2, Nat>, +v: Nat, +rest: String, +fits: {ToolSurface.req_fits(FTs.QBuild{ps, v}) == True{} : Bool}) -> {ToolSurface.read_req(ToolSurface.spell_req(FTs.QBuild{ps, v}, rest)) == Wr.Got{FTs.QBuild{ps, v}, rest} : Wr.Dec<FTs.Req>}:
  +hl = LLogicBool.wr_and_l(ToolSurface.ns_fit(ps), LawsBase.wire_fits(v), fits)
  +hn = LLogicBool.wr_and_r(ToolSurface.ns_fit(ps), LawsBase.wire_fits(v), fits)
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, ToolSurface.spell_ns(ps, Wr.put_nat(v, rest))), Wr.Got{ps, Wr.put_nat(v, rest)}, Wire.wire_list_round_trip(ps, Wr.put_nat(v, rest), hl)) : {ToolSurface.read_build(_) == Wr.Got{FTs.QBuild{ps, v}, rest} : Wr.Dec<FTs.Req>}
  %LWire.pw6.nat(v, rest, hn) : {ToolSurface.read_build.version(ps, _) == Wr.Got{FTs.QBuild{ps, v}, rest} : Wr.Dec<FTs.Req>}
  {==}

def ts.rt_join(+d: List<&2, Nat>, +t: Nat, +rest: String, +fits: {ToolSurface.req_fits(FTs.QJoin{d, t}) == True{} : Bool}) -> {ToolSurface.read_req(ToolSurface.spell_req(FTs.QJoin{d, t}, rest)) == Wr.Got{FTs.QJoin{d, t}, rest} : Wr.Dec<FTs.Req>}:
  +hl = LLogicBool.wr_and_l(ToolSurface.ns_fit(d), LawsBase.wire_fits(t), fits)
  +hn = LLogicBool.wr_and_r(ToolSurface.ns_fit(d), LawsBase.wire_fits(t), fits)
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, ToolSurface.spell_ns(d, Wr.put_nat(t, rest))), Wr.Got{d, Wr.put_nat(t, rest)}, Wire.wire_list_round_trip(d, Wr.put_nat(t, rest), hl)) : {ToolSurface.read_join(_) == Wr.Got{FTs.QJoin{d, t}, rest} : Wr.Dec<FTs.Req>}
  %LWire.pw6.nat(t, rest, hn) : {ToolSurface.read_join.t(d, _) == Wr.Got{FTs.QJoin{d, t}, rest} : Wr.Dec<FTs.Req>}
  {==}

def ts.rt_quit(+d: List<&2, Nat>, +t: Nat, +rest: String, +fits: {ToolSurface.req_fits(FTs.QQuit{d, t}) == True{} : Bool}) -> {ToolSurface.read_req(ToolSurface.spell_req(FTs.QQuit{d, t}, rest)) == Wr.Got{FTs.QQuit{d, t}, rest} : Wr.Dec<FTs.Req>}:
  +hl = LLogicBool.wr_and_l(ToolSurface.ns_fit(d), LawsBase.wire_fits(t), fits)
  +hn = LLogicBool.wr_and_r(ToolSurface.ns_fit(d), LawsBase.wire_fits(t), fits)
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, ToolSurface.spell_ns(d, Wr.put_nat(t, rest))), Wr.Got{d, Wr.put_nat(t, rest)}, Wire.wire_list_round_trip(d, Wr.put_nat(t, rest), hl)) : {ToolSurface.read_quit(_) == Wr.Got{FTs.QQuit{d, t}, rest} : Wr.Dec<FTs.Req>}
  %LWire.pw6.nat(t, rest, hn) : {ToolSurface.read_quit.t(d, _) == Wr.Got{FTs.QQuit{d, t}, rest} : Wr.Dec<FTs.Req>}
  {==}

def ts.rt_reach(+d: List<&2, Nat>, +t: Nat, +rest: String, +fits: {ToolSurface.req_fits(FTs.QReach{d, t}) == True{} : Bool}) -> {ToolSurface.read_req(ToolSurface.spell_req(FTs.QReach{d, t}, rest)) == Wr.Got{FTs.QReach{d, t}, rest} : Wr.Dec<FTs.Req>}:
  +hl = LLogicBool.wr_and_l(ToolSurface.ns_fit(d), LawsBase.wire_fits(t), fits)
  +hn = LLogicBool.wr_and_r(ToolSurface.ns_fit(d), LawsBase.wire_fits(t), fits)
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, ToolSurface.spell_ns(d, Wr.put_nat(t, rest))), Wr.Got{d, Wr.put_nat(t, rest)}, Wire.wire_list_round_trip(d, Wr.put_nat(t, rest), hl)) : {ToolSurface.read_reach(_) == Wr.Got{FTs.QReach{d, t}, rest} : Wr.Dec<FTs.Req>}
  %LWire.pw6.nat(t, rest, hn) : {ToolSurface.read_reach.t(d, _) == Wr.Got{FTs.QReach{d, t}, rest} : Wr.Dec<FTs.Req>}
  {==}

def ts.rt(q: FTs.Req, +rest: String, fits: {ToolSurface.req_fits(q) == True{} : Bool}) -> {ToolSurface.read_req(ToolSurface.spell_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FTs.Req>}:
  match q:
    case FTs.QBuild{ps, v}:
      ts.rt_build(ps, v, rest, fits)
    case FTs.QJoin{d, t}:
      ts.rt_join(d, t, rest, fits)
    case FTs.QQuit{d, t}:
      ts.rt_quit(d, t, rest, fits)
    case FTs.QReach{d, t}:
      ts.rt_reach(d, t, rest, fits)
