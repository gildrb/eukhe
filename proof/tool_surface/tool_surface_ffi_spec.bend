# eukhe: the proof of LAW tool_surface_ffi_spec
# The entry answers the laws' reader and spelled decision (LATs.ts.exact);
# that decision is the spec's (tool_surface_build_spec, _quit_spec,
# _reach_spec; a join by definition).

import Base
import ../../bend/ffi_tool_surface.bend as FTs
import ../../bend/tools.bend as Tl
import ../../bend/wire.bend as Wr
import ../../laws/tool_surface.bend as ToolSurface
import ./base.bend as LATs
import ./tool_surface_build_spec.bend as PToolSurfaceBuildSpec
import ./tool_surface_quit_spec.bend as PToolSurfaceQuitSpec
import ./tool_surface_reach_spec.bend as PToolSurfaceReachSpec

def tsf.reply(q: FTs.Req) -> {ToolSurface.spell_answer(q) == ToolSurface.ts_reply(q) : String}:
  match q:
    case FTs.QBuild{+ps, +v}:
      %ToolSurface.tool_surface_build_spec(ps, v) : {ToolSurface.spell_answer(FTs.QBuild{ps, v}) == ToolSurface.spell_schema(_) : String}
      {==}
    case FTs.QJoin{d, t}:
      {==}
    case FTs.QQuit{+d, +t}:
      %ToolSurface.tool_surface_quit_spec(Nil{}, d, Nil{}, t) : {ToolSurface.spell_answer(FTs.QQuit{d, t}) == ToolSurface.spell_ns(_, "") : String}
      {==}
    case FTs.QReach{+d, +t}:
      %ToolSurface.tool_surface_reach_spec(Nil{}, d, Nil{}, t) : {ToolSurface.spell_answer(FTs.QReach{d, t}) == Wr.put_bool(_, "") : String}
      {==}

def tsf.end(b: Bool, q: FTs.Req) -> {ToolSurface.spec.end(b, q) == ToolSurface.ts_spec.end(b, q) : String}:
  match b:
    case True{}:
      tsf.reply(q)
    case False{}:
      {==}

def tsf.run(r: Wr.Dec<FTs.Req>) -> {ToolSurface.spec.run(r) == ToolSurface.ts_spec.run(r) : String}:
  match r:
    case Wr.Got{q, s}:
      tsf.end(Wr.end(s), q)
    case Wr.Bad{}:
      {==}

def ToolSurface.tool_surface_ffi_spec(s):
  %tsf.run(ToolSurface.read_req(s)) : {FTs.ffi(s) == _ : String}
  LATs.ts.exact(s)
