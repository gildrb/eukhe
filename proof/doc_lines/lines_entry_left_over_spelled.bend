# eukhe: the proof of LAW lines_entry_left_over_spelled
#
# PROOF: per request: the spec's runs are the entry's put_run (lea_runs),
# they and the carry read back with the rest untouched (fln_runs,
# fdlrt_end); a projection reads back likewise (fdlrt_proj); the end check
# then sees the char left and answers the error form.

import Base
import ../../bend/doc_lines.bend as Dl
import ../../bend/ffi_doc_lines.bend as Fdl
import ../../bend/wire.bend as Wr
import ../../laws/doc_lines.bend as DocLines
import ../../laws/base.bend as LawsBase
import ../base/logic/bool.bend as LLogicBool
import ../base/ffi_doc_lines/round_trip.bend as LFdlRoundTrip
import ./lines_entry_refines.bend as PLinesEntryRefines
import ./lines_entry_answers.bend as PLinesEntryAnswers

# a plan with input after it
def llo_plan(+rs: List<&2, Dl.Run>, +c: Dl.End, +h: {DocLines.lines.WireFits(rs) == True{} : Bool}, +left: String) ->
  {Fdl.ffi(DocLines.lines.spell_req_on(DocLines.lines.Plan{rs, c}, left)) == Fdl.run.done(rs, c, Wr.end(left)) : String}:
  +tail = LawsBase.proj_spell_end(c, left)
  +ans = Fdl.run.done(rs, c, Wr.end(left))
  %PLinesEntryAnswers.lea_runs(rs, tail) : {Fdl.ffi(_) == ans : String}
  %Equal.sym(Wr.Dec<List<&2, Dl.Run>>, Wr.get_list(~Dl.Run, ~Fdl.get_run, Wr.put_list(~Dl.Run, ~Fdl.put_run, rs, tail)), Wr.Got{rs, tail}, PLinesEntryRefines.fln_runs(rs, tail, LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Dl.Run, rs)), DocLines.lines.RunsFit(rs), h), LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Dl.Run, rs)), DocLines.lines.RunsFit(rs), h))) : {Fdl.run.runs(_, Wr.put_list(~Dl.Run, ~Fdl.put_run, rs, tail)) == ans : String}
  %Equal.sym(Wr.Dec<Dl.End>, Fdl.get_end(tail), Wr.Got{c, left}, LFdlRoundTrip.fdlrt_end(c, left)) : {Fdl.run.carry(rs, _) == ans : String}
  {==}

# a load with input after it
def llo_load(+p: Dl.Proj, h: {LawsBase.proj_fits(p) == True{} : Bool}, +left: String) ->
  {Fdl.ffi(DocLines.lines.spell_req_on(DocLines.lines.Load{p}, left)) == Fdl.load.done(p, Wr.end(left)) : String}:
  %Equal.sym(Wr.Dec<Dl.Proj>, Fdl.get_proj(LawsBase.proj_spell(p, left)), Wr.Got{p, left}, LFdlRoundTrip.fdlrt_proj(p, left, h)) : {Fdl.load.run(_) == Fdl.load.done(p, Wr.end(left)) : String}
  {==}

# a write with input after it
def llo_write(+p: Dl.Proj, +q: Dl.Proj, +h: {Bool.and(LawsBase.proj_fits(p), LawsBase.proj_fits(q)) == True{} : Bool}, +left: String) ->
  {Fdl.ffi(DocLines.lines.spell_req_on(DocLines.lines.Write{p, q}, left)) == Fdl.write.done(p, q, Wr.end(left)) : String}:
  +tail = LawsBase.proj_spell(q, left)
  +ans = Fdl.write.done(p, q, Wr.end(left))
  %Equal.sym(Wr.Dec<Dl.Proj>, Fdl.get_proj(LawsBase.proj_spell(p, tail)), Wr.Got{p, tail}, LFdlRoundTrip.fdlrt_proj(p, tail, LLogicBool.wr_and_l(LawsBase.proj_fits(p), LawsBase.proj_fits(q), h))) : {Fdl.write.run(_) == ans : String}
  %Equal.sym(Wr.Dec<Dl.Proj>, Fdl.get_proj(tail), Wr.Got{q, left}, LFdlRoundTrip.fdlrt_proj(q, left, LLogicBool.wr_and_r(LawsBase.proj_fits(p), LawsBase.proj_fits(q), h))) : {Fdl.write.next(p, _) == ans : String}
  {==}

def DocLines.lines_entry_left_over_spelled(r, fits, c, rest):
  match r:
    case DocLines.lines.Plan{rs, k}:
      llo_plan(rs, k, fits, SCon{c, rest})
    case DocLines.lines.Load{p}:
      llo_load(p, fits, SCon{c, rest})
    case DocLines.lines.Write{p, q}:
      llo_write(p, q, fits, SCon{c, rest})
