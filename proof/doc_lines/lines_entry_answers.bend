# eukhe: the proof of LAW lines_entry_answers

import Base
import ../../bend/doc_lines.bend as Dl
import ../../bend/ffi_doc_lines.bend as Fdl
import ../../bend/wire.bend as Wr
import ../../laws/doc_lines.bend as DocLines
import ../../laws/base.bend as LawsBase
import ../base/logic/bool.bend as LLogicBool
import ../base/ffi_doc_lines/round_trip.bend as LFdlRoundTrip
import ./lines_entry_refines.bend as PLinesEntryRefines

# ==== the spec spellers are the codec's ====

# an ending: put_end is the spec's
def lea_end(e: Dl.End, -rest: String) -> {Fdl.put_end(e, rest) == LawsBase.proj_spell_end(e, rest) : String}:
  match e:
    case Dl.Lf{}:
      {==}
    case Dl.CrLf{}:
      {==}

# a run: put_run is the spec's
def lea_run(r: Dl.Run, -rest: String) -> {Fdl.put_run(r, rest) == DocLines.lines.spell_run(r, rest) : String}:
  match r:
    case Dl.Run{o, n}:
      match o:
        case None{}:
          {==}
        case Some{e}:
          match e:
            case Dl.Lf{}:
              {==}
            case Dl.CrLf{}:
              {==}

# one step of the list loop over runs: put_run is the spec's
def lea_run_step(x: Dl.Run, r: Nat & String) -> {Wr.put_list.step(~Dl.Run, ~Fdl.put_run, x, r) == Wr.put_list.step(~Dl.Run, ~DocLines.lines.spell_run, x, r) : Nat & String}:
  match r:
    case (n, s):
      %lea_run(x, s) : {(1n+n, Fdl.put_run(x, s)) == (1n+n, _) : Nat & String}
      {==}

# the list loop over runs: put_run is the spec's
def lea_runs_go(xs: List<&2, Dl.Run>, +rest: String) -> {Wr.put_list.go(~Dl.Run, ~Fdl.put_run, xs, rest) == Wr.put_list.go(~Dl.Run, ~DocLines.lines.spell_run, xs, rest) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %lea_runs_go(t, rest) : {Wr.put_list.step(~Dl.Run, ~Fdl.put_run, x, Wr.put_list.go(~Dl.Run, ~Fdl.put_run, t, rest)) == Wr.put_list.step(~Dl.Run, ~DocLines.lines.spell_run, x, _) : Nat & String}
      lea_run_step(x, Wr.put_list.go(~Dl.Run, ~Fdl.put_run, t, rest))

# a list of runs: the codec's spelling is the spec's
def lea_runs(xs: List<&2, Dl.Run>, +rest: String) -> {Wr.put_list(~Dl.Run, ~Fdl.put_run, xs, rest) == Wr.put_list(~Dl.Run, ~DocLines.lines.spell_run, xs, rest) : String}:
  %lea_runs_go(xs, rest) : {Wr.put_list.fin(Wr.put_list.go(~Dl.Run, ~Fdl.put_run, xs, rest)) == Wr.put_list.fin(_) : String}
  {==}

# a separator: put_seps is the spec's
def lea_seps1(x: Dl.Seps, -rest: String) -> {Fdl.put_seps(x, rest) == DocLines.lines.spell_seps(x, rest) : String}:
  match x:
    case Dl.Seps{e, n}:
      match e:
        case Dl.Lf{}:
          {==}
        case Dl.CrLf{}:
          {==}

# one step of the list loop over separators: put_seps is the spec's
def lea_seps_step(x: Dl.Seps, r: Nat & String) -> {Wr.put_list.step(~Dl.Seps, ~Fdl.put_seps, x, r) == Wr.put_list.step(~Dl.Seps, ~DocLines.lines.spell_seps, x, r) : Nat & String}:
  match r:
    case (n, s):
      %lea_seps1(x, s) : {(1n+n, Fdl.put_seps(x, s)) == (1n+n, _) : Nat & String}
      {==}

# the list loop over separators: put_seps is the spec's
def lea_seps_go(xs: List<&2, Dl.Seps>, +rest: String) -> {Wr.put_list.go(~Dl.Seps, ~Fdl.put_seps, xs, rest) == Wr.put_list.go(~Dl.Seps, ~DocLines.lines.spell_seps, xs, rest) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %lea_seps_go(t, rest) : {Wr.put_list.step(~Dl.Seps, ~Fdl.put_seps, x, Wr.put_list.go(~Dl.Seps, ~Fdl.put_seps, t, rest)) == Wr.put_list.step(~Dl.Seps, ~DocLines.lines.spell_seps, x, _) : Nat & String}
      lea_seps_step(x, Wr.put_list.go(~Dl.Seps, ~Fdl.put_seps, t, rest))

# a list of separators: the codec's spelling is the spec's
def lea_seps(xs: List<&2, Dl.Seps>, +rest: String) -> {Wr.put_list(~Dl.Seps, ~Fdl.put_seps, xs, rest) == Wr.put_list(~Dl.Seps, ~DocLines.lines.spell_seps, xs, rest) : String}:
  %lea_seps_go(xs, rest) : {Wr.put_list.fin(Wr.put_list.go(~Dl.Seps, ~Fdl.put_seps, xs, rest)) == Wr.put_list.fin(_) : String}
  {==}

# what a write keeps: put_kept is the spec's
def lea_kept(k: Dl.Kept) -> {Fdl.put_kept(k) == DocLines.lines.spell_kept(k) : String}:
  match k:
    case Dl.Kept{b, e, w}:
      match e:
        case Dl.Lf{}:
          {==}
        case Dl.CrLf{}:
          {==}

# ==== the requests ====

# a plan: the spec's request is put_req, answered by lines_entry_refines
def lea_plan(+rs: List<&2, Dl.Run>, +c: Dl.End, h: {DocLines.lines.WireFits(rs) == True{} : Bool}) -> {Fdl.ffi(DocLines.lines.spell_req(DocLines.lines.Plan{rs, c})) == DocLines.lines.answer(DocLines.lines.Plan{rs, c}) : String}:
  +ans = Wr.put_list(~Dl.Seps, ~DocLines.lines.spell_seps, Dl.plan(rs, c), "")
  %lea_runs(rs, LawsBase.proj_spell_end(c, "")) : {Fdl.ffi(_) == ans : String}
  %lea_end(c, "") : {Fdl.ffi(Wr.put_list(~Dl.Run, ~Fdl.put_run, rs, _)) == ans : String}
  %Equal.sym(String, Fdl.ffi(Fdl.put_req(rs, c, "")), Wr.put_list(~Dl.Seps, ~Fdl.put_seps, Dl.plan(rs, c), ""), PLinesEntryRefines.fln_entry(rs, c, h)) : {_ == ans : String}
  lea_seps(Dl.plan(rs, c), "")

# a load: `L` is no plan, the projection reads back, the carry is spelled
def lea_load(+p: Dl.Proj, h: {LawsBase.proj_fits(p) == True{} : Bool}) -> {Fdl.ffi(DocLines.lines.spell_req(DocLines.lines.Load{p})) == DocLines.lines.answer(DocLines.lines.Load{p}) : String}:
  %Equal.sym(Wr.Dec<Dl.Proj>, Fdl.get_proj(LawsBase.proj_spell(p, "")), Wr.Got{p, ""}, LFdlRoundTrip.fdlrt_proj(p, "", h)) : {Fdl.load.run(_) == LawsBase.proj_spell_end(Dl.carry(p), "") : String}
  lea_end(Dl.carry(p), "")

# a write: `W` is no plan, both projections read back, the decision is spelled
def lea_write(+p: Dl.Proj, +q: Dl.Proj, +h: {Bool.and(LawsBase.proj_fits(p), LawsBase.proj_fits(q)) == True{} : Bool}) -> {Fdl.ffi(DocLines.lines.spell_req(DocLines.lines.Write{p, q})) == DocLines.lines.answer(DocLines.lines.Write{p, q}) : String}:
  +tail = LawsBase.proj_spell(q, "")
  +ans = DocLines.lines.spell_kept(Dl.write(p, q))
  %Equal.sym(Wr.Dec<Dl.Proj>, Fdl.get_proj(LawsBase.proj_spell(p, tail)), Wr.Got{p, tail}, LFdlRoundTrip.fdlrt_proj(p, tail, LLogicBool.wr_and_l(LawsBase.proj_fits(p), LawsBase.proj_fits(q), h))) : {Fdl.write.run(_) == ans : String}
  %Equal.sym(Wr.Dec<Dl.Proj>, Fdl.get_proj(tail), Wr.Got{q, ""}, LFdlRoundTrip.fdlrt_proj(q, "", LLogicBool.wr_and_r(LawsBase.proj_fits(p), LawsBase.proj_fits(q), h))) : {Fdl.write.next(p, _) == ans : String}
  lea_kept(Dl.write(p, q))

def DocLines.lines_entry_answers(r, h):
  match r:
    case DocLines.lines.Plan{rs, c}:
      lea_plan(rs, c, h)
    case DocLines.lines.Load{p}:
      lea_load(p, h)
    case DocLines.lines.Write{p, q}:
      lea_write(p, q, h)
