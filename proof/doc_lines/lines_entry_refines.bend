# eukhe: the proof of LAW lines_entry_refines

import Base
import ../../bend/doc_lines.bend as Dl
import ../../bend/ffi_doc_lines.bend as Fdl
import ../../bend/wire.bend as Wr
import ../../laws/doc_lines.bend as DocLines
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire

# ==== lines codec ====

# an ending reads back
def fln_end(e: Dl.End, +rest: String) -> {Fdl.get_end(Fdl.put_end(e, rest)) == Wr.Got{e, rest} : Wr.Dec<Dl.End>}:
  match e:
    case Dl.Lf{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, {==})) : {Fdl.get_end.tag(_) == Wr.Got{Dl.Lf{}, rest} : Wr.Dec<Dl.End>}
      {==}
    case Dl.CrLf{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, rest)), Wr.Got{1n, rest}, Wire.wire_nat_round_trip(1n, rest, {==})) : {Fdl.get_end.tag(_) == Wr.Got{Dl.CrLf{}, rest} : Wr.Dec<Dl.End>}
      {==}

# the ending of a line's origin reads back
def fln_mend(o: Maybe<&2, Dl.End>, +rest: String) -> {Fdl.get_mend(Fdl.put_mend(o, rest)) == Wr.Got{o, rest} : Wr.Dec<Maybe<&2, Dl.End>>}:
  match o:
    case None{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, {==})) : {Fdl.get_mend.tag(_) == Wr.Got{None{}, rest} : Wr.Dec<Maybe<&2, Dl.End>>}
      {==}
    case Some{+e}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, Fdl.put_end(e, rest))), Wr.Got{1n, Fdl.put_end(e, rest)}, Wire.wire_nat_round_trip(1n, Fdl.put_end(e, rest), {==})) : {Fdl.get_mend.tag(_) == Wr.Got{Some{e}, rest} : Wr.Dec<Maybe<&2, Dl.End>>}
      %Equal.sym(Wr.Dec<Dl.End>, Fdl.get_end(Fdl.put_end(e, rest)), Wr.Got{e, rest}, fln_end(e, rest)) : {Fdl.get_mend.some(_) == Wr.Got{Some{e}, rest} : Wr.Dec<Maybe<&2, Dl.End>>}
      {==}

# a run reads back
def fln_run(r: Dl.Run, +rest: String, h: {DocLines.lines.RunFit(r) == True{} : Bool}) -> {Fdl.get_run(Fdl.put_run(r, rest)) == Wr.Got{r, rest} : Wr.Dec<Dl.Run>}:
  match r:
    case Dl.Run{+o, +n}:
      %Equal.sym(Wr.Dec<Maybe<&2, Dl.End>>, Fdl.get_mend(Fdl.put_mend(o, Wr.put_nat(n, rest))), Wr.Got{o, Wr.put_nat(n, rest)}, fln_mend(o, Wr.put_nat(n, rest))) : {Fdl.get_run.end(_) == Wr.Got{Dl.Run{o, n}, rest} : Wr.Dec<Dl.Run>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h)) : {Fdl.get_run.n(o, _) == Wr.Got{Dl.Run{o, n}, rest} : Wr.Dec<Dl.Run>}
      {==}

def fln_runs_items(xs: List<&2, Dl.Run>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      Fdl.put_run(x, fln_runs_items(t, rest))

def fln_runs_go(xs: List<&2, Dl.Run>, -rest: String) -> {Wr.put_list.go(~Dl.Run, ~Fdl.put_run, xs, rest) == (List.length(&2, Dl.Run, xs), fln_runs_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Dl.Run, ~Fdl.put_run, t, rest), (List.length(&2, Dl.Run, t), fln_runs_items(t, rest)), fln_runs_go(t, rest)) : {Wr.put_list.step(~Dl.Run, ~Fdl.put_run, x, _) == (1n+List.length(&2, Dl.Run, t), Fdl.put_run(x, fln_runs_items(t, rest))) : Nat & String}
      {==}

def fln_runs_put(+xs: List<&2, Dl.Run>, -rest: String) -> {Wr.put_list(~Dl.Run, ~Fdl.put_run, xs, rest) == Wr.put_nat(List.length(&2, Dl.Run, xs), fln_runs_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Dl.Run, ~Fdl.put_run, xs, rest), (List.length(&2, Dl.Run, xs), fln_runs_items(xs, rest)), fln_runs_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Dl.Run, xs), fln_runs_items(xs, rest)) : String}
  {==}

def fln_runs_loop(+t: List<&2, Dl.Run>, +x: Dl.Run, +rest: String, +hf: {DocLines.lines.RunsFit(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Dl.Run, ~Fdl.get_run, List.length(&2, Dl.Run, t), Fdl.get_run(Fdl.put_run(x, fln_runs_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Dl.Run>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Dl.Run>, Fdl.get_run(Fdl.put_run(x, rest)), Wr.Got{x, rest}, fln_run(x, rest, LLogicBool.wr_and_l(DocLines.lines.RunFit(x), True{}, hf))) : {Wr.get_list.go(~Dl.Run, ~Fdl.get_run, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Dl.Run>>}
      {==}
    case Con{+y, +u}:
      +r2 = Fdl.put_run(y, fln_runs_items(u, rest))
      %Equal.sym(Wr.Dec<Dl.Run>, Fdl.get_run(Fdl.put_run(x, r2)), Wr.Got{x, r2}, fln_run(x, r2, LLogicBool.wr_and_l(DocLines.lines.RunFit(x), DocLines.lines.RunsFit(y <> u), hf))) : {Wr.get_list.go(~Dl.Run, ~Fdl.get_run, 1n+List.length(&2, Dl.Run, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Dl.Run>>}
      %Equal.sym(Wr.Dec<List<&2, Dl.Run>>, Wr.get_list.go(~Dl.Run, ~Fdl.get_run, List.length(&2, Dl.Run, u), Fdl.get_run(r2)), Wr.Got{y <> u, rest}, fln_runs_loop(u, y, rest, LLogicBool.wr_and_r(DocLines.lines.RunFit(x), DocLines.lines.RunsFit(y <> u), hf))) : {Wr.get_list.cons(Dl.Run, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Dl.Run>>}
      {==}

# a list of runs reads back
def fln_runs(+xs: List<&2, Dl.Run>, +rest: String, hl: {LawsBase.wire_fits(List.length(&2, Dl.Run, xs)) == True{} : Bool}, hi: {DocLines.lines.RunsFit(xs) == True{} : Bool}) -> {Wr.get_list(~Dl.Run, ~Fdl.get_run, Wr.put_list(~Dl.Run, ~Fdl.put_run, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Dl.Run>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, hl)) : {Wr.get_list.start(~Dl.Run, ~Fdl.get_run, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Dl.Run>>}
      {==}
    case Con{+x, +t}:
      +items = fln_runs_items(x <> t, rest)
      %Equal.sym(String, Wr.put_list(~Dl.Run, ~Fdl.put_run, x <> t, rest), Wr.put_nat(List.length(&2, Dl.Run, x <> t), items), fln_runs_put(x <> t, rest)) : {Wr.get_list(~Dl.Run, ~Fdl.get_run, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Dl.Run>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Dl.Run, x <> t), items)), Wr.Got{List.length(&2, Dl.Run, x <> t), items}, Wire.wire_nat_round_trip(List.length(&2, Dl.Run, x <> t), items, hl)) : {Wr.get_list.start(~Dl.Run, ~Fdl.get_run, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Dl.Run>>}
      fln_runs_loop(t, x, rest, hi)

# the entry reads a request back and answers the model's separators
def fln_entry(+rs: List<&2, Dl.Run>, +c: Dl.End, +h: {DocLines.lines.WireFits(rs) == True{} : Bool}) -> {Fdl.ffi(Fdl.put_req(rs, c, "")) == Wr.put_list(~Dl.Seps, ~Fdl.put_seps, Dl.plan(rs, c), "") : String}:
  +tail = Fdl.put_end(c, "")
  %Equal.sym(Wr.Dec<List<&2, Dl.Run>>, Wr.get_list(~Dl.Run, ~Fdl.get_run, Wr.put_list(~Dl.Run, ~Fdl.put_run, rs, tail)), Wr.Got{rs, tail}, fln_runs(rs, tail, LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Dl.Run, rs)), DocLines.lines.RunsFit(rs), h), LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Dl.Run, rs)), DocLines.lines.RunsFit(rs), h))) : {Fdl.run.runs(_, Wr.put_list(~Dl.Run, ~Fdl.put_run, rs, tail)) == Wr.put_list(~Dl.Seps, ~Fdl.put_seps, Dl.plan(rs, c), "") : String}
  %Equal.sym(Wr.Dec<Dl.End>, Fdl.get_end(tail), Wr.Got{c, ""}, fln_end(c, "")) : {Fdl.run.carry(rs, _) == Wr.put_list(~Dl.Seps, ~Fdl.put_seps, Dl.plan(rs, c), "") : String}
  {==}

def DocLines.lines_entry_refines(rs, c, h):
  fln_entry(rs, c, h)
