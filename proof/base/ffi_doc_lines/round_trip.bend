# eukhe: the round trips of the projection decoder (bend/ffi_doc_lines.bend
# get_proj, get_line, get_mend, get_end) against the spec spellers
# (laws/base.bend proj_spell*), used by lines_entry_answers and
# rows_entry_answers

import Base
import ../../../bend/doc_lines.bend as Dl
import ../../../bend/ffi_doc_lines.bend as Fdl
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../logic/bool.bend as LLogicBool
import ../wire.bend as LWire
import ../../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip

# an ending the spec spells reads back
def fdlrt_end(e: Dl.End, +rest: String) -> {Fdl.get_end(LawsBase.proj_spell_end(e, rest)) == Wr.Got{e, rest} : Wr.Dec<Dl.End>}:
  match e:
    case Dl.Lf{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, {==})) : {Fdl.get_end.tag(_) == Wr.Got{Dl.Lf{}, rest} : Wr.Dec<Dl.End>}
      {==}
    case Dl.CrLf{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, rest)), Wr.Got{1n, rest}, Wire.wire_nat_round_trip(1n, rest, {==})) : {Fdl.get_end.tag(_) == Wr.Got{Dl.CrLf{}, rest} : Wr.Dec<Dl.End>}
      {==}

# a line's own ending the spec spells reads back
def fdlrt_mend(o: Maybe<&2, Dl.End>, +rest: String) -> {Fdl.get_mend(LawsBase.proj_spell_mend(o, rest)) == Wr.Got{o, rest} : Wr.Dec<Maybe<&2, Dl.End>>}:
  match o:
    case None{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, {==})) : {Fdl.get_mend.tag(_) == Wr.Got{None{}, rest} : Wr.Dec<Maybe<&2, Dl.End>>}
      {==}
    case Some{+e}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, LawsBase.proj_spell_end(e, rest))), Wr.Got{1n, LawsBase.proj_spell_end(e, rest)}, Wire.wire_nat_round_trip(1n, LawsBase.proj_spell_end(e, rest), {==})) : {Fdl.get_mend.tag(_) == Wr.Got{Some{e}, rest} : Wr.Dec<Maybe<&2, Dl.End>>}
      %Equal.sym(Wr.Dec<Dl.End>, Fdl.get_end(LawsBase.proj_spell_end(e, rest)), Wr.Got{e, rest}, fdlrt_end(e, rest)) : {Fdl.get_mend.some(_) == Wr.Got{Some{e}, rest} : Wr.Dec<Maybe<&2, Dl.End>>}
      {==}

# a line whose length fits (the head of a list that fits) reads back
def fdlrt_line(l: Dl.Line, -t: List<&2, Dl.Line>, +rest: String, h: {LawsBase.proj_lines_fit(l <> t) == True{} : Bool}) -> {Fdl.get_line(LawsBase.proj_spell_line(l, rest)) == Wr.Got{l, rest} : Wr.Dec<Dl.Line>}:
  match l:
    case Dl.Line{+n, +en}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, LawsBase.proj_spell_mend(en, rest))), Wr.Got{n, LawsBase.proj_spell_mend(en, rest)}, Wire.wire_nat_round_trip(n, LawsBase.proj_spell_mend(en, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(n), LawsBase.proj_lines_fit(t), h))) : {Fdl.get_line.len(_) == Wr.Got{Dl.Line{n, en}, rest} : Wr.Dec<Dl.Line>}
      %Equal.sym(Wr.Dec<Maybe<&2, Dl.End>>, Fdl.get_mend(LawsBase.proj_spell_mend(en, rest)), Wr.Got{en, rest}, fdlrt_mend(en, rest)) : {Fdl.get_line.end(n, _) == Wr.Got{Dl.Line{n, en}, rest} : Wr.Dec<Dl.Line>}
      {==}

# the tail of a list of lines that fits fits
def fdlrt_tail(l: Dl.Line, -t: List<&2, Dl.Line>, h: {LawsBase.proj_lines_fit(l <> t) == True{} : Bool}) -> {LawsBase.proj_lines_fit(t) == True{} : Bool}:
  match l:
    case Dl.Line{+n, en}:
      LLogicBool.wr_and_r(LawsBase.wire_fits(n), LawsBase.proj_lines_fit(t), h)

# the items the spec spells for a list of lines, then rest
def fdlrt_items(xs: List<&2, Dl.Line>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      LawsBase.proj_spell_line(x, fdlrt_items(t, rest))

# the list loop of the spec speller is the count and the items
def fdlrt_go(xs: List<&2, Dl.Line>, -rest: String) -> {Wr.put_list.go(~Dl.Line, ~LawsBase.proj_spell_line, xs, rest) == (List.length(&2, Dl.Line, xs), fdlrt_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Dl.Line, ~LawsBase.proj_spell_line, t, rest), (List.length(&2, Dl.Line, t), fdlrt_items(t, rest)), fdlrt_go(t, rest)) : {Wr.put_list.step(~Dl.Line, ~LawsBase.proj_spell_line, x, _) == (1n+List.length(&2, Dl.Line, t), LawsBase.proj_spell_line(x, fdlrt_items(t, rest))) : Nat & String}
      {==}

# the spec spelling of a list of lines is its count, then its items
def fdlrt_put(+xs: List<&2, Dl.Line>, -rest: String) -> {Wr.put_list(~Dl.Line, ~LawsBase.proj_spell_line, xs, rest) == Wr.put_nat(List.length(&2, Dl.Line, xs), fdlrt_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Dl.Line, ~LawsBase.proj_spell_line, xs, rest), (List.length(&2, Dl.Line, xs), fdlrt_items(xs, rest)), fdlrt_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Dl.Line, xs), fdlrt_items(xs, rest)) : String}
  {==}

# the decoder's loop reads back the items of a list that fits
def fdlrt_loop(+t: List<&2, Dl.Line>, +x: Dl.Line, +rest: String, +hf: {LawsBase.proj_lines_fit(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Dl.Line, ~Fdl.get_line, List.length(&2, Dl.Line, t), Fdl.get_line(LawsBase.proj_spell_line(x, fdlrt_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Dl.Line>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Dl.Line>, Fdl.get_line(LawsBase.proj_spell_line(x, rest)), Wr.Got{x, rest}, fdlrt_line(x, Nil{}, rest, hf)) : {Wr.get_list.go(~Dl.Line, ~Fdl.get_line, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Dl.Line>>}
      {==}
    case Con{+y, +u}:
      +r2 = LawsBase.proj_spell_line(y, fdlrt_items(u, rest))
      %Equal.sym(Wr.Dec<Dl.Line>, Fdl.get_line(LawsBase.proj_spell_line(x, r2)), Wr.Got{x, r2}, fdlrt_line(x, y <> u, r2, hf)) : {Wr.get_list.go(~Dl.Line, ~Fdl.get_line, 1n+List.length(&2, Dl.Line, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Dl.Line>>}
      %Equal.sym(Wr.Dec<List<&2, Dl.Line>>, Wr.get_list.go(~Dl.Line, ~Fdl.get_line, List.length(&2, Dl.Line, u), Fdl.get_line(r2)), Wr.Got{y <> u, rest}, fdlrt_loop(u, y, rest, fdlrt_tail(x, y <> u, hf))) : {Wr.get_list.cons(Dl.Line, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Dl.Line>>}
      {==}

# a list of lines that fits reads back
def fdlrt_lines(+xs: List<&2, Dl.Line>, +rest: String, hl: {LawsBase.wire_fits(List.length(&2, Dl.Line, xs)) == True{} : Bool}, hi: {LawsBase.proj_lines_fit(xs) == True{} : Bool}) -> {Wr.get_list(~Dl.Line, ~Fdl.get_line, Wr.put_list(~Dl.Line, ~LawsBase.proj_spell_line, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Dl.Line>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, hl)) : {Wr.get_list.start(~Dl.Line, ~Fdl.get_line, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Dl.Line>>}
      {==}
    case Con{+x, +t}:
      +items = fdlrt_items(x <> t, rest)
      %Equal.sym(String, Wr.put_list(~Dl.Line, ~LawsBase.proj_spell_line, x <> t, rest), Wr.put_nat(List.length(&2, Dl.Line, x <> t), items), fdlrt_put(x <> t, rest)) : {Wr.get_list(~Dl.Line, ~Fdl.get_line, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Dl.Line>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Dl.Line, x <> t), items)), Wr.Got{List.length(&2, Dl.Line, x <> t), items}, Wire.wire_nat_round_trip(List.length(&2, Dl.Line, x <> t), items, hl)) : {Wr.get_list.start(~Dl.Line, ~Fdl.get_line, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Dl.Line>>}
      fdlrt_loop(t, x, rest, hi)

# a projection whose numbers fit reads back
def fdlrt_proj(p: Dl.Proj, +rest: String, +h: {LawsBase.proj_fits(p) == True{} : Bool}) -> {Fdl.get_proj(LawsBase.proj_spell(p, rest)) == Wr.Got{p, rest} : Wr.Dec<Dl.Proj>}:
  match p:
    case Dl.Proj{+b, +ls}:
      +body = Wr.put_list(~Dl.Line, ~LawsBase.proj_spell_line, ls, rest)
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(b, body)), Wr.Got{b, body}, Wire.wire_bool_round_trip(b, body)) : {Fdl.get_proj.bom(_) == Wr.Got{Dl.Proj{b, ls}, rest} : Wr.Dec<Dl.Proj>}
      %Equal.sym(Wr.Dec<List<&2, Dl.Line>>, Wr.get_list(~Dl.Line, ~Fdl.get_line, body), Wr.Got{ls, rest}, fdlrt_lines(ls, rest, LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Dl.Line, ls)), LawsBase.proj_lines_fit(ls), h), LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Dl.Line, ls)), LawsBase.proj_lines_fit(ls), h))) : {Fdl.get_proj.lines(b, _) == Wr.Got{Dl.Proj{b, ls}, rest} : Wr.Dec<Dl.Proj>}
      {==}
