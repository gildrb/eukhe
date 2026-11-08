# eukhe: lemmas of LAW dir_ffi_answers_spelled: the entry's encoders
# write the laws' spelling
#
# The entry's put_layer, put_verdict, put_out, put_end, put_loop, its
# lists and its request are the spelling of laws/director.bend
# (dir_spell_*), field by field and tag by tag. So the round trip and the
# answer of the entry's own laws (dir_ffi_round_trip, dir_ffi_is_tick)
# speak of the spelled request and reply.

import Base
import ../../../bend/director.bend as Dr
import ../../../bend/ffi_director.bend as FDr
import ../../../bend/wire.bend as Wr
import ../../../laws/director.bend as Director
import ../base.bend as LA

# a layer
def pds.layer(l: Dr.Layer, -rest: String) -> {FDr.put_layer(l, rest) == Director.dir_spell_layer(l, rest) : String}:
  match l:
    case Dr.Layer{k, b}:
      {==}

# the items of a stack
def pds.ls.items(xs: List<&2, Dr.Layer>, -rest: String) -> {LA.pdf.ls.items(xs, rest) == Director.dir_spell_layers.items(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %pds.ls.items(t, rest) : {FDr.put_layer(x, LA.pdf.ls.items(t, rest)) == Director.dir_spell_layer(x, _) : String}
      pds.layer(x, LA.pdf.ls.items(t, rest))

# a stack: its count, then its items
def pds.layers(+xs: List<&2, Dr.Layer>, -rest: String) -> {Wr.put_list(~Dr.Layer, ~FDr.put_layer, xs, rest) == Director.dir_spell_layers(xs, rest) : String}:
  %pds.ls.items(xs, rest) : {Wr.put_list(~Dr.Layer, ~FDr.put_layer, xs, rest) == Wr.put_nat(List.length(&2, Dr.Layer, xs), _) : String}
  LA.pdf.ls.put(xs, rest)

# a verdict
def pds.verdict(v: Dr.Verdict, -rest: String) -> {FDr.put_verdict(v, rest) == Director.dir_spell_verdict(v, rest) : String}:
  match v:
    case Dr.Defer{}:
      {==}
    case Dr.Again{}:
      {==}
    case Dr.Yield{}:
      {==}
    case Dr.Stack{+l}:
      %pds.layer(l, rest) : {Wr.put_nat(3n, FDr.put_layer(l, rest)) == Wr.put_nat(3n, _) : String}
      {==}
    case Dr.Leave{}:
      {==}
    case Dr.Abort{}:
      {==}
    case Dr.Lead{}:
      {==}

# the items of a list of verdicts
def pds.vs.items(xs: List<&2, Dr.Verdict>, -rest: String) -> {LA.pdf.vs.items(xs, rest) == Director.dir_spell_verdicts.items(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %pds.vs.items(t, rest) : {FDr.put_verdict(x, LA.pdf.vs.items(t, rest)) == Director.dir_spell_verdict(x, _) : String}
      pds.verdict(x, LA.pdf.vs.items(t, rest))

# a list of verdicts: its count, then its items
def pds.verdicts(+xs: List<&2, Dr.Verdict>, -rest: String) -> {Wr.put_list(~Dr.Verdict, ~FDr.put_verdict, xs, rest) == Director.dir_spell_verdicts(xs, rest) : String}:
  %pds.vs.items(xs, rest) : {Wr.put_list(~Dr.Verdict, ~FDr.put_verdict, xs, rest) == Wr.put_nat(List.length(&2, Dr.Verdict, xs), _) : String}
  LA.pdf.vs.put(xs, rest)

# how a loop ended
def pds.end(m: Maybe<&2, Dr.Out>, -rest: String) -> {FDr.put_end(m, rest) == Director.dir_spell_end(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{o}:
      match o:
        case Dr.Cont{}:
          {==}
        case Dr.Hand{}:
          {==}
        case Dr.Failed{}:
          {==}

# a loop
def pds.loop(l: Dr.Loop, +rest: String) -> {FDr.put_loop(l, rest) == Director.dir_spell_loop(l, rest) : String}:
  match l:
    case Dr.Loop{+n, +st, +e}:
      %pds.end(e, rest) : {FDr.put_loop(Dr.Loop{n, st, e}, rest) == Wr.put_nat(n, Director.dir_spell_layers(st, _)) : String}
      %pds.layers(st, FDr.put_end(e, rest)) : {FDr.put_loop(Dr.Loop{n, st, e}, rest) == Wr.put_nat(n, _) : String}
      {==}

# a request
def pds.req(q: FDr.Req, +rest: String) -> {FDr.put_req(q, rest) == Director.dir_spell_req(q, rest) : String}:
  match q:
    case FDr.Req{+c, +l, +vs}:
      %pds.verdicts(vs, rest) : {FDr.put_req(FDr.Req{c, l, vs}, rest) == Wr.put_nat(c, Director.dir_spell_loop(l, _)) : String}
      %pds.loop(l, Wr.put_list(~Dr.Verdict, ~FDr.put_verdict, vs, rest)) : {FDr.put_req(FDr.Req{c, l, vs}, rest) == Wr.put_nat(c, _) : String}
      {==}

# the entry's answer to a request is the spelled loop after the tick
def pds.answer(q: FDr.Req) -> {FDr.ffi.run(q) == Director.dir_spell_answer(q) : String}:
  match q:
    case FDr.Req{c, l, vs}:
      pds.loop(Dr.tick(c, l, vs), "")
