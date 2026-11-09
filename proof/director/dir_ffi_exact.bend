# eukhe: the proof of LAW dir_ffi_exact
# The entry's decoder reads every input as the laws' reader does, stage by
# stage (de.*, the lists through list_ext.bend); the model's step is the
# laws' step, decision by decision; the entry spells the loop as the laws'
# speller does.

import Base
import ../../bend/director.bend as Dr
import ../../bend/ffi_director.bend as FDr
import ../../bend/wire.bend as Wr
import ../../laws/director.bend as Director
import ./list_ext.bend as LX

# Reading
# -------

def de.layer_b(k: Nat, r: Wr.Dec<Nat>) -> {FDr.get_layer.b(k, r) == Director.dirr.layer.b(k, r) : Wr.Dec<Dr.Layer>}:
  match r:
    case Wr.Got{b, s}:
      {==}
    case Wr.Bad{}:
      {==}

def de.layer_k(r: Wr.Dec<Nat>) -> {FDr.get_layer.k(r) == Director.dirr.layer.k(r) : Wr.Dec<Dr.Layer>}:
  match r:
    case Wr.Got{k, +s}:
      de.layer_b(k, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def de.layer(s: String) -> {FDr.get_layer(s) == Director.dirr.layer(s) : Wr.Dec<Dr.Layer>}:
  de.layer_k(Wr.get_nat(s))

def de.verdict_stack(r: Wr.Dec<Dr.Layer>) -> {FDr.get_verdict.stack(r) == Director.dirr.verdict.stack(r) : Wr.Dec<Dr.Verdict>}:
  match r:
    case Wr.Got{l, s}:
      {==}
    case Wr.Bad{}:
      {==}

def de.verdict_tag(t: Nat, +s: String) -> {FDr.get_verdict.tag(t, s) == Director.dirr.verdict.tag(t, s) : Wr.Dec<Dr.Verdict>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      %de.layer(s) : {FDr.get_verdict.stack(FDr.get_layer(s)) == Director.dirr.verdict.stack(_) : Wr.Dec<Dr.Verdict>}
      de.verdict_stack(FDr.get_layer(s))
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n+x:
      {==}

def de.verdict_go(r: Wr.Dec<Nat>) -> {FDr.get_verdict.go(r) == Director.dirr.verdict.go(r) : Wr.Dec<Dr.Verdict>}:
  match r:
    case Wr.Got{t, +s}:
      de.verdict_tag(t, s)
    case Wr.Bad{}:
      {==}

def de.verdict(s: String) -> {FDr.get_verdict(s) == Director.dirr.verdict(s) : Wr.Dec<Dr.Verdict>}:
  de.verdict_go(Wr.get_nat(s))

def de.end_out(t: Nat, -s: String) -> {FDr.get_end.out(t, s) == Director.dirr.end.out(t, s) : Wr.Dec<Maybe<&2, Dr.Out>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n+x:
      {==}

def de.end_some(r: Wr.Dec<Nat>) -> {FDr.get_end.some(r) == Director.dirr.end.some(r) : Wr.Dec<Maybe<&2, Dr.Out>>}:
  match r:
    case Wr.Got{t, s}:
      de.end_out(t, s)
    case Wr.Bad{}:
      {==}

def de.end_tag(t: Nat, +s: String) -> {FDr.get_end.tag(t, s) == Director.dirr.end.tag(t, s) : Wr.Dec<Maybe<&2, Dr.Out>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      de.end_some(Wr.get_nat(s))
    case 2n+x:
      {==}

def de.end_go(r: Wr.Dec<Nat>) -> {FDr.get_end.go(r) == Director.dirr.end(r) : Wr.Dec<Maybe<&2, Dr.Out>>}:
  match r:
    case Wr.Got{t, +s}:
      de.end_tag(t, s)
    case Wr.Bad{}:
      {==}

def de.loop_end(n: Nat, st: List<&2, Dr.Layer>, r: Wr.Dec<Maybe<&2, Dr.Out>>) -> {FDr.get_loop.end(n, st, r) == Director.dirr.loop.end(n, st, r) : Wr.Dec<Dr.Loop>}:
  match r:
    case Wr.Got{e, s}:
      {==}
    case Wr.Bad{}:
      {==}

def de.loop_stack(+n: Nat, r: Wr.Dec<List<&2, Dr.Layer>>) -> {FDr.get_loop.stack(n, r) == Director.dirr.loop.stack(n, r) : Wr.Dec<Dr.Loop>}:
  match r:
    case Wr.Got{+st, +s}:
      %de.end_go(Wr.get_nat(s)) : {FDr.get_loop.end(n, st, FDr.get_end(s)) == Director.dirr.loop.end(n, st, _) : Wr.Dec<Dr.Loop>}
      de.loop_end(n, st, FDr.get_end(s))
    case Wr.Bad{}:
      {==}

def de.loop(r: Wr.Dec<Nat>) -> {FDr.get_loop.left(r) == Director.dirr.loop(r) : Wr.Dec<Dr.Loop>}:
  match r:
    case Wr.Got{+n, +s}:
      %LX.lx.get(~Dr.Layer, ~FDr.get_layer, ~Director.dirr.layer, ~de.layer, s) : {FDr.get_loop.stack(n, Wr.get_list(~Dr.Layer, ~FDr.get_layer, s)) == Director.dirr.loop.stack(n, _) : Wr.Dec<Dr.Loop>}
      de.loop_stack(n, Wr.get_list(~Dr.Layer, ~FDr.get_layer, s))
    case Wr.Bad{}:
      {==}

def de.req_vs(c: Nat, l: Dr.Loop, r: Wr.Dec<List<&2, Dr.Verdict>>) -> {FDr.get_req.vs(c, l, r) == Director.dirr.req.vs(c, l, r) : Wr.Dec<FDr.Req>}:
  match r:
    case Wr.Got{vs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def de.req_loop(+c: Nat, r: Wr.Dec<Dr.Loop>) -> {FDr.get_req.loop(c, r) == Director.dirr.req.loop(c, r) : Wr.Dec<FDr.Req>}:
  match r:
    case Wr.Got{+l, +s}:
      %LX.lx.get(~Dr.Verdict, ~FDr.get_verdict, ~Director.dirr.verdict, ~de.verdict, s) : {FDr.get_req.vs(c, l, Wr.get_list(~Dr.Verdict, ~FDr.get_verdict, s)) == Director.dirr.req.vs(c, l, _) : Wr.Dec<FDr.Req>}
      de.req_vs(c, l, Wr.get_list(~Dr.Verdict, ~FDr.get_verdict, s))
    case Wr.Bad{}:
      {==}

def de.req(r: Wr.Dec<Nat>) -> {FDr.get_req.cap(r) == Director.dirr.req(r) : Wr.Dec<FDr.Req>}:
  match r:
    case Wr.Got{+c, +s}:
      %de.loop(Wr.get_nat(s)) : {FDr.get_req.loop(c, FDr.get_loop(s)) == Director.dirr.req.loop(c, _) : Wr.Dec<FDr.Req>}
      de.req_loop(c, FDr.get_loop(s))
    case Wr.Bad{}:
      {==}

# The step
# --------

def de.under(l: Dr.Layer, d: Dr.Dec) -> {Dr.under(l, d) == Director.dir_on_top(l, d) : Dr.Dec}:
  match d:
    case Dr.Dec{o, s}:
      {==}

def de.again(l: Dr.Layer, -rest: List<&2, Dr.Layer>) -> {Dr.spend(l, rest) == Director.dirs.again(l, rest) : Dr.Dec}:
  match l:
    case Dr.Layer{k, b}:
      match b:
        case 0n:
          {==}
        case 1n+c:
          {==}

def de.push(l: Dr.Layer, -n: Dr.Layer, -rest: List<&2, Dr.Layer>, room: Bool) -> {Dr.push(l, n, rest, room) == Director.dirs.push(l, n, rest, room) : Dr.Dec}:
  match l:
    case Dr.Layer{k, b}:
      match b:
        case 0n:
          {==}
        case 1n+c:
          match room:
            case True{}:
              {==}
            case False{}:
              {==}

def de.lead(stay: Bool, l: Dr.Layer, d: Dr.Dec) -> {Dr.lead(stay, l, d) == Director.dirs.lead(stay, l, d) : Dr.Dec}:
  match stay:
    case True{}:
      de.under(l, d)
    case False{}:
      {==}

def de.go(s: List<&2, Dr.Layer>, vs: List<&2, Dr.Verdict>, +room: Bool, +stay: Bool) -> {Dr.decide.go(s, vs, room, stay) == Director.dirs.go(s, vs, room, stay) : Dr.Dec}:
  match s:
    case Nil{}:
      {==}
    case +l <> +rest:
      match vs:
        case Nil{}:
          %de.go(rest, Nil{}, room, stay) : {Dr.under(l, Dr.decide.go(rest, Nil{}, room, stay)) == Director.dir_on_top(l, _) : Dr.Dec}
          de.under(l, Dr.decide.go(rest, Nil{}, room, stay))
        case v <> +vr:
          match v:
            case Dr.Defer{}:
              %de.go(rest, vr, room, stay) : {Dr.under(l, Dr.decide.go(rest, vr, room, stay)) == Director.dir_on_top(l, _) : Dr.Dec}
              de.under(l, Dr.decide.go(rest, vr, room, stay))
            case Dr.Again{}:
              de.again(l, rest)
            case Dr.Yield{}:
              {==}
            case Dr.Stack{n}:
              de.push(l, n, rest, room)
            case Dr.Unstack{}:
              de.go(rest, vr, room, stay)
            case Dr.Abort{}:
              {==}
            case Dr.Lead{}:
              %de.go(rest, vr, room, stay) : {Dr.lead(stay, l, Dr.decide.go(rest, vr, room, stay)) == Director.dirs.lead(stay, l, _) : Dr.Dec}
              de.lead(stay, l, Dr.decide.go(rest, vr, room, stay))

def de.stack(d: Dr.Dec) -> {Dr.Dec.stack(d) == Director.dirs.stack(d) : List<&2, Dr.Layer>}:
  match d:
    case Dr.Dec{o, t}:
      {==}

def de.kept(+s: List<&2, Dr.Layer>, +vs: List<&2, Dr.Verdict>, +cap: Nat) -> {Dr.kept(s, vs, cap) == Director.dirs.stack(Director.dirs.decide(s, vs, cap, True{})) : List<&2, Dr.Layer>}:
  %de.go(s, vs, Nat.is_lt(List.length(&2, Dr.Layer, s), cap), True{}) : {Dr.Dec.stack(Dr.decide.go(s, vs, Nat.is_lt(List.length(&2, Dr.Layer, s), cap), True{})) == Director.dirs.stack(_) : List<&2, Dr.Layer>}
  de.stack(Dr.decide.go(s, vs, Nat.is_lt(List.length(&2, Dr.Layer, s), cap), True{}))

def de.on(n: Nat, -t: List<&2, Dr.Layer>, +s: List<&2, Dr.Layer>, +vs: List<&2, Dr.Verdict>, +cap: Nat) -> {Dr.go.on(n, t, s, vs, cap) == Director.dirs.on(n, t, s, vs, cap) : Dr.Loop}:
  match n:
    case 0n:
      %de.kept(s, vs, cap) : {Dr.Loop{0n, Dr.kept(s, vs, cap), Some{Dr.Hand{}}} == Dr.Loop{0n, _, Some{Dr.Hand{}}} : Dr.Loop}
      {==}
    case 1n+m:
      {==}

def de.settle(d: Dr.Dec, +n: Nat, +s: List<&2, Dr.Layer>, +vs: List<&2, Dr.Verdict>, +cap: Nat) -> {Dr.settle(d, n, s, vs, cap) == Director.dirs.settle(d, n, s, vs, cap) : Dr.Loop}:
  match d:
    case Dr.Dec{o, t}:
      match o:
        case Dr.Cont{}:
          de.on(n, t, s, vs, cap)
        case Dr.Hand{}:
          %de.kept(s, vs, cap) : {Dr.Loop{n, Dr.kept(s, vs, cap), Some{Dr.Hand{}}} == Dr.Loop{n, _, Some{Dr.Hand{}}} : Dr.Loop}
          {==}
        case Dr.Failed{}:
          %de.kept(s, vs, cap) : {Dr.Loop{n, Dr.kept(s, vs, cap), Some{Dr.Failed{}}} == Dr.Loop{n, _, Some{Dr.Failed{}}} : Dr.Loop}
          {==}

def de.tick(+cap: Nat, l: Dr.Loop, +vs: List<&2, Dr.Verdict>) -> {Dr.tick(cap, l, vs) == Director.dirs.tick(cap, l, vs) : Dr.Loop}:
  match l:
    case Dr.Loop{+n, +s, e}:
      match e:
        case Some{x}:
          {==}
        case None{}:
          %de.go(s, vs, Nat.is_lt(List.length(&2, Dr.Layer, s), cap), False{}) : {Dr.settle(Dr.decide(s, vs, cap), n, s, vs, cap) == Director.dirs.settle(_, n, s, vs, cap) : Dr.Loop}
          de.settle(Dr.decide(s, vs, cap), n, s, vs, cap)

# Spelling
# --------

def de.layer_put(l: Dr.Layer, rest: String) -> {FDr.put_layer(l, rest) == Director.dirs.layer(l, rest) : String}:
  match l:
    case Dr.Layer{k, b}:
      {==}

def de.end_put(e: Maybe<&2, Dr.Out>, -rest: String) -> {FDr.put_end(e, rest) == Director.dirs.end(e, rest) : String}:
  match e:
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

def de.loop_put(l: Dr.Loop, +rest: String) -> {FDr.put_loop(l, rest) == Director.dirs.loop(l, rest) : String}:
  match l:
    case Dr.Loop{+n, +st, +e}:
      %de.end_put(e, rest) : {Wr.put_nat(n, Wr.put_list(~Dr.Layer, ~FDr.put_layer, st, FDr.put_end(e, rest))) == Wr.put_nat(n, Wr.put_list(~Dr.Layer, ~Director.dirs.layer, st, _)) : String}
      %LX.lx.put(~Dr.Layer, ~FDr.put_layer, ~Director.dirs.layer, ~de.layer_put, st, FDr.put_end(e, rest)) : {Wr.put_nat(n, Wr.put_list(~Dr.Layer, ~FDr.put_layer, st, FDr.put_end(e, rest))) == Wr.put_nat(n, _) : String}
      {==}

# The entry
# ---------

def de.whole(done: Bool, q: FDr.Req) -> {FDr.ffi.whole(q, done) == Director.dirs.whole(done, q) : String}:
  match done:
    case True{}:
      match q:
        case FDr.Req{+c, +l, +vs}:
          %de.tick(c, l, vs) : {FDr.put_loop(Dr.tick(c, l, vs), "") == Director.dirs.loop(_, "") : String}
          de.loop_put(Dr.tick(c, l, vs), "")
    case False{}:
      {==}

def de.run(r: Wr.Dec<FDr.Req>) -> {FDr.ffi.go(r) == Director.dirs.run(r) : String}:
  match r:
    case Wr.Got{q, +s}:
      de.whole(Wr.end(s), q)
    case Wr.Bad{}:
      {==}

def Director.dir_ffi_exact(s):
  %de.req(Wr.get_nat(s)) : {FDr.ffi.go(FDr.get_req(s)) == Director.dirs.run(_) : String}
  de.run(FDr.get_req(s))
