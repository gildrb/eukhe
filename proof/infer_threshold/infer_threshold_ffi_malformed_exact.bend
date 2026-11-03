# eukhe: the proof of LAW infer_threshold_ffi_malformed_exact
# The laws' reader reads every input as the entry does, request by
# request projected to the reader's (gtm.ask); where the reader finds no
# whole request, the entry found none either and answers its error form.

import Base
import ../../bend/infer_threshold.bend as M
import ../../bend/ffi_infer_threshold.bend as FT
import ../../bend/wire.bend as Wr
import ../../laws/infer_threshold.bend as InferThreshold

def gtm.ask(q: FT.Req) -> InferThreshold.Ask:
  match q:
    case FT.Req{on, t, last, w, r, m, keep, full, xs, cuts}:
      InferThreshold.Ask{on, t, last, w, r, m, keep, full, xs, cuts}

def gtm.dec(d: Wr.Dec<FT.Req>) -> Wr.Dec<InferThreshold.Ask>:
  match d:
    case Wr.Got{q, s}:
      Wr.Got{gtm.ask(q), s}
    case Wr.Bad{}:
      Wr.Bad{}

# The reader, stage by stage
# --------------------------

def gtm.up(d: Wr.Dec<Nat>) -> {InferThreshold.read_z.up(d) == FT.get_z.up(d) : Wr.Dec<M.Z>}:
  match d:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def gtm.down(d: Wr.Dec<Nat>) -> {InferThreshold.read_z.down(d) == FT.get_z.down(d) : Wr.Dec<M.Z>}:
  match d:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def gtm.z_tag(t: Nat, s: String) -> {InferThreshold.read_z.tag(t, s) == FT.get_z.tag(t, s) : Wr.Dec<M.Z>}:
  match t:
    case 0n:
      gtm.up(Wr.get_nat(s))
    case 1n:
      gtm.down(Wr.get_nat(s))
    case 2n+p:
      {==}

def gtm.z(d: Wr.Dec<Nat>) -> {InferThreshold.read_z(d) == FT.get_z(d) : Wr.Dec<M.Z>}:
  match d:
    case Wr.Got{t, s}:
      gtm.z_tag(t, s)
    case Wr.Bad{}:
      {==}

def gtm.cuts(on: Bool, t: Nat, last: Nat, w: Nat, r: M.Z, m: M.Z, keep: Nat, full: Nat, xs: List<&2, Nat>, d: Wr.Dec<List<&2, Nat>>) -> {InferThreshold.read_ask.cuts(on, t, last, w, r, m, keep, full, xs, d) == gtm.dec(FT.get_req.cuts(on, t, last, w, r, m, keep, full, xs, d)) : Wr.Dec<InferThreshold.Ask>}:
  match d:
    case Wr.Got{cuts, s}:
      {==}
    case Wr.Bad{}:
      {==}

def gtm.sizes(on: Bool, t: Nat, last: Nat, w: Nat, r: M.Z, m: M.Z, keep: Nat, full: Nat, d: Wr.Dec<List<&2, Nat>>) -> {InferThreshold.read_ask.sizes(on, t, last, w, r, m, keep, full, d) == gtm.dec(FT.get_req.sizes(on, t, last, w, r, m, keep, full, d)) : Wr.Dec<InferThreshold.Ask>}:
  match d:
    case Wr.Got{xs, s}:
      gtm.cuts(on, t, last, w, r, m, keep, full, xs, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      {==}

def gtm.full(on: Bool, t: Nat, last: Nat, w: Nat, r: M.Z, m: M.Z, keep: Nat, d: Wr.Dec<Nat>) -> {InferThreshold.read_ask.full(on, t, last, w, r, m, keep, d) == gtm.dec(FT.get_req.full(on, t, last, w, r, m, keep, d)) : Wr.Dec<InferThreshold.Ask>}:
  match d:
    case Wr.Got{full, s}:
      gtm.sizes(on, t, last, w, r, m, keep, full, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      {==}

def gtm.keep(on: Bool, t: Nat, last: Nat, w: Nat, r: M.Z, m: M.Z, d: Wr.Dec<Nat>) -> {InferThreshold.read_ask.keep(on, t, last, w, r, m, d) == gtm.dec(FT.get_req.keep(on, t, last, w, r, m, d)) : Wr.Dec<InferThreshold.Ask>}:
  match d:
    case Wr.Got{keep, s}:
      gtm.full(on, t, last, w, r, m, keep, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def gtm.margin(on: Bool, t: Nat, last: Nat, w: Nat, r: M.Z, d: Wr.Dec<M.Z>) -> {InferThreshold.read_ask.margin(on, t, last, w, r, d) == gtm.dec(FT.get_req.margin(on, t, last, w, r, d)) : Wr.Dec<InferThreshold.Ask>}:
  match d:
    case Wr.Got{m, s}:
      gtm.keep(on, t, last, w, r, m, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def gtm.reserve(+on: Bool, +t: Nat, +last: Nat, +w: Nat, d: Wr.Dec<M.Z>) -> {InferThreshold.read_ask.reserve(on, t, last, w, d) == gtm.dec(FT.get_req.reserve(on, t, last, w, d)) : Wr.Dec<InferThreshold.Ask>}:
  match d:
    case Wr.Got{+r, +s}:
      %gtm.z(Wr.get_nat(s)) : {InferThreshold.read_ask.margin(on, t, last, w, r, InferThreshold.read_z(Wr.get_nat(s))) == gtm.dec(FT.get_req.margin(on, t, last, w, r, _)) : Wr.Dec<InferThreshold.Ask>}
      gtm.margin(on, t, last, w, r, InferThreshold.read_z(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def gtm.window(+on: Bool, +t: Nat, +last: Nat, d: Wr.Dec<Nat>) -> {InferThreshold.read_ask.window(on, t, last, d) == gtm.dec(FT.get_req.window(on, t, last, d)) : Wr.Dec<InferThreshold.Ask>}:
  match d:
    case Wr.Got{+w, +s}:
      %gtm.z(Wr.get_nat(s)) : {InferThreshold.read_ask.reserve(on, t, last, w, InferThreshold.read_z(Wr.get_nat(s))) == gtm.dec(FT.get_req.reserve(on, t, last, w, _)) : Wr.Dec<InferThreshold.Ask>}
      gtm.reserve(on, t, last, w, InferThreshold.read_z(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def gtm.last(on: Bool, t: Nat, d: Wr.Dec<Nat>) -> {InferThreshold.read_ask.last(on, t, d) == gtm.dec(FT.get_req.last(on, t, d)) : Wr.Dec<InferThreshold.Ask>}:
  match d:
    case Wr.Got{last, s}:
      gtm.window(on, t, last, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def gtm.tokens(on: Bool, d: Wr.Dec<Nat>) -> {InferThreshold.read_ask.tokens(on, d) == gtm.dec(FT.get_req.tokens(on, d)) : Wr.Dec<InferThreshold.Ask>}:
  match d:
    case Wr.Got{t, s}:
      gtm.last(on, t, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def gtm.go(d: Wr.Dec<Bool>) -> {InferThreshold.read_ask.go(d) == gtm.dec(FT.get_req.go(d)) : Wr.Dec<InferThreshold.Ask>}:
  match d:
    case Wr.Got{on, s}:
      gtm.tokens(on, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

# The answer
# ----------

def gtm.if_none(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def gtm.some_none(-A: Data, -x: A, -G: Type, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  %e : gtm.if_none(A, _, G)
  Unit{}

def gtm.end(b: Bool, -q: FT.Req, no: {InferThreshold.read_ask.end(b, gtm.ask(q)) == None{} : Maybe<&2, InferThreshold.Ask>}) -> {FT.run.end(b, q) == SCon{'E', SCon{' ', "infer_threshold: malformed request"}} : String}:
  match b:
    case True{}:
      gtm.some_none(InferThreshold.Ask, gtm.ask(q), {FT.answer(q) == SCon{'E', SCon{' ', "infer_threshold: malformed request"}} : String}, no)
    case False{}:
      {==}

def gtm.whole(d: Wr.Dec<FT.Req>, no: {InferThreshold.read_ask.whole(gtm.dec(d)) == None{} : Maybe<&2, InferThreshold.Ask>}) -> {FT.run(d) == SCon{'E', SCon{' ', "infer_threshold: malformed request"}} : String}:
  match d:
    case Wr.Got{q, s}:
      gtm.end(Wr.end(s), q, no)
    case Wr.Bad{}:
      {==}

def gtm.no(x: Wr.Dec<Bool>, no: {InferThreshold.read_ask.whole(InferThreshold.read_ask.go(x)) == None{} : Maybe<&2, InferThreshold.Ask>}) -> {InferThreshold.read_ask.whole(gtm.dec(FT.get_req.go(x))) == None{} : Maybe<&2, InferThreshold.Ask>}:
  %gtm.go(x) : {InferThreshold.read_ask.whole(_) == None{} : Maybe<&2, InferThreshold.Ask>}
  no

def InferThreshold.infer_threshold_ffi_malformed_exact(s, no):
  gtm.whole(FT.get_req.go(Wr.get_bool(s)), gtm.no(Wr.get_bool(s), no))
