# eukhe: the proof of LAW infer_force_ffi_malformed_exact
# The laws' reader reads every input as the entry does, request by
# request projected to the reader's (ifm.ask); where the reader finds no
# whole request, the entry found none either and answers its error form.

import Base
import ../../bend/ffi_infer_force.bend as FF
import ../../bend/wire.bend as Wr
import ../../laws/infer_force.bend as InferForce

def ifm.ask(q: FF.Req) -> InferForce.Ask:
  match q:
    case FF.QFlag{i, sup, free}:
      InferForce.AFlag{i, sup, free}
    case FF.QAfter{i, r, c}:
      InferForce.AAfter{i, r, c}

def ifm.dec(d: Wr.Dec<FF.Req>) -> Wr.Dec<InferForce.Ask>:
  match d:
    case Wr.Got{q, s}:
      Wr.Got{ifm.ask(q), s}
    case Wr.Bad{}:
      Wr.Bad{}

# The reader, stage by stage
# --------------------------

def ifm.free(i: Nat, sup: Bool, d: Wr.Dec<Bool>) -> {InferForce.read_flag.free(i, sup, d) == ifm.dec(FF.get_flag.free(i, sup, d)) : Wr.Dec<InferForce.Ask>}:
  match d:
    case Wr.Got{b, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ifm.sup(i: Nat, d: Wr.Dec<Bool>) -> {InferForce.read_flag.sup(i, d) == ifm.dec(FF.get_flag.sup(i, d)) : Wr.Dec<InferForce.Ask>}:
  match d:
    case Wr.Got{sup, s}:
      ifm.free(i, sup, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def ifm.flag(d: Wr.Dec<Nat>) -> {InferForce.read_flag(d) == ifm.dec(FF.get_flag(d)) : Wr.Dec<InferForce.Ask>}:
  match d:
    case Wr.Got{i, s}:
      ifm.sup(i, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def ifm.called(i: Nat, r: Nat, d: Wr.Dec<Bool>) -> {InferForce.read_after.called(i, r, d) == ifm.dec(FF.get_after.called(i, r, d)) : Wr.Dec<InferForce.Ask>}:
  match d:
    case Wr.Got{c, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ifm.retries(i: Nat, d: Wr.Dec<Nat>) -> {InferForce.read_after.retries(i, d) == ifm.dec(FF.get_after.retries(i, d)) : Wr.Dec<InferForce.Ask>}:
  match d:
    case Wr.Got{r, s}:
      ifm.called(i, r, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def ifm.after(d: Wr.Dec<Nat>) -> {InferForce.read_after(d) == ifm.dec(FF.get_after(d)) : Wr.Dec<InferForce.Ask>}:
  match d:
    case Wr.Got{i, s}:
      ifm.retries(i, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def ifm.tag(t: Nat, s: String) -> {InferForce.read_ask.tag(t, s) == ifm.dec(FF.get_req.tag(t, s)) : Wr.Dec<InferForce.Ask>}:
  match t:
    case 0n:
      ifm.flag(Wr.get_nat(s))
    case 1n:
      ifm.after(Wr.get_nat(s))
    case 2n+p:
      {==}

def ifm.go(d: Wr.Dec<Nat>) -> {InferForce.read_ask.go(d) == ifm.dec(FF.get_req.go(d)) : Wr.Dec<InferForce.Ask>}:
  match d:
    case Wr.Got{t, s}:
      ifm.tag(t, s)
    case Wr.Bad{}:
      {==}

# The answer
# ----------

def ifm.if_none(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def ifm.some_none(-A: Data, -x: A, -G: Type, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  %e : ifm.if_none(A, _, G)
  Unit{}

def ifm.end(b: Bool, -q: FF.Req, no: {InferForce.read_ask.end(b, ifm.ask(q)) == None{} : Maybe<&2, InferForce.Ask>}) -> {FF.run.end(b, q) == SCon{'E', SCon{' ', "infer_force: malformed request"}} : String}:
  match b:
    case True{}:
      ifm.some_none(InferForce.Ask, ifm.ask(q), {FF.answer(q) == SCon{'E', SCon{' ', "infer_force: malformed request"}} : String}, no)
    case False{}:
      {==}

def ifm.whole(d: Wr.Dec<FF.Req>, no: {InferForce.read_ask.whole(ifm.dec(d)) == None{} : Maybe<&2, InferForce.Ask>}) -> {FF.run(d) == SCon{'E', SCon{' ', "infer_force: malformed request"}} : String}:
  match d:
    case Wr.Got{q, s}:
      ifm.end(Wr.end(s), q, no)
    case Wr.Bad{}:
      {==}

# the reader found no whole request: the entry's decode, projected, is that
def ifm.no(x: Wr.Dec<Nat>, no: {InferForce.read_ask.whole(InferForce.read_ask.go(x)) == None{} : Maybe<&2, InferForce.Ask>}) -> {InferForce.read_ask.whole(ifm.dec(FF.get_req.go(x))) == None{} : Maybe<&2, InferForce.Ask>}:
  %ifm.go(x) : {InferForce.read_ask.whole(_) == None{} : Maybe<&2, InferForce.Ask>}
  no

def InferForce.infer_force_ffi_malformed_exact(s, no):
  ifm.whole(FF.get_req.go(Wr.get_nat(s)), ifm.no(Wr.get_nat(s), no))
