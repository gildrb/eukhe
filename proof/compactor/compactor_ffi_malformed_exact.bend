# eukhe: the proof of LAW compactor_ffi_malformed_exact
# The laws' reader reads every input as the entry does, request by
# request projected to its numbers (cme.ask); where the reader finds no
# whole request, the entry found none either and answers its error form.

import Base
import ../../bend/compactor.bend as C
import ../../bend/ffi_compactor.bend as FC
import ../../bend/wire.bend as Wr
import ../../laws/compactor.bend as Compactor

# a request as its numbers
def cme.rep(r: FC.Rep) -> Maybe<&2, Nat>:
  match r:
    case FC.RErr{}:
      None{}
    case FC.RSays{n}:
      Some{n}

def cme.out(o: C.Outcome) -> Nat:
  match o:
    case C.Built{}:
      0n
    case C.Failed{}:
      1n
    case C.Disk{}:
      2n
    case C.Stopped{}:
      3n

def cme.ask(q: FC.Req) -> Compactor.Ask:
  match q:
    case FC.QOpen{t}:
      Compactor.AOpen{t}
    case FC.QStep{l, m, n, b, r}:
      Compactor.AStep{l, m, n, b, cme.rep(r)}
    case FC.QAfter{p, o}:
      Compactor.AAfter{p, cme.out(o)}

def cme.dec(r: Wr.Dec<FC.Req>) -> Wr.Dec<Compactor.Ask>:
  match r:
    case Wr.Got{q, s}:
      Wr.Got{cme.ask(q), s}
    case Wr.Bad{}:
      Wr.Bad{}

# The reader, stage by stage
# --------------------------

def cme.m_some(r: Wr.Dec<Nat>) -> {Compactor.read_m.some(r) == FC.get_mnat.some(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cme.m_tag(t: Nat, s: String) -> {Compactor.read_m.tag(t, s) == FC.get_mnat.tag(t, s) : Wr.Dec<Maybe<&2, Nat>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      cme.m_some(Wr.get_nat(s))
    case 2n+p:
      {==}

def cme.m(r: Wr.Dec<Nat>) -> {Compactor.read_m(r) == FC.get_mnat(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{t, s}:
      cme.m_tag(t, s)
    case Wr.Bad{}:
      {==}

def cme.open(r: Wr.Dec<Nat>) -> {Compactor.read_open(r) == cme.dec(FC.get_open(r)) : Wr.Dec<Compactor.Ask>}:
  match r:
    case Wr.Got{t, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cme.says(l: Nat, m: Nat, n: Nat, b: Maybe<&2, Nat>, r: Wr.Dec<Nat>) -> {Compactor.read_step.reply(l, m, n, b, Compactor.read_m.some(r)) == cme.dec(FC.get_step.says(l, m, n, b, r)) : Wr.Dec<Compactor.Ask>}:
  match r:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cme.rep_tag(l: Nat, m: Nat, n: Nat, b: Maybe<&2, Nat>, t: Nat, +s: String) -> {Compactor.read_step.reply(l, m, n, b, Compactor.read_m.tag(t, s)) == cme.dec(FC.get_step.rep(l, m, n, b, t, s)) : Wr.Dec<Compactor.Ask>}:
  match t:
    case 0n:
      {==}
    case 1n:
      cme.says(l, m, n, b, Wr.get_nat(s))
    case 2n+p:
      {==}

def cme.tag(l: Nat, m: Nat, n: Nat, b: Maybe<&2, Nat>, r: Wr.Dec<Nat>) -> {Compactor.read_step.reply(l, m, n, b, Compactor.read_m(r)) == cme.dec(FC.get_step.tag(l, m, n, b, r)) : Wr.Dec<Compactor.Ask>}:
  match r:
    case Wr.Got{t, s}:
      cme.rep_tag(l, m, n, b, t, s)
    case Wr.Bad{}:
      {==}

def cme.kind(l: Nat, m: Nat, n: Nat, r: Wr.Dec<Maybe<&2, Nat>>) -> {Compactor.read_step.best(l, m, n, r) == cme.dec(FC.get_step.kind(l, m, n, r)) : Wr.Dec<Compactor.Ask>}:
  match r:
    case Wr.Got{b, s}:
      cme.tag(l, m, n, b, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def cme.node(+l: Nat, +m: Nat, r: Wr.Dec<Nat>) -> {Compactor.read_step.node(l, m, r) == cme.dec(FC.get_step.node(l, m, r)) : Wr.Dec<Compactor.Ask>}:
  match r:
    case Wr.Got{+n, +s}:
      %cme.m(Wr.get_nat(s)) : {Compactor.read_step.best(l, m, n, Compactor.read_m(Wr.get_nat(s))) == cme.dec(FC.get_step.kind(l, m, n, _)) : Wr.Dec<Compactor.Ask>}
      cme.kind(l, m, n, Compactor.read_m(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def cme.made(l: Nat, r: Wr.Dec<Nat>) -> {Compactor.read_step.made(l, r) == cme.dec(FC.get_step.made(l, r)) : Wr.Dec<Compactor.Ask>}:
  match r:
    case Wr.Got{m, s}:
      cme.node(l, m, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def cme.step(r: Wr.Dec<Nat>) -> {Compactor.read_step(r) == cme.dec(FC.get_step(r)) : Wr.Dec<Compactor.Ask>}:
  match r:
    case Wr.Got{l, s}:
      cme.made(l, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def cme.out_tag(p: C.Pend, t: Nat, s: String) -> {Compactor.read_after.how.tag(p, t, s) == cme.dec(FC.get_outcome(p, t, s)) : Wr.Dec<Compactor.Ask>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n+q:
      {==}

def cme.how(p: C.Pend, r: Wr.Dec<Nat>) -> {Compactor.read_after.how(p, r) == cme.dec(FC.get_after.how(p, r)) : Wr.Dec<Compactor.Ask>}:
  match r:
    case Wr.Got{t, s}:
      cme.out_tag(p, t, s)
    case Wr.Bad{}:
      {==}

def cme.owed(r: Wr.Dec<Nat>) -> {Compactor.read_after.owed(r) == cme.dec(FC.get_after.owed(r)) : Wr.Dec<Compactor.Ask>}:
  match r:
    case Wr.Got{n, s}:
      cme.how(C.Owed{n}, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def cme.after_tag(t: Nat, s: String) -> {Compactor.read_after.tag(t, s) == cme.dec(FC.get_after.tag(t, s)) : Wr.Dec<Compactor.Ask>}:
  match t:
    case 0n:
      cme.how(C.Made{}, Wr.get_nat(s))
    case 1n:
      cme.owed(Wr.get_nat(s))
    case 2n+p:
      {==}

def cme.after(r: Wr.Dec<Nat>) -> {Compactor.read_after(r) == cme.dec(FC.get_after(r)) : Wr.Dec<Compactor.Ask>}:
  match r:
    case Wr.Got{t, s}:
      cme.after_tag(t, s)
    case Wr.Bad{}:
      {==}

def cme.ask_tag(t: Nat, s: String) -> {Compactor.read_ask.tag(t, s) == cme.dec(FC.get_req.tag(t, s)) : Wr.Dec<Compactor.Ask>}:
  match t:
    case 0n:
      cme.open(Wr.get_nat(s))
    case 1n:
      cme.step(Wr.get_nat(s))
    case 2n:
      cme.after(Wr.get_nat(s))
    case 3n+p:
      {==}

# the laws' reader reads every input as the entry does
def cme.go(r: Wr.Dec<Nat>) -> {Compactor.read_ask.go(r) == cme.dec(FC.get_req.go(r)) : Wr.Dec<Compactor.Ask>}:
  match r:
    case Wr.Got{t, s}:
      cme.ask_tag(t, s)
    case Wr.Bad{}:
      {==}

# The answer
# ----------

def cme.if_none(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def cme.some_none(-A: Data, -x: A, -G: Type, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  %e : cme.if_none(A, _, G)
  Unit{}

def cme.end(b: Bool, -q: FC.Req, no: {Compactor.read_ask.end(b, cme.ask(q)) == None{} : Maybe<&2, Compactor.Ask>}) -> {FC.run.end(b, q) == SCon{'E', SCon{' ', "compactor: malformed request"}} : String}:
  match b:
    case True{}:
      cme.some_none(Compactor.Ask, cme.ask(q), {FC.answer(q) == SCon{'E', SCon{' ', "compactor: malformed request"}} : String}, no)
    case False{}:
      {==}

def cme.whole(r: Wr.Dec<FC.Req>, no: {Compactor.read_ask.whole(cme.dec(r)) == None{} : Maybe<&2, Compactor.Ask>}) -> {FC.run(r) == SCon{'E', SCon{' ', "compactor: malformed request"}} : String}:
  match r:
    case Wr.Got{q, s}:
      cme.end(Wr.end(s), q, no)
    case Wr.Bad{}:
      {==}

# the reader found no whole request: the entry's decode, projected, is that
def cme.no(x: Wr.Dec<Nat>, no: {Compactor.read_ask.whole(Compactor.read_ask.go(x)) == None{} : Maybe<&2, Compactor.Ask>}) -> {Compactor.read_ask.whole(cme.dec(FC.get_req.go(x))) == None{} : Maybe<&2, Compactor.Ask>}:
  %cme.go(x) : {Compactor.read_ask.whole(_) == None{} : Maybe<&2, Compactor.Ask>}
  no

def Compactor.compactor_ffi_malformed_exact(s, no):
  cme.whole(FC.get_req.go(Wr.get_nat(s)), cme.no(Wr.get_nat(s), no))
