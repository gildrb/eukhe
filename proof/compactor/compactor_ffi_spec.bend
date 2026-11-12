# eukhe: the proof of LAW compactor_ffi_spec
# The laws' reader reads every input as the entry does, projected to its
# numbers (PMal.cme.go). On a whole request the entry's answer is the
# spec's: a line opens and a call of a pending line ends by computation,
# one case per constructor; a reply to a line is PStep.cst.decide, the
# entry's decision on the lengths, with the text of n one-byte characters
# a length stands for (its bytes are n: csp.ones).

import Base
import ../../bend/compactor.bend as C
import ../../bend/ffi_compactor.bend as FC
import ../../bend/wire.bend as Wr
import ../../laws/compactor.bend as Compactor
import ./compactor_ffi_malformed_exact.bend as PMal
import ./compactor_ffi_step.bend as PStep

# a text of n one-byte characters has n bytes
def csp.ones(n: Nat) -> {Compactor.bytes(Compactor.ones(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %csp.ones(k) : {1n+Compactor.bytes(Compactor.ones(k)) == 1n+_ : Nat}
      {==}

def csp.open(t: Nat) -> {FC.put_next(C.line.open(t, 0n, Nil{})) == Compactor.spell_next(Compactor.open_spec(t, 0n, Nil{})) : String}:
  match t:
    case 0n:
      {==}
    case 1n+q:
      {==}

# the best reply's length as read: the entry's decision on it is the spec's
def csp.best(l: Nat, m: Nat, n: Nat, b: Maybe<&2, Nat>, r: C.Reply) -> {FC.put_next(FC.reply(l, m, n, b, PStep.cst.rep(r))) == Compactor.spell_next(Compactor.step_spec(C.Lst{l, m, n, Compactor.ask_best(b), Compactor.ask_bl(b), Nil{}}, r)) : String}:
  match b:
    case None{}:
      PStep.cst.decide_orig(l, m, n, Nil{}, r, None{}, 0n)
    case Some{+k}:
      PStep.cst.decide_orig(l, m, n, Nil{}, r, Some{Compactor.ones(k)}, k)

def csp.step(l: Nat, m: Nat, n: Nat, b: Maybe<&2, Nat>, r: FC.Rep) -> {FC.put_next(FC.reply(l, m, n, b, r)) == Compactor.spell_next(Compactor.step_spec(C.Lst{l, m, n, Compactor.ask_best(b), Compactor.ask_bl(b), Nil{}}, Compactor.ask_reply(PMal.cme.rep(r)))) : String}:
  match r:
    case FC.RErr{}:
      csp.best(l, m, n, b, C.Erred{})
    case FC.RSays{+k}:
      %csp.ones(k) : {FC.put_next(FC.reply(l, m, n, b, FC.RSays{_})) == Compactor.spell_next(Compactor.step_spec(C.Lst{l, m, n, Compactor.ask_best(b), Compactor.ask_bl(b), Nil{}}, C.Says{Compactor.ones(k)})) : String}
      csp.best(l, m, n, b, C.Says{Compactor.ones(k)})

def csp.owed(o: C.Outcome, k: Nat) -> {FC.put_pend(C.Pend.after(C.Owed{k}, o)) == Compactor.spell_pend(Compactor.after_spec(C.Owed{k}, Compactor.ask_outcome(PMal.cme.out(o))), "") : String}:
  match o:
    case C.Built{}:
      {==}
    case C.Failed{}:
      match k:
        case 0n:
          {==}
        case 1n+j:
          {==}
    case C.Disk{}:
      {==}
    case C.Stopped{}:
      {==}

def csp.after(p: C.Pend, o: C.Outcome) -> {FC.put_pend(C.Pend.after(p, o)) == Compactor.spell_pend(Compactor.after_spec(p, Compactor.ask_outcome(PMal.cme.out(o))), "") : String}:
  match p:
    case C.Made{}:
      {==}
    case C.Owed{k}:
      csp.owed(o, k)

# the entry's answer to a whole request is the spec's
def csp.answer(q: FC.Req) -> {FC.answer(q) == Compactor.spec_answer(PMal.cme.ask_orig(q)) : String}:
  match q:
    case FC.QOpen{t}:
      csp.open(t)
    case FC.QStep{l, m, n, b, r}:
      csp.step(l, m, n, b, r)
    case FC.QAfter{p, o}:
      csp.after(p, o)

def csp.end(b: Bool, q: FC.Req) -> {FC.run.end(b, q) == Compactor.spec_entry(Compactor.read_ask.end(b, PMal.cme.ask_orig(q))) : String}:
  match b:
    case True{}:
      csp.answer(q)
    case False{}:
      {==}

def csp.run(d: Wr.Dec<FC.Req>) -> {FC.run(d) == Compactor.spec_entry(Compactor.read_ask.whole(PMal.cme.dec_orig(d))) : String}:
  match d:
    case Wr.Got{q, s}:
      csp.end(Wr.end(s), q)
    case Wr.Bad{}:
      {==}

def Compactor.compactor_ffi_spec(s):
  %Equal.sym(Wr.Dec<Compactor.Ask_orig>, Compactor.read_ask.go(Wr.get_nat(s)), PMal.cme.dec_orig(FC.get_req.go(Wr.get_nat(s))), PMal.cme.go_orig(Wr.get_nat(s))) : {FC.ffi(s) == Compactor.spec_entry(Compactor.read_ask.whole(_)) : String}
  csp.run(FC.get_req.go(Wr.get_nat(s)))
