# eukhe: the proof of LAW flight_step_refused_keeps
# A failed read or input left over answers the malformed-event error form
# with the desk kept. A whole event steps F.desk.step: its answer Off (out
# of turn) keeps the desk on every path (ark.desk); any other answer is
# spelled as a number first (a count, or the joiner Maybe's tag), which
# never opens with 'E' (Wire.wire_nat_not_err), against the premise.

import Base
import ../../bend/auth_flight.bend as F
import ../../bend/ffi_auth_flight.bend as FA
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/auth_flight/entry.bend as AuthFlightEntry
import ./base/entry.bend as LAE
import ../wire/wire_nat_not_err.bend as PWireNatNotErr

# an answer out of turn keeps the desk d
def ark.Keeps(+d: F.Desk, r: F.DRes) -> Type:
  match r:
    case F.DRes{d2, o}:
      match o:
        case F.Acts{xs}:
          Unit
        case F.Joined{j}:
          Unit
        case F.Off{}:
          {d2 == d : F.Desk}

def ark.board(fl: Bool, +k: Nat, +cs: List<&2, F.Cl>, +m: Nat) -> ark.Keeps(F.Desk{cs, m}, F.board(fl, k, cs, m)):
  match fl:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

def ark.go(fd: F.Fd, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +m: Nat) -> ark.Keeps(F.Desk{cs, m}, F.found.go(fd, k, p, cs, m)):
  match fd:
    case F.LoadFresh{}:
      Unit{}
    case F.LoadExpired{}:
      ark.board(F.inflight(p, cs), k, cs, m)
    case F.LoadFailed{}:
      Unit{}
    case F.CheckFresh{}:
      Unit{}
    case F.CheckExpired{}:
      Unit{}
    case F.FetchOk{}:
      Unit{}
    case F.FetchFailed{}:
      Unit{}
    case F.Stored{}:
      Unit{}

def ark.fit(fit: Bool, fd: F.Fd, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +m: Nat) -> ark.Keeps(F.Desk{cs, m}, F.found.fit(fit, fd, k, p, cs, m)):
  match fit:
    case True{}:
      ark.go(fd, k, p, cs, m)
    case False{}:
      {==}

def ark.found(r: Maybe<&2, F.Cl>, +fd: F.Fd, +k: Nat, +cs: List<&2, F.Cl>, +m: Nat) -> ark.Keeps(F.Desk{cs, m}, F.found(r, fd, k, cs, m)):
  match r:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case F.Cl{j, p, a}:
          ark.fit(Nat.is_eq(F.At.tag(a), F.Fd.tag(fd)), fd, k, p, cs, m)

def ark.lead(lead: Bool, +k: Nat, +p: String, +cs: List<&2, F.Cl>, +m: Nat) -> ark.Keeps(F.Desk{cs, m}, F.unwind.at(lead, k, p, cs, m)):
  match lead:
    case True{}:
      Unit{}
    case False{}:
      Unit{}

def ark.unwind(r: Maybe<&2, F.Cl>, +k: Nat, +cs: List<&2, F.Cl>, +m: Nat) -> ark.Keeps(F.Desk{cs, m}, F.unwind(r, k, cs, m)):
  match r:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case F.Cl{j, p, a}:
          ark.lead(F.leads(a), k, p, cs, m)

# every answer of the desk out of turn keeps it
def ark.desk(d: F.Desk, e: F.DEv) -> ark.Keeps(d, F.desk.step(d, e)):
  match d:
    case F.Desk{+cs, +m}:
      match e:
        case F.Comes{p}:
          Unit{}
        case F.Found{+k, +fd}:
          ark.found(F.find(k, cs), fd, k, cs, m)
        case F.Unwinds{+k}:
          ark.unwind(F.find(k, cs), k, cs, m)
        case F.Joiners{p}:
          Unit{}

# a number first never opens with 'E', against the premise
def ark.num(-G: Type, +n: Nat, +rest: String, err: {LawsBase.wire_opens_err(Wr.put_nat(n, rest)) == True{} : Bool}) -> G:
  LAE.ae.ft(G, Equal.trans(Bool, False{}, LawsBase.wire_opens_err(Wr.put_nat(n, rest)), True{}, Equal.sym(Bool, LawsBase.wire_opens_err(Wr.put_nat(n, rest)), False{}, Wire.wire_nat_not_err(n, rest)), err))

def ark.put(+d: F.Desk, r: F.DRes, k: ark.Keeps(d, r), err: {LawsBase.wire_opens_err(AuthFlightEntry.af_reply(FA.step.put(r))) == True{} : Bool}) -> {AuthFlightEntry.af_state(FA.step.put(r)) == FA.Open{d} : FA.St}:
  match r:
    case F.DRes{d2, o}:
      match o:
        case F.Acts{+xs}:
          ark.num({FA.Open{d2} == FA.Open{d} : FA.St}, List.length(&2, F.To, xs), FA.put_tos(xs, ""), err)
        case F.Joined{j}:
          match j:
            case None{}:
              ark.num({FA.Open{d2} == FA.Open{d} : FA.St}, 0n, "", err)
            case Some{+n}:
              ark.num({FA.Open{d2} == FA.Open{d} : FA.St}, 1n, Wr.put_nat(n, ""), err)
        case F.Off{}:
          Equal.cong(F.Desk, FA.St, x => FA.Open{x}, d2, d, k)

def ark.fin(b: Bool, +d: F.Desk, +e: F.DEv, err: {LawsBase.wire_opens_err(AuthFlightEntry.af_reply(FA.step.fin(b, d, e))) == True{} : Bool}) -> {AuthFlightEntry.af_state(FA.step.fin(b, d, e)) == FA.Open{d} : FA.St}:
  match b:
    case True{}:
      ark.put(d, F.desk.step(d, e), ark.desk(d, e), err)
    case False{}:
      {==}

def ark.read(+d: F.Desk, r: Wr.Dec<F.DEv>, err: {LawsBase.wire_opens_err(AuthFlightEntry.af_reply(FA.step.go(d, r))) == True{} : Bool}) -> {AuthFlightEntry.af_state(FA.step.go(d, r)) == FA.Open{d} : FA.St}:
  match r:
    case Wr.Got{+e, t}:
      ark.fin(Wr.end(t), d, e, err)
    case Wr.Bad{}:
      {==}

def AuthFlightEntry.flight_step_refused_keeps(d, s, err):
  ark.read(d, FA.get_ev(Wr.get_nat(s)), err)
