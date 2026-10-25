# eukhe: the proof of LAW approvals_desk_root_never_relays
# At a root the session's decision is never a relay (a case per session):
# a question is shown or ended, and a detach shows or ends each question
# waiting on the clients, by induction on the questions.

import Base
import ../../bend/approvals.bend as Am
import ../../laws/approvals/desk.bend as ApprovalsDesk

def arr.acts(r: List<&2, Am.Q> & List<&2, Am.Act>) -> List<&2, Am.Act>:
  (qs, as) = r
  as

def arr.q(w: Am.Wait, +k: Nat, +i: String, +es: List<&2, Nat>, h: Am.Here, r: List<&2, Am.Q> & List<&2, Am.Act>, ih: {ApprovalsDesk.ds_any_relay(arr.acts(r)) == False{} : Bool}) -> {ApprovalsDesk.ds_any_relay(arr.acts(Am.reroute.q(w, k, i, es, Am.next(es, h, False{}), r))) == False{} : Bool}:
  match w:
    case Am.OnParent{}:
      (qs, as) = r
      ih
    case Am.OnClients{}:
      match h:
        case Am.Nobody{}:
          (qs, as) = r
          ih
        case Am.GatewayOnly{}:
          (qs, as) = r
          ih
        case Am.Clients{}:
          (qs, as) = r
          ih

def arr.rr(qs: List<&2, Am.Q>, +h: Am.Here) -> {ApprovalsDesk.ds_any_relay(arr.acts(Am.reroute(qs, h, False{}))) == False{} : Bool}:
  match qs:
    case Nil{}:
      {==}
    case q <> +rest:
      match q:
        case Am.Q{k, i, es, w}:
          arr.q(w, k, i, es, h, Am.reroute(rest, h, False{}), arr.rr(rest, h))

def arr.put(+n: Nat, r: List<&2, Am.Q> & List<&2, Am.Act>, ih: {ApprovalsDesk.ds_any_relay(arr.acts(r)) == False{} : Bool}) -> {ApprovalsDesk.ds_any_relay(ApprovalsDesk.ds_acts(Am.detach.put(n, r))) == False{} : Bool}:
  (qs, as) = r
  ih

def arr.ask(d: Am.D, +id: String, +es: List<&2, Nat>, h: Am.Here) -> {ApprovalsDesk.ds_any_relay(ApprovalsDesk.ds_acts(Am.dstep(d, Am.EAsk{id, es, h, False{}}))) == False{} : Bool}:
  match d:
    case Am.D{n, qs}:
      match h:
        case Am.Nobody{}:
          {==}
        case Am.GatewayOnly{}:
          {==}
        case Am.Clients{}:
          {==}

def arr.detach(d: Am.D, h: Am.Here) -> {ApprovalsDesk.ds_any_relay(ApprovalsDesk.ds_acts(Am.dstep(d, Am.EDetach{h, False{}}))) == False{} : Bool}:
  match d:
    case Am.D{+n, +qs}:
      match h:
        case Am.Nobody{}:
          arr.put(n, Am.reroute(qs, Am.Nobody{}, False{}), arr.rr(qs, Am.Nobody{}))
        case Am.GatewayOnly{}:
          arr.put(n, Am.reroute(qs, Am.GatewayOnly{}, False{}), arr.rr(qs, Am.GatewayOnly{}))
        case Am.Clients{}:
          {==}

def arr.two(-a: Bool, -b: Bool, ea: {a == False{} : Bool}, eb: {b == False{} : Bool}) -> {[a, b] == [False{}, False{}] : List<&2, Bool>}:
  %Equal.sym(Bool, a, False{}, ea) : {[_, b] == [False{}, False{}] : List<&2, Bool>}
  %Equal.sym(Bool, b, False{}, eb) : {[False{}, _] == [False{}, False{}] : List<&2, Bool>}
  {==}

def ApprovalsDesk.approvals_desk_root_never_relays(d, id, es, h):
  arr.two(ApprovalsDesk.ds_any_relay(ApprovalsDesk.ds_acts(Am.dstep(d, Am.EAsk{id, es, h, False{}}))), ApprovalsDesk.ds_any_relay(ApprovalsDesk.ds_acts(Am.dstep(d, Am.EDetach{h, False{}}))), arr.ask(d, id, es, h), arr.detach(d, h))
