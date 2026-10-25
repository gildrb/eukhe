# eukhe: the proof of LAW approvals_desk_never_stranded
# With no interactive client the session's decision is never to show: a
# question waiting on the clients goes up (waiting on the parent) or ends;
# one waiting on the parent stays so; by induction on the questions.

import Base
import ../../bend/approvals.bend as Am
import ../../laws/approvals/desk.bend as ApprovalsDesk

def ans.qs(r: List<&2, Am.Q> & List<&2, Am.Act>) -> List<&2, Am.Q>:
  (qs, as) = r
  qs

def ans.qn(w: Am.Wait, +k: Nat, +i: String, +es: List<&2, Nat>, p: Bool, r: List<&2, Am.Q> & List<&2, Am.Act>, ih: {ApprovalsDesk.ds_any_clients(ans.qs(r)) == False{} : Bool}) -> {ApprovalsDesk.ds_any_clients(ans.qs(Am.reroute.q(w, k, i, es, Am.next(es, Am.Nobody{}, p), r))) == False{} : Bool}:
  match w:
    case Am.OnParent{}:
      (qs, as) = r
      ih
    case Am.OnClients{}:
      match p:
        case True{}:
          (qs, as) = r
          ih
        case False{}:
          (qs, as) = r
          ih

def ans.qg(w: Am.Wait, +k: Nat, +i: String, +es: List<&2, Nat>, p: Bool, r: List<&2, Am.Q> & List<&2, Am.Act>, ih: {ApprovalsDesk.ds_any_clients(ans.qs(r)) == False{} : Bool}) -> {ApprovalsDesk.ds_any_clients(ans.qs(Am.reroute.q(w, k, i, es, Am.next(es, Am.GatewayOnly{}, p), r))) == False{} : Bool}:
  match w:
    case Am.OnParent{}:
      (qs, as) = r
      ih
    case Am.OnClients{}:
      (qs, as) = r
      ih

def ans.rrn(qs: List<&2, Am.Q>, +p: Bool) -> {ApprovalsDesk.ds_any_clients(ans.qs(Am.reroute(qs, Am.Nobody{}, p))) == False{} : Bool}:
  match qs:
    case Nil{}:
      {==}
    case q <> +rest:
      match q:
        case Am.Q{k, i, es, w}:
          ans.qn(w, k, i, es, p, Am.reroute(rest, Am.Nobody{}, p), ans.rrn(rest, p))

def ans.rrg(qs: List<&2, Am.Q>, +p: Bool) -> {ApprovalsDesk.ds_any_clients(ans.qs(Am.reroute(qs, Am.GatewayOnly{}, p))) == False{} : Bool}:
  match qs:
    case Nil{}:
      {==}
    case q <> +rest:
      match q:
        case Am.Q{k, i, es, w}:
          ans.qg(w, k, i, es, p, Am.reroute(rest, Am.GatewayOnly{}, p), ans.rrg(rest, p))

def ans.put(+n: Nat, r: List<&2, Am.Q> & List<&2, Am.Act>, ih: {ApprovalsDesk.ds_any_clients(ans.qs(r)) == False{} : Bool}) -> {ApprovalsDesk.ds_any_clients(ApprovalsDesk.ds_qs(ApprovalsDesk.ds_desk(Am.detach.put(n, r)))) == False{} : Bool}:
  (qs, as) = r
  ih

def ans.two(-a: Bool, -b: Bool, ea: {a == False{} : Bool}, eb: {b == False{} : Bool}) -> {[a, b] == [False{}, False{}] : List<&2, Bool>}:
  %Equal.sym(Bool, a, False{}, ea) : {[_, b] == [False{}, False{}] : List<&2, Bool>}
  %Equal.sym(Bool, b, False{}, eb) : {[False{}, _] == [False{}, False{}] : List<&2, Bool>}
  {==}

def ApprovalsDesk.approvals_desk_never_stranded(d, p):
  match d:
    case Am.D{+n, +qs}:
      ans.two(ApprovalsDesk.ds_any_clients(ApprovalsDesk.ds_qs(ApprovalsDesk.ds_desk(Am.detach.put(n, Am.reroute(qs, Am.Nobody{}, p))))), ApprovalsDesk.ds_any_clients(ApprovalsDesk.ds_qs(ApprovalsDesk.ds_desk(Am.detach.put(n, Am.reroute(qs, Am.GatewayOnly{}, p))))), ans.put(n, Am.reroute(qs, Am.Nobody{}, p), ans.rrn(qs, p)), ans.put(n, Am.reroute(qs, Am.GatewayOnly{}, p), ans.rrg(qs, p)))
