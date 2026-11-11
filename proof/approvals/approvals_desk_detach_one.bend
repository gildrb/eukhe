# eukhe: the proof of LAW approvals_desk_detach_one
# PROOF: a case per session left (and, with no client, per parent): each
# side computes to the same desk and acts.

import Base
import ../../bend/approvals.bend as Am
import ../../laws/approvals/desk.bend as ApprovalsDesk

# a question waiting on the parent stays, whoever is left
def dd.parent(+n: Nat, +k: Nat, +i: String, +es: List<&2, Nat>, h: Am.Here, +p: Bool) -> {Am.dstep(Am.D{n, [Am.Q{k, i, es, Am.OnParent{}}]}, Am.EDetach{h, p}) == (Am.D{n, [Am.Q{k, i, es, Am.OnParent{}}]}, Nil{}) : Am.D & List<&2, Am.Act>}:
  match h:
    case Am.Nobody{}:
      {==}
    case Am.GatewayOnly{}:
      {==}
    case Am.Clients{}:
      {==}

# a question its clients all left goes where the ask of it goes now
def dd.nobody(+n: Nat, +k: Nat, +i: String, +es: List<&2, Nat>, p: Bool) -> {Am.dstep(Am.D{n, [Am.Q{k, i, es, Am.OnClients{}}]}, Am.EDetach{Am.Nobody{}, p}) == (Am.D{n, ApprovalsDesk.ds_qs(ApprovalsDesk.ds_desk(Am.dstep(Am.D{k, Nil{}}, Am.EAsk{i, es, Am.Nobody{}, p})))}, Am.ASettle{k} <> ApprovalsDesk.ds_acts(Am.dstep(Am.D{k, Nil{}}, Am.EAsk{i, es, Am.Nobody{}, p}))) : Am.D & List<&2, Am.Act>}:
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

def ApprovalsDesk.approvals_desk_detach_one(n, k, i, es, h, p):
  (dd.parent(n, k, i, es, h, p), {==}, dd.nobody(n, k, i, es, p), {==})
