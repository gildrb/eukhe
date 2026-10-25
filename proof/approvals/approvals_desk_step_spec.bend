# eukhe: the proof of LAW approvals_desk_step_spec
#
# PROOF: the model and the spec are the same table: the session's decision
# is the spec's (ad.next, a case per session and parent), the clients'
# answer computes to the spec's fate, the request ids compare char by char
# as the spec's text_same (ad.same), and the searches (find, take) and the
# rerouting walk the questions as the spec does, by induction on the list
# (ad.find, ad.take, ad.reroute); each event then builds the same desk and
# acts (a case per answer of the search).

import Base
import ../../bend/approvals.bend as Am
import ../../laws/base.bend as LawsBase
import ../../laws/approvals/desk.bend as ApprovalsDesk
import ./base/desk.bend as LAD

def ad.next(+es: List<&2, Nat>, h: Am.Here, p: Bool) -> {Am.next(es, h, p) == ApprovalsDesk.sp_next(es, h, p) : Am.Next}:
  match h:
    case Am.Nobody{}:
      match p:
        case True{}:
          {==}
        case False{}:
          {==}
    case Am.GatewayOnly{}:
      %LAD.ap.rule(es) : {Am.Ends{Am.rule(es)} == Am.Ends{_} : Am.Next}
      {==}
    case Am.Clients{}:
      {==}

def ad.same(a: String, b: String) -> {Am.same(a, b) == LawsBase.text_same(a, b) : Bool}:
  match a b:
    case SNil{} SNil{}:
      {==}
    case SNil{} SCon{y, v}:
      {==}
    case SCon{x, u} SNil{}:
      {==}
    case SCon{+x, u} SCon{+y, v}:
      %ad.same(u, v) : {Bool.and(Char.is_eq(x, y), Am.same(u, v)) == Bool.and(Char.is_eq(x, y), _) : Bool}
      {==}

def ad.hit(b: Bool, q: Am.Q, +rest: List<&2, Am.Q>, r: Am.QF) -> {Am.pick.q(b, q, rest, r) == ApprovalsDesk.sp_hit(b, q, rest, r) : Am.QF}:
  match b:
    case True{}:
      {==}
    case False{}:
      match r:
        case Am.QFound{q2, r2}:
          {==}
        case Am.QNone{}:
          {==}

def ad.clients(w: Am.Wait) -> {Am.Wait.clients(w) == ApprovalsDesk.sp_clients(w) : Bool}:
  match w:
    case Am.OnClients{}:
      {==}
    case Am.OnParent{}:
      {==}

def ad.find(qs: List<&2, Am.Q>, +id: String) -> {Am.find(qs, id) == ApprovalsDesk.sp_find(qs, id) : Am.QF}:
  match qs:
    case Nil{}:
      {==}
    case q <> +rest:
      match q:
        case Am.Q{+k, +i, +es, +w}:
          %ad.find(rest, id) : {Am.pick.q(Bool.and(Am.Wait.clients(w), Am.same(i, id)), Am.Q{k, i, es, w}, rest, Am.find(rest, id)) == ApprovalsDesk.sp_hit(Bool.and(ApprovalsDesk.sp_clients(w), LawsBase.text_same(i, id)), Am.Q{k, i, es, w}, rest, _) : Am.QF}
          %ad.same(i, id) : {Am.pick.q(Bool.and(Am.Wait.clients(w), Am.same(i, id)), Am.Q{k, i, es, w}, rest, Am.find(rest, id)) == ApprovalsDesk.sp_hit(Bool.and(ApprovalsDesk.sp_clients(w), _), Am.Q{k, i, es, w}, rest, Am.find(rest, id)) : Am.QF}
          %ad.clients(w) : {Am.pick.q(Bool.and(Am.Wait.clients(w), Am.same(i, id)), Am.Q{k, i, es, w}, rest, Am.find(rest, id)) == ApprovalsDesk.sp_hit(Bool.and(_, Am.same(i, id)), Am.Q{k, i, es, w}, rest, Am.find(rest, id)) : Am.QF}
          ad.hit(Bool.and(Am.Wait.clients(w), Am.same(i, id)), Am.Q{k, i, es, w}, rest, Am.find(rest, id))

def ad.take(qs: List<&2, Am.Q>, +key: Nat) -> {Am.take(qs, key) == ApprovalsDesk.sp_take(qs, key) : Am.QF}:
  match qs:
    case Nil{}:
      {==}
    case q <> +rest:
      match q:
        case Am.Q{+k, +i, +es, +w}:
          %ad.take(rest, key) : {Am.pick.q(Nat.is_eq(k, key), Am.Q{k, i, es, w}, rest, Am.take(rest, key)) == ApprovalsDesk.sp_hit(Nat.is_eq(k, key), Am.Q{k, i, es, w}, rest, _) : Am.QF}
          ad.hit(Nat.is_eq(k, key), Am.Q{k, i, es, w}, rest, Am.take(rest, key))

def ad.rq(w: Am.Wait, +k: Nat, +i: String, +es: List<&2, Nat>, x: Am.Next, r: List<&2, Am.Q> & List<&2, Am.Act>) -> {Am.reroute.q(w, k, i, es, x, r) == ApprovalsDesk.sp_reroute.q(w, k, i, es, x, r) : List<&2, Am.Q> & List<&2, Am.Act>}:
  match w:
    case Am.OnParent{}:
      (qs, as) = r
      {==}
    case Am.OnClients{}:
      match x:
        case Am.Show{}:
          (qs, as) = r
          {==}
        case Am.Relay{}:
          (qs, as) = r
          {==}
        case Am.Ends{f}:
          (qs, as) = r
          {==}

def ad.reroute(qs: List<&2, Am.Q>, +h: Am.Here, +p: Bool) -> {Am.reroute(qs, h, p) == ApprovalsDesk.sp_reroute(qs, h, p) : List<&2, Am.Q> & List<&2, Am.Act>}:
  match qs:
    case Nil{}:
      {==}
    case q <> +rest:
      match q:
        case Am.Q{+k, +i, +es, +w}:
          %ad.reroute(rest, h, p) : {Am.reroute.q(w, k, i, es, Am.next(es, h, p), Am.reroute(rest, h, p)) == ApprovalsDesk.sp_reroute.q(w, k, i, es, ApprovalsDesk.sp_next(es, h, p), _) : List<&2, Am.Q> & List<&2, Am.Act>}
          %ad.next(es, h, p) : {Am.reroute.q(w, k, i, es, Am.next(es, h, p), Am.reroute(rest, h, p)) == ApprovalsDesk.sp_reroute.q(w, k, i, es, _, Am.reroute(rest, h, p)) : List<&2, Am.Q> & List<&2, Am.Act>}
          ad.rq(w, k, i, es, Am.next(es, h, p), Am.reroute(rest, h, p))

def ad.ask(+n: Nat, +id: String, +es: List<&2, Nat>, +qs: List<&2, Am.Q>, x: Am.Next) -> {Am.ask.with(n, id, es, qs, x) == ApprovalsDesk.sp_ask(n, id, es, qs, x) : Am.D & List<&2, Am.Act>}:
  match x:
    case Am.Show{}:
      {==}
    case Am.Relay{}:
      {==}
    case Am.Ends{f}:
      {==}

def ad.answer(+n: Nat, +qs: List<&2, Am.Q>, +yes: Bool, r: Am.QF) -> {Am.answer.with(n, qs, yes, r) == ApprovalsDesk.sp_answer(n, qs, yes, r) : Am.D & List<&2, Am.Act>}:
  match r:
    case Am.QFound{q, rest}:
      match q:
        case Am.Q{+k, i, +es, w}:
          %LAD.ap.answered(es, yes) : {(Am.D{n, rest}, [Am.ASettle{k}, Am.AWake{k, Am.answered(es, yes)}, Am.ATook{}]) == (Am.D{n, rest}, [Am.ASettle{k}, Am.AWake{k, _}, Am.ATook{}]) : Am.D & List<&2, Am.Act>}
          {==}
    case Am.QNone{}:
      {==}

def ad.put(+n: Nat, r: List<&2, Am.Q> & List<&2, Am.Act>) -> {Am.detach.put(n, r) == ApprovalsDesk.sp_put(n, r) : Am.D & List<&2, Am.Act>}:
  (qs, as) = r
  {==}

def ad.detach(+n: Nat, +qs: List<&2, Am.Q>, h: Am.Here, +p: Bool) -> {Am.detach.with(n, qs, h, p) == ApprovalsDesk.sp_detach(n, qs, h, p) : Am.D & List<&2, Am.Act>}:
  match h:
    case Am.Clients{}:
      {==}
    case Am.Nobody{}:
      %ad.reroute(qs, Am.Nobody{}, p) : {Am.detach.put(n, Am.reroute(qs, Am.Nobody{}, p)) == ApprovalsDesk.sp_put(n, _) : Am.D & List<&2, Am.Act>}
      ad.put(n, Am.reroute(qs, Am.Nobody{}, p))
    case Am.GatewayOnly{}:
      %ad.reroute(qs, Am.GatewayOnly{}, p) : {Am.detach.put(n, Am.reroute(qs, Am.GatewayOnly{}, p)) == ApprovalsDesk.sp_put(n, _) : Am.D & List<&2, Am.Act>}
      ad.put(n, Am.reroute(qs, Am.GatewayOnly{}, p))

def ad.cancel(+n: Nat, +qs: List<&2, Am.Q>, r: Am.QF) -> {Am.cancel.with(n, qs, r) == ApprovalsDesk.sp_cancel(n, qs, r) : Am.D & List<&2, Am.Act>}:
  match r:
    case Am.QFound{q, rest}:
      match q:
        case Am.Q{k, i, es, w}:
          match w:
            case Am.OnClients{}:
              {==}
            case Am.OnParent{}:
              {==}
    case Am.QNone{}:
      {==}

def ad.back(+n: Nat, +qs: List<&2, Am.Q>, +f: Am.Fate, r: Am.QF) -> {Am.back.with(n, qs, f, r) == ApprovalsDesk.sp_back(n, qs, f, r) : Am.D & List<&2, Am.Act>}:
  match r:
    case Am.QFound{q, rest}:
      match q:
        case Am.Q{k, i, es, w}:
          match w:
            case Am.OnParent{}:
              {==}
            case Am.OnClients{}:
              {==}
    case Am.QNone{}:
      {==}

def ApprovalsDesk.approvals_desk_step_spec(d, e):
  match d:
    case Am.D{+n, +qs}:
      match e:
        case Am.EAsk{+id, +es, +h, +p}:
          %ad.next(es, h, p) : {Am.ask.with(n, id, es, qs, Am.next(es, h, p)) == ApprovalsDesk.sp_ask(n, id, es, qs, _) : Am.D & List<&2, Am.Act>}
          ad.ask(n, id, es, qs, Am.next(es, h, p))
        case Am.EAnswer{+id, +yes}:
          %ad.find(qs, id) : {Am.answer.with(n, qs, yes, Am.find(qs, id)) == ApprovalsDesk.sp_answer(n, qs, yes, _) : Am.D & List<&2, Am.Act>}
          ad.answer(n, qs, yes, Am.find(qs, id))
        case Am.EDetach{h, p}:
          ad.detach(n, qs, h, p)
        case Am.ECancel{+key}:
          %ad.take(qs, key) : {Am.cancel.with(n, qs, Am.take(qs, key)) == ApprovalsDesk.sp_cancel(n, qs, _) : Am.D & List<&2, Am.Act>}
          ad.cancel(n, qs, Am.take(qs, key))
        case Am.EBack{+key, +f}:
          %ad.take(qs, key) : {Am.back.with(n, qs, f, Am.take(qs, key)) == ApprovalsDesk.sp_back(n, qs, f, _) : Am.D & List<&2, Am.Act>}
          ad.back(n, qs, f, Am.take(qs, key))
