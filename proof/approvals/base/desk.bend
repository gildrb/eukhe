# eukhe: lemmas the proofs of laws/approvals/desk.bend share: the model's
# gateway rule and the clients' answer read through the laws' terms; the
# desk's searches (find: the oldest question its frame names, take: the
# first with a key) and its rerouting of a detach, walked by induction on
# the questions

import Base
import ../../../bend/approvals.bend as Am
import ../../../bend/tools.bend as Tl
import ../../../laws/base.bend as LawsBase
import ../../../laws/approvals/desk.bend as ApprovalsDesk
import ../../base/staging.bend as LStg

# Logic
# -----

def ad.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def ad.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : ad.BD(_, A, Unit)
  Unit{}

def ad.and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def ad.and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      ad.absurd({b == True{} : Bool}, e)

def ad.not_t(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      ad.absurd({True{} == False{} : Bool}, e)
    case False{}:
      {==}

def ad.or_true(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def ad.nat_refl(x: Nat) -> {Nat.is_eq(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      ad.nat_refl(p)

# The gateway rule and the clients' answer
# ----------------------------------------

# the model's membership is the spec's
def ap.has(xs: List<&2, Nat>, +x: Nat) -> {Tl.elem(xs, x) == ApprovalsDesk.sp_has(xs, x) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> rest:
      %ap.has(rest, x) : {Bool.or(Nat.is_eq(y, x), Tl.elem(rest, x)) == Bool.or(Nat.is_eq(y, x), _) : Bool}
      {==}

# the clients' answer
def ap.answered(+es: List<&2, Nat>, y: Bool) -> {Am.answered(es, y) == ApprovalsDesk.sp_answered(es, y) : Am.Fate}:
  match y:
    case True{}:
      {==}
    case False{}:
      {==}

# Request ids
# -----------

# the model compares ids char by char as the laws' text_same does
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

# an id is the same as itself
def ad.same_refl(+a: String) -> {Am.same(a, a) == True{} : Bool}:
  Equal.trans(Bool, Am.same(a, a), LawsBase.text_same(a, a), True{}, ad.same(a, a), LStg.stg.same_refl(a))

# a question the laws say waits on no clients under id is no hit of find
def ad.miss(w: Am.Wait, +i: String, +id: String, h: {Bool.not(Bool.and(ApprovalsDesk.sp_clients(w), LawsBase.text_same(i, id))) == True{} : Bool}) -> {Bool.and(Am.Wait.clients(w), Am.same(i, id)) == False{} : Bool}:
  match w:
    case Am.OnClients{}:
      %Equal.sym(Bool, Am.same(i, id), LawsBase.text_same(i, id), ad.same(i, id)) : {_ == False{} : Bool}
      ad.not_t(LawsBase.text_same(i, id), h)
    case Am.OnParent{}:
      {==}

# The searches
# ------------

# find: the first question waiting on the clients under id, after a pre
# with none
def ad.find_hit(pre: List<&2, Am.Q>, +k: Nat, +id: String, +es: List<&2, Nat>, +post: List<&2, Am.Q>, none: {ApprovalsDesk.ds_none_open(pre, id) == True{} : Bool}) -> {Am.find(List.append(&2, Am.Q, pre, Am.Q{k, id, es, Am.OnClients{}} <> post), id) == Am.QFound{Am.Q{k, id, es, Am.OnClients{}}, List.append(&2, Am.Q, pre, post)} : Am.QF}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, Am.same(id, id), True{}, ad.same_refl(id)) : {Am.pick.q(_, Am.Q{k, id, es, Am.OnClients{}}, post, Am.find(post, id)) == Am.QFound{Am.Q{k, id, es, Am.OnClients{}}, post} : Am.QF}
      {==}
    case q0 <> +rest:
      match q0:
        case Am.Q{+k0, +i0, +es0, +w0}:
          +h = none
          +a = Bool.not(Bool.and(ApprovalsDesk.sp_clients(w0), LawsBase.text_same(i0, id)))
          +miss = ad.miss(w0, i0, id, ad.and_l(a, ApprovalsDesk.ds_none_open(rest, id), h))
          +ih = ad.find_hit(rest, k, id, es, post, ad.and_r(a, ApprovalsDesk.ds_none_open(rest, id), h))
          +Q = {Am.Q{k, id, es, Am.OnClients{}} : Am.Q}
          +L = List.append(&2, Am.Q, rest, Q <> post)
          %Equal.sym(Bool, Bool.and(Am.Wait.clients(w0), Am.same(i0, id)), False{}, miss) : {Am.pick.q(_, Am.Q{k0, i0, es0, w0}, L, Am.find(L, id)) == Am.QFound{Q, Am.Q{k0, i0, es0, w0} <> List.append(&2, Am.Q, rest, post)} : Am.QF}
          %Equal.sym(Am.QF, Am.find(L, id), Am.QFound{Q, List.append(&2, Am.Q, rest, post)}, ih) : {Am.pick.q(False{}, Am.Q{k0, i0, es0, w0}, L, _) == Am.QFound{Q, Am.Q{k0, i0, es0, w0} <> List.append(&2, Am.Q, rest, post)} : Am.QF}
          {==}

# find: no question waiting on the clients under id, no hit
def ad.find_none(qs: List<&2, Am.Q>, +id: String, none: {ApprovalsDesk.ds_none_open(qs, id) == True{} : Bool}) -> {Am.find(qs, id) == Am.QNone{} : Am.QF}:
  match qs:
    case Nil{}:
      {==}
    case q0 <> +rest:
      match q0:
        case Am.Q{+k0, +i0, +es0, +w0}:
          +h = none
          +a = Bool.not(Bool.and(ApprovalsDesk.sp_clients(w0), LawsBase.text_same(i0, id)))
          +miss = ad.miss(w0, i0, id, ad.and_l(a, ApprovalsDesk.ds_none_open(rest, id), h))
          +ih = ad.find_none(rest, id, ad.and_r(a, ApprovalsDesk.ds_none_open(rest, id), h))
          %Equal.sym(Bool, Bool.and(Am.Wait.clients(w0), Am.same(i0, id)), False{}, miss) : {Am.pick.q(_, Am.Q{k0, i0, es0, w0}, rest, Am.find(rest, id)) == Am.QNone{} : Am.QF}
          %Equal.sym(Am.QF, Am.find(rest, id), Am.QNone{}, ih) : {Am.pick.q(False{}, Am.Q{k0, i0, es0, w0}, rest, _) == Am.QNone{} : Am.QF}
          {==}

# take: the first question with the key k, after a pre with none
def ad.take_hit(pre: List<&2, Am.Q>, +k: Nat, +i: String, +es: List<&2, Nat>, +w: Am.Wait, +post: List<&2, Am.Q>, none: {ApprovalsDesk.ds_no_key(pre, k) == True{} : Bool}) -> {Am.take(List.append(&2, Am.Q, pre, Am.Q{k, i, es, w} <> post), k) == Am.QFound{Am.Q{k, i, es, w}, List.append(&2, Am.Q, pre, post)} : Am.QF}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_eq(k, k), True{}, ad.nat_refl(k)) : {Am.pick.q(_, Am.Q{k, i, es, w}, post, Am.take(post, k)) == Am.QFound{Am.Q{k, i, es, w}, post} : Am.QF}
      {==}
    case q0 <> +rest:
      match q0:
        case Am.Q{+k0, +i0, +es0, +w0}:
          +h = none
          +a = Bool.not(Nat.is_eq(k0, k))
          +miss = ad.not_t(Nat.is_eq(k0, k), ad.and_l(a, ApprovalsDesk.ds_no_key(rest, k), h))
          +ih = ad.take_hit(rest, k, i, es, w, post, ad.and_r(a, ApprovalsDesk.ds_no_key(rest, k), h))
          +Q = {Am.Q{k, i, es, w} : Am.Q}
          +L = List.append(&2, Am.Q, rest, Q <> post)
          %Equal.sym(Bool, Nat.is_eq(k0, k), False{}, miss) : {Am.pick.q(_, Am.Q{k0, i0, es0, w0}, L, Am.take(L, k)) == Am.QFound{Q, Am.Q{k0, i0, es0, w0} <> List.append(&2, Am.Q, rest, post)} : Am.QF}
          %Equal.sym(Am.QF, Am.take(L, k), Am.QFound{Q, List.append(&2, Am.Q, rest, post)}, ih) : {Am.pick.q(False{}, Am.Q{k0, i0, es0, w0}, L, _) == Am.QFound{Q, Am.Q{k0, i0, es0, w0} <> List.append(&2, Am.Q, rest, post)} : Am.QF}
          {==}

# take: no question with the key k, no hit
def ad.take_none(qs: List<&2, Am.Q>, +k: Nat, none: {ApprovalsDesk.ds_no_key(qs, k) == True{} : Bool}) -> {Am.take(qs, k) == Am.QNone{} : Am.QF}:
  match qs:
    case Nil{}:
      {==}
    case q0 <> +rest:
      match q0:
        case Am.Q{+k0, +i0, +es0, +w0}:
          +h = none
          +a = Bool.not(Nat.is_eq(k0, k))
          +miss = ad.not_t(Nat.is_eq(k0, k), ad.and_l(a, ApprovalsDesk.ds_no_key(rest, k), h))
          +ih = ad.take_none(rest, k, ad.and_r(a, ApprovalsDesk.ds_no_key(rest, k), h))
          %Equal.sym(Bool, Nat.is_eq(k0, k), False{}, miss) : {Am.pick.q(_, Am.Q{k0, i0, es0, w0}, rest, Am.take(rest, k)) == Am.QNone{} : Am.QF}
          %Equal.sym(Am.QF, Am.take(rest, k), Am.QNone{}, ih) : {Am.pick.q(False{}, Am.Q{k0, i0, es0, w0}, rest, _) == Am.QNone{} : Am.QF}
          {==}

# The rerouting of a detach
# -------------------------

def ad.qs(r: List<&2, Am.Q> & List<&2, Am.Act>) -> List<&2, Am.Q>:
  (qs, as) = r
  qs

def ad.as(r: List<&2, Am.Q> & List<&2, Am.Act>) -> List<&2, Am.Act>:
  (qs, as) = r
  as

def ad.eta(r: List<&2, Am.Q> & List<&2, Am.Act>) -> {r == (ad.qs(r), ad.as(r)) : List<&2, Am.Q> & List<&2, Am.Act>}:
  (a, b) = r
  {==}

# one question rerouted before the pieces of the rest is that question
# rerouted before the first piece, then the second piece
def ad.rq_app(w: Am.Wait, +k: Nat, +i: String, +es: List<&2, Nat>, x: Am.Next, r: List<&2, Am.Q> & List<&2, Am.Act>, +ys: List<&2, Am.Q>, +bs: List<&2, Am.Act>) -> {Am.reroute.q(w, k, i, es, x, (List.append(&2, Am.Q, ad.qs(r), ys), List.append(&2, Am.Act, ad.as(r), bs))) == (List.append(&2, Am.Q, ad.qs(Am.reroute.q(w, k, i, es, x, r)), ys), List.append(&2, Am.Act, ad.as(Am.reroute.q(w, k, i, es, x, r)), bs)) : List<&2, Am.Q> & List<&2, Am.Act>}:
  match w:
    case Am.OnParent{}:
      (a, b) = r
      {==}
    case Am.OnClients{}:
      match x:
        case Am.Show{}:
          (a, b) = r
          {==}
        case Am.Relay{}:
          (a, b) = r
          {==}
        case Am.Ends{f}:
          (a, b) = r
          {==}

# the rerouting of xs then ys is xs's, then ys's
def ad.rr_app(xs: List<&2, Am.Q>, +ys: List<&2, Am.Q>, +h: Am.Here, +p: Bool) -> {Am.reroute(List.append(&2, Am.Q, xs, ys), h, p) == (List.append(&2, Am.Q, ad.qs(Am.reroute(xs, h, p)), ad.qs(Am.reroute(ys, h, p))), List.append(&2, Am.Act, ad.as(Am.reroute(xs, h, p)), ad.as(Am.reroute(ys, h, p)))) : List<&2, Am.Q> & List<&2, Am.Act>}:
  match xs:
    case Nil{}:
      ad.eta(Am.reroute(ys, h, p))
    case q <> +rest:
      match q:
        case Am.Q{+k, +i, +es, +w}:
          %Equal.sym(List<&2, Am.Q> & List<&2, Am.Act>, Am.reroute(List.append(&2, Am.Q, rest, ys), h, p), (List.append(&2, Am.Q, ad.qs(Am.reroute(rest, h, p)), ad.qs(Am.reroute(ys, h, p))), List.append(&2, Am.Act, ad.as(Am.reroute(rest, h, p)), ad.as(Am.reroute(ys, h, p)))), ad.rr_app(rest, ys, h, p)) : {Am.reroute.q(w, k, i, es, Am.next(es, h, p), _) == (List.append(&2, Am.Q, ad.qs(Am.reroute.q(w, k, i, es, Am.next(es, h, p), Am.reroute(rest, h, p))), ad.qs(Am.reroute(ys, h, p))), List.append(&2, Am.Act, ad.as(Am.reroute.q(w, k, i, es, Am.next(es, h, p), Am.reroute(rest, h, p))), ad.as(Am.reroute(ys, h, p)))) : List<&2, Am.Q> & List<&2, Am.Act>}
          ad.rq_app(w, k, i, es, Am.next(es, h, p), Am.reroute(rest, h, p), ad.qs(Am.reroute(ys, h, p)), ad.as(Am.reroute(ys, h, p)))

# a desk put from two pieces is the two desks' pieces
def ad.put2(+n: Nat, r1: List<&2, Am.Q> & List<&2, Am.Act>, r2: List<&2, Am.Q> & List<&2, Am.Act>) -> {Am.detach.put(n, (List.append(&2, Am.Q, ad.qs(r1), ad.qs(r2)), List.append(&2, Am.Act, ad.as(r1), ad.as(r2)))) == (Am.D{n, List.append(&2, Am.Q, ApprovalsDesk.ds_qs(ApprovalsDesk.ds_desk(Am.detach.put(n, r1))), ApprovalsDesk.ds_qs(ApprovalsDesk.ds_desk(Am.detach.put(n, r2))))}, List.append(&2, Am.Act, ApprovalsDesk.ds_acts(Am.detach.put(n, r1)), ApprovalsDesk.ds_acts(Am.detach.put(n, r2)))) : Am.D & List<&2, Am.Act>}:
  (a1, b1) = r1
  (a2, b2) = r2
  {==}
