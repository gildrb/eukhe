# eukhe: the proof of LAW approvals_desk_wakes_once
#
# PROOF: the keys stay fresh and distinct. A key x has a potential at a
# desk D{n, qs}: how many open questions hold it (pw.qc), plus 1 when x is
# at or above n, a key not handed out yet (pw.ge). Fresh and distinct keys
# are exactly potentials of at most 1, and the empty desk has potential 1
# for every key. Each event wakes x at most as often as its potential
# falls (pw.step, a case per event): an ask hands n out, to a kept
# question or to its own wake (pw.ge_step); an answer or a parent's answer
# moves the question it finds from the desk to its wake, and a cancel
# drops it (the searches split the desk: pw.find, pw.take); a detach moves
# each question it ends from the desk to its wake and keeps the others
# (pw.reroute). So the wakes over any run of events are at most the first
# desk's potential (pw.run): at most 1 from the empty desk.

import Base
import ../../bend/approvals.bend as Am
import ../../laws/approvals/desk.bend as ApprovalsDesk
import ../base/logic/logic.bend as LLogicLogic

# Numbers
# -------

def pw.le0(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pw.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pw.le_refl(p)

def pw.le_succ_r(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n q:
      {==}
    case 1n+p 0n:
      LLogicLogic.pc.absurd_ft({Nat.is_le(1n+p, 1n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pw.le_succ_r(p, q, e)

def pw.le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n q r:
      pw.le0(r)
    case 1n+p 0n r:
      LLogicLogic.pc.absurd_ft({Nat.is_le(1n+p, r) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      LLogicLogic.pc.absurd_ft({False{} == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      pw.le_trans(p, q, r, ab, bc)

# m <= h + m
def pw.le_add(h: Nat, +m: Nat) -> {Nat.is_le(m, Nat.add(h, m)) == True{} : Bool}:
  match h:
    case 0n:
      pw.le_refl(m)
    case 1n+p:
      +q = p
      pw.le_succ_r(m, Nat.add(q, m), pw.le_add(q, m))

# c + a <= c + b when a <= b
def pw.le_mono(c: Nat, -a: Nat, -b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}:
  match c:
    case 0n:
      e
    case 1n+p:
      pw.le_mono(p, a, b, e)

def pw.le_eq(-a: Nat, +b: Nat, e: {a == b : Nat}) -> {Nat.is_le(a, b) == True{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {Nat.is_le(_, b) == True{} : Bool}
  pw.le_refl(b)

def pw.add_succ_r(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, 1n+b), 1n+Nat.add(p, b), pw.add_succ_r(p, b))

def pw.assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, Nat.add(b, c)), Nat.add(Nat.add(p, b), c), pw.assoc(p, b, c))

# a + (b + c) = b + (a + c)
def pw.swap(a: Nat, +b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+Nat.add(p, c)), 1n+Nat.add(b, Nat.add(p, c)), pw.add_succ_r(b, Nat.add(p, c))) : {1n+Nat.add(p, Nat.add(b, c)) == _ : Nat}
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, Nat.add(b, c)), Nat.add(b, Nat.add(p, c)), pw.swap(p, b, c))

# Counts
# ------

def pw.add_hit(+a: Nat, b: Bool, -c: Nat) -> {Nat.add(a, ApprovalsDesk.dw_hit(b, c)) == ApprovalsDesk.dw_hit(b, Nat.add(a, c)) : Nat}:
  match b:
    case True{}:
      pw.add_succ_r(a, c)
    case False{}:
      {==}

def pw.hit_add(b: Bool, -a: Nat, -c: Nat) -> {ApprovalsDesk.dw_hit(b, Nat.add(a, c)) == Nat.add(ApprovalsDesk.dw_hit(b, a), c) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def pw.hit0(b: Bool, -c: Nat) -> {Nat.add(ApprovalsDesk.dw_hit(b, 0n), c) == ApprovalsDesk.dw_hit(b, c) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the count of x in a ++ b, split
def pw.count_split(a: List<&2, Nat>, -b: List<&2, Nat>, +x: Nat) -> {Nat.add(ApprovalsDesk.dw_count(a, x), ApprovalsDesk.dw_count(b, x)) == ApprovalsDesk.dw_count(List.append(&2, Nat, a, b), x) : Nat}:
  match a:
    case Nil{}:
      {==}
    case +y <> t:
      %pw.count_split(t, b, x) : {Nat.add(ApprovalsDesk.dw_hit(Nat.is_eq(y, x), ApprovalsDesk.dw_count(t, x)), ApprovalsDesk.dw_count(b, x)) == ApprovalsDesk.dw_hit(Nat.is_eq(y, x), _) : Nat}
      Equal.sym(Nat, ApprovalsDesk.dw_hit(Nat.is_eq(y, x), Nat.add(ApprovalsDesk.dw_count(t, x), ApprovalsDesk.dw_count(b, x))), Nat.add(ApprovalsDesk.dw_hit(Nat.is_eq(y, x), ApprovalsDesk.dw_count(t, x)), ApprovalsDesk.dw_count(b, x)), pw.hit_add(Nat.is_eq(y, x), ApprovalsDesk.dw_count(t, x), ApprovalsDesk.dw_count(b, x)))

# Potential
# ---------

# how many questions of qs hold the key x
def pw.qc(qs: List<&2, Am.Q>, +x: Nat) -> Nat:
  match qs:
    case Nil{}:
      0n
    case q <> t:
      match q:
        case Am.Q{k, i, es, w}:
          ApprovalsDesk.dw_hit(Nat.is_eq(k, x), pw.qc(t, x))

# 1 when the key x is at or above n (not handed out yet), else 0
def pw.ge(n: Nat, x: Nat) -> Nat:
  match n x:
    case 0n _:
      1n
    case 1n+m 0n:
      0n
    case 1n+m 1n+y:
      pw.ge(m, y)

def pw.pot(d: Am.D, +x: Nat) -> Nat:
  match d:
    case Am.D{n, qs}:
      Nat.add(pw.qc(qs, x), pw.ge(n, x))

# the wakes of x in r's acts, plus the potential of x at r's desk
def pw.after(r: Am.D & List<&2, Am.Act>, +x: Nat) -> Nat:
  (d, as) = r
  Nat.add(ApprovalsDesk.dw_count(ApprovalsDesk.dw_woke(as), x), pw.pot(d, x))

def pw.proj(r: Am.D & List<&2, Am.Act>, +x: Nat) -> {pw.after(r, x) == Nat.add(ApprovalsDesk.dw_count(ApprovalsDesk.dw_woke(ApprovalsDesk.ds_acts(r)), x), pw.pot(ApprovalsDesk.ds_desk(r), x)) : Nat}:
  (d, as) = r
  {==}

# handing n out: the key n leaves the keys ahead
def pw.ge_step(n: Nat, x: Nat) -> {Nat.add(ApprovalsDesk.dw_hit(Nat.is_eq(n, x), 0n), pw.ge(1n+n, x)) == pw.ge(n, x) : Nat}:
  match n x:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+m 0n:
      {==}
    case 1n+m 1n+y:
      pw.ge_step(m, y)

def pw.qc_append(qs: List<&2, Am.Q>, -l: List<&2, Am.Q>, +x: Nat) -> {pw.qc(List.append(&2, Am.Q, qs, l), x) == Nat.add(pw.qc(qs, x), pw.qc(l, x)) : Nat}:
  match qs:
    case Nil{}:
      {==}
    case q <> t:
      match q:
        case Am.Q{+k, i, es, w}:
          %Equal.sym(Nat, pw.qc(List.append(&2, Am.Q, t, l), x), Nat.add(pw.qc(t, x), pw.qc(l, x)), pw.qc_append(t, l, x)) : {ApprovalsDesk.dw_hit(Nat.is_eq(k, x), _) == Nat.add(ApprovalsDesk.dw_hit(Nat.is_eq(k, x), pw.qc(t, x)), pw.qc(l, x)) : Nat}
          pw.hit_add(Nat.is_eq(k, x), pw.qc(t, x), pw.qc(l, x))

# The searches split the desk
# ---------------------------

# the potential of x in what a search found and what it left
def pw.qf(r: Am.QF, +qs: List<&2, Am.Q>, +x: Nat) -> Nat:
  match r:
    case Am.QFound{q, rest}:
      Nat.add(pw.qc([q], x), pw.qc(rest, x))
    case Am.QNone{}:
      pw.qc(qs, x)

def pw.pick(b: Bool, +k: Nat, i: String, es: List<&2, Nat>, w: Am.Wait, +rest: List<&2, Am.Q>, r: Am.QF, +x: Nat, ih: {pw.qf(r, rest, x) == pw.qc(rest, x) : Nat}) -> {pw.qf(Am.pick.q(b, Am.Q{k, i, es, w}, rest, r), Am.Q{k, i, es, w} <> rest, x) == pw.qc(Am.Q{k, i, es, w} <> rest, x) : Nat}:
  match b:
    case True{}:
      pw.hit0(Nat.is_eq(k, x), pw.qc(rest, x))
    case False{}:
      match r:
        case Am.QFound{q2, r2}:
          %ih : {Nat.add(pw.qc([q2], x), ApprovalsDesk.dw_hit(Nat.is_eq(k, x), pw.qc(r2, x))) == ApprovalsDesk.dw_hit(Nat.is_eq(k, x), _) : Nat}
          pw.add_hit(pw.qc([q2], x), Nat.is_eq(k, x), pw.qc(r2, x))
        case Am.QNone{}:
          {==}

def pw.find(qs: List<&2, Am.Q>, +id: String, +x: Nat) -> {pw.qf(Am.find(qs, id), qs, x) == pw.qc(qs, x) : Nat}:
  match qs:
    case Nil{}:
      {==}
    case q <> +rest:
      match q:
        case Am.Q{+k, +i, +es, +w}:
          pw.pick(Bool.and(Am.Wait.clients(w), Am.same(i, id)), k, i, es, w, rest, Am.find(rest, id), x, pw.find(rest, id, x))

def pw.take(qs: List<&2, Am.Q>, +key: Nat, +x: Nat) -> {pw.qf(Am.take(qs, key), qs, x) == pw.qc(qs, x) : Nat}:
  match qs:
    case Nil{}:
      {==}
    case q <> +rest:
      match q:
        case Am.Q{+k, +i, +es, +w}:
          pw.pick(Nat.is_eq(k, key), k, i, es, w, rest, Am.take(rest, key), x, pw.take(rest, key, x))

# A detach moves each question it ends to its wake
# ------------------------------------------------

def pw.rq(r: List<&2, Am.Q> & List<&2, Am.Act>) -> List<&2, Am.Q>:
  (qs, as) = r
  qs

def pw.ra(r: List<&2, Am.Q> & List<&2, Am.Act>) -> List<&2, Am.Act>:
  (qs, as) = r
  as

# a kept question: its key stays on the desk
def pw.keep(+w0: Nat, b: Bool, +q0: Nat, -c: Nat, ih: {Nat.add(w0, q0) == c : Nat}) -> {Nat.add(w0, ApprovalsDesk.dw_hit(b, q0)) == ApprovalsDesk.dw_hit(b, c) : Nat}:
  %ih : {Nat.add(w0, ApprovalsDesk.dw_hit(b, q0)) == ApprovalsDesk.dw_hit(b, _) : Nat}
  pw.add_hit(w0, b, q0)

# an ended question: its key goes to its wake
def pw.ends(b: Bool, -w0: Nat, -q0: Nat, -c: Nat, ih: {Nat.add(w0, q0) == c : Nat}) -> {Nat.add(ApprovalsDesk.dw_hit(b, w0), q0) == ApprovalsDesk.dw_hit(b, c) : Nat}:
  %ih : {Nat.add(ApprovalsDesk.dw_hit(b, w0), q0) == ApprovalsDesk.dw_hit(b, _) : Nat}
  Equal.sym(Nat, ApprovalsDesk.dw_hit(b, Nat.add(w0, q0)), Nat.add(ApprovalsDesk.dw_hit(b, w0), q0), pw.hit_add(b, w0, q0))

def pw.rq1(w: Am.Wait, +k: Nat, +i: String, +es: List<&2, Nat>, nx: Am.Next, r: List<&2, Am.Q> & List<&2, Am.Act>, +x: Nat, -c: Nat, ih: {Nat.add(ApprovalsDesk.dw_count(ApprovalsDesk.dw_woke(pw.ra(r)), x), pw.qc(pw.rq(r), x)) == c : Nat}) -> {Nat.add(ApprovalsDesk.dw_count(ApprovalsDesk.dw_woke(pw.ra(Am.reroute.q(w, k, i, es, nx, r))), x), pw.qc(pw.rq(Am.reroute.q(w, k, i, es, nx, r)), x)) == ApprovalsDesk.dw_hit(Nat.is_eq(k, x), c) : Nat}:
  match w:
    case Am.OnParent{}:
      (qs, as) = r
      pw.keep(ApprovalsDesk.dw_count(ApprovalsDesk.dw_woke(as), x), Nat.is_eq(k, x), pw.qc(qs, x), c, ih)
    case Am.OnClients{}:
      match nx:
        case Am.Show{}:
          (qs, as) = r
          pw.keep(ApprovalsDesk.dw_count(ApprovalsDesk.dw_woke(as), x), Nat.is_eq(k, x), pw.qc(qs, x), c, ih)
        case Am.Relay{}:
          (qs, as) = r
          pw.keep(ApprovalsDesk.dw_count(ApprovalsDesk.dw_woke(as), x), Nat.is_eq(k, x), pw.qc(qs, x), c, ih)
        case Am.Ends{f}:
          (qs, as) = r
          pw.ends(Nat.is_eq(k, x), ApprovalsDesk.dw_count(ApprovalsDesk.dw_woke(as), x), pw.qc(qs, x), c, ih)

def pw.reroute(qs: List<&2, Am.Q>, +h: Am.Here, +p: Bool, +x: Nat) -> {Nat.add(ApprovalsDesk.dw_count(ApprovalsDesk.dw_woke(pw.ra(Am.reroute(qs, h, p))), x), pw.qc(pw.rq(Am.reroute(qs, h, p)), x)) == pw.qc(qs, x) : Nat}:
  match qs:
    case Nil{}:
      {==}
    case q <> +rest:
      match q:
        case Am.Q{+k, +i, +es, +w}:
          pw.rq1(w, k, i, es, Am.next(es, h, p), Am.reroute(rest, h, p), x, pw.qc(rest, x), pw.reroute(rest, h, p, x))

# Each event
# ----------

# the desk n, qs before an event whose reply's wakes and desk total t
def pw.goal(+t: Nat, +n: Nat, +qs: List<&2, Am.Q>, +x: Nat) -> Type:
  {Nat.is_le(t, Nat.add(pw.qc(qs, x), pw.ge(n, x))) == True{} : Bool}

# a question kept on the desk under the next key
def pw.fresh(+n: Nat, id: String, es: List<&2, Nat>, +qs: List<&2, Am.Q>, w: Am.Wait, +x: Nat) -> {Nat.is_le(Nat.add(pw.qc(List.append(&2, Am.Q, qs, [Am.Q{n, id, es, w}]), x), pw.ge(1n+n, x)), Nat.add(pw.qc(qs, x), pw.ge(n, x))) == True{} : Bool}:
  %Equal.sym(Nat, pw.qc(List.append(&2, Am.Q, qs, [Am.Q{n, id, es, w}]), x), Nat.add(pw.qc(qs, x), ApprovalsDesk.dw_hit(Nat.is_eq(n, x), 0n)), pw.qc_append(qs, [Am.Q{n, id, es, w}], x)) : {Nat.is_le(Nat.add(_, pw.ge(1n+n, x)), Nat.add(pw.qc(qs, x), pw.ge(n, x))) == True{} : Bool}
  %pw.assoc(pw.qc(qs, x), ApprovalsDesk.dw_hit(Nat.is_eq(n, x), 0n), pw.ge(1n+n, x)) : {Nat.is_le(_, Nat.add(pw.qc(qs, x), pw.ge(n, x))) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(ApprovalsDesk.dw_hit(Nat.is_eq(n, x), 0n), pw.ge(1n+n, x)), pw.ge(n, x), pw.ge_step(n, x)) : {Nat.is_le(Nat.add(pw.qc(qs, x), _), Nat.add(pw.qc(qs, x), pw.ge(n, x))) == True{} : Bool}
  pw.le_refl(Nat.add(pw.qc(qs, x), pw.ge(n, x)))

def pw.ask(+n: Nat, id: String, es: List<&2, Nat>, +qs: List<&2, Am.Q>, nx: Am.Next, +x: Nat) -> pw.goal(pw.after(Am.ask.with(n, id, es, qs, nx), x), n, qs, x):
  match nx:
    case Am.Show{}:
      pw.fresh(n, id, es, qs, Am.OnClients{}, x)
    case Am.Relay{}:
      pw.fresh(n, id, es, qs, Am.OnParent{}, x)
    case Am.Ends{f}:
      +hn = ApprovalsDesk.dw_hit(Nat.is_eq(n, x), 0n)
      +q0 = pw.qc(qs, x)
      pw.le_eq(Nat.add(hn, Nat.add(q0, pw.ge(1n+n, x))), Nat.add(q0, pw.ge(n, x)), Equal.trans(Nat, Nat.add(hn, Nat.add(q0, pw.ge(1n+n, x))), Nat.add(q0, Nat.add(hn, pw.ge(1n+n, x))), Nat.add(q0, pw.ge(n, x)), pw.swap(hn, q0, pw.ge(1n+n, x)), Equal.cong(Nat, Nat, z => Nat.add(q0, z), Nat.add(hn, pw.ge(1n+n, x)), pw.ge(n, x), pw.ge_step(n, x))))

# a found question's key moves from the desk to its wake
def pw.moved(+k: Nat, +rest: List<&2, Am.Q>, +g: Nat, +x: Nat, +c: Nat, sp: {Nat.add(ApprovalsDesk.dw_hit(Nat.is_eq(k, x), 0n), pw.qc(rest, x)) == c : Nat}) -> {Nat.is_le(Nat.add(ApprovalsDesk.dw_hit(Nat.is_eq(k, x), 0n), Nat.add(pw.qc(rest, x), g)), Nat.add(c, g)) == True{} : Bool}:
  +hk = ApprovalsDesk.dw_hit(Nat.is_eq(k, x), 0n)
  +q0 = pw.qc(rest, x)
  pw.le_eq(Nat.add(hk, Nat.add(q0, g)), Nat.add(c, g), Equal.trans(Nat, Nat.add(hk, Nat.add(q0, g)), Nat.add(Nat.add(hk, q0), g), Nat.add(c, g), pw.assoc(hk, q0, g), Equal.cong(Nat, Nat, z => Nat.add(z, g), Nat.add(hk, q0), c, sp)))

# a found question's key leaves the desk with no wake
def pw.dropped(+k: Nat, +rest: List<&2, Am.Q>, +g: Nat, +x: Nat, -c: Nat, sp: {Nat.add(ApprovalsDesk.dw_hit(Nat.is_eq(k, x), 0n), pw.qc(rest, x)) == c : Nat}) -> {Nat.is_le(Nat.add(pw.qc(rest, x), g), Nat.add(c, g)) == True{} : Bool}:
  %sp : {Nat.is_le(Nat.add(pw.qc(rest, x), g), Nat.add(_, g)) == True{} : Bool}
  %pw.assoc(ApprovalsDesk.dw_hit(Nat.is_eq(k, x), 0n), pw.qc(rest, x), g) : {Nat.is_le(Nat.add(pw.qc(rest, x), g), _) == True{} : Bool}
  pw.le_add(ApprovalsDesk.dw_hit(Nat.is_eq(k, x), 0n), Nat.add(pw.qc(rest, x), g))

def pw.answer(+n: Nat, +qs: List<&2, Am.Q>, +yes: Bool, r: Am.QF, +x: Nat, sp: {pw.qf(r, qs, x) == pw.qc(qs, x) : Nat}) -> pw.goal(pw.after(Am.answer.with(n, qs, yes, r), x), n, qs, x):
  match r:
    case Am.QFound{q, rest}:
      match q:
        case Am.Q{+k, i, es, w}:
          pw.moved(k, rest, pw.ge(n, x), x, pw.qc(qs, x), sp)
    case Am.QNone{}:
      pw.le_refl(Nat.add(pw.qc(qs, x), pw.ge(n, x)))

def pw.cancel(+n: Nat, +qs: List<&2, Am.Q>, r: Am.QF, +x: Nat, sp: {pw.qf(r, qs, x) == pw.qc(qs, x) : Nat}) -> pw.goal(pw.after(Am.cancel.with(n, qs, r), x), n, qs, x):
  match r:
    case Am.QFound{q, rest}:
      match q:
        case Am.Q{+k, i, es, w}:
          match w:
            case Am.OnClients{}:
              pw.dropped(k, rest, pw.ge(n, x), x, pw.qc(qs, x), sp)
            case Am.OnParent{}:
              pw.dropped(k, rest, pw.ge(n, x), x, pw.qc(qs, x), sp)
    case Am.QNone{}:
      pw.le_refl(Nat.add(pw.qc(qs, x), pw.ge(n, x)))

def pw.back(+n: Nat, +qs: List<&2, Am.Q>, +f: Am.Fate, r: Am.QF, +x: Nat, sp: {pw.qf(r, qs, x) == pw.qc(qs, x) : Nat}) -> pw.goal(pw.after(Am.back.with(n, qs, f, r), x), n, qs, x):
  match r:
    case Am.QFound{q, rest}:
      match q:
        case Am.Q{+k, i, es, w}:
          match w:
            case Am.OnParent{}:
              pw.moved(k, rest, pw.ge(n, x), x, pw.qc(qs, x), sp)
            case Am.OnClients{}:
              pw.le_refl(Nat.add(pw.qc(qs, x), pw.ge(n, x)))
    case Am.QNone{}:
      pw.le_refl(Nat.add(pw.qc(qs, x), pw.ge(n, x)))

def pw.put(+n: Nat, r: List<&2, Am.Q> & List<&2, Am.Act>, +x: Nat, +c: Nat, e: {Nat.add(ApprovalsDesk.dw_count(ApprovalsDesk.dw_woke(pw.ra(r)), x), pw.qc(pw.rq(r), x)) == c : Nat}) -> {Nat.is_le(pw.after(Am.detach.put(n, r), x), Nat.add(c, pw.ge(n, x))) == True{} : Bool}:
  (rq, as) = r
  +w0 = ApprovalsDesk.dw_count(ApprovalsDesk.dw_woke(as), x)
  +q0 = pw.qc(rq, x)
  +g = pw.ge(n, x)
  pw.le_eq(Nat.add(w0, Nat.add(q0, g)), Nat.add(c, g), Equal.trans(Nat, Nat.add(w0, Nat.add(q0, g)), Nat.add(Nat.add(w0, q0), g), Nat.add(c, g), pw.assoc(w0, q0, g), Equal.cong(Nat, Nat, z => Nat.add(z, g), Nat.add(w0, q0), c, e)))

def pw.detach(+n: Nat, +qs: List<&2, Am.Q>, h: Am.Here, +p: Bool, +x: Nat) -> pw.goal(pw.after(Am.detach.with(n, qs, h, p), x), n, qs, x):
  match h:
    case Am.Clients{}:
      pw.le_refl(Nat.add(pw.qc(qs, x), pw.ge(n, x)))
    case Am.Nobody{}:
      pw.put(n, Am.reroute(qs, Am.Nobody{}, p), x, pw.qc(qs, x), pw.reroute(qs, Am.Nobody{}, p, x))
    case Am.GatewayOnly{}:
      pw.put(n, Am.reroute(qs, Am.GatewayOnly{}, p), x, pw.qc(qs, x), pw.reroute(qs, Am.GatewayOnly{}, p, x))

# one event wakes x at most as often as its potential falls
def pw.step(d: Am.D, e: Am.Ev, +x: Nat) -> {Nat.is_le(pw.after(Am.dstep(d, e), x), pw.pot(d, x)) == True{} : Bool}:
  match d:
    case Am.D{+n, +qs}:
      match e:
        case Am.EAsk{id, +es, +h, +p}:
          pw.ask(n, id, es, qs, Am.next(es, h, p), x)
        case Am.EAnswer{+id, yes}:
          pw.answer(n, qs, yes, Am.find(qs, id), x, pw.find(qs, id, x))
        case Am.EDetach{h, p}:
          pw.detach(n, qs, h, p, x)
        case Am.ECancel{+key}:
          pw.cancel(n, qs, Am.take(qs, key), x, pw.take(qs, key, x))
        case Am.EBack{+key, f}:
          pw.back(n, qs, f, Am.take(qs, key), x, pw.take(qs, key, x))

# the step, with the run's projections
def pw.step2(+d: Am.D, +e: Am.Ev, +x: Nat) -> {Nat.is_le(Nat.add(ApprovalsDesk.dw_count(ApprovalsDesk.dw_woke(ApprovalsDesk.ds_acts(Am.dstep(d, e))), x), pw.pot(ApprovalsDesk.ds_desk(Am.dstep(d, e)), x)), pw.pot(d, x)) == True{} : Bool}:
  %pw.proj(Am.dstep(d, e), x) : {Nat.is_le(_, pw.pot(d, x)) == True{} : Bool}
  pw.step(d, e, x)

# the wakes of x over a run are at most the first desk's potential
def pw.run(es: List<&2, Am.Ev>, +d: Am.D, +x: Nat) -> {Nat.is_le(ApprovalsDesk.dw_count(ApprovalsDesk.dw_run(es, d), x), pw.pot(d, x)) == True{} : Bool}:
  match es:
    case Nil{}:
      pw.le0(pw.pot(d, x))
    case +e <> +t:
      %pw.count_split(ApprovalsDesk.dw_woke(ApprovalsDesk.ds_acts(Am.dstep(d, e))), ApprovalsDesk.dw_run(t, ApprovalsDesk.ds_desk(Am.dstep(d, e))), x) : {Nat.is_le(_, pw.pot(d, x)) == True{} : Bool}
      pw.le_trans(Nat.add(ApprovalsDesk.dw_count(ApprovalsDesk.dw_woke(ApprovalsDesk.ds_acts(Am.dstep(d, e))), x), ApprovalsDesk.dw_count(ApprovalsDesk.dw_run(t, ApprovalsDesk.ds_desk(Am.dstep(d, e))), x)), Nat.add(ApprovalsDesk.dw_count(ApprovalsDesk.dw_woke(ApprovalsDesk.ds_acts(Am.dstep(d, e))), x), pw.pot(ApprovalsDesk.ds_desk(Am.dstep(d, e)), x)), pw.pot(d, x), pw.le_mono(ApprovalsDesk.dw_count(ApprovalsDesk.dw_woke(ApprovalsDesk.ds_acts(Am.dstep(d, e))), x), ApprovalsDesk.dw_count(ApprovalsDesk.dw_run(t, ApprovalsDesk.ds_desk(Am.dstep(d, e))), x), pw.pot(ApprovalsDesk.ds_desk(Am.dstep(d, e)), x), pw.run(t, ApprovalsDesk.ds_desk(Am.dstep(d, e)), x)), pw.step2(d, e, x))

def ApprovalsDesk.approvals_desk_wakes_once(es, k):
  pw.run(es, Am.D{0n, Nil{}}, k)
