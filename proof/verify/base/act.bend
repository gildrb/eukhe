# eukhe: lemmas the proofs of area verify share on the acts and the
# verifier's step: a refuted premise proves anything; numbers (a number
# equals itself and is not below itself, adding 0 and a successor on the
# right); n open slots; put writes exactly one slot (va.set) or finds
# none; the first due check is the spec's lead (va.due_lead); a spec
# label that reports every check confirmed leaves no check due; the step
# by cases of what is due and of the label

import Base
import ../../../bend/verify.bend as V
import ../../../spec/verified/verify.bend as S
import ../../../laws/verify.bend as Verify

# Refuted premises
# ----------------

def va.IfF(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

def va.IfT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# a premise False == True proves anything
def va.absurd_ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : va.IfF(_, G)
  Unit{}

# a premise True == False proves anything
def va.absurd_tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : va.IfT(_, G)
  Unit{}

def va.IfLT(c: Cmp, G: Type) -> Type:
  match c:
    case LT{}:
      G
    case EQ{}:
      Unit
    case GT{}:
      Unit

# a premise EQ == LT proves anything
def va.absurd_el(-G: Type, e: {EQ{} == LT{} : Cmp}) -> G:
  %e : va.IfLT(_, G)
  Unit{}

# a premise GT == LT proves anything
def va.absurd_gl(-G: Type, e: {GT{} == LT{} : Cmp}) -> G:
  %e : va.IfLT(_, G)
  Unit{}

def va.IfNone(m: Maybe<&2, V.Slot>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

# a premise Some == None proves anything
def va.absurd_some(-x: V.Slot, -G: Type, e: {Some{x} == None{} : Maybe<&2, V.Slot>}) -> G:
  %e : va.IfNone(_, G)
  Unit{}

def va.IfVerified(l: V.Label, G: Type) -> Type:
  match l:
    case V.Verified{}:
      G
    case V.Failed{}:
      Unit
    case V.Unverified{}:
      Unit
    case V.Passed{}:
      Unit

def va.IfPassed(l: V.Label, G: Type) -> Type:
  match l:
    case V.Verified{}:
      Unit
    case V.Failed{}:
      Unit
    case V.Unverified{}:
      Unit
    case V.Passed{}:
      G

def va.IfEnd(x: V.Action, G: Type) -> Type:
  match x:
    case V.Rest{}:
      Unit
    case V.Run{i}:
      Unit
    case V.Return{}:
      Unit
    case V.End{l}:
      G

def va.IfEndVerified(x: V.Action, G: Type) -> Type:
  match x:
    case V.Rest{}:
      Unit
    case V.Run{i}:
      Unit
    case V.Return{}:
      Unit
    case V.End{l}:
      va.IfVerified(l, G)

def va.IfEndPassed(x: V.Action, G: Type) -> Type:
  match x:
    case V.Rest{}:
      Unit
    case V.Run{i}:
      Unit
    case V.Return{}:
      Unit
    case V.End{l}:
      va.IfPassed(l, G)

# a premise Rest == End{l} proves anything
def va.absurd_rest(-l: V.Label, -G: Type, e: {V.Rest{} == V.End{l} : V.Action}) -> G:
  %e : va.IfEnd(_, G)
  Unit{}

# a premise Run == End{l} proves anything
def va.absurd_run(-i: Nat, -l: V.Label, -G: Type, e: {V.Run{i} == V.End{l} : V.Action}) -> G:
  %e : va.IfEnd(_, G)
  Unit{}

# a premise Return == End{l} proves anything
def va.absurd_return(-l: V.Label, -G: Type, e: {V.Return{} == V.End{l} : V.Action}) -> G:
  %e : va.IfEnd(_, G)
  Unit{}

# an end verified that is an end with a label reporting every check
# confirmed: that label is verified
def va.end_v(l: V.Label, ok: {Verify.sp_succeeds(l) == True{} : Bool}, e: {V.End{V.Verified{}} == V.End{l} : V.Action}) -> {V.Verified{} == l : V.Label}:
  match l:
    case V.Verified{}:
      {==}
    case V.Failed{}:
      va.absurd_ft({V.Verified{} == V.Failed{} : V.Label}, ok)
    case V.Unverified{}:
      va.absurd_ft({V.Verified{} == V.Unverified{} : V.Label}, ok)
    case V.Passed{}:
      %e : va.IfEndPassed(_, {V.Verified{} == V.Passed{} : V.Label})
      Unit{}

# an end passed that is an end with a label reporting every check
# confirmed: that label is passed
def va.end_p(l: V.Label, ok: {Verify.sp_succeeds(l) == True{} : Bool}, e: {V.End{V.Passed{}} == V.End{l} : V.Action}) -> {V.Passed{} == l : V.Label}:
  match l:
    case V.Verified{}:
      %e : va.IfEndVerified(_, {V.Passed{} == V.Verified{} : V.Label})
      Unit{}
    case V.Failed{}:
      va.absurd_ft({V.Passed{} == V.Failed{} : V.Label}, ok)
    case V.Unverified{}:
      va.absurd_ft({V.Passed{} == V.Unverified{} : V.Label}, ok)
    case V.Passed{}:
      {==}

# a premise End{Failed} == End{l}, l reporting every check confirmed,
# proves anything
def va.end_f(l: V.Label, -G: Type, ok: {Verify.sp_succeeds(l) == True{} : Bool}, e: {V.End{V.Failed{}} == V.End{l} : V.Action}) -> G:
  match l:
    case V.Verified{}:
      %e : va.IfEndVerified(_, G)
      Unit{}
    case V.Failed{}:
      va.absurd_ft(G, ok)
    case V.Unverified{}:
      va.absurd_ft(G, ok)
    case V.Passed{}:
      %e : va.IfEndPassed(_, G)
      Unit{}

# a premise End{Unverified} == End{l}, l reporting every check confirmed,
# proves anything
def va.end_u(l: V.Label, -G: Type, ok: {Verify.sp_succeeds(l) == True{} : Bool}, e: {V.End{V.Unverified{}} == V.End{l} : V.Action}) -> G:
  match l:
    case V.Verified{}:
      %e : va.IfEndVerified(_, G)
      Unit{}
    case V.Failed{}:
      va.absurd_ft(G, ok)
    case V.Unverified{}:
      va.absurd_ft(G, ok)
    case V.Passed{}:
      %e : va.IfEndPassed(_, G)
      Unit{}

# Numbers
# -------

# a number equals itself
def va.eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      va.eq_refl(p)

# a number is not below itself
def va.lt_irrefl(n: Nat) -> {Nat.is_lt(n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      va.lt_irrefl(p)

def va.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %va.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def va.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %va.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

# a number below another is below its successor
def va.cmp_lt_succ(a: Nat, b: Nat, e: {Nat.cmp(a, b) == LT{} : Cmp}) -> {Nat.cmp(a, 1n+b) == LT{} : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      va.absurd_gl({Nat.cmp(1n+ap, 1n) == LT{} : Cmp}, e)
    case 1n+ap 1n+bp:
      va.cmp_lt_succ(ap, bp, e)

# a comparison that is LT is not EQ
def va.lt_not_eq(c: Cmp, -G: Type, lt: {c == LT{} : Cmp}, e: {Cmp.is_eq(c) == True{} : Bool}) -> G:
  match c:
    case LT{}:
      va.absurd_ft(G, e)
    case EQ{}:
      va.absurd_el(G, lt)
    case GT{}:
      va.absurd_gl(G, lt)

# Assign: n open slots
# --------------------

def va.opens_length(n: Nat) -> {List.length(&2, V.Slot, V.opens(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %va.opens_length(p) : {1n+List.length(&2, V.Slot, V.opens(p)) == 1n+_ : Nat}
      {==}

def va.opens_count(n: Nat) -> {S.opens(V.opens(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %va.opens_count(p) : {1n+S.opens(V.opens(p)) == 1n+_ : Nat}
      {==}

# the owner's Assign of at most max_checks checks, as a value
def va.assign_is(-n: Nat, -rev: Nat, -slots: List<&2, V.Slot>, -claimed: Bool, -tries: Nat, few: {Nat.is_le(n, V.max_checks()) == True{} : Bool}) -> {(True{}, V.Acc{1n+rev, V.opens(n), False{}, 0n}) == V.act(V.Owner{}, V.Assign{n}, V.Acc{rev, slots, claimed, tries}) : Bool & V.Acc}:
  %few : {V.act.assign.fits(_, n, V.Acc{rev, slots, claimed, tries}) == V.act(V.Owner{}, V.Assign{n}, V.Acc{rev, slots, claimed, tries}) : Bool & V.Acc}
  {==}

# Record: put writes one slot
# ---------------------------

# put finds no slot where nth finds none
def va.put_none(i: Nat, -s: V.Slot, slots: List<&2, V.Slot>, none: {S.nth(i, slots) == None{} : Maybe<&2, V.Slot>}) -> {V.put(i, s, slots) == None{} : Maybe<&2, List<&2, V.Slot>>}:
  match i:
    case 0n:
      match slots:
        case Nil{}:
          {==}
        case Con{h, t}:
          va.absurd_some(h, {V.put(0n, s, h <> t) == None{} : Maybe<&2, List<&2, V.Slot>>}, none)
    case 1n+p:
      match slots:
        case Nil{}:
          {==}
        case Con{h, t}:
          %va.put_none(p, s, t, none) : {V.put.cons(h, V.put(p, s, t)) == V.put.cons(h, _) : Maybe<&2, List<&2, V.Slot>>}
          {==}

# `slots` with the slot at index i replaced by s (`slots` when there is
# none)
def va.set(i: Nat, s: V.Slot, slots: List<&2, V.Slot>) -> List<&2, V.Slot>:
  match i:
    case 0n:
      match slots:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          s <> t
    case 1n+p:
      match slots:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          h <> va.set(p, s, t)

# put at an index below the length is va.set
def va.put_some(i: Nat, -s: V.Slot, slots: List<&2, V.Slot>, has: {Nat.is_lt(i, List.length(&2, V.Slot, slots)) == True{} : Bool}) -> {V.put(i, s, slots) == Some{va.set(i, s, slots)} : Maybe<&2, List<&2, V.Slot>>}:
  match i:
    case 0n:
      match slots:
        case Nil{}:
          va.absurd_ft({V.put(0n, s, Nil{}) == Some{va.set(0n, s, Nil{})} : Maybe<&2, List<&2, V.Slot>>}, has)
        case Con{h, t}:
          {==}
    case 1n+p:
      match slots:
        case Nil{}:
          va.absurd_ft({V.put(1n+p, s, Nil{}) == Some{va.set(1n+p, s, Nil{})} : Maybe<&2, List<&2, V.Slot>>}, has)
        case Con{h, t}:
          %va.put_some(p, s, t, has) : {V.put.cons(h, V.put(p, s, t)) == V.put.cons(h, _) : Maybe<&2, List<&2, V.Slot>>}
          {==}

# the slot at every index j of va.set at an index below the length: s at
# that index, the slot that was there otherwise
def va.set_nth(i: Nat, -s: V.Slot, slots: List<&2, V.Slot>, j: Nat, has: {Nat.is_lt(i, List.length(&2, V.Slot, slots)) == True{} : Bool}) -> {S.nth(j, va.set(i, s, slots)) == S.pick(Nat.is_eq(j, i), s, S.nth(j, slots)) : Maybe<&2, V.Slot>}:
  match i:
    case 0n:
      match slots:
        case Nil{}:
          va.absurd_ft({S.nth(j, va.set(0n, s, Nil{})) == S.pick(Nat.is_eq(j, 0n), s, S.nth(j, Nil{})) : Maybe<&2, V.Slot>}, has)
        case Con{h, t}:
          match j:
            case 0n:
              {==}
            case 1n+q:
              {==}
    case 1n+p:
      match slots:
        case Nil{}:
          va.absurd_ft({S.nth(j, va.set(1n+p, s, Nil{})) == S.pick(Nat.is_eq(j, 1n+p), s, S.nth(j, Nil{})) : Maybe<&2, V.Slot>}, has)
        case Con{h, t}:
          match j:
            case 0n:
              {==}
            case 1n+q:
              va.set_nth(p, s, t, q, has)

# the verifier's Record for a check of the current revision that exists,
# as a value
def va.record_is(i: Nat, -v: V.Verdict, -at: Nat, rev: Nat, slots: List<&2, V.Slot>, -claimed: Bool, -tries: Nat, has: {Nat.is_lt(i, List.length(&2, V.Slot, slots)) == True{} : Bool}) -> {(True{}, V.Acc{rev, va.set(i, V.Judged{v, at}, slots), claimed, tries}) == V.act(V.Verifier{}, V.Record{rev, i, v, at}, V.Acc{rev, slots, claimed, tries}) : Bool & V.Acc}:
  %va.put_some(i, V.Judged{v, at}, slots, has) : {V.act.put(_, rev, slots, claimed, tries) == V.act(V.Verifier{}, V.Record{rev, i, v, at}, V.Acc{rev, slots, claimed, tries}) : Bool & V.Acc}
  %va.eq_refl(rev) : {V.act.stamp(_, i, V.Judged{v, at}, rev, slots, claimed, tries) == V.act(V.Verifier{}, V.Record{rev, i, v, at}, V.Acc{rev, slots, claimed, tries}) : Bool & V.Acc}
  {==}

# what the laws read of that Record: admitted, the slot at every index,
# the revision, the claim and the tries
def va.record_all(+i: Nat, -v: V.Verdict, -at: Nat, rev: Nat, +slots: List<&2, V.Slot>, -claimed: Bool, -tries: Nat, j: Nat, +has: {Nat.is_lt(i, List.length(&2, V.Slot, slots)) == True{} : Bool}) -> {S.admitted(V.act(V.Verifier{}, V.Record{rev, i, v, at}, V.Acc{rev, slots, claimed, tries})) == True{} : Bool} & {S.nth(j, S.slots(S.after(V.act(V.Verifier{}, V.Record{rev, i, v, at}, V.Acc{rev, slots, claimed, tries})))) == S.pick(Nat.is_eq(j, i), V.Judged{v, at}, S.nth(j, slots)) : Maybe<&2, V.Slot>} & {S.rev(S.after(V.act(V.Verifier{}, V.Record{rev, i, v, at}, V.Acc{rev, slots, claimed, tries}))) == rev : Nat} & {S.claimed(S.after(V.act(V.Verifier{}, V.Record{rev, i, v, at}, V.Acc{rev, slots, claimed, tries}))) == claimed : Bool} & {S.tries(S.after(V.act(V.Verifier{}, V.Record{rev, i, v, at}, V.Acc{rev, slots, claimed, tries}))) == tries : Nat}:
  %va.record_is(i, v, at, rev, slots, claimed, tries, has) : ({S.admitted(_) == True{} : Bool} & {S.nth(j, S.slots(S.after(_))) == S.pick(Nat.is_eq(j, i), V.Judged{v, at}, S.nth(j, slots)) : Maybe<&2, V.Slot>} & {S.rev(S.after(_)) == rev : Nat} & {S.claimed(S.after(_)) == claimed : Bool} & {S.tries(S.after(_)) == tries : Nat})
  ({==}, (va.set_nth(i, V.Judged{v, at}, slots, j, has), ({==}, ({==}, {==}))))

# The first due check is the spec's lead
# --------------------------------------

# x when lt, else nothing
def va.sel(lt: Bool, x: Nat) -> Maybe<&2, Nat>:
  match lt:
    case True{}:
      Some{x}
    case False{}:
      None{}

def va.due_step(b: Bool, -i: Nat, l: Nat, -n: Nat) -> {V.due.pick(b, i, va.sel(Nat.is_lt(l, n), Nat.add(l, 1n+i))) == va.sel(Nat.is_lt(S.lead.step(b, l), 1n+n), Nat.add(S.lead.step(b, l), i)) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      %va.add_succ(l, i) : {va.sel(Nat.is_lt(l, n), Nat.add(l, 1n+i)) == va.sel(Nat.is_lt(l, n), _) : Maybe<&2, Nat>}
      {==}
    case False{}:
      {==}

# the first due check, counted from i: the spec's lead (plus i) when the
# lead is below the number of checks, else none
def va.due_lead(+now: Nat, +slots: List<&2, V.Slot>, +i: Nat) -> {V.due(now, slots, i) == va.sel(Nat.is_lt(S.lead(now, slots), List.length(&2, V.Slot, slots)), Nat.add(S.lead(now, slots), i)) : Maybe<&2, Nat>}:
  match slots:
    case Nil{}:
      {==}
    case Con{s, t}:
      match s:
        case V.Open{}:
          {==}
        case V.Judged{v, at}:
          %va.due_step(Nat.is_eq(at, now), i, S.lead(now, t), List.length(&2, V.Slot, t)) : {V.due.pick(Nat.is_eq(at, now), i, V.due(now, t, 1n+i)) == _ : Maybe<&2, Nat>}
          %va.due_lead(now, t, 1n+i) : {V.due.pick(Nat.is_eq(at, now), i, V.due(now, t, 1n+i)) == V.due.pick(Nat.is_eq(at, now), i, _) : Maybe<&2, Nat>}
          {==}

# while the lead is below the number of checks, the check at the lead is
# due
def va.due_some(+now: Nat, +slots: List<&2, V.Slot>, left: {Nat.is_lt(S.lead(now, slots), List.length(&2, V.Slot, slots)) == True{} : Bool}) -> {V.due(now, slots, 0n) == Some{S.lead(now, slots)} : Maybe<&2, Nat>}:
  %va.add_zero(S.lead(now, slots)) : {V.due(now, slots, 0n) == Some{_} : Maybe<&2, Nat>}
  %left : {V.due(now, slots, 0n) == va.sel(_, Nat.add(S.lead(now, slots), 0n)) : Maybe<&2, Nat>}
  va.due_lead(now, slots, 0n)

# once the lead is the number of checks, none is due
def va.due_none(+now: Nat, +slots: List<&2, V.Slot>, done: {S.lead(now, slots) == List.length(&2, V.Slot, slots) : Nat}) -> {V.due(now, slots, 0n) == None{} : Maybe<&2, Nat>}:
  %va.lt_irrefl(List.length(&2, V.Slot, slots)) : {V.due(now, slots, 0n) == va.sel(_, Nat.add(S.lead(now, slots), 0n)) : Maybe<&2, Nat>}
  %done : {V.due(now, slots, 0n) == va.sel(Nat.is_lt(_, List.length(&2, V.Slot, slots)), Nat.add(S.lead(now, slots), 0n)) : Maybe<&2, Nat>}
  va.due_lead(now, slots, 0n)

# A verified spec label leaves no check due
# -----------------------------------------

def va.bound_step(b: Bool, c: Nat, n: Nat, ih: {Nat.cmp(c, 1n+n) == LT{} : Cmp}) -> {Nat.cmp(Nat.add(S.bit(b), c), 2n+n) == LT{} : Cmp}:
  match b:
    case True{}:
      ih
    case False{}:
      va.cmp_lt_succ(c, 1n+n, ih)

# the confirmed checks are at most the checks
def va.bound(+now: Nat, +slots: List<&2, V.Slot>) -> {Nat.cmp(S.confirmed(now, slots), 1n+List.length(&2, V.Slot, slots)) == LT{} : Cmp}:
  match slots:
    case Nil{}:
      {==}
    case Con{s, t}:
      va.bound_step(S.confirms(now, s), S.confirmed(now, t), List.length(&2, V.Slot, t), va.bound(now, t))

# every check confirmed: the first one is
def va.head_true(b: Bool, c: Nat, n: Nat, lt: {Nat.cmp(c, 1n+n) == LT{} : Cmp}, e: {Nat.is_eq(Nat.add(S.bit(b), c), 1n+n) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      va.lt_not_eq(Nat.cmp(c, 1n+n), {False{} == True{} : Bool}, lt, e)

# every check confirmed: every later one is
def va.tail_true(b: Bool, c: Nat, n: Nat, lt: {Nat.cmp(c, 1n+n) == LT{} : Cmp}, e: {Nat.is_eq(Nat.add(S.bit(b), c), 1n+n) == True{} : Bool}) -> {Nat.is_eq(c, n) == True{} : Bool}:
  match b:
    case True{}:
      e
    case False{}:
      va.lt_not_eq(Nat.cmp(c, 1n+n), {Nat.is_eq(c, n) == True{} : Bool}, lt, e)

# a confirmation taken on the state now judged it
def va.confirms_judged(-now: Nat, s: V.Slot, e: {S.confirms(now, s) == True{} : Bool}) -> {V.judged(now, s) == True{} : Bool}:
  match s:
    case V.Open{}:
      e
    case V.Judged{v, at}:
      match v:
        case V.Confirmed{}:
          e
        case V.Refuted{}:
          va.absurd_ft({Nat.is_eq(at, now) == True{} : Bool}, e)
        case V.Broken{}:
          va.absurd_ft({Nat.is_eq(at, now) == True{} : Bool}, e)
        case V.Unjudged{}:
          va.absurd_ft({Nat.is_eq(at, now) == True{} : Bool}, e)

# with every check confirmed on the state now, none is due
def va.conf_due(+now: Nat, +slots: List<&2, V.Slot>, +i: Nat, +e: {Nat.is_eq(S.confirmed(now, slots), List.length(&2, V.Slot, slots)) == True{} : Bool}) -> {V.due(now, slots, i) == None{} : Maybe<&2, Nat>}:
  match slots:
    case Nil{}:
      {==}
    case Con{s, t}:
      %va.conf_due(now, t, 1n+i, va.tail_true(S.confirms(now, s), S.confirmed(now, t), List.length(&2, V.Slot, t), va.bound(now, t), e)) : {V.due.pick(V.judged(now, s), i, V.due(now, t, 1n+i)) == V.due.pick(True{}, i, _) : Maybe<&2, Nat>}
      %va.confirms_judged(now, s, va.head_true(S.confirms(now, s), S.confirmed(now, t), List.length(&2, V.Slot, t), va.bound(now, t), e)) : {V.due.pick(V.judged(now, s), i, V.due(now, t, 1n+i)) == V.due.pick(_, i, V.due(now, t, 1n+i)) : Maybe<&2, Nat>}
      {==}

def va.all_ok(conf: Bool, b: Bool, ok: {Verify.sp_succeeds(S.label.all(conf, b)) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      va.absurd_ft({False{} == True{} : Bool}, ok)

# a spec label that reports every check confirmed: every check is
# confirmed
def va.ok_all(conf: Bool, bad: Nat, good: Nat, n: Nat, ok: {Verify.sp_succeeds(S.label.of(conf, bad, good, n)) == True{} : Bool}) -> {Nat.is_eq(good, n) == True{} : Bool}:
  match bad:
    case 0n:
      match n:
        case 0n:
          va.absurd_ft({Nat.is_eq(good, 0n) == True{} : Bool}, ok)
        case 1n+m:
          va.all_ok(conf, Nat.is_eq(good, 1n+m), ok)
    case 1n+p:
      va.absurd_ft({Nat.is_eq(good, n) == True{} : Bool}, ok)

# a spec label on the state now that reports every check confirmed: no
# check is due
def va.ok_none(conf: Bool, +now: Nat, +slots: List<&2, V.Slot>, ok: {Verify.sp_succeeds(S.label(conf, now, slots)) == True{} : Bool}) -> {V.due(now, slots, 0n) == None{} : Maybe<&2, Nat>}:
  va.conf_due(now, slots, 0n, va.ok_all(conf, S.refuted(now, slots), S.confirmed(now, slots), List.length(&2, V.Slot, slots), ok))

# a label equal to one that reports every check confirmed reports it too
def va.ok_of(m: V.Label, l: V.Label, e: {m == l : V.Label}, ok: {Verify.sp_succeeds(l) == True{} : Bool}) -> {Verify.sp_succeeds(m) == True{} : Bool}:
  %Equal.sym(V.Label, m, l, e) : {Verify.sp_succeeds(_) == True{} : Bool}
  ok

# a label that reports every check confirmed settles the claim with it
def va.settle_ok(l: V.Label, -now: Nat, -cap: Nat, -rev: Nat, -slots: List<&2, V.Slot>, -tries: Nat, ok: {Verify.sp_succeeds(l) == True{} : Bool}) -> {V.settle(l, now, cap, rev, slots, tries) == (V.End{l}, V.Acc{rev, slots, False{}, 0n}) : V.Action & V.Acc}:
  match l:
    case V.Verified{}:
      {==}
    case V.Failed{}:
      va.absurd_ft({V.settle(V.Failed{}, now, cap, rev, slots, tries) == (V.End{V.Failed{}}, V.Acc{rev, slots, False{}, 0n}) : V.Action & V.Acc}, ok)
    case V.Unverified{}:
      va.absurd_ft({V.settle(V.Unverified{}, now, cap, rev, slots, tries) == (V.End{V.Unverified{}}, V.Acc{rev, slots, False{}, 0n}) : V.Action & V.Acc}, ok)
    case V.Passed{}:
      {==}

# a claim whose spec label l reports every check confirmed ends with l
# (lab: the label is the spec's)
def va.advance_ok(+conf: Bool, +now: Nat, -cap: Nat, -rev: Nat, +slots: List<&2, V.Slot>, -tries: Nat, +l: V.Label, +ok: {Verify.sp_succeeds(l) == True{} : Bool}, +all: {S.label(conf, now, slots) == l : V.Label}, lab: {V.label(conf, now, slots) == S.label(conf, now, slots) : V.Label}) -> {V.advance(conf, now, cap, V.Acc{rev, slots, True{}, tries}) == (V.End{l}, V.Acc{rev, slots, False{}, 0n}) : V.Action & V.Acc}:
  %va.settle_ok(l, now, cap, rev, slots, tries, ok) : {V.advance(conf, now, cap, V.Acc{rev, slots, True{}, tries}) == _ : V.Action & V.Acc}
  %all : {V.advance(conf, now, cap, V.Acc{rev, slots, True{}, tries}) == V.settle(_, now, cap, rev, slots, tries) : V.Action & V.Acc}
  %lab : {V.advance(conf, now, cap, V.Acc{rev, slots, True{}, tries}) == V.settle(_, now, cap, rev, slots, tries) : V.Action & V.Acc}
  %va.ok_none(conf, now, slots, va.ok_of(S.label(conf, now, slots), l, all, ok)) : {V.advance(conf, now, cap, V.Acc{rev, slots, True{}, tries}) == V.advance.go(conf, _, now, cap, rev, slots, tries) : V.Action & V.Acc}
  {==}

# A step that ends a claim with a label
# -------------------------------------

def va.failed_said(room: Bool, -rev: Nat, -slots: List<&2, V.Slot>, -tries: Nat, l: V.Label, -G: Type, ok: {Verify.sp_succeeds(l) == True{} : Bool}, said: {S.action(V.settle.failed(room, rev, slots, tries)) == V.End{l} : V.Action}) -> G:
  match room:
    case True{}:
      va.absurd_return(l, G, said)
    case False{}:
      va.end_f(l, G, ok, said)

def va.broken_said(room: Bool, -now: Nat, -rev: Nat, -slots: List<&2, V.Slot>, -tries: Nat, l: V.Label, -G: Type, ok: {Verify.sp_succeeds(l) == True{} : Bool}, said: {S.action(V.settle.broken(room, now, rev, slots, tries)) == V.End{l} : V.Action}) -> G:
  match room:
    case True{}:
      va.absurd_return(l, G, said)
    case False{}:
      va.end_u(l, G, ok, said)

def va.open_said(any: Bool, room: Bool, -now: Nat, -rev: Nat, -slots: List<&2, V.Slot>, -tries: Nat, l: V.Label, -G: Type, ok: {Verify.sp_succeeds(l) == True{} : Bool}, said: {S.action(V.settle.open(any, room, now, rev, slots, tries)) == V.End{l} : V.Action}) -> G:
  match any:
    case True{}:
      va.broken_said(room, now, rev, slots, tries, l, G, ok, said)
    case False{}:
      va.end_u(l, G, ok, said)

# a settled claim that ends with a label l reporting every check
# confirmed was settled on l
def va.settle_said(k: V.Label, -now: Nat, cap: Nat, -rev: Nat, +slots: List<&2, V.Slot>, tries: Nat, l: V.Label, ok: {Verify.sp_succeeds(l) == True{} : Bool}, said: {S.action(V.settle(k, now, cap, rev, slots, tries)) == V.End{l} : V.Action}) -> {k == l : V.Label}:
  match k:
    case V.Verified{}:
      va.end_v(l, ok, said)
    case V.Failed{}:
      va.failed_said(Nat.is_lt(tries, cap), rev, slots, tries, l, {V.Failed{} == l : V.Label}, ok, said)
    case V.Unverified{}:
      va.open_said(V.some(slots), Nat.is_lt(tries, cap), now, rev, slots, tries, l, {V.Unverified{} == l : V.Label}, ok, said)
    case V.Passed{}:
      va.end_p(l, ok, said)

# a step of a waiting claim that ends with a label l reporting every check
# confirmed, by what is due d: the spec's label is l (lab: the label is
# the spec's)
def va.go_said(conf: Bool, d: Maybe<&2, Nat>, now: Nat, cap: Nat, -rev: Nat, +slots: List<&2, V.Slot>, tries: Nat, l: V.Label, ok: {Verify.sp_succeeds(l) == True{} : Bool}, said: {S.action(V.advance.go(conf, d, now, cap, rev, slots, tries)) == V.End{l} : V.Action}, lab: {V.label(conf, now, slots) == S.label(conf, now, slots) : V.Label}) -> {S.label(conf, now, slots) == l : V.Label}:
  match d:
    case None{}:
      %lab : {_ == l : V.Label}
      va.settle_said(V.label(conf, now, slots), now, cap, rev, slots, tries, l, ok, said)
    case Some{i}:
      va.absurd_run(i, l, {S.label(conf, now, slots) == l : V.Label}, said)

# A step of programs run unconfined never ends verified
# ----------------------------------------------------

def va.failed_unconf(room: Bool, -rev: Nat, -slots: List<&2, V.Slot>, -tries: Nat) -> {Verify.sp_ends_verified(S.action(V.settle.failed(room, rev, slots, tries))) == False{} : Bool}:
  match room:
    case True{}:
      {==}
    case False{}:
      {==}

def va.broken_unconf(room: Bool, -now: Nat, -rev: Nat, -slots: List<&2, V.Slot>, -tries: Nat) -> {Verify.sp_ends_verified(S.action(V.settle.broken(room, now, rev, slots, tries))) == False{} : Bool}:
  match room:
    case True{}:
      {==}
    case False{}:
      {==}

def va.open_unconf(any: Bool, room: Bool, -now: Nat, -rev: Nat, -slots: List<&2, V.Slot>, -tries: Nat) -> {Verify.sp_ends_verified(S.action(V.settle.open(any, room, now, rev, slots, tries))) == False{} : Bool}:
  match any:
    case True{}:
      va.broken_unconf(room, now, rev, slots, tries)
    case False{}:
      {==}

# a claim settled on a label that is not verified does not end verified
def va.settle_unconf(l: V.Label, -now: Nat, cap: Nat, -rev: Nat, +slots: List<&2, V.Slot>, tries: Nat, ok: {Verify.sp_is_verified(l) == False{} : Bool}) -> {Verify.sp_ends_verified(S.action(V.settle(l, now, cap, rev, slots, tries))) == False{} : Bool}:
  match l:
    case V.Verified{}:
      va.absurd_tf({Verify.sp_ends_verified(S.action(V.settle(V.Verified{}, now, cap, rev, slots, tries))) == False{} : Bool}, ok)
    case V.Failed{}:
      va.failed_unconf(Nat.is_lt(tries, cap), rev, slots, tries)
    case V.Unverified{}:
      va.open_unconf(V.some(slots), Nat.is_lt(tries, cap), now, rev, slots, tries)
    case V.Passed{}:
      {==}

# a step of a waiting claim of programs run unconfined, by what is due d,
# whose label is not verified (ok), does not end verified
def va.go_unconf(d: Maybe<&2, Nat>, now: Nat, cap: Nat, -rev: Nat, +slots: List<&2, V.Slot>, tries: Nat, ok: {Verify.sp_is_verified(V.label(False{}, now, slots)) == False{} : Bool}) -> {Verify.sp_ends_verified(S.action(V.advance.go(False{}, d, now, cap, rev, slots, tries))) == False{} : Bool}:
  match d:
    case None{}:
      va.settle_unconf(V.label(False{}, now, slots), now, cap, rev, slots, tries, ok)
    case Some{i}:
      {==}

# A return for a broken check opens it again
# ------------------------------------------

# one slot, by whether it is on the state now (b): the spec's rerun is the
# code's reopen
def va.rerun_at(v: V.Verdict, b: Bool, -at: Nat) -> {Some{V.reopen.pick(Bool.and(V.retry(v), b), V.Judged{v, at})} == Some{S.rerun.pick(Bool.and(b, Bool.not(Bool.or(Bool.and(S.passes(v), b), Bool.and(S.fails(v), b)))), V.Judged{v, at})} : Maybe<&2, V.Slot>}:
  match v:
    case V.Confirmed{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case V.Refuted{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case V.Broken{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case V.Unjudged{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}

# one slot: the spec's rerun is the code's reopen
def va.rerun_one(now: Nat, s: V.Slot) -> {Some{V.reopen.pick(V.again(now, s), s)} == S.rerun(now, Some{s}) : Maybe<&2, V.Slot>}:
  match s:
    case V.Open{}:
      {==}
    case V.Judged{v, at}:
      va.rerun_at(v, Nat.is_eq(at, now), at)

# the slot at every index j of the reopened slots is the spec's rerun of
# the slot there before
def va.reopen_nth(+now: Nat, slots: List<&2, V.Slot>, j: Nat) -> {S.nth(j, V.reopen(now, slots)) == S.rerun(now, S.nth(j, slots)) : Maybe<&2, V.Slot>}:
  match slots:
    case Nil{}:
      match j:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case Con{s, t}:
      match j:
        case 0n:
          va.rerun_one(now, s)
        case 1n+p:
          va.reopen_nth(now, t, p)

# a claim with a check, every check judged on the state now and an
# unverified spec label, with room, returns with the broken checks opened
# (lab: the label is the spec's)
def va.broken_is(conf: Bool, +now: Nat, cap: Nat, -rev: Nat, +s: V.Slot, +t: List<&2, V.Slot>, +tries: Nat, done: {S.lead(now, s <> t) == List.length(&2, V.Slot, s <> t) : Nat}, un: {S.label(conf, now, s <> t) == V.Unverified{} : V.Label}, room: {Nat.is_lt(tries, cap) == True{} : Bool}, lab: {V.label(conf, now, s <> t) == S.label(conf, now, s <> t) : V.Label}) -> {(V.Return{}, V.Acc{rev, V.reopen(now, s <> t), False{}, 1n+tries}) == V.advance(conf, now, cap, V.Acc{rev, s <> t, True{}, tries}) : V.Action & V.Acc}:
  %room : {V.settle.broken(_, now, rev, s <> t, tries) == V.advance(conf, now, cap, V.Acc{rev, s <> t, True{}, tries}) : V.Action & V.Acc}
  %un : {V.settle(_, now, cap, rev, s <> t, tries) == V.advance(conf, now, cap, V.Acc{rev, s <> t, True{}, tries}) : V.Action & V.Acc}
  %lab : {V.settle(_, now, cap, rev, s <> t, tries) == V.advance(conf, now, cap, V.Acc{rev, s <> t, True{}, tries}) : V.Action & V.Acc}
  %va.due_none(now, s <> t, done) : {V.advance.go(conf, _, now, cap, rev, s <> t, tries) == V.advance(conf, now, cap, V.Acc{rev, s <> t, True{}, tries}) : V.Action & V.Acc}
  {==}

# what verify_advance_broken_returns reads of a step r
def va.Returned(j: Nat, now: Nat, rev: Nat, slots: List<&2, V.Slot>, tries: Nat, r: V.Action & V.Acc) -> Type:
  {S.action(r) == V.Return{} : V.Action} & {S.rev(S.stepped(r)) == rev : Nat} & {S.nth(j, S.slots(S.stepped(r))) == S.rerun(now, S.nth(j, slots)) : Maybe<&2, V.Slot>} & {S.claimed(S.stepped(r)) == False{} : Bool} & {S.tries(S.stepped(r)) == 1n+tries : Nat}

# A step writes no verdict
# ------------------------

# what verify_advance_keeps_verdicts reads of a step r
def va.Keeps(j: Nat, rev: Nat, slots: List<&2, V.Slot>, r: V.Action & V.Acc) -> Type:
  {S.undo_open(S.nth(j, S.slots(S.stepped(r))), S.nth(j, slots)) == S.nth(j, slots) : Maybe<&2, V.Slot>} & {S.rev(S.stepped(r)) == rev : Nat}

# a kept slot put back is itself
def va.undo_refl(m: Maybe<&2, V.Slot>) -> {S.undo_open(m, m) == m : Maybe<&2, V.Slot>}:
  match m:
    case None{}:
      {==}
    case Some{s}:
      match s:
        case V.Open{}:
          {==}
        case V.Judged{v, at}:
          {==}

def va.undo_pick(b: Bool, s: V.Slot) -> {S.undo_open(Some{V.reopen.pick(b, s)}, Some{s}) == Some{s} : Maybe<&2, V.Slot>}:
  match b:
    case True{}:
      {==}
    case False{}:
      va.undo_refl(Some{s})

# the reopened slots, put back, are the slots before
def va.reopen_keeps(+now: Nat, slots: List<&2, V.Slot>, j: Nat) -> {S.undo_open(S.nth(j, V.reopen(now, slots)), S.nth(j, slots)) == S.nth(j, slots) : Maybe<&2, V.Slot>}:
  match slots:
    case Nil{}:
      match j:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case Con{+s, t}:
      match j:
        case 0n:
          va.undo_pick(V.again(now, s), s)
        case 1n+p:
          va.reopen_keeps(now, t, p)

def va.failed_keeps(room: Bool, -rev: Nat, slots: List<&2, V.Slot>, -tries: Nat, j: Nat) -> va.Keeps(j, rev, slots, V.settle.failed(room, rev, slots, tries)):
  match room:
    case True{}:
      (va.undo_refl(S.nth(j, slots)), {==})
    case False{}:
      (va.undo_refl(S.nth(j, slots)), {==})

def va.broken_keeps(room: Bool, now: Nat, -rev: Nat, slots: List<&2, V.Slot>, -tries: Nat, j: Nat) -> va.Keeps(j, rev, slots, V.settle.broken(room, now, rev, slots, tries)):
  match room:
    case True{}:
      (va.reopen_keeps(now, slots, j), {==})
    case False{}:
      (va.undo_refl(S.nth(j, slots)), {==})

def va.open_keeps(any: Bool, room: Bool, now: Nat, -rev: Nat, slots: List<&2, V.Slot>, -tries: Nat, j: Nat) -> va.Keeps(j, rev, slots, V.settle.open(any, room, now, rev, slots, tries)):
  match any:
    case True{}:
      va.broken_keeps(room, now, rev, slots, tries, j)
    case False{}:
      (va.undo_refl(S.nth(j, slots)), {==})

def va.settle_keeps(l: V.Label, now: Nat, cap: Nat, -rev: Nat, +slots: List<&2, V.Slot>, tries: Nat, j: Nat) -> va.Keeps(j, rev, slots, V.settle(l, now, cap, rev, slots, tries)):
  match l:
    case V.Verified{}:
      (va.undo_refl(S.nth(j, slots)), {==})
    case V.Failed{}:
      va.failed_keeps(Nat.is_lt(tries, cap), rev, slots, tries, j)
    case V.Unverified{}:
      va.open_keeps(V.some(slots), Nat.is_lt(tries, cap), now, rev, slots, tries, j)
    case V.Passed{}:
      (va.undo_refl(S.nth(j, slots)), {==})

# a step of a waiting claim, by what is due d
def va.go_keeps(conf: Bool, d: Maybe<&2, Nat>, +now: Nat, cap: Nat, -rev: Nat, +slots: List<&2, V.Slot>, tries: Nat, j: Nat) -> va.Keeps(j, rev, slots, V.advance.go(conf, d, now, cap, rev, slots, tries)):
  match d:
    case None{}:
      va.settle_keeps(V.label(conf, now, slots), now, cap, rev, slots, tries, j)
    case Some{i}:
      (va.undo_refl(S.nth(j, slots)), {==})
