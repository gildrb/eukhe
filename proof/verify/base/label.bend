# eukhe: lemmas the proofs of area verify share on the label and the exit
# code: a number equals itself; what a slot says of a state is the spec's;
# the model's folds (every check holds, some check is refuted) are the
# spec's counts; one unconfirmed or refuted check anywhere decides the
# fold; n confirmations hold and refute nothing; the label and the exit
# code by cases

import Base
import ../../../bend/verify.bend as V
import ../../../spec/verified/verify.bend as S
import ../../../laws/verify.bend as Verify

# Numbers
# -------

# a number equals itself
def vl.eq_refl(n: Nat) -> {True{} == Nat.is_eq(n, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      vl.eq_refl(p)

def vl.IfLT(c: Cmp, G: Type) -> Type:
  match c:
    case LT{}:
      G
    case EQ{}:
      Unit
    case GT{}:
      Unit

# a premise GT == LT proves anything
def vl.absurd_gt(-G: Type, e: {GT{} == LT{} : Cmp}) -> G:
  %e : vl.IfLT(_, G)
  Unit{}

# a number below another is below its successor
def vl.lt_succ(a: Nat, b: Nat, e: {Nat.cmp(a, b) == LT{} : Cmp}) -> {Nat.cmp(a, 1n+b) == LT{} : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      vl.absurd_gt({Nat.cmp(1n+p, 1n) == LT{} : Cmp}, e)
    case 1n+p 1n+q:
      vl.lt_succ(p, q, e)

# Booleans
# --------

def vl.and_false(a: Bool) -> {False{} == Bool.and(a, False{}) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def vl.or_true(a: Bool) -> {True{} == Bool.or(a, True{}) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# One slot
# --------

def vl.confirms.at(v: V.Verdict, b: Bool) -> {Bool.and(S.passes(v), b) == V.is_confirmed(V.seen.at(b, v)) : Bool}:
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

# a slot is a confirmation taken on the state now (the spec's S1) exactly
# when the model sees it confirmed on that state
def vl.confirms(now: Nat, s: V.Slot) -> {S.confirms(now, s) == V.is_confirmed(V.seen(now, s)) : Bool}:
  match s:
    case V.Open{}:
      {==}
    case V.Judged{v, at}:
      vl.confirms.at(v, Nat.is_eq(at, now))

def vl.refutes.at(v: V.Verdict, b: Bool) -> {Bool.and(S.fails(v), b) == V.is_refuted(V.seen.at(b, v)) : Bool}:
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

# a slot is a refutation taken on the state now (the spec's S1) exactly
# when the model sees it refuted on that state
def vl.refutes(now: Nat, s: V.Slot) -> {S.refutes(now, s) == V.is_refuted(V.seen(now, s)) : Bool}:
  match s:
    case V.Open{}:
      {==}
    case V.Judged{v, at}:
      vl.refutes.at(v, Nat.is_eq(at, now))

# a slot that is no confirmation taken on the state now is not seen
# confirmed on it
def vl.unconfirmed(now: Nat, s: V.Slot, un: {S.confirms(now, s) == False{} : Bool}) -> {False{} == V.is_confirmed(V.seen(now, s)) : Bool}:
  %vl.confirms(now, s) : {False{} == _ : Bool}
  %un : {_ == S.confirms(now, s) : Bool}
  {==}

# The folds are the counts
# ------------------------

def vl.below.step(b: Bool, c: Nat, l: Nat, ih: {Nat.cmp(c, 1n+l) == LT{} : Cmp}) -> {Nat.cmp(Nat.add(S.bit(b), c), 2n+l) == LT{} : Cmp}:
  match b:
    case True{}:
      ih
    case False{}:
      vl.lt_succ(c, 1n+l, ih)

# no more checks are confirmed than there are
def vl.below(+now: Nat, xs: List<&2, V.Slot>) -> {Nat.cmp(S.confirmed(now, xs), 1n+List.length(&2, V.Slot, xs)) == LT{} : Cmp}:
  match xs:
    case Nil{}:
      {==}
    case Con{s, +t}:
      vl.below.step(S.confirms(now, s), S.confirmed(now, t), List.length(&2, V.Slot, t), vl.below(now, t))

def vl.holds.step(b: Bool, -h: Bool, -c: Nat, -l: Nat, lt: {Nat.cmp(c, 1n+l) == LT{} : Cmp}, ih: {Nat.is_eq(c, l) == h : Bool}) -> {Nat.is_eq(Nat.add(S.bit(b), c), 1n+l) == Bool.and(b, h) : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Cmp, Nat.cmp(c, 1n+l), LT{}, lt) : {Cmp.is_eq(_) == False{} : Bool}
      {==}

# every check holds exactly when as many are confirmed as there are
def vl.holds(+now: Nat, xs: List<&2, V.Slot>) -> {Nat.is_eq(S.confirmed(now, xs), List.length(&2, V.Slot, xs)) == V.holds(now, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      %vl.confirms(now, s) : {Nat.is_eq(Nat.add(S.bit(S.confirms(now, s)), S.confirmed(now, t)), 1n+List.length(&2, V.Slot, t)) == Bool.and(_, V.holds(now, t)) : Bool}
      vl.holds.step(S.confirms(now, s), V.holds(now, t), S.confirmed(now, t), List.length(&2, V.Slot, t), vl.below(now, t), vl.holds(now, t))

def vl.refuted.step(b: Bool, -x: Bool, -n: Nat, ih: {Bool.not(Nat.is_eq(n, 0n)) == x : Bool}) -> {Bool.not(Nat.is_eq(Nat.add(S.bit(b), n), 0n)) == Bool.or(b, x) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# some check is refuted exactly when the count of the refuted is not 0
def vl.refuted(+now: Nat, xs: List<&2, V.Slot>) -> {Bool.not(Nat.is_eq(S.refuted(now, xs), 0n)) == V.refuted(now, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+s, t}:
      %vl.refutes(now, s) : {Bool.not(Nat.is_eq(Nat.add(S.bit(S.refutes(now, s)), S.refuted(now, t)), 0n)) == Bool.or(_, V.refuted(now, t)) : Bool}
      vl.refuted.step(S.refutes(now, s), V.refuted(now, t), S.refuted(now, t), vl.refuted(now, t))

# One check anywhere
# ------------------

# there is a check wherever one stands among others
def vl.some_around(pre: List<&2, V.Slot>, -s: V.Slot, -post: List<&2, V.Slot>) -> {True{} == V.some(Verify.sp_around(pre, s, post)) : Bool}:
  match pre:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

# one check that is no confirmation taken on the state now, anywhere,
# and not every check holds
def vl.holds_around(+now: Nat, pre: List<&2, V.Slot>, s: V.Slot, -post: List<&2, V.Slot>, un: {S.confirms(now, s) == False{} : Bool}) -> {False{} == V.holds(now, Verify.sp_around(pre, s, post)) : Bool}:
  match pre:
    case Nil{}:
      %vl.unconfirmed(now, s, un) : {False{} == Bool.and(_, V.holds(now, post)) : Bool}
      {==}
    case Con{h, t}:
      %vl.holds_around(now, t, s, post, un) : {False{} == Bool.and(V.is_confirmed(V.seen(now, h)), _) : Bool}
      vl.and_false(V.is_confirmed(V.seen(now, h)))

# one check refuted on the state now, anywhere, and some check is refuted
def vl.refuted_around(+now: Nat, pre: List<&2, V.Slot>, -post: List<&2, V.Slot>) -> {True{} == V.refuted(now, Verify.sp_around(pre, V.Judged{V.Refuted{}, now}, post)) : Bool}:
  match pre:
    case Nil{}:
      %vl.eq_refl(now) : {True{} == Bool.or(V.is_refuted(V.seen.at(_, V.Refuted{})), V.refuted(now, post)) : Bool}
      {==}
    case Con{h, t}:
      %vl.refuted_around(now, t, post) : {True{} == Bool.or(V.is_refuted(V.seen(now, h)), _) : Bool}
      vl.or_true(V.is_refuted(V.seen(now, h)))

# Confirmations only
# ------------------

# n confirmations taken on the state now all hold on it
def vl.pass_holds(+now: Nat, n: Nat) -> {True{} == V.holds(now, Verify.sp_all_pass(n, now)) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %vl.eq_refl(now) : {True{} == Bool.and(V.is_confirmed(V.seen.at(_, V.Confirmed{})), V.holds(now, Verify.sp_all_pass(p, now))) : Bool}
      vl.pass_holds(now, p)

# n confirmations taken on the state now refute nothing on it
def vl.pass_unrefuted(+now: Nat, n: Nat) -> {False{} == V.refuted(now, Verify.sp_all_pass(n, now)) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %vl.eq_refl(now) : {False{} == Bool.or(V.is_refuted(V.seen.at(_, V.Confirmed{})), V.refuted(now, Verify.sp_all_pass(p, now))) : Bool}
      vl.pass_unrefuted(now, p)

# The label and the exit code by cases
# ------------------------------------

def vl.label.ok(conf: Bool) -> {V.label.good(conf) == S.label.ok(conf) : V.Label}:
  match conf:
    case True{}:
      {==}
    case False{}:
      {==}

def vl.label.all(conf: Bool, b: Bool) -> {V.label.of(conf, False{}, b) == S.label.all(conf, b) : V.Label}:
  match b:
    case True{}:
      vl.label.ok(conf)
    case False{}:
      {==}

# the model's label of the folds is the spec's label of the counts
def vl.label.of(conf: Bool, r: Nat, xs: List<&2, V.Slot>, c: Nat) -> {V.label.of(conf, Bool.not(Nat.is_eq(r, 0n)), Bool.and(V.some(xs), Nat.is_eq(c, List.length(&2, V.Slot, xs)))) == S.label.of(conf, r, c, List.length(&2, V.Slot, xs)) : V.Label}:
  match r:
    case 0n:
      match xs:
        case Nil{}:
          {==}
        case Con{h, t}:
          vl.label.all(conf, Nat.is_eq(c, 1n+List.length(&2, V.Slot, t)))
    case 1n+p:
      {==}

# a label whose checks do not all hold is neither verified nor passed
def vl.unheld(conf: Bool, r: Bool) -> {Verify.sp_succeeds(V.label.of(conf, r, False{})) == False{} : Bool}:
  match r:
    case True{}:
      {==}
    case False{}:
      {==}

def vl.unfailed.ok(conf: Bool) -> {Verify.sp_is_failed(V.label.good(conf)) == False{} : Bool}:
  match conf:
    case True{}:
      {==}
    case False{}:
      {==}

# a label with no check refuted is not failed
def vl.unfailed(conf: Bool, g: Bool) -> {Verify.sp_is_failed(V.label.of(conf, False{}, g)) == False{} : Bool}:
  match g:
    case True{}:
      vl.unfailed.ok(conf)
    case False{}:
      {==}

# the label is passed exactly when programs run unconfined and it reports
# every check confirmed, verified exactly when they run confined and it
# does
def vl.qualifier(conf: Bool, b: Bool, g: Bool) -> {Verify.sp_is_passed(V.label.of(conf, b, g)) == Bool.and(Bool.not(conf), Verify.sp_succeeds(V.label.of(conf, b, g))) : Bool} & {Verify.sp_is_verified(V.label.of(conf, b, g)) == Bool.and(conf, Verify.sp_succeeds(V.label.of(conf, b, g))) : Bool}:
  match conf:
    case True{}:
      match b:
        case True{}:
          ({==}, {==})
        case False{}:
          match g:
            case True{}:
              ({==}, {==})
            case False{}:
              ({==}, {==})
    case False{}:
      match b:
        case True{}:
          ({==}, {==})
        case False{}:
          match g:
            case True{}:
              ({==}, {==})
            case False{}:
              ({==}, {==})

# a label of programs run unconfined is never verified
def vl.unconfined(b: Bool, g: Bool) -> {Verify.sp_is_verified(V.label.of(False{}, b, g)) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      match g:
        case True{}:
          {==}
        case False{}:
          {==}

# the model's exit code is the spec's
def vl.exit(ok: Bool, base: Nat) -> {V.exit.code(ok, base) == S.exit.of(ok, base) : Nat}:
  match ok:
    case True{}:
      {==}
    case False{}:
      match base:
        case 0n:
          {==}
        case 1n+p:
          match p:
            case 0n:
              {==}
            case 1n+q:
              {==}

# a run whose checks do not all hold exits nonzero
def vl.exit_nonzero(base: Nat) -> {Nat.is_eq(V.exit.code(False{}, base), 0n) == False{} : Bool}:
  match base:
    case 0n:
      {==}
    case 1n+p:
      {==}
