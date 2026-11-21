# eukhe: lemmas of the proofs of area strength on the model
# (bend/strength.bend): the strength of a check is the spec's grade
# (sg.strength), the folds of certified are the spec's counts (sg.shown,
# sg.clear, sg.certified), the label, the first due check (sg.due), the
# step, the record (sg.put_none, sg.put_some, sg.nth_set) and the exit
# code by cases

import Base
import ../../../bend/verify.bend as V
import ../../../bend/strength.bend as St
import ../../../bend/headless_task.bend as Ht
import ../../../spec/verified/verify.bend as SV
import ../../../spec/verified/strength.bend as S
import ../../../laws/strength.bend as Strength

# Verify's folds and exit code (as proof/verify/base/label.bend proves
# them; restated here so this area's check needs no verify proof)
# -----------------------------------------------------------------

def sv.eq_refl(n: Nat) -> {True{} == Nat.is_eq(n, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      sv.eq_refl(p)

def sv.IfLT(c: Cmp, G: Type) -> Type:
  match c:
    case LT{}:
      G
    case EQ{}:
      Unit
    case GT{}:
      Unit

def sv.absurd_gt(-G: Type, e: {GT{} == LT{} : Cmp}) -> G:
  %e : sv.IfLT(_, G)
  Unit{}

def sv.lt_succ(a: Nat, b: Nat, e: {Nat.cmp(a, b) == LT{} : Cmp}) -> {Nat.cmp(a, 1n+b) == LT{} : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      sv.absurd_gt({Nat.cmp(1n+p, 1n) == LT{} : Cmp}, e)
    case 1n+p 1n+q:
      sv.lt_succ(p, q, e)

def sv.and_false(a: Bool) -> {False{} == Bool.and(a, False{}) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def sv.confirms.at(v: V.Verdict, b: Bool) -> {Bool.and(SV.passes(v), b) == V.is_confirmed(V.seen.at(b, v)) : Bool}:
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

def sv.confirms(now: Nat, s: V.Slot) -> {SV.confirms(now, s) == V.is_confirmed(V.seen(now, s)) : Bool}:
  match s:
    case V.Open{}:
      {==}
    case V.Judged{v, at}:
      sv.confirms.at(v, Nat.is_eq(at, now))

def sv.below.step(b: Bool, c: Nat, l: Nat, ih: {Nat.cmp(c, 1n+l) == LT{} : Cmp}) -> {Nat.cmp(Nat.add(SV.bit(b), c), 2n+l) == LT{} : Cmp}:
  match b:
    case True{}:
      ih
    case False{}:
      sv.lt_succ(c, 1n+l, ih)

def sv.below(+now: Nat, xs: List<&2, V.Slot>) -> {Nat.cmp(SV.confirmed(now, xs), 1n+List.length(&2, V.Slot, xs)) == LT{} : Cmp}:
  match xs:
    case Nil{}:
      {==}
    case Con{s, +t}:
      sv.below.step(SV.confirms(now, s), SV.confirmed(now, t), List.length(&2, V.Slot, t), sv.below(now, t))

def sv.holds.step(b: Bool, -h: Bool, -c: Nat, -l: Nat, lt: {Nat.cmp(c, 1n+l) == LT{} : Cmp}, ih: {Nat.is_eq(c, l) == h : Bool}) -> {Nat.is_eq(Nat.add(SV.bit(b), c), 1n+l) == Bool.and(b, h) : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Cmp, Nat.cmp(c, 1n+l), LT{}, lt) : {Cmp.is_eq(_) == False{} : Bool}
      {==}

def sv.holds(+now: Nat, xs: List<&2, V.Slot>) -> {Nat.is_eq(SV.confirmed(now, xs), List.length(&2, V.Slot, xs)) == V.holds(now, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+s, +t}:
      %sv.confirms(now, s) : {Nat.is_eq(Nat.add(SV.bit(SV.confirms(now, s)), SV.confirmed(now, t)), 1n+List.length(&2, V.Slot, t)) == Bool.and(_, V.holds(now, t)) : Bool}
      sv.holds.step(SV.confirms(now, s), V.holds(now, t), SV.confirmed(now, t), List.length(&2, V.Slot, t), sv.below(now, t), sv.holds(now, t))

def sv.exit(ok: Bool, base: Nat) -> {V.exit.code(ok, base) == SV.exit.of(ok, base) : Nat}:
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

# Bool and Nat
# ------------

def sg.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

# a premise False == True proves anything
def sg.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : sg.BD(_, A, Unit)
  Unit{}

# a premise True == False proves anything
def sg.absurd_t(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : sg.BD(_, Unit, A)
  Unit{}

# a number below another is not at least it
def sg.lt_not_le(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {False{} == Nat.is_le(b, a) : Bool}:
  match a b:
    case 0n 0n:
      sg.absurd({False{} == Nat.is_le(0n, 0n) : Bool}, e)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      sg.absurd({False{} == Nat.is_le(0n, 1n+p) : Bool}, e)
    case 1n+p 1n+q:
      sg.lt_not_le(p, q, e)

def sg.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %sg.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def sg.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %sg.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

# The strength of one check (K1)
# ------------------------------

def sg.caught(e: Bool) -> {St.strength.caught(e) == S.grade(True{}, False{}, e) : St.Strength}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def sg.ran(z: Bool, +pct: Nat, +c: Nat, +r: Nat) -> {St.strength.ran(Bool.not(z), pct, c, r) == S.grade(True{}, z, Nat.is_le(Nat.mul(pct, r), Nat.mul(100n, c))) : St.Strength}:
  match z:
    case True{}:
      {==}
    case False{}:
      sg.caught(Nat.is_le(Nat.mul(pct, r), Nat.mul(100n, c)))

def sg.full(f: Bool, +pct: Nat, +c: Nat, +r: Nat) -> {St.strength.full(f, pct, c, r) == S.grade(f, Nat.is_eq(r, 0n), Nat.is_le(Nat.mul(pct, r), Nat.mul(100n, c))) : St.Strength}:
  match f:
    case True{}:
      sg.ran(Nat.is_eq(r, 0n), pct, c, r)
    case False{}:
      {==}

def sg.on(a: Bool, +pct: Nat, +c: Nat, +r: Nat, +p: Nat) -> {St.strength.on(a, pct, c, r, p) == S.grade(Bool.and(a, Nat.is_le(p, r)), Nat.is_eq(r, 0n), Nat.is_le(Nat.mul(pct, r), Nat.mul(100n, c))) : St.Strength}:
  match a:
    case True{}:
      sg.full(Nat.is_le(p, r), pct, c, r)
    case False{}:
      {==}

# the model's strength of a check is the spec's
def sg.strength(+now: Nat, g: St.Gauge) -> {St.strength(now, g) == S.strength(now, g) : St.Strength}:
  match g:
    case St.Gauge{b, m}:
      match b:
        case St.Exempt{}:
          {==}
        case St.Waived{}:
          {==}
        case St.Needs{pct}:
          match pct:
            case 0n:
              {==}
            case 1n+q:
              match m:
                case St.Unmeasured{}:
                  {==}
                case St.Measured{c, r, p, at}:
                  sg.on(Nat.is_eq(at, now), 1n+q, c, r, p)

# a whole measurement on the state now with breaks run whose catch is short
# of the share (1 percent or more) is weak
def sg.weak(-pct: Nat, -c: Nat, -n: Nat, -p: Nat, +now: Nat, whole: {Nat.is_le(p, n) == True{} : Bool}, ran: {Nat.is_eq(n, 0n) == False{} : Bool}, short: {Nat.is_le(Nat.mul(1n+pct, n), Nat.mul(100n, c)) == False{} : Bool}) -> {St.strength(now, St.Gauge{St.Needs{1n+pct}, St.Measured{c, n, p, now}}) == St.Weak{} : St.Strength}:
  %sv.eq_refl(now) : {St.strength.on(_, 1n+pct, c, n, p) == St.Weak{} : St.Strength}
  %Equal.sym(Bool, Nat.is_le(p, n), True{}, whole) : {St.strength.full(_, 1n+pct, c, n) == St.Weak{} : St.Strength}
  %Equal.sym(Bool, Nat.is_eq(n, 0n), False{}, ran) : {St.strength.ran(Bool.not(_), 1n+pct, c, n) == St.Weak{} : St.Strength}
  %Equal.sym(Bool, Nat.is_le(Nat.mul(1n+pct, n), Nat.mul(100n, c)), False{}, short) : {St.strength.caught(_) == St.Weak{} : St.Strength}
  {==}

# a whole measurement on the state now with breaks run whose catch meets the
# share (1 percent or more) is strong
def sg.strong(-pct: Nat, -c: Nat, -n: Nat, -p: Nat, +now: Nat, whole: {Nat.is_le(p, n) == True{} : Bool}, ran: {Nat.is_eq(n, 0n) == False{} : Bool}, met: {Nat.is_le(Nat.mul(1n+pct, n), Nat.mul(100n, c)) == True{} : Bool}) -> {St.strength(now, St.Gauge{St.Needs{1n+pct}, St.Measured{c, n, p, now}}) == St.Strong{} : St.Strength}:
  %sv.eq_refl(now) : {St.strength.on(_, 1n+pct, c, n, p) == St.Strong{} : St.Strength}
  %Equal.sym(Bool, Nat.is_le(p, n), True{}, whole) : {St.strength.full(_, 1n+pct, c, n) == St.Strong{} : St.Strength}
  %Equal.sym(Bool, Nat.is_eq(n, 0n), False{}, ran) : {St.strength.ran(Bool.not(_), 1n+pct, c, n) == St.Strong{} : St.Strength}
  %Equal.sym(Bool, Nat.is_le(Nat.mul(1n+pct, n), Nat.mul(100n, c)), True{}, met) : {St.strength.caught(_) == St.Strong{} : St.Strength}
  {==}

# Certified (K2)
# --------------

def sg.is_strong(x: St.Strength) -> {St.is_strong(x) == S.strong(x) : Bool}:
  match x:
    case St.Strong{}:
      {==}
    case St.Weak{}:
      {==}
    case St.Unshown{}:
      {==}
    case St.Free{}:
      {==}

def sg.blocks(x: St.Strength) -> {St.blocks(x) == S.blocking(x) : Bool}:
  match x:
    case St.Strong{}:
      {==}
    case St.Weak{}:
      {==}
    case St.Unshown{}:
      {==}
    case St.Free{}:
      {==}

def sg.or_step(b: Bool, -n: Nat) -> {Bool.or(b, Bool.not(Nat.is_eq(n, 0n))) == Bool.not(Nat.is_eq(Nat.add(S.bit(b), n), 0n)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sg.and_step(b: Bool, -n: Nat) -> {Bool.and(Bool.not(b), Nat.is_eq(n, 0n)) == Nat.is_eq(Nat.add(S.bit(b), n), 0n) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# some check is strong exactly when the spec counts one
def sg.shown(+now: Nat, gs: List<&2, St.Gauge>) -> {St.shown(now, gs) == Bool.not(Nat.is_eq(S.strongs(now, gs), 0n)) : Bool}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      %sg.or_step(S.strong(S.strength(now, g)), S.strongs(now, t)) : {St.shown(now, g <> t) == _ : Bool}
      %sg.shown(now, t) : {St.shown(now, g <> t) == Bool.or(S.strong(S.strength(now, g)), _) : Bool}
      %sg.strength(now, g) : {St.shown(now, g <> t) == Bool.or(S.strong(_), St.shown(now, t)) : Bool}
      %sg.is_strong(St.strength(now, g)) : {St.shown(now, g <> t) == Bool.or(_, St.shown(now, t)) : Bool}
      {==}

# no check blocks exactly when the spec counts none
def sg.clear(+now: Nat, gs: List<&2, St.Gauge>) -> {St.clear(now, gs) == Nat.is_eq(S.blockers(now, gs), 0n) : Bool}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      %sg.and_step(S.blocking(S.strength(now, g)), S.blockers(now, t)) : {St.clear(now, g <> t) == _ : Bool}
      %sg.clear(now, t) : {St.clear(now, g <> t) == Bool.and(Bool.not(S.blocking(S.strength(now, g))), _) : Bool}
      %sg.strength(now, g) : {St.clear(now, g <> t) == Bool.and(Bool.not(S.blocking(_)), St.clear(now, t)) : Bool}
      %sg.blocks(St.strength(now, g)) : {St.clear(now, g <> t) == Bool.and(Bool.not(_), St.clear(now, t)) : Bool}
      {==}

# the model's certified is the spec's
def sg.certified(+now: Nat, +gs: List<&2, St.Gauge>) -> {St.certified(now, gs) == S.certified(now, gs) : Bool}:
  %sg.shown(now, gs) : {St.certified(now, gs) == Bool.and(_, Nat.is_eq(S.blockers(now, gs), 0n)) : Bool}
  %sg.clear(now, gs) : {St.certified(now, gs) == Bool.and(St.shown(now, gs), _) : Bool}
  {==}

# a blocking check anywhere makes the checks unclear
def sg.clear_around(+now: Nat, pre: List<&2, St.Gauge>, +g: St.Gauge, -post: List<&2, St.Gauge>, weak: {S.blocking(S.strength(now, g)) == True{} : Bool}) -> {False{} == St.clear(now, Strength.sp_around(pre, g, post)) : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(St.Strength, St.strength(now, g), S.strength(now, g), sg.strength(now, g)) : {False{} == Bool.and(Bool.not(St.blocks(_)), St.clear(now, post)) : Bool}
      %Equal.sym(Bool, St.blocks(S.strength(now, g)), S.blocking(S.strength(now, g)), sg.blocks(S.strength(now, g))) : {False{} == Bool.and(Bool.not(_), St.clear(now, post)) : Bool}
      %Equal.sym(Bool, S.blocking(S.strength(now, g)), True{}, weak) : {False{} == Bool.and(Bool.not(_), St.clear(now, post)) : Bool}
      {==}
    case Con{+h, t}:
      %sg.clear_around(now, t, g, post, weak) : {False{} == Bool.and(Bool.not(St.blocks(St.strength(now, h))), _) : Bool}
      sv.and_false(Bool.not(St.blocks(St.strength(now, h))))

# The label (K3)
# --------------

def sg.label.ok(b: Bool, l: V.Label) -> {St.label.cert(b, l) == S.label.ok(b, St.lift(l)) : St.Label}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the model's label is the spec's
def sg.label(+l: V.Label, +now: Nat, +gs: List<&2, St.Gauge>) -> {St.label(l, now, gs) == S.label(l, now, gs) : St.Label}:
  match l:
    case V.Verified{}:
      %sg.certified(now, gs) : {St.label.cert(St.certified(now, gs), V.Verified{}) == S.label.ok(_, St.Verified{}) : St.Label}
      sg.label.ok(St.certified(now, gs), V.Verified{})
    case V.Failed{}:
      {==}
    case V.Unverified{}:
      {==}
    case V.Passed{}:
      %sg.certified(now, gs) : {St.label.cert(St.certified(now, gs), V.Passed{}) == S.label.ok(_, St.Passed{}) : St.Label}
      sg.label.ok(St.certified(now, gs), V.Passed{})

def sg.uc(b: Bool, -l: V.Label, e: {S.is_uncertified(St.lift(l)) == False{} : Bool}) -> {S.is_uncertified(St.label.cert(b, l)) == Bool.not(b) : Bool}:
  match b:
    case True{}:
      e
    case False{}:
      {==}

def sg.done.cert(b: Bool, -l: V.Label, e: {S.is_done(St.label.cert(b, l)) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

# a label that says done has done certified
def sg.done(+l: V.Label, +now: Nat, +gs: List<&2, St.Gauge>, done: {S.is_done(St.label(l, now, gs)) == True{} : Bool}) -> {St.certified(now, gs) == True{} : Bool}:
  match l:
    case V.Verified{}:
      sg.done.cert(St.certified(now, gs), V.Verified{}, done)
    case V.Failed{}:
      sg.absurd({St.certified(now, gs) == True{} : Bool}, done)
    case V.Unverified{}:
      sg.absurd({St.certified(now, gs) == True{} : Bool}, done)
    case V.Passed{}:
      sg.done.cert(St.certified(now, gs), V.Passed{}, done)

# The verifier's step (K4)
# ------------------------

def sg.unm(+now: Nat, g: St.Gauge) -> {S.due_here(now, g) == St.unmeasured(now, g) : Bool}:
  match g:
    case St.Gauge{b, m}:
      match b:
        case St.Exempt{}:
          {==}
        case St.Waived{}:
          {==}
        case St.Needs{pct}:
          match pct:
            case 0n:
              {==}
            case 1n+q:
              match m:
                case St.Unmeasured{}:
                  {==}
                case St.Measured{c, r, p, at}:
                  {==}

# Some n when b
def sg.opt(b: Bool, n: Nat) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{n}
    case False{}:
      None{}

def sg.step(h: Bool, -d: Nat, +L: Nat, +i: Nat) -> {St.due.pick(h, i, sg.opt(Bool.not(Nat.is_eq(d, 0n)), Nat.add(L, 1n+i))) == sg.opt(Bool.not(Nat.is_eq(Nat.add(S.bit(h), d), 0n)), Nat.add(S.lead.step(h, L), i)) : Maybe<&2, Nat>}:
  match h:
    case True{}:
      {==}
    case False{}:
      %sg.add_succ(L, i) : {sg.opt(Bool.not(Nat.is_eq(d, 0n)), Nat.add(L, 1n+i)) == sg.opt(Bool.not(Nat.is_eq(d, 0n)), _) : Maybe<&2, Nat>}
      {==}

# the first due check, counted from i, is the spec's lead past i, when the
# spec counts one due
def sg.due(+now: Nat, gs: List<&2, St.Gauge>, +i: Nat) -> {St.due(now, gs, i) == sg.opt(Bool.not(Nat.is_eq(S.dues(now, gs), 0n)), Nat.add(S.lead(now, gs), i)) : Maybe<&2, Nat>}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +t}:
      %Equal.sym(Maybe<&2, Nat>, St.due(now, t, 1n+i), sg.opt(Bool.not(Nat.is_eq(S.dues(now, t), 0n)), Nat.add(S.lead(now, t), 1n+i)), sg.due(now, t, 1n+i)) : {St.due.pick(St.unmeasured(now, g), i, _) == sg.opt(Bool.not(Nat.is_eq(Nat.add(S.bit(S.due_here(now, g)), S.dues(now, t)), 0n)), Nat.add(S.lead.step(S.due_here(now, g), S.lead(now, t)), i)) : Maybe<&2, Nat>}
      %sg.unm(now, g) : {St.due.pick(_, i, sg.opt(Bool.not(Nat.is_eq(S.dues(now, t), 0n)), Nat.add(S.lead(now, t), 1n+i))) == sg.opt(Bool.not(Nat.is_eq(Nat.add(S.bit(S.due_here(now, g)), S.dues(now, t)), 0n)), Nat.add(S.lead.step(S.due_here(now, g), S.lead(now, t)), i)) : Maybe<&2, Nat>}
      sg.step(S.due_here(now, g), S.dues(now, t), S.lead(now, t), i)

def sg.settle.of(b: Bool, +l: V.Label, +now: Nat, +gs: List<&2, St.Gauge>) -> {St.settle.due(sg.opt(b, Nat.add(S.lead(now, gs), 0n)), l, now, gs) == S.settle.of(b, l, now, gs) : St.Step}:
  match b:
    case True{}:
      %sg.add_zero(S.lead(now, gs)) : {St.Measure{Nat.add(S.lead(now, gs), 0n)} == St.Measure{_} : St.Step}
      {==}
    case False{}:
      %sg.label(l, now, gs) : {St.End{St.label(l, now, gs)} == St.End{_} : St.Step}
      {==}

# the model's step is the spec's
def sg.settle(+l: V.Label, +now: Nat, +gs: List<&2, St.Gauge>) -> {St.settle(l, now, gs) == S.settle(l, now, gs) : St.Step}:
  match l:
    case V.Verified{}:
      %Equal.sym(Maybe<&2, Nat>, St.due(now, gs, 0n), sg.opt(Bool.not(Nat.is_eq(S.dues(now, gs), 0n)), Nat.add(S.lead(now, gs), 0n)), sg.due(now, gs, 0n)) : {St.settle.due(_, V.Verified{}, now, gs) == S.settle(V.Verified{}, now, gs) : St.Step}
      sg.settle.of(Bool.not(Nat.is_eq(S.dues(now, gs), 0n)), V.Verified{}, now, gs)
    case V.Failed{}:
      {==}
    case V.Unverified{}:
      {==}
    case V.Passed{}:
      %Equal.sym(Maybe<&2, Nat>, St.due(now, gs, 0n), sg.opt(Bool.not(Nat.is_eq(S.dues(now, gs), 0n)), Nat.add(S.lead(now, gs), 0n)), sg.due(now, gs, 0n)) : {St.settle.due(_, V.Passed{}, now, gs) == S.settle(V.Passed{}, now, gs) : St.Step}
      sg.settle.of(Bool.not(Nat.is_eq(S.dues(now, gs), 0n)), V.Passed{}, now, gs)

def sg.ends.due(d: Maybe<&2, Nat>, +l: V.Label, +now: Nat, +gs: List<&2, St.Gauge>, e: {S.ends_done(St.settle.due(d, l, now, gs)) == True{} : Bool}) -> {St.certified(now, gs) == True{} : Bool}:
  match d:
    case None{}:
      sg.done(l, now, gs, e)
    case Some{i}:
      sg.absurd({St.certified(now, gs) == True{} : Bool}, e)

# a step that ends done has done certified
def sg.ends(+l: V.Label, +now: Nat, +gs: List<&2, St.Gauge>, done: {S.ends_done(St.settle(l, now, gs)) == True{} : Bool}) -> {St.certified(now, gs) == True{} : Bool}:
  match l:
    case V.Verified{}:
      sg.ends.due(St.due(now, gs, 0n), V.Verified{}, now, gs, done)
    case V.Failed{}:
      sg.absurd({St.certified(now, gs) == True{} : Bool}, done)
    case V.Unverified{}:
      sg.absurd({St.certified(now, gs) == True{} : Bool}, done)
    case V.Passed{}:
      sg.ends.due(St.due(now, gs, 0n), V.Passed{}, now, gs, done)

# Who records a mark (K5)
# -----------------------

def sg.MN(m: Maybe<&2, St.Gauge>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def sg.some_none(-g: St.Gauge, -G: Type, e: {Some{g} == None{} : Maybe<&2, St.Gauge>}) -> G:
  %e : sg.MN(_, G)
  Unit{}

# with no check i, put finds none
def sg.put_none(i: Nat, -m: St.Mark, gs: List<&2, St.Gauge>, none: {S.nth(i, gs) == None{} : Maybe<&2, St.Gauge>}) -> {None{} == St.put(i, m, gs) : Maybe<&2, List<&2, St.Gauge>>}:
  match i:
    case 0n:
      match gs:
        case Nil{}:
          {==}
        case Con{g, t}:
          sg.some_none(g, {None{} == St.put(0n, m, g <> t) : Maybe<&2, List<&2, St.Gauge>>}, none)
    case 1n+p:
      match gs:
        case Nil{}:
          {==}
        case Con{h, t}:
          %sg.put_none(p, m, t, none) : {None{} == St.put.cons(h, _) : Maybe<&2, List<&2, St.Gauge>>}
          {==}

# gs with the mark of check i replaced by m
def sg.set(i: Nat, m: St.Mark, gs: List<&2, St.Gauge>) -> List<&2, St.Gauge>:
  match i:
    case 0n:
      match gs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          St.put.mark(m, h) <> t
    case 1n+p:
      match gs:
        case Nil{}:
          Nil{}
        case Con{h, t}:
          h <> sg.set(p, m, t)

# with a check i, put writes it
def sg.put_some(i: Nat, -m: St.Mark, gs: List<&2, St.Gauge>, has: {Nat.is_lt(i, List.length(&2, St.Gauge, gs)) == True{} : Bool}) -> {Some{sg.set(i, m, gs)} == St.put(i, m, gs) : Maybe<&2, List<&2, St.Gauge>>}:
  match i:
    case 0n:
      match gs:
        case Nil{}:
          sg.absurd({Some{sg.set(0n, m, Nil{})} == St.put(0n, m, Nil{}) : Maybe<&2, List<&2, St.Gauge>>}, has)
        case Con{h, t}:
          {==}
    case 1n+p:
      match gs:
        case Nil{}:
          sg.absurd({Some{sg.set(1n+p, m, Nil{})} == St.put(1n+p, m, Nil{}) : Maybe<&2, List<&2, St.Gauge>>}, has)
        case Con{h, t}:
          %sg.put_some(p, m, t, has) : {Some{h <> sg.set(p, m, t)} == St.put.cons(h, _) : Maybe<&2, List<&2, St.Gauge>>}
          {==}

def sg.remark_none(b: Bool, -m: St.Mark) -> {None{} == S.remark_if(b, m, None{}) : Maybe<&2, St.Gauge>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the check at every index j after the write
def sg.nth_set(j: Nat, i: Nat, +m: St.Mark, gs: List<&2, St.Gauge>) -> {S.nth(j, sg.set(i, m, gs)) == S.remark_if(Nat.is_eq(j, i), m, S.nth(j, gs)) : Maybe<&2, St.Gauge>}:
  match j i:
    case 0n 0n:
      match gs:
        case Nil{}:
          {==}
        case Con{h, t}:
          match h:
            case St.Gauge{b, old}:
              {==}
    case 0n 1n+p:
      match gs:
        case Nil{}:
          {==}
        case Con{h, t}:
          {==}
    case 1n+q 0n:
      match gs:
        case Nil{}:
          {==}
        case Con{h, t}:
          {==}
    case 1n+q 1n+p:
      match gs:
        case Nil{}:
          sg.remark_none(Nat.is_eq(q, p), m)
        case Con{h, t}:
          sg.nth_set(q, p, m, t)

# The exit code (K6)
# ------------------

def sg.some(slots: List<&2, V.Slot>) -> {Bool.not(V.some(slots)) == Nat.is_eq(List.length(&2, V.Slot, slots), 0n) : Bool}:
  match slots:
    case Nil{}:
      {==}
    case Con{s, t}:
      {==}

def sg.ecert(ok: Bool, base: Nat) -> {St.exit.cert(ok, base) == S.exit.cert(ok, base) : Nat}:
  match ok:
    case True{}:
      {==}
    case False{}:
      match base:
        case 0n:
          {==}
        case 1n+p:
          {==}

def sg.exit.all(h: Bool, +base: Nat, +now: Nat, +slots: List<&2, V.Slot>, +gs: List<&2, St.Gauge>) -> {St.exit.held(h, base, now, slots, gs) == S.exit.all(h, base, now, slots, gs) : Nat}:
  match h:
    case True{}:
      %sg.some(slots) : {St.exit.cert(Bool.or(Bool.not(V.some(slots)), St.certified(now, gs)), base) == S.exit.cert(Bool.or(_, S.certified(now, gs)), base) : Nat}
      %sg.certified(now, gs) : {St.exit.cert(Bool.or(Bool.not(V.some(slots)), St.certified(now, gs)), base) == S.exit.cert(Bool.or(Bool.not(V.some(slots)), _), base) : Nat}
      sg.ecert(Bool.or(Bool.not(V.some(slots)), St.certified(now, gs)), base)
    case False{}:
      sv.exit(False{}, base)

# the model's exit code is the spec's
def sg.exit(+base: Nat, +now: Nat, +slots: List<&2, V.Slot>, +gs: List<&2, St.Gauge>) -> {St.exit(base, now, slots, gs) == S.exit(base, now, slots, gs) : Nat}:
  %sv.holds(now, slots) : {St.exit.held(_, base, now, slots, gs) == S.exit(base, now, slots, gs) : Nat}
  sg.exit.all(SV.all_confirmed(now, slots), base, now, slots, gs)

def sg.ez.cert(c: Bool, base: Nat) -> {Nat.is_eq(S.exit.cert(c, base), 0n) == Bool.and(Nat.is_eq(base, 0n), c) : Bool}:
  match c:
    case True{}:
      match base:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case False{}:
      match base:
        case 0n:
          {==}
        case 1n+p:
          {==}

def sg.ez.all(a: Bool, +base: Nat, +now: Nat, +slots: List<&2, V.Slot>, +gs: List<&2, St.Gauge>) -> {Nat.is_eq(S.exit.all(a, base, now, slots, gs), 0n) == Bool.and(Nat.is_eq(base, 0n), Bool.and(a, Bool.or(Nat.is_eq(List.length(&2, V.Slot, slots), 0n), S.certified(now, gs)))) : Bool}:
  match a:
    case True{}:
      sg.ez.cert(Bool.or(Nat.is_eq(List.length(&2, V.Slot, slots), 0n), S.certified(now, gs)), base)
    case False{}:
      match base:
        case 0n:
          {==}
        case 1n+p:
          {==}

def sg.keep.cert(ok: Bool, -p: Nat) -> {St.exit.cert(ok, 1n+p) == 1n+p : Nat}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def sg.keep(h: Bool, -p: Nat, +now: Nat, +slots: List<&2, V.Slot>, +gs: List<&2, St.Gauge>) -> {St.exit.held(h, 1n+p, now, slots, gs) == 1n+p : Nat}:
  match h:
    case True{}:
      sg.keep.cert(Bool.or(Bool.not(V.some(slots)), St.certified(now, gs)), p)
    case False{}:
      {==}

# a run of code 0 whose checks (one or more) are all confirmed while done
# is not certified exits the unjudged code
def sg.three(+now: Nat, +slots: List<&2, V.Slot>, +gs: List<&2, St.Gauge>, all: {SV.all_confirmed(now, slots) == True{} : Bool}, some: {Nat.is_eq(List.length(&2, V.Slot, slots), 0n) == False{} : Bool}, un: {S.certified(now, gs) == False{} : Bool}) -> {St.exit(0n, now, slots, gs) == Ht.unjudged_code() : Nat}:
  %Equal.sym(Nat, St.exit(0n, now, slots, gs), S.exit(0n, now, slots, gs), sg.exit(0n, now, slots, gs)) : {_ == Ht.unjudged_code() : Nat}
  %Equal.sym(Bool, SV.all_confirmed(now, slots), True{}, all) : {S.exit.all(_, 0n, now, slots, gs) == Ht.unjudged_code() : Nat}
  %Equal.sym(Bool, Nat.is_eq(List.length(&2, V.Slot, slots), 0n), False{}, some) : {S.exit.cert(Bool.or(_, S.certified(now, gs)), 0n) == Ht.unjudged_code() : Nat}
  %Equal.sym(Bool, S.certified(now, gs), False{}, un) : {S.exit.cert(_, 0n) == Ht.unjudged_code() : Nat}
  {==}
