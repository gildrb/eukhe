# eukhe: lemmas of the proofs of area attack on the model
# (bend/attack.bend): the folds of certified are the spec's counts
# (am.unsurvived, am.cleans, am.certified), a survivor anywhere is seen
# (am.survived_around), an unrun outcome anywhere changes no fold
# (am.survived_unrun, am.cleans_unrun), no outcome leaves
# bend/strength.bend's certified (am.cert_none), and the label and the
# exit code by cases

import Base
import ../../../bend/verify.bend as V
import ../../../bend/strength.bend as St
import ../../../bend/attack.bend as At
import ../../../bend/headless_task.bend as Ht
import ../../../spec/verified/verify.bend as SV
import ../../../spec/verified/strength.bend as S
import ../../../spec/verified/attack.bend as SA
import ../../strength/base/model.bend as LS

# Bool
# ----

def am.true_or(x: Bool) -> {True{} == Bool.or(x, True{}) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# not x is false where x is true
def am.not_true(x: Bool, e: {x == True{} : Bool}) -> {Bool.not(x) == False{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      LS.sg.absurd({Bool.not(False{}) == False{} : Bool}, e)

def am.or_ff(a: Bool, -b: Bool, ea: {a == False{} : Bool}, eb: {b == False{} : Bool}) -> {Bool.or(a, b) == False{} : Bool}:
  match a:
    case True{}:
      LS.sg.absurd_t({Bool.or(True{}, b) == False{} : Bool}, ea)
    case False{}:
      eb

def am.or_and_false(c: Bool, d: Bool) -> {Bool.or(c, Bool.and(d, False{})) == c : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      match d:
        case True{}:
          {==}
        case False{}:
          {==}

# the shape of certified: some check strong and clear, or clear and
# enough clean attacks, is clear and either
def am.cert_bool(x: Bool, sh: Bool, cl: Bool, k: Bool) -> {Bool.and(x, Bool.or(Bool.and(sh, cl), Bool.and(cl, k))) == Bool.and(x, Bool.and(cl, Bool.or(sh, k))) : Bool}:
  match x:
    case True{}:
      match sh:
        case True{}:
          match cl:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match cl:
            case True{}:
              {==}
            case False{}:
              {==}
    case False{}:
      {==}

# Survivors and clean attacks
# ---------------------------

# a survivor anywhere among the outcomes is seen
def am.survived_around(pre: List<&2, At.Outcome>, -post: List<&2, At.Outcome>) -> {True{} == At.survived(List.append(&2, At.Outcome, pre, At.Survived{} <> post)) : Bool}:
  match pre:
    case Nil{}:
      {==}
    case Con{+o, t}:
      %am.survived_around(t, post) : {True{} == Bool.or(At.is_survived(o), _) : Bool}
      am.true_or(At.is_survived(o))

# no attack survived exactly when the spec counts none
def am.unsurvived(os: List<&2, At.Outcome>) -> {Bool.not(At.survived(os)) == Nat.is_eq(SA.survivors(os), 0n) : Bool}:
  match os:
    case Nil{}:
      {==}
    case Con{o, t}:
      match o:
        case At.Survived{}:
          {==}
        case At.Clean{}:
          am.unsurvived(t)
        case At.Unrun{}:
          am.unsurvived(t)

# the clean attacks are the spec's count
def am.cleans(os: List<&2, At.Outcome>) -> {At.cleans(os) == SA.cleans(os) : Nat}:
  match os:
    case Nil{}:
      {==}
    case Con{o, t}:
      match o:
        case At.Survived{}:
          am.cleans(t)
        case At.Clean{}:
          %am.cleans(t) : {1n+At.cleans(t) == 1n+_ : Nat}
          {==}
        case At.Unrun{}:
          am.cleans(t)

# an unrun outcome anywhere changes whether one survived
def am.survived_unrun(pre: List<&2, At.Outcome>, -post: List<&2, At.Outcome>) -> {At.survived(List.append(&2, At.Outcome, pre, At.Unrun{} <> post)) == At.survived(List.append(&2, At.Outcome, pre, post)) : Bool}:
  match pre:
    case Nil{}:
      {==}
    case Con{+o, t}:
      %am.survived_unrun(t, post) : {Bool.or(At.is_survived(o), At.survived(List.append(&2, At.Outcome, t, At.Unrun{} <> post))) == Bool.or(At.is_survived(o), _) : Bool}
      {==}

# an unrun outcome anywhere changes no count of clean attacks
def am.cleans_unrun(pre: List<&2, At.Outcome>, -post: List<&2, At.Outcome>) -> {At.cleans(List.append(&2, At.Outcome, pre, At.Unrun{} <> post)) == At.cleans(List.append(&2, At.Outcome, pre, post)) : Nat}:
  match pre:
    case Nil{}:
      {==}
    case Con{+o, t}:
      %am.cleans_unrun(t, post) : {At.cleans.add(At.is_clean(o), At.cleans(List.append(&2, At.Outcome, t, At.Unrun{} <> post))) == At.cleans.add(At.is_clean(o), _) : Nat}
      {==}

# Certified
# ---------

# outcomes with the same survivors and clean attacks certify alike
def am.cert_eq(-now: Nat, -gs: List<&2, St.Gauge>, -os1: List<&2, At.Outcome>, -os2: List<&2, At.Outcome>, es: {At.survived(os1) == At.survived(os2) : Bool}, ec: {At.cleans(os1) == At.cleans(os2) : Nat}) -> {At.certified(now, gs, os1) == At.certified(now, gs, os2) : Bool}:
  %es : {At.certified(now, gs, os1) == Bool.and(Bool.not(_), Bool.or(St.certified(now, gs), Bool.and(St.clear(now, gs), Nat.is_le(At.needed(), At.cleans(os2))))) : Bool}
  %ec : {At.certified(now, gs, os1) == Bool.and(Bool.not(At.survived(os1)), Bool.or(St.certified(now, gs), Bool.and(St.clear(now, gs), Nat.is_le(At.needed(), _)))) : Bool}
  {==}

# a survivor anywhere keeps done from being certified
def am.cert_survivor(-now: Nat, -gs: List<&2, St.Gauge>, pre: List<&2, At.Outcome>, -post: List<&2, At.Outcome>) -> {At.certified(now, gs, List.append(&2, At.Outcome, pre, At.Survived{} <> post)) == False{} : Bool}:
  %am.survived_around(pre, post) : {Bool.and(Bool.not(_), Bool.or(St.certified(now, gs), Bool.and(St.clear(now, gs), Nat.is_le(At.needed(), At.cleans(List.append(&2, At.Outcome, pre, At.Survived{} <> post)))))) == False{} : Bool}
  {==}

def am.blocked(cl: Bool, x: Bool, sh: Bool, -k: Bool, e: {cl == False{} : Bool}) -> {Bool.and(x, Bool.or(Bool.and(sh, cl), Bool.and(cl, k))) == False{} : Bool}:
  match cl:
    case True{}:
      LS.sg.absurd_t({Bool.and(x, Bool.or(Bool.and(sh, True{}), Bool.and(True{}, k))) == False{} : Bool}, e)
    case False{}:
      match x:
        case True{}:
          match sh:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          {==}

# with no outcome, done is certified as bend/strength.bend says
def am.cert_none(+now: Nat, +gs: List<&2, St.Gauge>) -> {At.certified(now, gs, Nil{}) == St.certified(now, gs) : Bool}:
  am.or_and_false(St.certified(now, gs), St.clear(now, gs))

def am.judge(sh: Bool, cl: Bool, -x: Bool, -k: Bool, esh: {sh == False{} : Bool}, ecl: {cl == True{} : Bool}) -> {Bool.and(x, Bool.or(Bool.and(sh, cl), Bool.and(cl, k))) == Bool.and(x, k) : Bool}:
  match sh:
    case True{}:
      LS.sg.absurd_t({Bool.and(x, Bool.or(Bool.and(True{}, cl), Bool.and(cl, k))) == Bool.and(x, k) : Bool}, esh)
    case False{}:
      match cl:
        case True{}:
          {==}
        case False{}:
          LS.sg.absurd({Bool.and(x, Bool.or(Bool.and(False{}, False{}), Bool.and(False{}, k))) == Bool.and(x, k) : Bool}, ecl)

# no check strong on the state now: none is shown
def am.shown_false(+now: Nat, +gs: List<&2, St.Gauge>, none: {S.strongs(now, gs) == 0n : Nat}) -> {St.shown(now, gs) == False{} : Bool}:
  %none : {St.shown(now, gs) == Bool.not(Nat.is_eq(_, 0n)) : Bool}
  LS.sg.shown(now, gs)

# the model's certified is the spec's
def am.certified(+now: Nat, +gs: List<&2, St.Gauge>, +os: List<&2, At.Outcome>) -> {At.certified(now, gs, os) == SA.certified(now, gs, os) : Bool}:
  %am.unsurvived(os) : {At.certified(now, gs, os) == Bool.and(_, Bool.and(Nat.is_eq(S.blockers(now, gs), 0n), Bool.or(Bool.not(Nat.is_eq(S.strongs(now, gs), 0n)), Nat.is_le(2n, SA.cleans(os))))) : Bool}
  %LS.sg.clear(now, gs) : {At.certified(now, gs, os) == Bool.and(Bool.not(At.survived(os)), Bool.and(_, Bool.or(Bool.not(Nat.is_eq(S.strongs(now, gs), 0n)), Nat.is_le(2n, SA.cleans(os))))) : Bool}
  %LS.sg.shown(now, gs) : {At.certified(now, gs, os) == Bool.and(Bool.not(At.survived(os)), Bool.and(St.clear(now, gs), Bool.or(_, Nat.is_le(2n, SA.cleans(os))))) : Bool}
  %am.cleans(os) : {At.certified(now, gs, os) == Bool.and(Bool.not(At.survived(os)), Bool.and(St.clear(now, gs), Bool.or(St.shown(now, gs), Nat.is_le(2n, _)))) : Bool}
  am.cert_bool(Bool.not(At.survived(os)), St.shown(now, gs), St.clear(now, gs), Nat.is_le(2n, At.cleans(os)))

# The label and the exit code
# ---------------------------

# the model's label is the spec's
def am.label(+l: V.Label, +now: Nat, +gs: List<&2, St.Gauge>, +os: List<&2, At.Outcome>) -> {At.label(l, now, gs, os) == SA.label(l, now, gs, os) : St.Label}:
  match l:
    case V.Verified{}:
      %am.certified(now, gs, os) : {St.label.cert(At.certified(now, gs, os), V.Verified{}) == S.label.ok(_, St.Verified{}) : St.Label}
      LS.sg.label.ok(At.certified(now, gs, os), V.Verified{})
    case V.Failed{}:
      {==}
    case V.Unverified{}:
      {==}
    case V.Passed{}:
      %am.certified(now, gs, os) : {St.label.cert(At.certified(now, gs, os), V.Passed{}) == S.label.ok(_, St.Passed{}) : St.Label}
      LS.sg.label.ok(At.certified(now, gs, os), V.Passed{})

def am.label_unc(p: Bool, c: Bool, -l: V.Label, ep: {p == True{} : Bool}, ec: {c == False{} : Bool}) -> {St.label.pass(p, c, l) == St.Uncertified{} : St.Label}:
  match p:
    case True{}:
      match c:
        case True{}:
          LS.sg.absurd_t({St.label.pass(True{}, True{}, l) == St.Uncertified{} : St.Label}, ec)
        case False{}:
          {==}
    case False{}:
      LS.sg.absurd({St.label.pass(False{}, c, l) == St.Uncertified{} : St.Label}, ep)

def am.exit.all(h: Bool, +base: Nat, +now: Nat, +slots: List<&2, V.Slot>, +gs: List<&2, St.Gauge>, +os: List<&2, At.Outcome>) -> {At.exit.held(h, base, now, slots, gs, os) == SA.exit.all(h, base, now, slots, gs, os) : Nat}:
  match h:
    case True{}:
      %LS.sg.some(slots) : {St.exit.cert(Bool.or(Bool.not(V.some(slots)), At.certified(now, gs, os)), base) == S.exit.cert(Bool.or(_, SA.certified(now, gs, os)), base) : Nat}
      %am.certified(now, gs, os) : {St.exit.cert(Bool.or(Bool.not(V.some(slots)), At.certified(now, gs, os)), base) == S.exit.cert(Bool.or(Bool.not(V.some(slots)), _), base) : Nat}
      LS.sg.ecert(Bool.or(Bool.not(V.some(slots)), At.certified(now, gs, os)), base)
    case False{}:
      LS.sv.exit(False{}, base)

# the model's exit code is the spec's
def am.exit(+base: Nat, +now: Nat, +slots: List<&2, V.Slot>, +gs: List<&2, St.Gauge>, +os: List<&2, At.Outcome>) -> {At.exit(base, now, slots, gs, os) == SA.exit(base, now, slots, gs, os) : Nat}:
  %LS.sv.holds(now, slots) : {At.exit.held(_, base, now, slots, gs, os) == SA.exit(base, now, slots, gs, os) : Nat}
  am.exit.all(SV.all_confirmed(now, slots), base, now, slots, gs, os)

# with no outcome, the exit code is bend/strength.bend's
def am.exit_none(h: Bool, +base: Nat, +now: Nat, +slots: List<&2, V.Slot>, +gs: List<&2, St.Gauge>) -> {At.exit.held(h, base, now, slots, gs, Nil{}) == St.exit.held(h, base, now, slots, gs) : Nat}:
  match h:
    case True{}:
      %am.cert_none(now, gs) : {St.exit.cert(Bool.or(Bool.not(V.some(slots)), At.certified(now, gs, Nil{})), base) == St.exit.cert(Bool.or(Bool.not(V.some(slots)), _), base) : Nat}
      {==}
    case False{}:
      {==}

def am.ecert_false(ok: Bool, base: Nat, e: {ok == False{} : Bool}) -> {Nat.is_eq(St.exit.cert(ok, base), 0n) == False{} : Bool}:
  match ok:
    case True{}:
      LS.sg.absurd_t({Nat.is_eq(St.exit.cert(True{}, base), 0n) == False{} : Bool}, e)
    case False{}:
      match base:
        case 0n:
          {==}
        case 1n+p:
          {==}

# a run with a check whose done is not certified never exits 0
def am.exit_uncertified(h: Bool, base: Nat, +now: Nat, +slots: List<&2, V.Slot>, +gs: List<&2, St.Gauge>, +os: List<&2, At.Outcome>, es: {V.some(slots) == True{} : Bool}, ec: {At.certified(now, gs, os) == False{} : Bool}) -> {Nat.is_eq(At.exit.held(h, base, now, slots, gs, os), 0n) == False{} : Bool}:
  match h:
    case True{}:
      am.ecert_false(Bool.or(Bool.not(V.some(slots)), At.certified(now, gs, os)), base, am.or_ff(Bool.not(V.some(slots)), At.certified(now, gs, os), am.not_true(V.some(slots), es), ec))
    case False{}:
      match base:
        case 0n:
          {==}
        case 1n+p:
          {==}
