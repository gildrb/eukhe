# eukhe: lemmas the proofs of area autonomous share: the entry's decoder
# is the laws' reader (spec/autonomous/autonomous.bend), stage by stage; a
# spelled request reads back whole; the entry spells a step as the spec
# does

import Base
import ../../bend/verify.bend as V
import ../../bend/autonomous.bend as Au
import ../../bend/ffi_autonomous.bend as FAu
import ../../bend/work_left.bend as Wl
import ../../bend/wire.bend as Wr
import ../../spec/autonomous/autonomous.bend as SpA
import ../../spec/agents/work_left.bend as SpL
import ../../laws/autonomous.bend as Autonomous
import ../../laws/wire.bend as Wire

# The reader
# ----------

def au.answer(d: Wr.Dec<Nat>) -> {FAu.get_answer(d) == SpA.r_answer(d) : Wr.Dec<Au.Answer>}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n+u:
          {==}
    case Wr.Bad{}:
      {==}

def au.label(d: Wr.Dec<Nat>) -> {FAu.get_label(d) == SpA.r_label(d) : Wr.Dec<V.Label>}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n+u:
          {==}
    case Wr.Bad{}:
      {==}

def au.ended(d: Wr.Dec<V.Label>) -> {FAu.get_checks.ended(d) == SpA.r_checks.ended(d) : Wr.Dec<Au.Checks>}:
  match d:
    case Wr.Got{l, s}:
      {==}
    case Wr.Bad{}:
      {==}

def au.checks(d: Wr.Dec<Nat>) -> {FAu.get_checks(d) == SpA.r_checks(d) : Wr.Dec<Au.Checks>}:
  match d:
    case Wr.Got{t, +s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          %au.label(Wr.get_nat(s)) : {FAu.get_checks.ended(FAu.get_label(Wr.get_nat(s))) == SpA.r_checks.ended(_) : Wr.Dec<Au.Checks>}
          au.ended(FAu.get_label(Wr.get_nat(s)))
        case 3n+u:
          {==}
    case Wr.Bad{}:
      {==}

def au.budget(d: Wr.Dec<Nat>) -> {FAu.get_budget(d) == SpA.r_budget(d) : Wr.Dec<Au.Budget>}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n+u:
          {==}
    case Wr.Bad{}:
      {==}

def au.reading(d: Wr.Dec<Nat>) -> {FAu.get_reading(d) == SpA.r_reading(d) : Wr.Dec<Wl.Reading>}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n+u:
          {==}
    case Wr.Bad{}:
      {==}

def au.after_reading(on: Bool, a: Au.Answer, c: Au.Checks, b: Au.Budget, d: Wr.Dec<Wl.Reading>) -> {FAu.get_facts.reading(on, a, c, b, d) == SpA.r_req.reading(on, a, c, b, d) : Wr.Dec<Au.Facts>}:
  match d:
    case Wr.Got{r, s}:
      {==}
    case Wr.Bad{}:
      {==}

def au.after_budget(+on: Bool, +a: Au.Answer, +c: Au.Checks, d: Wr.Dec<Au.Budget>) -> {FAu.get_facts.budget(on, a, c, d) == SpA.r_req.budget(on, a, c, d) : Wr.Dec<Au.Facts>}:
  match d:
    case Wr.Got{+b, +s}:
      %au.reading(Wr.get_nat(s)) : {FAu.get_facts.reading(on, a, c, b, FAu.get_reading(Wr.get_nat(s))) == SpA.r_req.reading(on, a, c, b, _) : Wr.Dec<Au.Facts>}
      au.after_reading(on, a, c, b, FAu.get_reading(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def au.after_checks(+on: Bool, +a: Au.Answer, d: Wr.Dec<Au.Checks>) -> {FAu.get_facts.checks(on, a, d) == SpA.r_req.checks(on, a, d) : Wr.Dec<Au.Facts>}:
  match d:
    case Wr.Got{+c, +s}:
      %au.budget(Wr.get_nat(s)) : {FAu.get_facts.budget(on, a, c, FAu.get_budget(Wr.get_nat(s))) == SpA.r_req.budget(on, a, c, _) : Wr.Dec<Au.Facts>}
      au.after_budget(on, a, c, FAu.get_budget(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def au.after_answer(+on: Bool, d: Wr.Dec<Au.Answer>) -> {FAu.get_facts.answer(on, d) == SpA.r_req.answer(on, d) : Wr.Dec<Au.Facts>}:
  match d:
    case Wr.Got{+a, +s}:
      %au.checks(Wr.get_nat(s)) : {FAu.get_facts.checks(on, a, FAu.get_checks(Wr.get_nat(s))) == SpA.r_req.checks(on, a, _) : Wr.Dec<Au.Facts>}
      au.after_checks(on, a, FAu.get_checks(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def au.after_on(d: Wr.Dec<Bool>) -> {FAu.get_facts.on(d) == SpA.r_req.on(d) : Wr.Dec<Au.Facts>}:
  match d:
    case Wr.Got{+on, +s}:
      %au.answer(Wr.get_nat(s)) : {FAu.get_facts.answer(on, FAu.get_answer(Wr.get_nat(s))) == SpA.r_req.answer(on, _) : Wr.Dec<Au.Facts>}
      au.after_answer(on, FAu.get_answer(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

# the entry reads a request as the laws' reader does
def au.req(+s: String) -> {FAu.get_facts(s) == SpA.r_req(s) : Wr.Dec<Au.Facts>}:
  au.after_on(Wr.get_bool(s))

# Read back
# ---------

def au.answer_rt(a: Au.Answer, -rest: String) -> {SpA.r_answer(Wr.get_nat(SpA.w_answer(a, rest))) == Wr.Got{a, rest} : Wr.Dec<Au.Answer>}:
  match a:
    case Au.Settled{}:
      {==}
    case Au.Broken{}:
      {==}

def au.label_rt(l: V.Label, -rest: String) -> {SpA.r_label(Wr.get_nat(SpA.w_label(l, rest))) == Wr.Got{l, rest} : Wr.Dec<V.Label>}:
  match l:
    case V.Verified{}:
      {==}
    case V.Failed{}:
      {==}
    case V.Unverified{}:
      {==}
    case V.Passed{}:
      {==}

def au.checks_rt(c: Au.Checks, +rest: String) -> {SpA.r_checks(Wr.get_nat(SpA.w_checks(c, rest))) == Wr.Got{c, rest} : Wr.Dec<Au.Checks>}:
  match c:
    case Au.Unchecked{}:
      {==}
    case Au.Returned{}:
      {==}
    case Au.Ended{+l}:
      %Equal.sym(Wr.Dec<V.Label>, SpA.r_label(Wr.get_nat(SpA.w_label(l, rest))), Wr.Got{l, rest}, au.label_rt(l, rest)) : {SpA.r_checks.ended(_) == Wr.Got{Au.Ended{l}, rest} : Wr.Dec<Au.Checks>}
      {==}

def au.budget_rt(b: Au.Budget, -rest: String) -> {SpA.r_budget(Wr.get_nat(SpA.w_budget(b, rest))) == Wr.Got{b, rest} : Wr.Dec<Au.Budget>}:
  match b:
    case Au.Working{}:
      {==}
    case Au.Short{}:
      {==}

def au.reading_rt(r: Wl.Reading, -rest: String) -> {SpA.r_reading(Wr.get_nat(SpL.w_reading(r, rest))) == Wr.Got{r, rest} : Wr.Dec<Wl.Reading>}:
  match r:
    case Wl.Unread{}:
      {==}
    case Wl.Finished{}:
      {==}
    case Wl.Left{}:
      {==}
    case Wl.Unjudged{}:
      {==}

# a spelled request reads back (with the laws' reader), and the rest is
# untouched
def au.req_rt(+f: Au.Facts, +rest: String) -> {SpA.r_req(SpA.w_req(f, rest)) == Wr.Got{f, rest} : Wr.Dec<Au.Facts>}:
  match f:
    case Au.Facts{+on, +a, +c, +b, +r}:
      +r4 = SpL.w_reading(r, rest)
      +r3 = SpA.w_budget(b, r4)
      +r2 = SpA.w_checks(c, r3)
      +r1 = SpA.w_answer(a, r2)
      -q = {Wr.Got{Au.Facts{on, a, c, b, r}, rest} : Wr.Dec<Au.Facts>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(on, r1)), Wr.Got{on, r1}, Wire.wire_bool_round_trip(on, r1)) : {SpA.r_req.on(_) == q : Wr.Dec<Au.Facts>}
      %Equal.sym(Wr.Dec<Au.Answer>, SpA.r_answer(Wr.get_nat(r1)), Wr.Got{a, r2}, au.answer_rt(a, r2)) : {SpA.r_req.answer(on, _) == q : Wr.Dec<Au.Facts>}
      %Equal.sym(Wr.Dec<Au.Checks>, SpA.r_checks(Wr.get_nat(r2)), Wr.Got{c, r3}, au.checks_rt(c, r3)) : {SpA.r_req.checks(on, a, _) == q : Wr.Dec<Au.Facts>}
      %Equal.sym(Wr.Dec<Au.Budget>, SpA.r_budget(Wr.get_nat(r3)), Wr.Got{b, r4}, au.budget_rt(b, r4)) : {SpA.r_req.budget(on, a, c, _) == q : Wr.Dec<Au.Facts>}
      %Equal.sym(Wr.Dec<Wl.Reading>, SpA.r_reading(Wr.get_nat(r4)), Wr.Got{r, rest}, au.reading_rt(r, rest)) : {SpA.r_req.reading(on, a, c, b, _) == q : Wr.Dec<Au.Facts>}
      {==}

# The reply
# ---------

def au.put_label(l: V.Label, -rest: String) -> {FAu.put_label(l, rest) == SpA.w_label(l, rest) : String}:
  match l:
    case V.Verified{}:
      {==}
    case V.Failed{}:
      {==}
    case V.Unverified{}:
      {==}
    case V.Passed{}:
      {==}

# the entry spells a step as the spec does
def au.put(t: Au.Step, +rest: String) -> {FAu.put_step(t, rest) == SpA.w_step(t, rest) : String}:
  match t:
    case Au.Off{}:
      {==}
    case Au.Hold{}:
      {==}
    case Au.Continue{}:
      {==}
    case Au.Stop{c}:
      match c:
        case Au.ByChecks{+l}:
          %Equal.sym(String, FAu.put_label(l, rest), SpA.w_label(l, rest), au.put_label(l, rest)) : {Wr.put_nat(3n, Wr.put_nat(0n, _)) == Wr.put_nat(3n, Wr.put_nat(0n, SpA.w_label(l, rest))) : String}
          {==}
        case Au.ByBudget{}:
          {==}
    case Au.Ask{}:
      {==}
    case Au.Finish{}:
      {==}
