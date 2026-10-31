# eukhe: lemmas the proofs of laws/approvals/desk.bend share: the model's
# gateway rule and fates are the spec's

import Base
import ../../../bend/approvals.bend as Am
import ../../../bend/tools.bend as Tl
import ../../../laws/approvals/desk.bend as ApprovalsDesk

# the model's membership is the spec's
def ap.has(xs: List<&2, Nat>, +x: Nat) -> {Tl.elem(xs, x) == ApprovalsDesk.sp_has(xs, x) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> rest:
      %ap.has(rest, x) : {Bool.or(Nat.is_eq(y, x), Tl.elem(rest, x)) == Bool.or(Nat.is_eq(y, x), _) : Bool}
      {==}

def ap.guard(g: Bool) -> {Am.guard(g) == ApprovalsDesk.sp_guard(g) : Am.Fate}:
  match g:
    case True{}:
      {==}
    case False{}:
      {==}

# the model's gateway rule is the spec's
def ap.rule(+es: List<&2, Nat>) -> {Am.rule(es) == ApprovalsDesk.sp_rule(es) : Am.Fate}:
  %ap.has(es, 5n) : {Am.guard(Tl.elem(es, 5n)) == ApprovalsDesk.sp_guard(_) : Am.Fate}
  ap.guard(Tl.elem(es, 5n))

# the clients' answer
def ap.answered(+es: List<&2, Nat>, y: Bool) -> {Am.answered(es, y) == ApprovalsDesk.sp_answered(es, y) : Am.Fate}:
  match y:
    case True{}:
      {==}
    case False{}:
      {==}
