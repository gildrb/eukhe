# eukhe: lemmas the proofs of area tools share

import Base
import ../../bend/approvals.bend as Am
import ../../bend/tools.bend as Tl
import ../base/logic/logic.bend as LLogicLogic

def tools.pl.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : LLogicLogic.tools.pl.BD(_, Unit, A)
  Unit{}

def tools.pl.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      tools.pl.eq_refl(p)

def pl.le0(t: Nat) -> {Nat.is_le(0n, t) == True{} : Bool}:
  match t:
    case 0n:
      {==}
    case 1n+q:
      {==}

def pl.ids_refl(r: List<&2, Nat>) -> {Tl.ids.eq(r, r) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case +y <> yr:
      %tools.pl.eq_refl(y) : {Bool.and(_, Tl.ids.eq(yr, yr)) == True{} : Bool}
      pl.ids_refl(yr)

# 2. The schema
# -------------

def pl.add_has(b: Bool, +ps: List<&2, Nat>, e: {Tl.elem(ps, Tl.intent()) == b : Bool}) -> {Tl.elem(Tl.add_intent(b, ps), Tl.intent()) == True{} : Bool}:
  match b:
    case True{}:
      e
    case False{}:
      {==}

# 3. A path
# ---------

def pl.len(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case y <> rest:
      1n+pl.len(rest)

# 4. The approval gate
# --------------------

def pl.steps_add(+s: Tl.Step, r: Tl.Ran) -> {s <> Tl.Ran.steps(r) == Tl.Ran.steps(Tl.ran.add(s, r)) : List<&2, Tl.Step>}:
  match r:
    case Tl.Ran{ss, e}:
      {==}

# a denied step runs nothing
def pl.gate_no(s: Tl.Step, r: Tl.Ran) -> {Nil{} == Tl.Ran.steps(Tl.gate(False{}, s, r)) : List<&2, Tl.Step>}:
  match s:
    case Tl.Step{i, f}:
      {==}

# ---- shell ----

# proof_shell: the G2 laws (shell classification) of
# the gate model in bend/tools.bend part 4. An effect of a part is in the
# join of the parts (`ps.elem_app_l`, `ps.elem_app_r`, by induction on the
# parts before it). A step with one effect that is not within the auto set
# is not within it (`ps.within_out`, by induction on its effects, with the
# head test as a parameter). The gate reads `within` of
# the head step: a rewrite with it runs the step free, or with no answer
# denies it.

# Logic
# -----

def shell.ps.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def shell.ps.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : shell.ps.BD(_, A, Unit)
  Unit{}

def shell.ps.and_f(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def shell.ps.or_tr(a: Bool, +b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

def shell.ps.eq_of_is_eq(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      shell.ps.absurdF({0n == 1n+bp : Nat}, h)
    case 1n+ap 0n:
      shell.ps.absurdF({1n+ap == 0n : Nat}, h)
    case 1n+ap 1n+bp:
      %shell.ps.eq_of_is_eq(ap, bp, h) : {1n+ap == 1n+_ : Nat}
      {==}

# A step made of parts
# --------------------

# an element of ys is an element of xs ++ ys
def ps.elem_app_r(xs: List<&2, Nat>, +ys: List<&2, Nat>, +c: Nat, h: {Tl.elem(ys, c) == True{} : Bool}) -> {Tl.elem(List.append(&2, Nat, xs, ys), c) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +x <> +xr:
      shell.ps.or_tr(Nat.is_eq(x, c), Tl.elem(List.append(&2, Nat, xr, ys), c), ps.elem_app_r(xr, ys, c, h))

# the head test b of an element of xs: either b, or c is in the rest
def ps.app_head(b: Bool, +xr: List<&2, Nat>, +ys: List<&2, Nat>, +c: Nat, h: {Bool.or(b, Tl.elem(xr, c)) == True{} : Bool}, ih: {Tl.elem(xr, c) == True{} : Bool} -> {Tl.elem(List.append(&2, Nat, xr, ys), c) == True{} : Bool}) -> {Bool.or(b, Tl.elem(List.append(&2, Nat, xr, ys), c)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(h)

# an element of xs is an element of xs ++ ys
def ps.elem_app_l(xs: List<&2, Nat>, +ys: List<&2, Nat>, +c: Nat, h: {Tl.elem(xs, c) == True{} : Bool}) -> {Tl.elem(List.append(&2, Nat, xs, ys), c) == True{} : Bool}:
  match xs:
    case Nil{}:
      shell.ps.absurdF({Tl.elem(ys, c) == True{} : Bool}, h)
    case +x <> +xr:
      ps.app_head(Nat.is_eq(x, c), xr, ys, c, h, k => ps.elem_app_l(xr, ys, c, k))

def ps.step_holds_every_part(+pre: List<&2, List<&2, Nat>>, +p: List<&2, Nat>, +post: List<&2, List<&2, Nat>>, +c: Nat, has: {Tl.elem(p, c) == True{} : Bool}) -> {Tl.elem(Tl.join(List.append(&2, List<&2, Nat>, pre, p <> post)), c) == True{} : Bool}:
  match pre:
    case Nil{}:
      ps.elem_app_l(p, Tl.join(post), c, has)
    case q <> pr:
      ps.elem_app_r(q, Tl.join(List.append(&2, List<&2, Nat>, pr, p <> post)), c, ps.step_holds_every_part(pr, p, post, c, has))

# The secret effect
# -----------------

def shell.ps.or_assoc(b: Bool, +p: Bool, +q: Bool) -> {Bool.or(b, Bool.or(p, q)) == Bool.or(Bool.or(b, p), q) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# c is in xs ++ ys exactly when it is in xs or in ys
def ps.elem_app(xs: List<&2, Nat>, +ys: List<&2, Nat>, +c: Nat) -> {Tl.elem(List.append(&2, Nat, xs, ys), c) == Bool.or(Tl.elem(xs, c), Tl.elem(ys, c)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +xr:
      %Equal.sym(Bool, Tl.elem(List.append(&2, Nat, xr, ys), c), Bool.or(Tl.elem(xr, c), Tl.elem(ys, c)), ps.elem_app(xr, ys, c)) : {Bool.or(Nat.is_eq(x, c), _) == Bool.or(Bool.or(Nat.is_eq(x, c), Tl.elem(xr, c)), Tl.elem(ys, c)) : Bool}
      shell.ps.or_assoc(Nat.is_eq(x, c), Tl.elem(xr, c), Tl.elem(ys, c))

# the head c of the codes, with test b = Nat.is_eq(c, 6n): a dropped 6
# leaves the rest, a kept code is not 6
def ps.plain_head(b: Bool, +c: Nat, +acc: List<&2, Nat>, e: {Nat.is_eq(c, 6n) == b : Bool}, ih: {Tl.elem(acc, 6n) == False{} : Bool}) -> {Tl.elem(Tl.plain.add(b, c, acc), 6n) == False{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Bool, Nat.is_eq(c, 6n), False{}, e) : {Bool.or(_, Tl.elem(acc, 6n)) == False{} : Bool}
      ih

# the plain codes hold no secret
def ps.plain_no_secret(cs: List<&2, Nat>) -> {Tl.elem(Tl.plain(cs), 6n) == False{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +rest:
      ps.plain_head(Nat.is_eq(c, 6n), c, Tl.plain(rest), {==}, ps.plain_no_secret(rest))

# a part has the secret effect exactly when it names a secret path
def ps.part_secret(p: Tl.Part) -> {Tl.elem(Tl.part.effs(p), 6n) == Tl.Part.secret(p) : Bool}:
  match p:
    case Tl.Part{o, s}:
      match s:
        case True{}:
          {==}
        case False{}:
          ps.plain_no_secret(o)

# a step has the secret effect exactly when one of its parts names a
# secret path
def ps.secret_iff(xs: List<&2, Tl.Part>) -> {Tl.elem(Tl.join(Tl.parts.effs(xs)), 6n) == Tl.parts.secret(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +p <> +rest:
      %Equal.sym(Bool, Tl.elem(List.append(&2, Nat, Tl.part.effs(p), Tl.join(Tl.parts.effs(rest))), 6n), Bool.or(Tl.elem(Tl.part.effs(p), 6n), Tl.elem(Tl.join(Tl.parts.effs(rest)), 6n)), ps.elem_app(Tl.part.effs(p), Tl.join(Tl.parts.effs(rest)), 6n)) : {_ == Bool.or(Tl.Part.secret(p), Tl.parts.secret(rest)) : Bool}
      %Equal.sym(Bool, Tl.elem(Tl.part.effs(p), 6n), Tl.Part.secret(p), ps.part_secret(p)) : {Bool.or(_, Tl.elem(Tl.join(Tl.parts.effs(rest)), 6n)) == Bool.or(Tl.Part.secret(p), Tl.parts.secret(rest)) : Bool}
      %Equal.sym(Bool, Tl.elem(Tl.join(Tl.parts.effs(rest)), 6n), Tl.parts.secret(rest), ps.secret_iff(rest)) : {Bool.or(Tl.Part.secret(p), _) == Bool.or(Tl.Part.secret(p), Tl.parts.secret(rest)) : Bool}
      {==}

# Within the auto set
# -------------------

# the head x of effs, with test b = Nat.is_eq(x, c): when x is c, x is not
# within; else c is in the rest, which is then not within
def ps.within_head(+x: Nat, +rest: List<&2, Nat>, +auto: List<&2, Nat>, +c: Nat, b: Bool, e: {Nat.is_eq(x, c) == b : Bool}, has: {Bool.or(b, Tl.elem(rest, c)) == True{} : Bool}, out: {Bool.and(Tl.grantable(c), Tl.elem(auto, c)) == False{} : Bool}, ih: {Tl.elem(rest, c) == True{} : Bool} -> {Tl.within(rest, auto) == False{} : Bool}) -> {Bool.and(Bool.and(Tl.grantable(x), Tl.elem(auto, x)), Tl.within(rest, auto)) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, x, c, shell.ps.eq_of_is_eq(x, c, e)) : {Bool.and(Bool.and(Tl.grantable(_), Tl.elem(auto, _)), Tl.within(rest, auto)) == False{} : Bool}
      %Equal.sym(Bool, Bool.and(Tl.grantable(c), Tl.elem(auto, c)), False{}, out) : {Bool.and(_, Tl.within(rest, auto)) == False{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, Tl.within(rest, auto), False{}, ih(has)) : {Bool.and(Bool.and(Tl.grantable(x), Tl.elem(auto, x)), _) == False{} : Bool}
      shell.ps.and_f(Bool.and(Tl.grantable(x), Tl.elem(auto, x)))

# effects with one effect c that is not grantable or not in auto are not
# within auto
def ps.within_out(effs: List<&2, Nat>, +auto: List<&2, Nat>, +c: Nat, has: {Tl.elem(effs, c) == True{} : Bool}, +out: {Bool.and(Tl.grantable(c), Tl.elem(auto, c)) == False{} : Bool}) -> {Tl.within(effs, auto) == False{} : Bool}:
  match effs:
    case Nil{}:
      shell.ps.absurdF({Tl.within(Nil{}, auto) == False{} : Bool}, has)
    case +x <> +rest:
      ps.within_head(x, rest, auto, c, Nat.is_eq(x, c), {==}, has, out, k => ps.within_out(rest, auto, c, k, out))

def ps.auto_needs_every_effect(+s: Tl.Step, +auto: List<&2, Nat>, +c: Nat, has: {Tl.elem(Tl.Step.effs(s), c) == True{} : Bool}, out: {Bool.and(Tl.grantable(c), Tl.elem(auto, c)) == False{} : Bool}) -> {Tl.auto.at(auto, s) == False{} : Bool}:
  ps.within_out(Tl.Step.effs(s), auto, c, has, out)

def approvals.pa.absurdT(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : LLogicLogic.approvals.pa.BD(_, Unit, A)
  Unit{}

# it lets the step run when the guarded code is absent
def pa.guard_false(b: Bool, h: {b == False{} : Bool}) -> {Am.guard(b) == Am.Runs{} : Am.Fate}:
  match b:
    case True{}:
      approvals.pa.absurdT({Am.guard(True{}) == Am.Runs{} : Am.Fate}, h)
    case False{}:
      {==}

# a step not within the auto set goes its route
def pa.gate_routed(w: Bool, +es: List<&2, Nat>, +ds: List<&2, Am.Desk>, h: {w == False{} : Bool}) -> {Am.gate.by(w, es, ds) == Am.routed(es, Am.route(ds)) : Am.Gated}:
  match w:
    case True{}:
      approvals.pa.absurdT({Am.gate.by(True{}, es, ds) == Am.routed(es, Am.route(ds)) : Am.Gated}, h)
    case False{}:
      {==}

# the gateway's outcome as the gate gives it
def pa.phone_gate(+auto: List<&2, Nat>, +es: List<&2, Nat>, +above: List<&2, Am.Desk>, -f: Am.Fate, w: {Tl.within(es, auto) == False{} : Bool}, r: {Am.rule(es) == f : Am.Fate}) -> {Am.gate(auto, es, Am.Phone{} <> above) == Am.Routed{Am.Out{Nil{}, Am.Ruled{0n}}, f} : Am.Gated}:
  Equal.trans(Am.Gated, Am.gate(auto, es, Am.Phone{} <> above), Am.Routed{Am.Out{Nil{}, Am.Ruled{0n}}, Am.rule(es)}, Am.Routed{Am.Out{Nil{}, Am.Ruled{0n}}, f}, pa.gate_routed(Tl.within(es, auto), es, Am.Phone{} <> above, w), Equal.cong(Am.Fate, Am.Gated, x => Am.Routed{Am.Out{Nil{}, Am.Ruled{0n}}, x}, Am.rule(es), f, r))
