# proof_shell: the G2 laws (docs/tools.md S7, shell classification) of
# the gate model in bend/tools.bend part 4. An effect of a part is in the
# join of the parts (`ps.elem_app_l`, `ps.elem_app_r`, by induction on the
# parts before it). A step with one effect that is not within the auto set
# is not within it (`ps.within_out`, by induction on its effects, with the
# head test as a parameter). Codes 4, 5 and 6 are not grantable
# (`ps.big`, four levels of literal match). The gate reads `within` of
# the head step: a rewrite with it runs the step free, or with no answer
# denies it.

import Base
import ./tools.bend as Tl

# Logic
# -----

def ps.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def ps.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : ps.BD(_, A, Unit)
  Unit{}

def ps.and_f(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def ps.or_tr(a: Bool, +b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

def ps.eq_of_is_eq(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      ps.absurdF({0n == 1n+bp : Nat}, h)
    case 1n+ap 0n:
      ps.absurdF({1n+ap == 0n : Nat}, h)
    case 1n+ap 1n+bp:
      %ps.eq_of_is_eq(ap, bp, h) : {1n+ap == 1n+_ : Nat}
      {==}

# A step made of parts
# --------------------

# an element of ys is an element of xs ++ ys
def ps.elem_app_r(xs: List<&2, Nat>, +ys: List<&2, Nat>, +c: Nat, h: {Tl.elem(ys, c) == True{} : Bool}) -> {Tl.elem(List.append(&2, Nat, xs, ys), c) == True{} : Bool}:
  match xs:
    case Nil{}:
      h
    case +x <> +xr:
      ps.or_tr(Nat.is_eq(x, c), Tl.elem(List.append(&2, Nat, xr, ys), c), ps.elem_app_r(xr, ys, c, h))

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
      ps.absurdF({Tl.elem(ys, c) == True{} : Bool}, h)
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

def ps.or_assoc(b: Bool, +p: Bool, +q: Bool) -> {Bool.or(b, Bool.or(p, q)) == Bool.or(Bool.or(b, p), q) : Bool}:
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
      ps.or_assoc(Nat.is_eq(x, c), Tl.elem(xr, c), Tl.elem(ys, c))

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

def ps.secret_needs_a_secret_path(+xs: List<&2, Tl.Part>, has: {Tl.elem(Tl.join(Tl.parts.effs(xs)), 6n) == True{} : Bool}) -> {Tl.parts.secret(xs) == True{} : Bool}:
  Equal.trans(Bool, Tl.parts.secret(xs), Tl.elem(Tl.join(Tl.parts.effs(xs)), 6n), True{}, Equal.sym(Bool, Tl.elem(Tl.join(Tl.parts.effs(xs)), 6n), Tl.parts.secret(xs), ps.secret_iff(xs)), has)

# a part that names a secret path makes some part of the step name one
def ps.some_secret(+pre: List<&2, Tl.Part>, +p: Tl.Part, +post: List<&2, Tl.Part>, named: {Tl.Part.secret(p) == True{} : Bool}) -> {Tl.parts.secret(List.append(&2, Tl.Part, pre, p <> post)) == True{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, Tl.Part.secret(p), True{}, named) : {Bool.or(_, Tl.parts.secret(post)) == True{} : Bool}
      {==}
    case q <> pr:
      ps.or_tr(Tl.Part.secret(q), Tl.parts.secret(List.append(&2, Tl.Part, pr, p <> post)), ps.some_secret(pr, p, post, named))

def ps.secret_path_gives_secret(+pre: List<&2, Tl.Part>, +p: Tl.Part, +post: List<&2, Tl.Part>, named: {Tl.Part.secret(p) == True{} : Bool}) -> {Tl.elem(Tl.join(Tl.parts.effs(List.append(&2, Tl.Part, pre, p <> post))), 6n) == True{} : Bool}:
  +all = List.append(&2, Tl.Part, pre, p <> post)
  Equal.trans(Bool, Tl.elem(Tl.join(Tl.parts.effs(all)), 6n), Tl.parts.secret(all), True{}, ps.secret_iff(all), ps.some_secret(pre, p, post, named))

# Within the auto set
# -------------------

# the head x of effs, with test b = Nat.is_eq(x, c): when x is c, x is not
# within; else c is in the rest, which is then not within
def ps.within_head(+x: Nat, +rest: List<&2, Nat>, +auto: List<&2, Nat>, +c: Nat, b: Bool, e: {Nat.is_eq(x, c) == b : Bool}, has: {Bool.or(b, Tl.elem(rest, c)) == True{} : Bool}, out: {Bool.and(Tl.grantable(c), Tl.elem(auto, c)) == False{} : Bool}, ih: {Tl.elem(rest, c) == True{} : Bool} -> {Tl.within(rest, auto) == False{} : Bool}) -> {Bool.and(Bool.and(Tl.grantable(x), Tl.elem(auto, x)), Tl.within(rest, auto)) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, x, c, ps.eq_of_is_eq(x, c, e)) : {Bool.and(Bool.and(Tl.grantable(_), Tl.elem(auto, _)), Tl.within(rest, auto)) == False{} : Bool}
      %Equal.sym(Bool, Bool.and(Tl.grantable(c), Tl.elem(auto, c)), False{}, out) : {Bool.and(_, Tl.within(rest, auto)) == False{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, Tl.within(rest, auto), False{}, ih(has)) : {Bool.and(Bool.and(Tl.grantable(x), Tl.elem(auto, x)), _) == False{} : Bool}
      ps.and_f(Bool.and(Tl.grantable(x), Tl.elem(auto, x)))

# effects with one effect c that is not grantable or not in auto are not
# within auto
def ps.within_out(effs: List<&2, Nat>, +auto: List<&2, Nat>, +c: Nat, has: {Tl.elem(effs, c) == True{} : Bool}, +out: {Bool.and(Tl.grantable(c), Tl.elem(auto, c)) == False{} : Bool}) -> {Tl.within(effs, auto) == False{} : Bool}:
  match effs:
    case Nil{}:
      ps.absurdF({Tl.within(Nil{}, auto) == False{} : Bool}, has)
    case +x <> +rest:
      ps.within_head(x, rest, auto, c, Nat.is_eq(x, c), {==}, has, out, k => ps.within_out(rest, auto, c, k, out))

def ps.auto_needs_every_effect(+s: Tl.Step, +auto: List<&2, Nat>, +c: Nat, has: {Tl.elem(Tl.Step.effs(s), c) == True{} : Bool}, out: {Bool.and(Tl.grantable(c), Tl.elem(auto, c)) == False{} : Bool}) -> {Tl.auto.at(auto, s) == False{} : Bool}:
  ps.within_out(Tl.Step.effs(s), auto, c, has, out)

# codes 4 and above are not grantable
def ps.big(c: Nat, h: {Nat.is_le(4n, c) == True{} : Bool}) -> {Tl.grantable(c) == False{} : Bool}:
  match c:
    case 0n:
      ps.absurdF({Tl.grantable(0n) == False{} : Bool}, h)
    case 1n+a:
      match a:
        case 0n:
          ps.absurdF({Tl.grantable(1n) == False{} : Bool}, h)
        case 1n+b:
          match b:
            case 0n:
              ps.absurdF({Tl.grantable(2n) == False{} : Bool}, h)
            case 1n+d:
              match d:
                case 0n:
                  ps.absurdF({Tl.grantable(3n) == False{} : Bool}, h)
                case 1n+e:
                  {==}

# a code of 4 and above is not within any auto set
def ps.out_big(+c: Nat, +auto: List<&2, Nat>, h: {Nat.is_le(4n, c) == True{} : Bool}) -> {Bool.and(Tl.grantable(c), Tl.elem(auto, c)) == False{} : Bool}:
  %Equal.sym(Bool, Tl.grantable(c), False{}, ps.big(c, h)) : {Bool.and(_, Tl.elem(auto, c)) == False{} : Bool}
  {==}

def ps.auto_never_sensitive(+s: Tl.Step, +auto: List<&2, Nat>, +c: Nat, has: {Tl.elem(Tl.Step.effs(s), c) == True{} : Bool}, held: {Nat.is_le(4n, c) == True{} : Bool}) -> {Tl.auto.at(auto, s) == False{} : Bool}:
  ps.auto_needs_every_effect(s, auto, c, has, ps.out_big(c, auto, held))

def ps.composed_needs_every_part(+i: Nat, +pre: List<&2, List<&2, Nat>>, +p: List<&2, Nat>, +post: List<&2, List<&2, Nat>>, +auto: List<&2, Nat>, +c: Nat, has: {Tl.elem(p, c) == True{} : Bool}, out: {Bool.and(Tl.grantable(c), Tl.elem(auto, c)) == False{} : Bool}) -> {Tl.auto.at(auto, Tl.Step{i, Tl.join(List.append(&2, List<&2, Nat>, pre, p <> post))}) == False{} : Bool}:
  ps.within_out(Tl.join(List.append(&2, List<&2, Nat>, pre, p <> post)), auto, c, ps.step_holds_every_part(pre, p, post, c, has), out)

# The gate reads within
# ---------------------

def ps.auto_runs_within(+s: Tl.Step, +post: List<&2, Tl.Step>, +auto: List<&2, Nat>, ans: List<&2, Bool>, w: {Tl.within(Tl.Step.effs(s), auto) == True{} : Bool}) -> {Tl.exec(s <> post, auto, ans) == Tl.ran.add(s, Tl.exec(post, auto, ans)) : Tl.Ran}:
  %Equal.sym(Bool, Tl.within(Tl.Step.effs(s), auto), True{}, w) : {Tl.exec.go(s <> post, auto, _, ans) == Tl.ran.add(s, Tl.exec(post, auto, ans)) : Tl.Ran}
  {==}

# a denied step runs nothing and names itself
def ps.gate_den(s: Tl.Step, r: Tl.Ran) -> {Tl.gate(False{}, s, r) == Tl.Ran{Nil{}, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}:
  match s:
    case Tl.Step{i, e}:
      {==}

def ps.held_needs_a_yes(+s: Tl.Step, +post: List<&2, Tl.Step>, +auto: List<&2, Nat>, w: {Tl.within(Tl.Step.effs(s), auto) == False{} : Bool}) -> {Tl.exec(s <> post, auto, Nil{}) == Tl.Ran{Nil{}, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}:
  %Equal.sym(Bool, Tl.within(Tl.Step.effs(s), auto), False{}, w) : {Tl.exec.go(s <> post, auto, _, Nil{}) == Tl.Ran{Nil{}, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}
  ps.gate_den(s, Tl.Ran{Nil{}, Tl.Finished{}})
