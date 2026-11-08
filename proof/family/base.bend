# eukhe: lemmas of the decision proofs of area family: the code's steps
# are the spec's (fp.*), what an admitted verdict says (fd.*), and the
# spec's batch arithmetic (fb.*)

import Base
import ../../bend/family.bend as F
import ../../spec/rlm/family.bend as FamSpec
import ../../laws/family.bend as Family
import ../base/staging.bend as LStg

# The code's steps are the spec's
# -------------------------------

def fp.reason(p: Bool, i: Bool, t: Bool, u: Bool, +k: Nat, x: Maybe<&2, Nat>) -> {F.bad.at(F.reason.of(p, i, t, u), k, x) == FamSpec.first_bad.of(Bool.or(p, Bool.or(i, Bool.or(t, Bool.or(u, False{})))), k, x) : Maybe<&2, Nat>}:
  match p:
    case True{}:
      {==}
    case False{}:
      match i:
        case True{}:
          {==}
        case False{}:
          match t:
            case True{}:
              {==}
            case False{}:
              match u:
                case True{}:
                  {==}
                case False{}:
                  {==}

# the first why that is no reason is the spec's
def fp.bad(ws: List<&2, String>, +k: Nat) -> {F.bad(ws, k) == FamSpec.first_bad(ws, k) : Maybe<&2, Nat>}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      %fp.bad(t, 1n+k) : {F.bad.at(F.reason(w), k, F.bad(t, 1n+k)) == FamSpec.first_bad.of(FamSpec.allowed(w), k, _) : Maybe<&2, Nat>}
      fp.reason(String.eq(w, "parallel"), String.eq(w, "isolate"), String.eq(w, "tools"), String.eq(w, "user"), k, F.bad(t, 1n+k))

def fp.capb(b: Bool, +c: Nat, +d: Nat) -> {F.decide.cap(Bool.not(b), c, d) == FamSpec.verdict.cap(Bool.or(False{}, b), c, d) : F.Verdict}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def fp.cap(c: Nat, +x: Nat, +d: Nat) -> {F.decide.cap(F.full.of(c, x), c, d) == FamSpec.verdict.cap(Bool.or(Nat.is_eq(c, 0n), Nat.is_le(x, c)), c, d) : F.Verdict}:
  match c:
    case 0n:
      {==}
    case 1n++k:
      fp.capb(Nat.is_le(x, 1n+k), 1n+k, d)

def fp.deep(x: Bool, +d: Nat, +r: Nat, +c: Nat, +n: Nat) -> {F.decide.depth(x, d, r, c, n) == FamSpec.verdict.deep(x, d, r, c, n) : F.Verdict}:
  match x:
    case True{}:
      {==}
    case False{}:
      fp.cap(c, Nat.add(r, n), d)

def fp.why(b: Maybe<&2, Nat>, +d: Nat, +m: Nat, +r: Nat, +c: Nat, +n: Nat) -> {F.decide.why(b, d, m, r, c, n) == FamSpec.verdict.of(b, d, m, r, c, n) : F.Verdict}:
  match b:
    case Some{i}:
      {==}
    case None{}:
      fp.deep(Nat.is_le(m, d), d, r, c, n)

# What a verdict says
# -------------------

def fd.If(v: F.Verdict, G: Type) -> Type:
  match v:
    case F.Admit{k}:
      G
    case F.Refuse{f}:
      Unit

def fd.depth_of(v: F.Verdict) -> Nat:
  match v:
    case F.Admit{k}:
      k
    case F.Refuse{f}:
      0n

# a refusal is no admission
def fd.absurd(-G: Type, -f: F.Refusal, -k: Nat, e: {F.Refuse{f} == F.Admit{k} : F.Verdict}) -> G:
  %e : fd.If(_, G)
  Unit{}

def fd.le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a caller below the bound has a child within it
def fd.below(m: Nat, d: Nat, h: {Nat.is_le(m, d) == False{} : Bool}) -> {Nat.is_le(1n+d, m) == True{} : Bool}:
  match m d:
    case 0n 0n:
      LStg.stg.absurd({Nat.is_le(1n, 0n) == True{} : Bool}, h)
    case 0n 1n+q:
      LStg.stg.absurd({Nat.is_le(2n+q, 0n) == True{} : Bool}, h)
    case 1n+p 0n:
      fd.le_zero(p)
    case 1n+p 1n+q:
      fd.below(p, q, h)

def fd.cap(y: Bool, +d: Nat, +m: Nat, +c: Nat, +k: Nat, h: {Nat.is_le(m, d) == False{} : Bool}, e: {FamSpec.verdict.cap(y, c, d) == F.Admit{k} : F.Verdict}) -> {k == 1n+d : Nat} & {Nat.is_le(k, m) == True{} : Bool}:
  match y:
    case True{}:
      +ek = Equal.cong(F.Verdict, Nat, v => fd.depth_of(v), F.Admit{1n+d}, F.Admit{k}, e)
      +b = fd.below(m, d, h)
      (Equal.sym(Nat, 1n+d, k, ek), Equal.trans(Bool, Nat.is_le(k, m), Nat.is_le(1n+d, m), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(z, m), k, 1n+d, Equal.sym(Nat, 1n+d, k, ek)), b))
    case False{}:
      fd.absurd({k == 1n+d : Nat} & {Nat.is_le(k, m) == True{} : Bool}, F.FamilyFull{c}, k, e)

def fd.deep(x: Bool, +d: Nat, +m: Nat, +r: Nat, +c: Nat, +n: Nat, +k: Nat, h: {Nat.is_le(m, d) == x : Bool}, e: {FamSpec.verdict.deep(x, d, r, c, n) == F.Admit{k} : F.Verdict}) -> {k == 1n+d : Nat} & {Nat.is_le(k, m) == True{} : Bool}:
  match x:
    case True{}:
      fd.absurd({k == 1n+d : Nat} & {Nat.is_le(k, m) == True{} : Bool}, F.DepthLimit{}, k, e)
    case False{}:
      fd.cap(FamSpec.cap_ok(r, c, n), d, m, c, k, h, e)

# an admitted verdict of the spec: the child one level deeper, within the bound
def fd.of(b: Maybe<&2, Nat>, +d: Nat, +m: Nat, +r: Nat, +c: Nat, +n: Nat, +k: Nat, e: {FamSpec.verdict.of(b, d, m, r, c, n) == F.Admit{k} : F.Verdict}) -> {k == 1n+d : Nat} & {Nat.is_le(k, m) == True{} : Bool}:
  match b:
    case Some{i}:
      fd.absurd({k == 1n+d : Nat} & {Nat.is_le(k, m) == True{} : Bool}, F.NoReason{i}, k, e)
    case None{}:
      fd.deep(Nat.is_le(m, d), d, m, r, c, n, k, {==}, e)

# Admission in the spec
# ---------------------

# None and x; Some: false
def fa.nz(b: Maybe<&2, Nat>, x: Bool) -> Bool:
  match b:
    case None{}:
      x
    case Some{i}:
      False{}

def fa.cap(y: Bool, +c: Nat, +d: Nat) -> {Family.fam_admitted(FamSpec.verdict.cap(y, c, d)) == y : Bool}:
  match y:
    case True{}:
      {==}
    case False{}:
      {==}

def fa.deep(x: Bool, +d: Nat, +r: Nat, +c: Nat, +n: Nat) -> {Family.fam_admitted(FamSpec.verdict.deep(x, d, r, c, n)) == Bool.and(Bool.not(x), FamSpec.cap_ok(r, c, n)) : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      fa.cap(FamSpec.cap_ok(r, c, n), c, d)

def fa.of(b: Maybe<&2, Nat>, +d: Nat, +m: Nat, +r: Nat, +c: Nat, +n: Nat) -> {Family.fam_admitted(FamSpec.verdict.of(b, d, m, r, c, n)) == fa.nz(b, Bool.and(Bool.not(FamSpec.deep(d, m)), FamSpec.cap_ok(r, c, n))) : Bool}:
  match b:
    case Some{i}:
      {==}
    case None{}:
      fa.deep(FamSpec.deep(d, m), d, r, c, n)

def fa.step(a: Bool, +k: Nat, rest: Maybe<&2, Nat>, -al: Bool, +x: Bool, ih: {fa.nz(rest, x) == Bool.and(al, x) : Bool}) -> {fa.nz(FamSpec.first_bad.of(a, k, rest), x) == Bool.and(Bool.and(a, al), x) : Bool}:
  match a:
    case True{}:
      ih
    case False{}:
      {==}

# no why is bad exactly when all are reasons
def fa.bad(ws: List<&2, String>, +k: Nat, +x: Bool) -> {fa.nz(FamSpec.first_bad(ws, k), x) == Bool.and(FamSpec.all_ok(ws), x) : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      fa.step(FamSpec.allowed(w), k, FamSpec.first_bad(t, 1n+k), FamSpec.all_ok(t), x, fa.bad(t, 1n+k, x))

def fa.assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# the spec's verdict admits exactly when the spec admits
def fa.verdict(+d: Nat, +m: Nat, +r: Nat, +c: Nat, +ws: List<&2, String>) -> {Family.fam_admitted(FamSpec.verdict(d, m, r, c, ws)) == FamSpec.admits(d, m, r, c, ws) : Bool}:
  Equal.trans(Bool, Family.fam_admitted(FamSpec.verdict(d, m, r, c, ws)), fa.nz(FamSpec.first_bad(ws, 0n), Bool.and(Bool.not(FamSpec.deep(d, m)), FamSpec.cap_ok(r, c, List.length(&2, String, ws)))), FamSpec.admits(d, m, r, c, ws), fa.of(FamSpec.first_bad(ws, 0n), d, m, r, c, List.length(&2, String, ws)), fa.bad(ws, 0n, Bool.and(Bool.not(FamSpec.deep(d, m)), FamSpec.cap_ok(r, c, List.length(&2, String, ws)))))

# The batch arithmetic
# --------------------

def fb.all(xs: List<&2, String>, +ys: List<&2, String>) -> {FamSpec.all_ok(List.append(&2, String, xs, ys)) == Bool.and(FamSpec.all_ok(xs), FamSpec.all_ok(ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+w, +t}:
      %Equal.sym(Bool, FamSpec.all_ok(List.append(&2, String, t, ys)), Bool.and(FamSpec.all_ok(t), FamSpec.all_ok(ys)), fb.all(t, ys)) : {Bool.and(FamSpec.allowed(w), _) == Bool.and(Bool.and(FamSpec.allowed(w), FamSpec.all_ok(t)), FamSpec.all_ok(ys)) : Bool}
      Equal.sym(Bool, Bool.and(Bool.and(FamSpec.allowed(w), FamSpec.all_ok(t)), FamSpec.all_ok(ys)), Bool.and(FamSpec.allowed(w), Bool.and(FamSpec.all_ok(t), FamSpec.all_ok(ys))), fa.assoc(FamSpec.allowed(w), FamSpec.all_ok(t), FamSpec.all_ok(ys)))

def fb.len(xs: List<&2, String>, +ys: List<&2, String>) -> {List.length(&2, String, List.append(&2, String, xs, ys)) == Nat.add(List.length(&2, String, xs), List.length(&2, String, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{w, +t}:
      Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, String, List.append(&2, String, t, ys)), Nat.add(List.length(&2, String, t), List.length(&2, String, ys)), fb.len(t, ys))

def fb.add_assoc(r: Nat, -a: Nat, -b: Nat) -> {Nat.add(r, Nat.add(a, b)) == Nat.add(Nat.add(r, a), b) : Nat}:
  match r:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, Nat.add(a, b)), Nat.add(Nat.add(p, a), b), fb.add_assoc(p, a, b))

# x is at most c when x plus b is
def fb.mono(x: Nat, c: Nat, +b: Nat, h: {Nat.is_le(Nat.add(x, b), c) == True{} : Bool}) -> {Nat.is_le(x, c) == True{} : Bool}:
  match x c:
    case 0n _:
      fd.le_zero(c)
    case 1n+p 0n:
      LStg.stg.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))
    case 1n+p 1n+q:
      fb.mono(p, q, b, h)

def fb.and_t(p: Bool, h: {p == True{} : Bool}) -> {Bool.and(p, True{}) == True{} : Bool}:
  match p:
    case True{}:
      {==}
    case False{}:
      LStg.stg.absurd({Bool.and(False{}, True{}) == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))

def fb.and_f(p: Bool) -> {Bool.and(p, False{}) == False{} : Bool}:
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

def fb.and_mono(p: Bool, q: Bool) -> ({q == True{} : Bool} -> {p == True{} : Bool}) -> {Bool.and(p, q) == q : Bool}:
  match q:
    case True{}:
      f => fb.and_t(p, f({==}))
    case False{}:
      f => fb.and_f(p)

def fb.le_split(+x: Nat, +b: Nat, +c: Nat) -> {Nat.is_le(Nat.add(x, b), c) == Bool.and(Nat.is_le(x, c), Nat.is_le(Nat.add(x, b), c)) : Bool}:
  Equal.sym(Bool, Bool.and(Nat.is_le(x, c), Nat.is_le(Nat.add(x, b), c)), Nat.is_le(Nat.add(x, b), c), fb.and_mono(Nat.is_le(x, c), Nat.is_le(Nat.add(x, b), c))(h => fb.mono(x, c, b, h)))

# a cap fits a + b exactly when it fits a and then b
def fb.cap(+r: Nat, c: Nat, +a: Nat, +b: Nat) -> {FamSpec.cap_ok(r, c, Nat.add(a, b)) == Bool.and(FamSpec.cap_ok(r, c, a), FamSpec.cap_ok(Nat.add(r, a), c, b)) : Bool}:
  match c:
    case 0n:
      {==}
    case 1n++k:
      %Equal.sym(Nat, Nat.add(r, Nat.add(a, b)), Nat.add(Nat.add(r, a), b), fb.add_assoc(r, a, b)) : {Nat.is_le(_, 1n+k) == Bool.and(Nat.is_le(Nat.add(r, a), 1n+k), Nat.is_le(Nat.add(Nat.add(r, a), b), 1n+k)) : Bool}
      fb.le_split(Nat.add(r, a), b, 1n+k)

# the batch's and the parts' admissions, with the depth shared
def fb.bool5(a1: Bool, a2: Bool, n: Bool, c1: Bool, c2: Bool) -> {Bool.and(Bool.and(a1, a2), Bool.and(n, Bool.and(c1, c2))) == Bool.and(Bool.and(a1, Bool.and(n, c1)), Bool.and(a2, Bool.and(n, c2))) : Bool}:
  match a1:
    case True{}:
      match a2:
        case True{}:
          match n:
            case True{}:
              match c1:
                case True{}:
                  match c2:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match c2:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case False{}:
              match c1:
                case True{}:
                  match c2:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match c2:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
        case False{}:
          match n:
            case True{}:
              match c1:
                case True{}:
                  match c2:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match c2:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case False{}:
              match c1:
                case True{}:
                  match c2:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match c2:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
    case False{}:
      match a2:
        case True{}:
          match n:
            case True{}:
              match c1:
                case True{}:
                  match c2:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match c2:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case False{}:
              match c1:
                case True{}:
                  match c2:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match c2:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
        case False{}:
          match n:
            case True{}:
              match c1:
                case True{}:
                  match c2:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match c2:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
            case False{}:
              match c1:
                case True{}:
                  match c2:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  match c2:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
