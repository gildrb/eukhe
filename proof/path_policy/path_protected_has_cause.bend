# eukhe: the proof of LAW path_protected_has_cause
#
# PROOF: the class is the model's class of the real path (pcc.cls_eq); it
# is Protected only when the model's protected test holds (phc.found):
# some rule covers the path (phc.cover splits the rules at it): a Tree
# rule's path is a suffix of the path (pin.usplit), a Dir rule's directory
# is the path or its parent (phc.dir), a Named rule's name is among the
# names below the deepest root (phc.elem, pc.below_root); or the path is a
# strict ancestor of a rule's entry (phc.entry) or of a secret entry
# (phc.secret): the entry is the path with one name or more below it
# (phc.strict). Each case is one the premises refute.

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy/policy.bend as PathPolicy
import ./base.bend as LA
import ./base/lemmas.bend as LAE
import ./path_inside_needs_root.bend as PPathInsideNeedsRoot
import ./base/root.bend as LAR
import ./base/class.bend as LAC

# A at Protected, Unit elsewhere: refutes {c == Protected} for c not
# Protected
def phc.PM(c: Pp.Cls, A: Type) -> Type:
  match c:
    case Pp.Inside{}:
      Unit
    case Pp.Outside{}:
      Unit
    case Pp.Protected{}:
      A
    case Pp.Secret{}:
      Unit

# the class picked is Protected only when the protected test holds
def phc.found(s: Bool, p: Bool, i: Bool, l: Bool, h: {Pp.demote(Pp.cls.pick(s, p, i), l) == Pp.Protected{} : Pp.Cls}) -> {p == True{} : Bool}:
  match s:
    case True{}:
      %h : phc.PM(_, {p == True{} : Bool})
      Unit{}
    case False{}:
      match p:
        case True{}:
          {==}
        case False{}:
          match i:
            case True{}:
              match l:
                case True{}:
                  %h : phc.PM(_, {False{} == True{} : Bool})
                  Unit{}
                case False{}:
                  %h : phc.PM(_, {False{} == True{} : Bool})
                  Unit{}
            case False{}:
              %h : phc.PM(_, {False{} == True{} : Bool})
              Unit{}

def phc.or_cases(-G: Type, a: Bool, -b: Bool, h: {Bool.or(a, b) == True{} : Bool}, ka: {a == True{} : Bool} -> G, kb: {b == True{} : Bool} -> G) -> G:
  match a:
    case True{}:
      ka({==})
    case False{}:
      kb(h)

def phc.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def phc.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LA.pp.absurdF({b == True{} : Bool}, h)

# Witnesses
# ---------

# p is the path at or its parent: at is k ++ p with at most one name k
def phc.DirW(at: List<&2, Nat>, p: List<&2, Nat>) -> Type:
  &k: List<&2, Nat> -> ({at == List.append(&2, Nat, k, p) : List<&2, Nat>} & {Nat.is_lt(List.length(&2, Nat, k), 2n) == True{} : Bool})

# n is among xs: xs is a ++ n :: b
def phc.ElemW(xs: List<&2, Nat>, n: Nat) -> Type:
  &a: List<&2, Nat> -> &b: List<&2, Nat> -> {xs == List.append(&2, Nat, a, n <> b) : List<&2, Nat>}

# a rule r of ru covers at: ru is ru1 ++ r :: ru2
def phc.CoverW(ru: List<&2, Pp.Rule>, at: List<&2, Nat>, low: List<&2, Nat>) -> Type:
  &ru1: List<&2, Pp.Rule> -> &r: Pp.Rule -> &ru2: List<&2, Pp.Rule> -> ({ru == List.append(&2, Pp.Rule, ru1, r <> ru2) : List<&2, Pp.Rule>} & {Pp.covers(r, at, low) == True{} : Bool})

# p is the path at with one name m or more below it
def phc.StrictW(at: List<&2, Nat>, p: List<&2, Nat>) -> Type:
  &m: Nat -> &k: List<&2, Nat> -> {p == m <> List.append(&2, Nat, k, at) : List<&2, Nat>}

# a Tree or Dir rule of ru has its entry strictly below at
def phc.EntryW(ru: List<&2, Pp.Rule>, at: List<&2, Nat>) -> Type:
  &ru1: List<&2, Pp.Rule> -> &t: Bool -> &m: Nat -> &k: List<&2, Nat> -> &ru2: List<&2, Pp.Rule> -> {ru == List.append(&2, Pp.Rule, ru1, PathPolicy.pp_entry_rule(t, m <> List.append(&2, Nat, k, at)) <> ru2) : List<&2, Pp.Rule>}

# a secret entry of se is strictly below at
def phc.SecretW(se: List<&2, List<&2, Nat>>, at: List<&2, Nat>) -> Type:
  &se1: List<&2, List<&2, Nat>> -> &m: Nat -> &k: List<&2, Nat> -> &se2: List<&2, List<&2, Nat>> -> {se == List.append(&2, List<&2, Nat>, se1, (m <> List.append(&2, Nat, k, at)) <> se2) : List<&2, List<&2, Nat>>}

# a Dir rule on p covers the path: p is the path or its parent
def phc.dir(at: List<&2, Nat>, +p: List<&2, Nat>, h: {Bool.or(Tl.ids.eq(at, p), Pp.parent_is(at, p)) == True{} : Bool}) -> phc.DirW(at, p):
  match at:
    case Nil{}:
      phc.or_cases(phc.DirW(Nil{}, p), Tl.ids.eq(Nil{}, p), False{}, h, e => (Nil{}, (LAE.pp.ids_sound(Nil{}, p, e), {==})), e => LA.pp.absurdF(phc.DirW(Nil{}, p), e))
    case +x <> +r:
      phc.or_cases(phc.DirW(x <> r, p), Tl.ids.eq(x <> r, p), Tl.ids.eq(r, p), h, e => (Nil{}, (LAE.pp.ids_sound(x <> r, p, e), {==})), e => ([x], (Equal.cong(List<&2, Nat>, List<&2, Nat>, z => x <> z, r, p, LAE.pp.ids_sound(r, p, e)), {==})))

def phc.elem_cons(+x: Nat, -rest: List<&2, Nat>, -n: Nat, s: phc.ElemW(rest, n)) -> phc.ElemW(x <> rest, n):
  match s:
    case (+a, t):
      match t:
        case (+b, e):
          (x <> a, (b, Equal.cong(List<&2, Nat>, List<&2, Nat>, z => x <> z, rest, List.append(&2, Nat, a, n <> b), e)))

def phc.elem_at(c: Bool, +x: Nat, +rest: List<&2, Nat>, +n: Nat, ec: {Nat.is_eq(x, n) == c : Bool}, h: {Bool.or(c, Tl.elem(rest, n)) == True{} : Bool}, ih: {Tl.elem(rest, n) == True{} : Bool} -> phc.ElemW(rest, n)) -> phc.ElemW(x <> rest, n):
  match c:
    case True{}:
      (Nil{}, (rest, Equal.cong(Nat, List<&2, Nat>, z => z <> rest, x, n, LAE.pp.eq_true(x, n, ec))))
    case False{}:
      phc.elem_cons(x, rest, n, ih(h))

# n is among the names xs: xs splits at n
def phc.elem(xs: List<&2, Nat>, +n: Nat) -> {Tl.elem(xs, n) == True{} : Bool} -> phc.ElemW(xs, n):
  match xs:
    case Nil{}:
      h => LA.pp.absurdF(phc.ElemW(Nil{}, n), h)
    case +x <> +rest:
      h => phc.elem_at(Nat.is_eq(x, n), x, rest, n, {==}, h, phc.elem(rest, n))

def phc.cover_cons(+r: Pp.Rule, -rest: List<&2, Pp.Rule>, -at: List<&2, Nat>, -low: List<&2, Nat>, s: phc.CoverW(rest, at, low)) -> phc.CoverW(r <> rest, at, low):
  match s:
    case (+ru1, s1):
      match s1:
        case (+r2, s2):
          match s2:
            case (+ru2, s3):
              match s3:
                case (e, c):
                  (r <> ru1, (r2, (ru2, (Equal.cong(List<&2, Pp.Rule>, List<&2, Pp.Rule>, z => r <> z, rest, List.append(&2, Pp.Rule, ru1, r2 <> ru2), e), c))))

def phc.cover_at(b: Bool, +r: Pp.Rule, +rest: List<&2, Pp.Rule>, +at: List<&2, Nat>, +low: List<&2, Nat>, eb: {Pp.covers(r, at, low) == b : Bool}, h: {Bool.or(b, Pp.any_covers(rest, at, low)) == True{} : Bool}, ih: {Pp.any_covers(rest, at, low) == True{} : Bool} -> phc.CoverW(rest, at, low)) -> phc.CoverW(r <> rest, at, low):
  match b:
    case True{}:
      (Nil{}, (r, (rest, ({==}, eb))))
    case False{}:
      phc.cover_cons(r, rest, at, low, ih(h))

# some rule of ru covers the path: ru splits at it
def phc.cover(ru: List<&2, Pp.Rule>, +at: List<&2, Nat>, +low: List<&2, Nat>) -> {Pp.any_covers(ru, at, low) == True{} : Bool} -> phc.CoverW(ru, at, low):
  match ru:
    case Nil{}:
      h => LA.pp.absurdF(phc.CoverW(Nil{}, at, low), h)
    case +r <> +rest:
      h => phc.cover_at(Pp.covers(r, at, low), r, rest, at, low, {==}, h, phc.cover(rest, at, low))

# p is the path with k0 below it: k0 is no name (p is the path, which the
# premise denies) or m then k
def phc.strict_k(k0: List<&2, Nat>, +at: List<&2, Nat>, +p: List<&2, Nat>, e: {p == List.append(&2, Nat, k0, at) : List<&2, Nat>}, hn: {Bool.not(Tl.ids.eq(at, p)) == True{} : Bool}) -> phc.StrictW(at, p):
  match k0:
    case Nil{}:
      +t1 = Equal.trans(Bool, Tl.ids.eq(at, p), Tl.ids.eq(at, at), True{}, Equal.cong(List<&2, Nat>, Bool, z => Tl.ids.eq(at, z), p, at, e), LAR.pc.ids_refl(at))
      +t2 = Equal.cong(Bool, Bool, z => Bool.not(z), Tl.ids.eq(at, p), True{}, t1)
      LA.pp.absurdF(phc.StrictW(at, p), Equal.trans(Bool, False{}, Bool.not(Tl.ids.eq(at, p)), True{}, Equal.sym(Bool, Bool.not(Tl.ids.eq(at, p)), False{}, t2), hn))
    case m <> k:
      (m, (k, e))

def phc.strict_at(+at: List<&2, Nat>, +p: List<&2, Nat>, s: PPathInsideNeedsRoot.pin.Suf(at, p), hn: {Bool.not(Tl.ids.eq(at, p)) == True{} : Bool}) -> phc.StrictW(at, p):
  match s:
    case (k0, e):
      phc.strict_k(k0, at, p, e, hn)

# the path is a strict ancestor of p: p is the path with one name m or
# more below it
def phc.strict(+at: List<&2, Nat>, +p: List<&2, Nat>, +h: {Bool.and(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p))) == True{} : Bool}) -> phc.StrictW(at, p):
  phc.strict_at(at, p, PPathInsideNeedsRoot.pin.usplit(at, p)(phc.and_l(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p)), h)), phc.and_r(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p)), h))

def phc.entry_here(+t: Bool, -p: List<&2, Nat>, +rest: List<&2, Pp.Rule>, +at: List<&2, Nat>, s: phc.StrictW(at, p)) -> phc.EntryW(PathPolicy.pp_entry_rule(t, p) <> rest, at):
  match s:
    case (+m, s1):
      match s1:
        case (+k, e):
          (Nil{}, (t, (m, (k, (rest, Equal.cong(List<&2, Nat>, List<&2, Pp.Rule>, z => PathPolicy.pp_entry_rule(t, z) <> rest, p, m <> List.append(&2, Nat, k, at), e))))))

def phc.entry_cons(+r: Pp.Rule, -rest: List<&2, Pp.Rule>, -at: List<&2, Nat>, s: phc.EntryW(rest, at)) -> phc.EntryW(r <> rest, at):
  match s:
    case (+ru1, s1):
      match s1:
        case (+t, s2):
          match s2:
            case (+m, s3):
              match s3:
                case (+k, s4):
                  match s4:
                    case (+ru2, e):
                      (r <> ru1, (t, (m, (k, (ru2, Equal.cong(List<&2, Pp.Rule>, List<&2, Pp.Rule>, z => r <> z, rest, List.append(&2, Pp.Rule, ru1, PathPolicy.pp_entry_rule(t, m <> List.append(&2, Nat, k, at)) <> ru2), e))))))

def phc.entry_at(b: Bool, +t: Bool, +p: List<&2, Nat>, +rest: List<&2, Pp.Rule>, +at: List<&2, Nat>, eb: {Bool.and(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p))) == b : Bool}, h: {Bool.or(b, Pp.any_ancestor(Pp.entries(rest), at)) == True{} : Bool}, ih: {Pp.any_ancestor(Pp.entries(rest), at) == True{} : Bool} -> phc.EntryW(rest, at)) -> phc.EntryW(PathPolicy.pp_entry_rule(t, p) <> rest, at):
  match b:
    case True{}:
      phc.entry_here(t, p, rest, at, phc.strict(at, p, eb))
    case False{}:
      phc.entry_cons(PathPolicy.pp_entry_rule(t, p), rest, at, ih(h))

# some rule's entry is strictly below the path: ru splits at that rule
def phc.entry(ru: List<&2, Pp.Rule>, +at: List<&2, Nat>) -> {Pp.any_ancestor(Pp.entries(ru), at) == True{} : Bool} -> phc.EntryW(ru, at):
  match ru:
    case Nil{}:
      h => LA.pp.absurdF(phc.EntryW(Nil{}, at), h)
    case r <> +rest:
      match r:
        case Pp.Tree{+p}:
          h => phc.entry_at(Bool.and(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p))), True{}, p, rest, at, {==}, h, phc.entry(rest, at))
        case Pp.Dir{+p}:
          h => phc.entry_at(Bool.and(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p))), False{}, p, rest, at, {==}, h, phc.entry(rest, at))
        case Pp.Named{+n}:
          h => phc.entry_cons(Pp.Named{n}, rest, at, phc.entry(rest, at)(h))

def phc.secret_here(-s: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, w: phc.StrictW(at, s)) -> phc.SecretW(s <> rest, at):
  match w:
    case (+m, w1):
      match w1:
        case (+k, e):
          (Nil{}, (m, (k, (rest, Equal.cong(List<&2, Nat>, List<&2, List<&2, Nat>>, z => z <> rest, s, m <> List.append(&2, Nat, k, at), e)))))

def phc.secret_cons(+s: List<&2, Nat>, -rest: List<&2, List<&2, Nat>>, -at: List<&2, Nat>, w: phc.SecretW(rest, at)) -> phc.SecretW(s <> rest, at):
  match w:
    case (+se1, w1):
      match w1:
        case (+m, w2):
          match w2:
            case (+k, w3):
              match w3:
                case (+se2, e):
                  (s <> se1, (m, (k, (se2, Equal.cong(List<&2, List<&2, Nat>>, List<&2, List<&2, Nat>>, z => s <> z, rest, List.append(&2, List<&2, Nat>, se1, (m <> List.append(&2, Nat, k, at)) <> se2), e)))))

def phc.secret_at(b: Bool, +s: List<&2, Nat>, +rest: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, eb: {Bool.and(Pp.under(at, s), Bool.not(Tl.ids.eq(at, s))) == b : Bool}, h: {Bool.or(b, Pp.any_ancestor(rest, at)) == True{} : Bool}, ih: {Pp.any_ancestor(rest, at) == True{} : Bool} -> phc.SecretW(rest, at)) -> phc.SecretW(s <> rest, at):
  match b:
    case True{}:
      phc.secret_here(s, rest, at, phc.strict(at, s, eb))
    case False{}:
      phc.secret_cons(s, rest, at, ih(h))

# some secret entry is strictly below the path: se splits at it
def phc.secret(se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>) -> {Pp.any_ancestor(se, at) == True{} : Bool} -> phc.SecretW(se, at):
  match se:
    case Nil{}:
      h => LA.pp.absurdF(phc.SecretW(Nil{}, at), h)
    case +s <> +rest:
      h => phc.secret_at(Bool.and(Pp.under(at, s), Bool.not(Tl.ids.eq(at, s))), s, rest, at, {==}, h, phc.secret(rest, at))

# Refutations
# -----------

def phc.tree_use(+p: List<&2, Nat>, -at: List<&2, Nat>, -ru: List<&2, Pp.Rule>, +ru1: List<&2, Pp.Rule>, +ru2: List<&2, Pp.Rule>, eru: {ru == List.append(&2, Pp.Rule, ru1, Pp.Tree{p} <> ru2) : List<&2, Pp.Rule>}, s: PPathInsideNeedsRoot.pin.Suf(p, at), tree: @ru1: List<&2, Pp.Rule> -> @p: List<&2, Nat> -> @ru2: List<&2, Pp.Rule> -> @k: List<&2, Nat> -> {ru == List.append(&2, Pp.Rule, ru1, Pp.Tree{p} <> ru2) : List<&2, Pp.Rule>} -> {at == List.append(&2, Nat, k, p) : List<&2, Nat>} -> Empty) -> Empty:
  match s:
    case (k, e):
      tree(ru1, p, ru2, k, eru, e)

def phc.dir_use(+p: List<&2, Nat>, -at: List<&2, Nat>, -ru: List<&2, Pp.Rule>, +ru1: List<&2, Pp.Rule>, +ru2: List<&2, Pp.Rule>, eru: {ru == List.append(&2, Pp.Rule, ru1, Pp.Dir{p} <> ru2) : List<&2, Pp.Rule>}, w: phc.DirW(at, p), dir: @ru1: List<&2, Pp.Rule> -> @p: List<&2, Nat> -> @ru2: List<&2, Pp.Rule> -> @k: List<&2, Nat> -> {ru == List.append(&2, Pp.Rule, ru1, Pp.Dir{p} <> ru2) : List<&2, Pp.Rule>} -> {at == List.append(&2, Nat, k, p) : List<&2, Nat>} -> {Nat.is_lt(List.length(&2, Nat, k), 2n) == True{} : Bool} -> Empty) -> Empty:
  match w:
    case (k, w1):
      match w1:
        case (e, lt):
          dir(ru1, p, ru2, k, eru, e, lt)

def phc.named_use(+ro: List<&2, List<&2, Nat>>, +n: Nat, +at: List<&2, Nat>, -ru: List<&2, Pp.Rule>, +ru1: List<&2, Pp.Rule>, +ru2: List<&2, Pp.Rule>, eru: {ru == List.append(&2, Pp.Rule, ru1, Pp.Named{n} <> ru2) : List<&2, Pp.Rule>}, w: phc.ElemW(Pp.below(at, Pp.root.of(ro, at)), n), named: @ru1: List<&2, Pp.Rule> -> @n: Nat -> @ru2: List<&2, Pp.Rule> -> @xs: List<&2, Nat> -> @ys: List<&2, Nat> -> {ru == List.append(&2, Pp.Rule, ru1, Pp.Named{n} <> ru2) : List<&2, Pp.Rule>} -> {PathPolicy.pp_below_root(ro, at) == List.append(&2, Nat, xs, n <> ys) : List<&2, Nat>} -> Empty) -> Empty:
  match w:
    case (+xs, w1):
      match w1:
        case (+ys, e):
          named(ru1, n, ru2, xs, ys, eru, Equal.trans(List<&2, Nat>, PathPolicy.pp_below_root(ro, at), Pp.below(at, Pp.root.of(ro, at)), List.append(&2, Nat, xs, n <> ys), Equal.sym(List<&2, Nat>, Pp.below(at, Pp.root.of(ro, at)), PathPolicy.pp_below_root(ro, at), LAR.pc.below_root(ro, at)), e))

# a rule r between ru1 and ru2 covers the path: the premise of its kind
# refutes it
def phc.rule(r: Pp.Rule, +ro: List<&2, List<&2, Nat>>, -ru: List<&2, Pp.Rule>, +ru1: List<&2, Pp.Rule>, +ru2: List<&2, Pp.Rule>, +at: List<&2, Nat>, eru: {ru == List.append(&2, Pp.Rule, ru1, r <> ru2) : List<&2, Pp.Rule>}, c: {Pp.covers(r, at, Pp.below(at, Pp.root.of(ro, at))) == True{} : Bool}, tree: @ru1: List<&2, Pp.Rule> -> @p: List<&2, Nat> -> @ru2: List<&2, Pp.Rule> -> @k: List<&2, Nat> -> {ru == List.append(&2, Pp.Rule, ru1, Pp.Tree{p} <> ru2) : List<&2, Pp.Rule>} -> {at == List.append(&2, Nat, k, p) : List<&2, Nat>} -> Empty, dir: @ru1: List<&2, Pp.Rule> -> @p: List<&2, Nat> -> @ru2: List<&2, Pp.Rule> -> @k: List<&2, Nat> -> {ru == List.append(&2, Pp.Rule, ru1, Pp.Dir{p} <> ru2) : List<&2, Pp.Rule>} -> {at == List.append(&2, Nat, k, p) : List<&2, Nat>} -> {Nat.is_lt(List.length(&2, Nat, k), 2n) == True{} : Bool} -> Empty, named: @ru1: List<&2, Pp.Rule> -> @n: Nat -> @ru2: List<&2, Pp.Rule> -> @xs: List<&2, Nat> -> @ys: List<&2, Nat> -> {ru == List.append(&2, Pp.Rule, ru1, Pp.Named{n} <> ru2) : List<&2, Pp.Rule>} -> {PathPolicy.pp_below_root(ro, at) == List.append(&2, Nat, xs, n <> ys) : List<&2, Nat>} -> Empty) -> Empty:
  match r:
    case Pp.Tree{+p}:
      phc.tree_use(p, at, ru, ru1, ru2, eru, PPathInsideNeedsRoot.pin.usplit(p, at)(c), tree)
    case Pp.Dir{+p}:
      phc.dir_use(p, at, ru, ru1, ru2, eru, phc.dir(at, p, c), dir)
    case Pp.Named{+n}:
      phc.named_use(ro, n, at, ru, ru1, ru2, eru, phc.elem(Pp.below(at, Pp.root.of(ro, at)), n)(c), named)

def phc.cover_use(+ro: List<&2, List<&2, Nat>>, -ru: List<&2, Pp.Rule>, +at: List<&2, Nat>, w: phc.CoverW(ru, at, Pp.below(at, Pp.root.of(ro, at))), tree: @ru1: List<&2, Pp.Rule> -> @p: List<&2, Nat> -> @ru2: List<&2, Pp.Rule> -> @k: List<&2, Nat> -> {ru == List.append(&2, Pp.Rule, ru1, Pp.Tree{p} <> ru2) : List<&2, Pp.Rule>} -> {at == List.append(&2, Nat, k, p) : List<&2, Nat>} -> Empty, dir: @ru1: List<&2, Pp.Rule> -> @p: List<&2, Nat> -> @ru2: List<&2, Pp.Rule> -> @k: List<&2, Nat> -> {ru == List.append(&2, Pp.Rule, ru1, Pp.Dir{p} <> ru2) : List<&2, Pp.Rule>} -> {at == List.append(&2, Nat, k, p) : List<&2, Nat>} -> {Nat.is_lt(List.length(&2, Nat, k), 2n) == True{} : Bool} -> Empty, named: @ru1: List<&2, Pp.Rule> -> @n: Nat -> @ru2: List<&2, Pp.Rule> -> @xs: List<&2, Nat> -> @ys: List<&2, Nat> -> {ru == List.append(&2, Pp.Rule, ru1, Pp.Named{n} <> ru2) : List<&2, Pp.Rule>} -> {PathPolicy.pp_below_root(ro, at) == List.append(&2, Nat, xs, n <> ys) : List<&2, Nat>} -> Empty) -> Empty:
  match w:
    case (+ru1, w1):
      match w1:
        case (r, w2):
          match w2:
            case (+ru2, w3):
              match w3:
                case (e, c):
                  phc.rule(r, ro, ru, ru1, ru2, at, e, c, tree, dir, named)

def phc.entry_use(-ru: List<&2, Pp.Rule>, -at: List<&2, Nat>, w: phc.EntryW(ru, at), entry: @ru1: List<&2, Pp.Rule> -> @t: Bool -> @m: Nat -> @k: List<&2, Nat> -> @ru2: List<&2, Pp.Rule> -> {ru == List.append(&2, Pp.Rule, ru1, PathPolicy.pp_entry_rule(t, m <> List.append(&2, Nat, k, at)) <> ru2) : List<&2, Pp.Rule>} -> Empty) -> Empty:
  match w:
    case (ru1, w1):
      match w1:
        case (t, w2):
          match w2:
            case (m, w3):
              match w3:
                case (k, w4):
                  match w4:
                    case (ru2, e):
                      entry(ru1, t, m, k, ru2, e)

def phc.secret_use(-se: List<&2, List<&2, Nat>>, -at: List<&2, Nat>, w: phc.SecretW(se, at), secret: @se1: List<&2, List<&2, Nat>> -> @m: Nat -> @k: List<&2, Nat> -> @se2: List<&2, List<&2, Nat>> -> {se == List.append(&2, List<&2, Nat>, se1, (m <> List.append(&2, Nat, k, at)) <> se2) : List<&2, List<&2, Nat>>} -> Empty) -> Empty:
  match w:
    case (se1, w1):
      match w1:
        case (m, w2):
          match w2:
            case (k, w3):
              match w3:
                case (se2, e):
                  secret(se1, m, k, se2, e)

# the class is Protected: one of the causes the premises refute holds
def phc.main(+ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, +l: Bool, hc: {Pp.demote(Pp.class_of(Pp.Pol{ro, ru, se}, at), l) == Pp.Protected{} : Pp.Cls}, tree: @ru1: List<&2, Pp.Rule> -> @p: List<&2, Nat> -> @ru2: List<&2, Pp.Rule> -> @k: List<&2, Nat> -> {ru == List.append(&2, Pp.Rule, ru1, Pp.Tree{p} <> ru2) : List<&2, Pp.Rule>} -> {at == List.append(&2, Nat, k, p) : List<&2, Nat>} -> Empty, dir: @ru1: List<&2, Pp.Rule> -> @p: List<&2, Nat> -> @ru2: List<&2, Pp.Rule> -> @k: List<&2, Nat> -> {ru == List.append(&2, Pp.Rule, ru1, Pp.Dir{p} <> ru2) : List<&2, Pp.Rule>} -> {at == List.append(&2, Nat, k, p) : List<&2, Nat>} -> {Nat.is_lt(List.length(&2, Nat, k), 2n) == True{} : Bool} -> Empty, named: @ru1: List<&2, Pp.Rule> -> @n: Nat -> @ru2: List<&2, Pp.Rule> -> @xs: List<&2, Nat> -> @ys: List<&2, Nat> -> {ru == List.append(&2, Pp.Rule, ru1, Pp.Named{n} <> ru2) : List<&2, Pp.Rule>} -> {PathPolicy.pp_below_root(ro, at) == List.append(&2, Nat, xs, n <> ys) : List<&2, Nat>} -> Empty, entry: @ru1: List<&2, Pp.Rule> -> @t: Bool -> @m: Nat -> @k: List<&2, Nat> -> @ru2: List<&2, Pp.Rule> -> {ru == List.append(&2, Pp.Rule, ru1, PathPolicy.pp_entry_rule(t, m <> List.append(&2, Nat, k, at)) <> ru2) : List<&2, Pp.Rule>} -> Empty, secret: @se1: List<&2, List<&2, Nat>> -> @m: Nat -> @k: List<&2, Nat> -> @se2: List<&2, List<&2, Nat>> -> {se == List.append(&2, List<&2, Nat>, se1, (m <> List.append(&2, Nat, k, at)) <> se2) : List<&2, List<&2, Nat>>} -> Empty) -> Empty:
  +low = Pp.below(at, Pp.root.of(ro, at))
  +A = Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(ru), se), at)
  +hpr = phc.found(Pp.any_under(se, at), Pp.protects(Pp.Pol{ro, ru, se}, at), Maybe.is_some(&2, List<&2, Nat>, Pp.root.of(ro, at)), l, hc)
  phc.or_cases(Empty, Pp.any_covers(ru, at, low), A, hpr,
    c => phc.cover_use(ro, ru, at, phc.cover(ru, at, low)(c), tree, dir, named),
    c => phc.or_cases(Empty, Pp.any_ancestor(Pp.entries(ru), at), Pp.any_ancestor(se, at), Equal.trans(Bool, Bool.or(Pp.any_ancestor(Pp.entries(ru), at), Pp.any_ancestor(se, at)), A, True{}, Equal.sym(Bool, A, Bool.or(Pp.any_ancestor(Pp.entries(ru), at), Pp.any_ancestor(se, at)), LAR.pc.anc_append(Pp.entries(ru), se, at)), c),
      c1 => phc.entry_use(ru, at, phc.entry(ru, at)(c1), entry),
      c2 => phc.secret_use(se, at, phc.secret(se, at)(c2), secret)))

def PathPolicy.path_protected_has_cause(ro, ru, se, ls, segs, at, l, res, tree, dir, named, entry, secret):
  hp => phc.main(ro, ru, se, at, l, Equal.trans(Pp.Cls, Pp.demote(Pp.class_of(Pp.Pol{ro, ru, se}, at), l), Pp.class(Pp.Pol{ro, ru, se}, ls, segs), Pp.Protected{}, Equal.sym(Pp.Cls, Pp.class(Pp.Pol{ro, ru, se}, ls, segs), Pp.demote(Pp.class_of(Pp.Pol{ro, ru, se}, at), l), LAC.pcc.cls_eq(Pp.Pol{ro, ru, se}, ls, segs, at, l, res)), hp), tree, dir, named, entry, secret)
