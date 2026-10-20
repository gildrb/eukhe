# proof_path_policy: the (G1) laws (laws/path_policy.bend) of the path
# policy model in bend/path_policy.bend.
#
# A resolution keeps its invariant `looped or linkfree(at)`: a name it
# pushes is no link (the link test is the `look` it carries), `..` keeps
# a prefix, and a link's target starts from `/` or from the link's
# directory (`pp.go_lf`). The class picks Secret first and Inside last
# (`pp.pick_inside`, `pp.pick_guarded`); `demote` only moves Inside to
# Outside. A gated effect (outside, protected, secret: code 4 and up) is
# never grantable, so a write that is not Inside, or a read of a secret,
# reduces to the user's answer. A write that runs without a yes is Inside,
# so its real location is not guarded, and a write there leaves every
# guarded cell as it was (`pp.guarded_set`).

import Base
import ./tools.bend as Tl
import ./path_policy.bend as Pp

# Logic
# -----

def pp.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pp.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pp.BD(_, Unit, A)
  Unit{}

def pp.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pp.BD(_, A, Unit)
  Unit{}

# A at Inside, Unit elsewhere: refutes {c == Inside} for c not Inside
def pp.CM(c: Pp.Cls, A: Type) -> Type:
  match c:
    case Pp.Inside{}:
      A
    case Pp.Outside{}:
      Unit
    case Pp.Protected{}:
      Unit
    case Pp.Secret{}:
      Unit

def pp.not_inside(-A: Type, c: Pp.Cls, n: {Pp.Cls.inside(c) == False{} : Bool}, e: {c == Pp.Inside{} : Pp.Cls}) -> A:
  match c:
    case Pp.Inside{}:
      pp.absurd(A, n)
    case Pp.Outside{}:
      %e : pp.CM(_, A)
      Unit{}
    case Pp.Protected{}:
      %e : pp.CM(_, A)
      Unit{}
    case Pp.Secret{}:
      %e : pp.CM(_, A)
      Unit{}

def pp.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      pp.absurdF({b == True{} : Bool}, h)

def pp.or_tr(a: Bool, +b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

def pp.or_false_l(a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      pp.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def pp.or_false_r(a: Bool, +b: Bool, h: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      pp.absurd({b == False{} : Bool}, h)
    case False{}:
      h

def pp.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      pp.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      pp.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pp.eq_true(p, q, h))

def pp.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pp.absurdF({False{} == True{} : Bool}, h)

# two lists that ids.eq calls equal are equal
def pp.ids_sound(a: List<&2, Nat>, b: List<&2, Nat>, +h: {Tl.ids.eq(a, b) == True{} : Bool}) -> {a == b : List<&2, Nat>}:
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          {==}
        case y <> yr:
          pp.absurdF({Nil{} == y <> yr : List<&2, Nat>}, h)
    case +x <> +xr:
      match b:
        case Nil{}:
          pp.absurdF({x <> xr == Nil{} : List<&2, Nat>}, h)
        case +y <> +yr:
          %pp.eq_true(x, y, pp.and_l(Nat.is_eq(x, y), Tl.ids.eq(xr, yr), h)) : {x <> xr == _ <> yr : List<&2, Nat>}
          %pp.ids_sound(xr, yr, pp.and_r(Nat.is_eq(x, y), Tl.ids.eq(xr, yr), h)) : {x <> xr == x <> _ : List<&2, Nat>}
          {==}

# 1. The real path
# ----------------

# the invariant of a resolution's result
def pp.ok(+ls: List<&2, Pp.Link>, +r: Pp.Res) -> Bool:
  Bool.or(Pp.Res.looped(r), Pp.linkfree(ls, Pp.Res.at(r)))

# `..` keeps a link-free prefix link-free
def pp.lf_up(+ls: List<&2, Pp.Link>, at: List<&2, Nat>, h: {Pp.linkfree(ls, at) == True{} : Bool}) -> {Pp.linkfree(ls, Pp.up(at)) == True{} : Bool}:
  match at:
    case Nil{}:
      {==}
    case a <> +above:
      pp.and_r(Maybe.is_none(&2, Pp.Link, Pp.link.find(ls, a <> above)), Pp.linkfree(ls, above), h)

def pp.inv_up(looped: Bool, +ls: List<&2, Pp.Link>, +at: List<&2, Nat>, h: {Bool.or(looped, Pp.linkfree(ls, at)) == True{} : Bool}) -> {Bool.or(looped, Pp.linkfree(ls, Pp.up(at))) == True{} : Bool}:
  match looped:
    case True{}:
      {==}
    case False{}:
      pp.lf_up(ls, at, h)

# a name pushed while looped or with no link at it keeps the invariant
def pp.inv_name(looped: Bool, m: Maybe<&2, Pp.Link>, +lf: Bool, h: {Bool.or(looped, lf) == True{} : Bool}) -> {Bool.or(Bool.or(looped, Maybe.is_some(&2, Pp.Link, m)), Bool.and(Maybe.is_none(&2, Pp.Link, m), lf)) == True{} : Bool}:
  match looped:
    case True{}:
      {==}
    case False{}:
      match m:
        case None{}:
          h
        case Some{l}:
          {==}

# a name with no link at it keeps a link-free prefix link-free
def pp.inv_none(+ls: List<&2, Pp.Link>, +n: Nat, +at: List<&2, Nat>, +looped: Bool, e: {None{} == Pp.link.find(ls, n <> at) : Maybe<&2, Pp.Link>}, h: {Bool.or(looped, Pp.linkfree(ls, at)) == True{} : Bool}) -> {Bool.or(looped, Pp.linkfree(ls, n <> at)) == True{} : Bool}:
  %e : {Bool.or(looped, Bool.and(Maybe.is_none(&2, Pp.Link, _), Pp.linkfree(ls, at))) == True{} : Bool}
  h

def pp.go_lf(fuel: Nat, segs: List<&2, Tl.Seg>, +ls: List<&2, Pp.Link>, +at: List<&2, Nat>, +looped: Bool, +look: Maybe<&2, Pp.Link>, +lk: {look == Pp.look.at(ls, segs, at) : Maybe<&2, Pp.Link>}, +h: {Bool.or(looped, Pp.linkfree(ls, at)) == True{} : Bool}) -> {pp.ok(ls, Pp.go(fuel, segs, ls, at, looped, look)) == True{} : Bool}:
  match fuel:
    case 0n:
      match segs:
        case Nil{}:
          h
        case s <> +rest:
          match s:
            case Tl.Name{+n}:
              %Equal.sym(Maybe<&2, Pp.Link>, look, Pp.link.find(ls, n <> at), lk) : {pp.ok(ls, Pp.go(0n, Tl.Name{n} <> rest, ls, at, looped, _)) == True{} : Bool}
              pp.go_lf(0n, rest, ls, n <> at, Bool.or(looped, Maybe.is_some(&2, Pp.Link, Pp.link.find(ls, n <> at))), Pp.look.at(ls, rest, n <> at), {==}, pp.inv_name(looped, Pp.link.find(ls, n <> at), Pp.linkfree(ls, at), h))
            case Tl.Up{}:
              pp.go_lf(0n, rest, ls, Pp.up(at), looped, Pp.look.at(ls, rest, Pp.up(at)), {==}, pp.inv_up(looped, ls, at, h))
            case Tl.Here{}:
              pp.go_lf(0n, rest, ls, at, looped, Pp.look.at(ls, rest, at), {==}, h)
    case 1n+f:
      match segs:
        case Nil{}:
          h
        case s <> +rest:
          match s:
            case Tl.Name{+n}:
              match look:
                case None{}:
                  pp.go_lf(1n+f, rest, ls, n <> at, looped, Pp.look.at(ls, rest, n <> at), {==}, pp.inv_none(ls, n, at, looped, lk, h))
                case Some{l}:
                  match l:
                    case Pp.Link{la, abs, +to}:
                      match abs:
                        case True{}:
                          pp.go_lf(f, List.append(&2, Tl.Seg, to, rest), ls, Nil{}, looped, Pp.look.at(ls, List.append(&2, Tl.Seg, to, rest), Nil{}), {==}, pp.or_tr(looped, True{}, {==}))
                        case False{}:
                          pp.go_lf(f, List.append(&2, Tl.Seg, to, rest), ls, at, looped, Pp.look.at(ls, List.append(&2, Tl.Seg, to, rest), at), {==}, h)
            case Tl.Up{}:
              pp.go_lf(1n+f, rest, ls, Pp.up(at), looped, Pp.look.at(ls, rest, Pp.up(at)), {==}, pp.inv_up(looped, ls, at, h))
            case Tl.Here{}:
              pp.go_lf(1n+f, rest, ls, at, looped, Pp.look.at(ls, rest, at), {==}, h)

def pp.path_real_has_no_link(+ls: List<&2, Pp.Link>, +segs: List<&2, Tl.Seg>) -> {Bool.or(Pp.Res.looped(Pp.real(ls, segs)), Pp.linkfree(ls, Pp.Res.at(Pp.real(ls, segs)))) == True{} : Bool}:
  pp.go_lf(Pp.max_links(), segs, ls, Nil{}, False{}, Pp.look.at(ls, segs, Nil{}), {==}, {==})

# 2. The class
# ------------

def pp.secret_res(+pol: Pp.Pol, r: Pp.Res, hit: {Pp.any_under(Pp.Pol.secret(pol), Pp.Res.at(r)) == True{} : Bool}) -> {Pp.class_res(pol, r) == Pp.Secret{} : Pp.Cls}:
  match r:
    case Pp.Res{+at, looped}:
      %Equal.sym(Bool, Pp.any_under(Pp.Pol.secret(pol), at), True{}, hit) : {Pp.demote(Pp.cls.pick(_, Pp.protects(pol, at), Maybe.is_some(&2, List<&2, Nat>, Pp.root.of(Pp.Pol.roots(pol), at))), looped) == Pp.Secret{} : Pp.Cls}
      {==}

def pp.path_secret_wins(+pol: Pp.Pol, +ls: List<&2, Pp.Link>, +segs: List<&2, Tl.Seg>, hit: {Pp.any_under(Pp.Pol.secret(pol), Pp.Res.at(Pp.real(ls, segs))) == True{} : Bool}) -> {Pp.class(pol, ls, segs) == Pp.Secret{} : Pp.Cls}:
  pp.secret_res(pol, Pp.real(ls, segs), hit)

# Inside exactly when no secret, nothing protects, and a root holds it
def pp.pick_inside(sec: Bool, prot: Bool, ins: Bool) -> {Pp.Cls.inside(Pp.cls.pick(sec, prot, ins)) == Pp.inside_ok(sec, prot, ins) : Bool}:
  match sec:
    case True{}:
      {==}
    case False{}:
      match prot:
        case True{}:
          {==}
        case False{}:
          match ins:
            case True{}:
              {==}
            case False{}:
              {==}

# demote gives Inside only for an Inside that did not loop
def pp.demote_inside(c: Pp.Cls, looped: Bool, h: {Pp.demote(c, looped) == Pp.Inside{} : Pp.Cls}) -> {Bool.and(Bool.not(looped), Pp.Cls.inside(c)) == True{} : Bool}:
  match c:
    case Pp.Inside{}:
      match looped:
        case True{}:
          %h : pp.CM(_, {Bool.and(Bool.not(True{}), True{}) == True{} : Bool})
          Unit{}
        case False{}:
          {==}
    case Pp.Outside{}:
      %h : pp.CM(_, {Bool.and(Bool.not(looped), False{}) == True{} : Bool})
      Unit{}
    case Pp.Protected{}:
      %h : pp.CM(_, {Bool.and(Bool.not(looped), False{}) == True{} : Bool})
      Unit{}
    case Pp.Secret{}:
      %h : pp.CM(_, {Bool.and(Bool.not(looped), False{}) == True{} : Bool})
      Unit{}

def pp.inside_safe(+pol: Pp.Pol, r: Pp.Res, h: {Pp.class_res(pol, r) == Pp.Inside{} : Pp.Cls}) -> {Pp.safe(pol, r) == True{} : Bool}:
  match r:
    case Pp.Res{+at, +looped}:
      %pp.pick_inside(Pp.any_under(Pp.Pol.secret(pol), at), Pp.protects(pol, at), Maybe.is_some(&2, List<&2, Nat>, Pp.root.of(Pp.Pol.roots(pol), at))) : {Bool.and(Bool.not(looped), _) == True{} : Bool}
      pp.demote_inside(Pp.class_of(pol, at), looped, h)

def pp.path_inside_is_safe(+pol: Pp.Pol, +ls: List<&2, Pp.Link>, +segs: List<&2, Tl.Seg>, inside: {Pp.class(pol, ls, segs) == Pp.Inside{} : Pp.Cls}) -> {Pp.safe(pol, Pp.real(ls, segs)) == True{} : Bool}:
  pp.inside_safe(pol, Pp.real(ls, segs), inside)

def pp.pick_guarded(sec: Bool, ins: Bool) -> {Pp.Cls.guarded(Pp.cls.pick(sec, True{}, ins)) == True{} : Bool}:
  match sec:
    case True{}:
      {==}
    case False{}:
      {==}

def pp.demote_guarded(c: Pp.Cls, looped: Bool, h: {Pp.Cls.guarded(c) == True{} : Bool}) -> {Pp.Cls.guarded(Pp.demote(c, looped)) == True{} : Bool}:
  match c:
    case Pp.Inside{}:
      pp.absurdF({Pp.Cls.guarded(Pp.demote(Pp.Inside{}, looped)) == True{} : Bool}, h)
    case Pp.Outside{}:
      pp.absurdF({Pp.Cls.guarded(Pp.demote(Pp.Outside{}, looped)) == True{} : Bool}, h)
    case Pp.Protected{}:
      {==}
    case Pp.Secret{}:
      {==}

def pp.anc_res(+pol: Pp.Pol, r: Pp.Res, anc: {Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(Pp.Pol.rules(pol)), Pp.Pol.secret(pol)), Pp.Res.at(r)) == True{} : Bool}) -> {Pp.Cls.guarded(Pp.class_res(pol, r)) == True{} : Bool}:
  match r:
    case Pp.Res{+at, looped}:
      +sec = Pp.any_under(Pp.Pol.secret(pol), at)
      +ins = Maybe.is_some(&2, List<&2, Nat>, Pp.root.of(Pp.Pol.roots(pol), at))
      +hp = pp.or_tr(Pp.any_covers(Pp.Pol.rules(pol), at, Pp.below(at, Pp.root.of(Pp.Pol.roots(pol), at))), Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(Pp.Pol.rules(pol)), Pp.Pol.secret(pol)), at), anc)
      +g = pp.pick_guarded(sec, ins)
      %Equal.sym(Bool, Pp.protects(pol, at), True{}, hp) : {Pp.Cls.guarded(Pp.demote(Pp.cls.pick(sec, _, ins), looped)) == True{} : Bool}
      pp.demote_guarded(Pp.cls.pick(sec, True{}, ins), looped, g)

def pp.path_ancestor_guarded(+pol: Pp.Pol, +ls: List<&2, Pp.Link>, +segs: List<&2, Tl.Seg>, anc: {Pp.any_ancestor(List.append(&2, List<&2, Nat>, Pp.entries(Pp.Pol.rules(pol)), Pp.Pol.secret(pol)), Pp.Res.at(Pp.real(ls, segs))) == True{} : Bool}) -> {Pp.Cls.guarded(Pp.class(pol, ls, segs)) == True{} : Bool}:
  pp.anc_res(pol, Pp.real(ls, segs), anc)

# 3. The gate
# -----------

# a yes that is not a yes
def pp.yes_clash(-A: Type, ans: Pp.Ans, ran: {Pp.Ans.yes(ans) == True{} : Bool}, no: {Pp.Ans.yes(ans) == False{} : Bool}) -> A:
  pp.absurd(A, Equal.trans(Bool, True{}, Pp.Ans.yes(ans), False{}, Equal.sym(Bool, Pp.Ans.yes(ans), True{}, ran), no))

def pp.gate_write_auto_only_inside(c: Pp.Cls, +auto: List<&2, Nat>, +ans: Pp.Ans, ran: {Pp.runs(c, Pp.Wr{}, auto, ans) == True{} : Bool}, no: {Pp.Ans.yes(ans) == False{} : Bool}) -> {c == Pp.Inside{} : Pp.Cls}:
  match c:
    case Pp.Inside{}:
      {==}
    case Pp.Outside{}:
      pp.yes_clash({Pp.Outside{} == Pp.Inside{} : Pp.Cls}, ans, ran, no)
    case Pp.Protected{}:
      pp.yes_clash({Pp.Protected{} == Pp.Inside{} : Pp.Cls}, ans, ran, no)
    case Pp.Secret{}:
      pp.yes_clash({Pp.Secret{} == Pp.Inside{} : Pp.Cls}, ans, ran, no)

def pp.gate_secret_read_needs_yes(c: Pp.Cls, a: Pp.Acc, +auto: List<&2, Nat>, +ans: Pp.Ans, s: {Pp.secret_read(c, a) == True{} : Bool}, ran: {Pp.runs(c, a, auto, ans) == True{} : Bool}) -> {Pp.Ans.yes(ans) == True{} : Bool}:
  match c:
    case Pp.Secret{}:
      match a:
        case Pp.Rd{}:
          ran
        case Pp.Ls{}:
          ran
        case Pp.Sr{h}:
          match h:
            case True{}:
              ran
            case False{}:
              ran
        case Pp.Wr{}:
          pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
    case Pp.Inside{}:
      match a:
        case Pp.Rd{}:
          pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
        case Pp.Ls{}:
          pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
        case Pp.Sr{h}:
          match h:
            case True{}:
              ran
            case False{}:
              pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
        case Pp.Wr{}:
          pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
    case Pp.Outside{}:
      match a:
        case Pp.Rd{}:
          pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
        case Pp.Ls{}:
          pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
        case Pp.Sr{h}:
          match h:
            case True{}:
              ran
            case False{}:
              pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
        case Pp.Wr{}:
          pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
    case Pp.Protected{}:
      match a:
        case Pp.Rd{}:
          pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
        case Pp.Ls{}:
          pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
        case Pp.Sr{h}:
          match h:
            case True{}:
              ran
            case False{}:
              pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)
        case Pp.Wr{}:
          pp.absurdF({Pp.Ans.yes(ans) == True{} : Bool}, s)

def pp.gate_yes_runs(c: Pp.Cls, a: Pp.Acc, +auto: List<&2, Nat>) -> {Pp.runs(c, a, auto, Pp.Yes{}) == True{} : Bool}:
  pp.or_tr(Pp.allows(auto, Pp.effs(c, a)), True{}, {==})

def pp.gate_inside_write_runs(+auto: List<&2, Nat>, +ans: Pp.Ans, w: {Tl.elem(auto, 1n) == True{} : Bool}) -> {Pp.runs(Pp.Inside{}, Pp.Wr{}, auto, ans) == True{} : Bool}:
  %Equal.sym(Bool, Tl.elem(auto, 1n), True{}, w) : {Bool.or(_, Pp.Ans.yes(ans)) == True{} : Bool}
  {==}

# 4. The store
# ------------

def pp.inside_unguarded(c: Pp.Cls, h: {Pp.Cls.inside(c) == True{} : Bool}) -> {Pp.Cls.guarded(c) == False{} : Bool}:
  match c:
    case Pp.Inside{}:
      {==}
    case Pp.Outside{}:
      pp.absurdF({False{} == False{} : Bool}, h)
    case Pp.Protected{}:
      pp.absurdF({True{} == False{} : Bool}, h)
    case Pp.Secret{}:
      pp.absurdF({True{} == False{} : Bool}, h)

# the real location of a path judged Inside is not guarded
def pp.inside_res(+pol: Pp.Pol, r: Pp.Res, h: {Pp.class_res(pol, r) == Pp.Inside{} : Pp.Cls}) -> {Pp.Cls.guarded(Pp.class_of(pol, Pp.Res.at(r))) == False{} : Bool}:
  match r:
    case Pp.Res{+at, +looped}:
      pp.inside_unguarded(Pp.class_of(pol, at), pp.and_r(Bool.not(looped), Pp.Cls.inside(Pp.class_of(pol, at)), pp.demote_inside(Pp.class_of(pol, at), looped, h)))

# one cell of a set, by the head test b
def pp.set_pick(b: Bool, +c: Pp.Cell, +rest: List<&2, Pp.Cell>, +pol: Pp.Pol, +k: List<&2, Nat>, +v: Nat, e: {Tl.ids.eq(Pp.Cell.at(c), k) == b : Bool}, +hk: {Pp.Cls.guarded(Pp.class_of(pol, k)) == False{} : Bool}, ih: {Pp.guarded(Pp.set(rest, k, v), pol) == Pp.guarded(rest, pol) : List<&2, Pp.Cell>}) -> {Pp.guarded(Pp.set.pick(b, c, k, v, rest, Pp.set(rest, k, v)), pol) == Pp.guarded(c <> rest, pol) : List<&2, Pp.Cell>}:
  match b:
    case True{}:
      +same = pp.ids_sound(Pp.Cell.at(c), k, e)
      %Equal.sym(Bool, Pp.Cls.guarded(Pp.class_of(pol, k)), False{}, hk) : {Pp.keep.pick(_, Pp.Cell{k, v}, Pp.guarded(rest, pol)) == Pp.guarded(c <> rest, pol) : List<&2, Pp.Cell>}
      %Equal.sym(List<&2, Nat>, Pp.Cell.at(c), k, same) : {Pp.guarded(rest, pol) == Pp.keep.pick(Pp.Cls.guarded(Pp.class_of(pol, _)), c, Pp.guarded(rest, pol)) : List<&2, Pp.Cell>}
      %Equal.sym(Bool, Pp.Cls.guarded(Pp.class_of(pol, k)), False{}, hk) : {Pp.guarded(rest, pol) == Pp.keep.pick(_, c, Pp.guarded(rest, pol)) : List<&2, Pp.Cell>}
      {==}
    case False{}:
      %Equal.sym(List<&2, Pp.Cell>, Pp.guarded(Pp.set(rest, k, v), pol), Pp.guarded(rest, pol), ih) : {Pp.keep.pick(Pp.Cls.guarded(Pp.class_of(pol, Pp.Cell.at(c))), c, _) == Pp.guarded(c <> rest, pol) : List<&2, Pp.Cell>}
      {==}

# a write at a location that is not guarded keeps every guarded cell
def pp.guarded_set(cs: List<&2, Pp.Cell>, +pol: Pp.Pol, +k: List<&2, Nat>, +v: Nat, +hk: {Pp.Cls.guarded(Pp.class_of(pol, k)) == False{} : Bool}) -> {Pp.guarded(Pp.set(cs, k, v), pol) == Pp.guarded(cs, pol) : List<&2, Pp.Cell>}:
  match cs:
    case Nil{}:
      %Equal.sym(Bool, Pp.Cls.guarded(Pp.class_of(pol, k)), False{}, hk) : {Pp.keep.pick(_, Pp.Cell{k, v}, Nil{}) == Nil{} : List<&2, Pp.Cell>}
      {==}
    case +c <> +rest:
      pp.set_pick(Tl.ids.eq(Pp.Cell.at(c), k), c, rest, pol, k, v, {==}, hk, pp.guarded_set(rest, pol, k, v, hk))

# one write, by the gate's verdict b
def pp.put_keep(b: Bool, +pol: Pp.Pol, +ls: List<&2, Pp.Link>, +auto: List<&2, Nat>, cs: List<&2, Pp.Cell>, +segs: List<&2, Tl.Seg>, +v: Nat, +ans: Pp.Ans, e: {Pp.runs(Pp.class(pol, ls, segs), Pp.Wr{}, auto, ans) == b : Bool}, no: {Pp.Ans.yes(ans) == False{} : Bool}) -> {Pp.guarded(Pp.put.pick(b, cs, Pp.Res.at(Pp.real(ls, segs)), v), pol) == Pp.guarded(cs, pol) : List<&2, Pp.Cell>}:
  match b:
    case True{}:
      +inside = pp.gate_write_auto_only_inside(Pp.class(pol, ls, segs), auto, ans, e, no)
      pp.guarded_set(cs, pol, Pp.Res.at(Pp.real(ls, segs)), v, pp.inside_res(pol, Pp.real(ls, segs), inside))
    case False{}:
      {==}

def pp.config_needs_yes(es: List<&2, Pp.Put>, +pol: Pp.Pol, +ls: List<&2, Pp.Link>, +auto: List<&2, Nat>, +cs: List<&2, Pp.Cell>, +no: {Pp.any_yes(es) == False{} : Bool}) -> {Pp.guarded(Pp.run(es, pol, ls, auto, cs), pol) == Pp.guarded(cs, pol) : List<&2, Pp.Cell>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Pp.Put{+segs, +v, +ans}:
          +na = pp.or_false_l(Pp.Ans.yes(ans), Pp.any_yes(rest), no)
          +nr = pp.or_false_r(Pp.Ans.yes(ans), Pp.any_yes(rest), no)
          +next = Pp.step(pol, ls, auto, cs, Pp.Put{segs, v, ans})
          Equal.trans(List<&2, Pp.Cell>, Pp.guarded(Pp.run(rest, pol, ls, auto, next), pol), Pp.guarded(next, pol), Pp.guarded(cs, pol), pp.config_needs_yes(rest, pol, ls, auto, next, nr), pp.put_keep(Pp.runs(Pp.class(pol, ls, segs), Pp.Wr{}, auto, ans), pol, ls, auto, cs, segs, v, ans, {==}, na))
