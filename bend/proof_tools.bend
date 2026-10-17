# proof_tools: the S7 laws (docs/harness.md) of the tool surface model in
# bend/tools.bend. An event never touches the roster, and a turn sends
# the session's roster (`pl.sent_go`, by induction on the events). A join
# appends to `dyn`; a quit drops every copy (`pl.drop_go`, with the head
# test as a parameter). `build` adds the intent parameter only when it is
# missing, and lifts the version to at least 1. A walk keeps its depth
# equal to the names it holds (`pl.esc`, `pl.ins`). The gate lemmas speak
# of `exec.go` at any head test: what ran is a prefix, a gated step that
# ran used one approval, a denial stops at the denied step, and a script
# that finished ran every step.

import Base
import ./tools.bend as Tl

# Logic
# -----

def pl.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def pl.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : pl.BD(_, Unit, A)
  Unit{}

def pl.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : pl.BD(_, A, Unit)
  Unit{}

def pl.ND(n: Nat, z: Type, s: Type) -> Type:
  match n:
    case 0n:
      z
    case 1n+p:
      s

def pl.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      pl.absurdF({False{} == True{} : Bool}, h)

def pl.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      pl.absurdF({b == True{} : Bool}, h)

def pl.and_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

def pl.or_tr(a: Bool, +b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

def pl.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pl.eq_refl(p)

def pl.le0(t: Nat) -> {Nat.is_le(0n, t) == True{} : Bool}:
  match t:
    case 0n:
      {==}
    case 1n+q:
      {==}

# 1. The roster
# -------------

def pl.roster_step(s: Tl.Sess, e: Tl.Ev) -> {Tl.Sess.roster(Tl.step(s, e)) == Tl.Sess.roster(s) : List<&2, Nat>}:
  match s:
    case Tl.Sess{r, d, x}:
      match e:
        case Tl.Join{t}:
          {==}
        case Tl.Quit{t}:
          {==}
        case Tl.Turn{}:
          {==}

def pl.roster_fixed(es: List<&2, Tl.Ev>, +s: Tl.Sess) -> {Tl.Sess.roster(Tl.run(es, s)) == Tl.Sess.roster(s) : List<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case +e <> rest:
      Equal.trans(List<&2, Nat>, Tl.Sess.roster(Tl.run(rest, Tl.step(s, e))), Tl.Sess.roster(Tl.step(s, e)), Tl.Sess.roster(s), pl.roster_fixed(rest, Tl.step(s, e)), pl.roster_step(s, e))

def pl.ids_refl(r: List<&2, Nat>) -> {Tl.ids.eq(r, r) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case +y <> yr:
      %pl.eq_refl(y) : {Bool.and(_, Tl.ids.eq(yr, yr)) == True{} : Bool}
      pl.ids_refl(yr)

# a turn sends r after rosters that are all r
def pl.all_snoc(x: List<&2, List<&2, Nat>>, +r: List<&2, Nat>, +h: {Tl.all_eq(x, r) == True{} : Bool}) -> {Tl.all_eq(List.append(&2, List<&2, Nat>, x, [r]), r) == True{} : Bool}:
  match x:
    case Nil{}:
      %Equal.sym(Bool, Tl.ids.eq(r, r), True{}, pl.ids_refl(r)) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case +y <> +rest:
      pl.and_t(Tl.ids.eq(y, r), Tl.all_eq(List.append(&2, List<&2, Nat>, rest, [r]), r), pl.and_l(Tl.ids.eq(y, r), Tl.all_eq(rest, r), h), pl.all_snoc(rest, r, pl.and_r(Tl.ids.eq(y, r), Tl.all_eq(rest, r), h)))

def pl.sent_go(es: List<&2, Tl.Ev>, +r: List<&2, Nat>, +d: List<&2, Nat>, +x: List<&2, List<&2, Nat>>, +h: {Tl.all_eq(x, r) == True{} : Bool}) -> {Tl.all_eq(Tl.Sess.sent(Tl.run(es, Tl.Sess{r, d, x})), r) == True{} : Bool}:
  match es:
    case Nil{}:
      h
    case +e <> rest:
      match e:
        case Tl.Join{+t}:
          pl.sent_go(rest, r, List.append(&2, Nat, d, [t]), x, h)
        case Tl.Quit{+t}:
          pl.sent_go(rest, r, Tl.drop(d, t), x, h)
        case Tl.Turn{}:
          pl.sent_go(rest, r, d, List.append(&2, List<&2, Nat>, x, [r]), pl.all_snoc(x, r, h))

def pl.roster_sent_fixed(es: List<&2, Tl.Ev>, +r: List<&2, Nat>, d: List<&2, Nat>) -> {Tl.all_eq(Tl.Sess.sent(Tl.run(es, Tl.Sess{r, d, Nil{}})), r) == True{} : Bool}:
  pl.sent_go(es, r, d, Nil{}, {==})

def pl.elem_snoc(d: List<&2, Nat>, +t: Nat) -> {Tl.elem(List.append(&2, Nat, d, [t]), t) == True{} : Bool}:
  match d:
    case Nil{}:
      %pl.eq_refl(t) : {Bool.or(_, False{}) == True{} : Bool}
      {==}
    case +y <> +rest:
      pl.or_tr(Nat.is_eq(y, t), Tl.elem(List.append(&2, Nat, rest, [t]), t), pl.elem_snoc(rest, t))

def pl.dyn_reaches_joined(+s: Tl.Sess, +t: Nat) -> {Tl.dyn_call(Tl.step(s, Tl.Join{t}), t) == True{} : Bool}:
  match s:
    case Tl.Sess{r, d, x}:
      pl.elem_snoc(d, t)

# a drop leaves no copy of t; hit is the head test
def pl.drop_go(xs: List<&2, Nat>, +t: Nat, hit: Bool, e: {Tl.is.at(xs, t) == hit : Bool}) -> {Tl.elem(Tl.drop.go(xs, t, hit), t) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> +rest:
      match hit:
        case True{}:
          pl.drop_go(rest, t, Tl.is.at(rest, t), {==})
        case False{}:
          %Equal.sym(Bool, Nat.is_eq(y, t), False{}, e) : {Bool.or(_, Tl.elem(Tl.drop.go(rest, t, Tl.is.at(rest, t)), t)) == False{} : Bool}
          pl.drop_go(rest, t, Tl.is.at(rest, t), {==})

def pl.dyn_drops_quit(+s: Tl.Sess, +t: Nat) -> {Tl.dyn_call(Tl.step(s, Tl.Quit{t}), t) == False{} : Bool}:
  match s:
    case Tl.Sess{r, +d, x}:
      pl.drop_go(d, t, Tl.is.at(d, t), {==})

# 2. The schema
# -------------

def pl.add_has(b: Bool, +ps: List<&2, Nat>, e: {Tl.elem(ps, Tl.intent()) == b : Bool}) -> {Tl.elem(Tl.add_intent(b, ps), Tl.intent()) == True{} : Bool}:
  match b:
    case True{}:
      e
    case False{}:
      {==}

def pl.schema_has_intent(s: Tl.Schema) -> {Tl.elem(Tl.Schema.params(Tl.build(s)), Tl.intent()) == True{} : Bool}:
  match s:
    case Tl.Schema{+ps, v}:
      pl.add_has(Tl.elem(ps, Tl.intent()), ps, {==})

def pl.ver(v: Nat) -> {Nat.is_le(1n, Nat.max(v, 1n)) == True{} : Bool}:
  match v:
    case 0n:
      {==}
    case 1n+p:
      pl.le0(Nat.max(p, 0n))

def pl.schema_versioned(s: Tl.Schema) -> {Nat.is_le(1n, Tl.Schema.version(Tl.build(s))) == True{} : Bool}:
  match s:
    case Tl.Schema{ps, v}:
      pl.ver(v)

def pl.keep(b: Bool, +ps: List<&2, Nat>, +x: Nat, has: {Tl.elem(ps, x) == True{} : Bool}) -> {Tl.elem(Tl.add_intent(b, ps), x) == True{} : Bool}:
  match b:
    case True{}:
      has
    case False{}:
      pl.or_tr(Nat.is_eq(Tl.intent(), x), Tl.elem(ps, x), has)

def pl.schema_keeps_params(+s: Tl.Schema, +x: Nat, has: {Tl.elem(Tl.Schema.params(s), x) == True{} : Bool}) -> {Tl.elem(Tl.Schema.params(Tl.build(s)), x) == True{} : Bool}:
  match s:
    case Tl.Schema{+ps, v}:
      pl.keep(Tl.elem(ps, Tl.intent()), ps, x, has)

def pl.max0(p: Nat) -> {Nat.max(p, 0n) == Nat.max(Nat.max(p, 0n), 0n) : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      {==}

def pl.max1(v: Nat) -> {Nat.max(v, 1n) == Nat.max(Nat.max(v, 1n), 1n) : Nat}:
  match v:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.max(p, 0n), Nat.max(Nat.max(p, 0n), 0n), pl.max0(p))

def pl.schema_build_idempotent(+s: Tl.Schema) -> {Tl.build(Tl.build(s)) == Tl.build(s) : Tl.Schema}:
  match s:
    case Tl.Schema{+ps, +v}:
      +p = Tl.add_intent(Tl.elem(ps, Tl.intent()), ps)
      %Equal.sym(Bool, Tl.elem(p, Tl.intent()), True{}, pl.add_has(Tl.elem(ps, Tl.intent()), ps, {==})) : {Tl.Schema{Tl.add_intent(_, p), Nat.max(Nat.max(v, 1n), 1n)} == Tl.Schema{p, Nat.max(v, 1n)} : Tl.Schema}
      %pl.max1(v) : {Tl.Schema{Tl.add_intent(True{}, p), _} == Tl.Schema{p, Nat.max(v, 1n)} : Tl.Schema}
      {==}

# 3. A path
# ---------

def pl.len(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case y <> rest:
      1n+pl.len(rest)

# a walk that goes above its root, from the names at, is None
def pl.esc(segs: List<&2, Tl.Seg>, at: List<&2, Nat>, h: {Tl.stays(segs, pl.len(at)) == False{} : Bool}) -> {Tl.walk(segs, at) == None{} : Maybe<&2, List<&2, Nat>>}:
  match segs:
    case Nil{}:
      pl.absurd({Tl.walk(Nil{}, at) == None{} : Maybe<&2, List<&2, Nat>>}, h)
    case s <> rest:
      match s:
        case Tl.Name{n}:
          pl.esc(rest, n <> at, h)
        case Tl.Here{}:
          pl.esc(rest, at, h)
        case Tl.Up{}:
          match at:
            case Nil{}:
              {==}
            case a <> above:
              pl.esc(rest, above, h)

def pl.path_rejects_escape(+segs: List<&2, Tl.Seg>, out: {Tl.stays(segs, 0n) == False{} : Bool}) -> {Tl.resolve(segs) == None{} : Maybe<&2, List<&2, Nat>>}:
  pl.esc(segs, Nil{}, out)

# a walk that stays under its root, from the names at, is Some
def pl.ins(segs: List<&2, Tl.Seg>, at: List<&2, Nat>, h: {Tl.stays(segs, pl.len(at)) == True{} : Bool}) -> {Maybe.is_some(&2, List<&2, Nat>, Tl.walk(segs, at)) == True{} : Bool}:
  match segs:
    case Nil{}:
      {==}
    case s <> rest:
      match s:
        case Tl.Name{n}:
          pl.ins(rest, n <> at, h)
        case Tl.Here{}:
          pl.ins(rest, at, h)
        case Tl.Up{}:
          match at:
            case Nil{}:
              pl.absurdF({Maybe.is_some(&2, List<&2, Nat>, Tl.walk(Tl.Up{} <> rest, Nil{})) == True{} : Bool}, h)
            case a <> above:
              pl.ins(rest, above, h)

def pl.path_resolves_inside(+segs: List<&2, Tl.Seg>, inside: {Tl.stays(segs, 0n) == True{} : Bool}) -> {Maybe.is_some(&2, List<&2, Nat>, Tl.resolve(segs)) == True{} : Bool}:
  pl.ins(segs, Nil{}, inside)

# 4. The approval gate
# --------------------

def pl.steps_add(+s: Tl.Step, r: Tl.Ran) -> {s <> Tl.Ran.steps(r) == Tl.Ran.steps(Tl.ran.add(s, r)) : List<&2, Tl.Step>}:
  match r:
    case Tl.Ran{ss, e}:
      {==}

def pl.fin_add(+s: Tl.Step, r: Tl.Ran, h: {Tl.End.finished(Tl.Ran.end(Tl.ran.add(s, r))) == True{} : Bool}) -> {Tl.End.finished(Tl.Ran.end(r)) == True{} : Bool}:
  match r:
    case Tl.Ran{ss, e}:
      h

# a denied step runs nothing
def pl.gate_no(s: Tl.Step, r: Tl.Ran) -> {Nil{} == Tl.Ran.steps(Tl.gate(False{}, s, r)) : List<&2, Tl.Step>}:
  match s:
    case Tl.Step{i, f}:
      {==}

def pl.gate_den(s: Tl.Step, r: Tl.Ran) -> {Tl.gate(False{}, s, r) == Tl.Ran{Nil{}, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}:
  match s:
    case Tl.Step{i, f}:
      {==}

def pl.gate_no_fin(-A: Type, s: Tl.Step, r: Tl.Ran, h: {Tl.End.finished(Tl.Ran.end(Tl.gate(False{}, s, r))) == True{} : Bool}) -> A:
  match s:
    case Tl.Step{i, f}:
      pl.absurdF(A, h)

def pl.step_refl(s: Tl.Step) -> {Tl.step.eq(s, s) == True{} : Bool}:
  match s:
    case Tl.Step{+i, +f}:
      %pl.eq_refl(i) : {Bool.and(_, Nat.is_eq(Tl.Eff.code(f), Tl.Eff.code(f))) == True{} : Bool}
      %pl.eq_refl(Tl.Eff.code(f)) : {Bool.and(True{}, _) == True{} : Bool}
      {==}

def pl.prefix_cons(+s: Tl.Step, xs: List<&2, Tl.Step>, ys: List<&2, Tl.Step>, h: {Tl.prefix(xs, ys) == True{} : Bool}) -> {Tl.prefix(s <> xs, s <> ys) == True{} : Bool}:
  %Equal.sym(Bool, Tl.step.eq(s, s), True{}, pl.step_refl(s)) : {Bool.and(_, Tl.prefix(xs, ys)) == True{} : Bool}
  h

# what ran is a prefix of the script, at any head test
def pl.prefix_go(ss: List<&2, Tl.Step>, +auto: List<&2, Nat>, free: Bool, +ans: List<&2, Bool>) -> {Tl.prefix(Tl.Ran.steps(Tl.exec.go(ss, auto, free, ans)), ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +rest:
      match free:
        case True{}:
          %pl.steps_add(s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), ans)) : {Tl.prefix(_, s <> rest) == True{} : Bool}
          pl.prefix_cons(s, Tl.Ran.steps(Tl.exec.go(rest, auto, Tl.free.at(rest, auto), ans)), rest, pl.prefix_go(rest, auto, Tl.free.at(rest, auto), ans))
        case False{}:
          match ans:
            case Nil{}:
              %pl.gate_no(s, Tl.Ran{Nil{}, Tl.Finished{}}) : {Tl.prefix(_, s <> rest) == True{} : Bool}
              {==}
            case +a <> +more:
              match a:
                case True{}:
                  %pl.steps_add(s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), more)) : {Tl.prefix(_, s <> rest) == True{} : Bool}
                  pl.prefix_cons(s, Tl.Ran.steps(Tl.exec.go(rest, auto, Tl.free.at(rest, auto), more)), rest, pl.prefix_go(rest, auto, Tl.free.at(rest, auto), more))
                case False{}:
                  %pl.gate_no(s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), more)) : {Tl.prefix(_, s <> rest) == True{} : Bool}
                  {==}

def pl.gate_prefix(+ss: List<&2, Tl.Step>, +auto: List<&2, Nat>, ans: List<&2, Bool>) -> {Tl.prefix(Tl.Ran.steps(Tl.exec(ss, auto, ans)), ss) == True{} : Bool}:
  pl.prefix_go(ss, auto, Tl.free.at(ss, auto), ans)

# every gated step that ran used one approval; free is the head test
def pl.yes_go(ss: List<&2, Tl.Step>, +auto: List<&2, Nat>, free: Bool, +ans: List<&2, Bool>, e: {Tl.free.at(ss, auto) == free : Bool}) -> {Nat.is_le(Tl.gated(Tl.Ran.steps(Tl.exec.go(ss, auto, free, ans)), auto), Tl.yeses(ans)) == True{} : Bool}:
  match ss:
    case Nil{}:
      pl.le0(Tl.yeses(ans))
    case +s <> +rest:
      match free:
        case True{}:
          %pl.steps_add(s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), ans)) : {Nat.is_le(Tl.gated(_, auto), Tl.yeses(ans)) == True{} : Bool}
          %Equal.sym(Bool, Tl.auto.at(auto, s), True{}, e) : {Nat.is_le(Nat.add(Tl.gated.one(_), Tl.gated(Tl.Ran.steps(Tl.exec.go(rest, auto, Tl.free.at(rest, auto), ans)), auto)), Tl.yeses(ans)) == True{} : Bool}
          pl.yes_go(rest, auto, Tl.free.at(rest, auto), ans, {==})
        case False{}:
          match ans:
            case Nil{}:
              %pl.gate_no(s, Tl.Ran{Nil{}, Tl.Finished{}}) : {Nat.is_le(Tl.gated(_, auto), Tl.yeses(Nil{})) == True{} : Bool}
              {==}
            case +a <> +more:
              match a:
                case True{}:
                  %pl.steps_add(s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), more)) : {Nat.is_le(Tl.gated(_, auto), Tl.yeses(True{} <> more)) == True{} : Bool}
                  %Equal.sym(Bool, Tl.auto.at(auto, s), False{}, e) : {Nat.is_le(Nat.add(Tl.gated.one(_), Tl.gated(Tl.Ran.steps(Tl.exec.go(rest, auto, Tl.free.at(rest, auto), more)), auto)), Tl.yeses(True{} <> more)) == True{} : Bool}
                  pl.yes_go(rest, auto, Tl.free.at(rest, auto), more, {==})
                case False{}:
                  %pl.gate_no(s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), more)) : {Nat.is_le(Tl.gated(_, auto), Tl.yeses(False{} <> more)) == True{} : Bool}
                  pl.le0(Tl.yeses(more))

def pl.gate_needs_yes(+ss: List<&2, Tl.Step>, +auto: List<&2, Nat>, +ans: List<&2, Bool>) -> {Nat.is_le(Tl.gated(Tl.Ran.steps(Tl.exec(ss, auto, ans)), auto), Tl.yeses(ans)) == True{} : Bool}:
  pl.yes_go(ss, auto, Tl.free.at(ss, auto), ans, {==})

# a free head adds no gated step
def pl.one_zero(b: Bool, -g: Nat, h: {Nat.add(Tl.gated.one(b), g) == 0n : Nat}, hb: {b == True{} : Bool}) -> {g == 0n : Nat}:
  match b:
    case True{}:
      h
    case False{}:
      pl.absurdF({g == 0n : Nat}, hb)

# a held head adds a gated step
def pl.one_nz(-A: Type, b: Bool, -g: Nat, h: {Nat.add(Tl.gated.one(b), g) == 0n : Nat}, hb: {b == False{} : Bool}) -> A:
  match b:
    case True{}:
      pl.absurd(A, hb)
    case False{}:
      %h : pl.ND(_, A, Unit)
      Unit{}

# free steps run through to the held step s, which a denial stops
def pl.deny_go(pre: List<&2, Tl.Step>, +s: Tl.Step, +post: List<&2, Tl.Step>, +auto: List<&2, Nat>, +ans: List<&2, Bool>, free: Bool, e: {Tl.free.at(List.append(&2, Tl.Step, pre, s <> post), auto) == free : Bool}, gf: {Tl.gated(pre, auto) == 0n : Nat}, held: {Tl.auto.at(auto, s) == False{} : Bool}) -> {Tl.exec.go(List.append(&2, Tl.Step, pre, s <> post), auto, free, False{} <> ans) == Tl.Ran{pre, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}:
  match pre:
    case Nil{}:
      match free:
        case True{}:
          pl.absurd({Tl.exec.go(s <> post, auto, True{}, False{} <> ans) == Tl.Ran{Nil{}, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}, Equal.trans(Bool, True{}, Tl.auto.at(auto, s), False{}, Equal.sym(Bool, Tl.auto.at(auto, s), True{}, e), held))
        case False{}:
          pl.gate_den(s, Tl.exec.go(post, auto, Tl.free.at(post, auto), ans))
    case +p <> +prest:
      match free:
        case True{}:
          Equal.cong(Tl.Ran, Tl.Ran, r => Tl.ran.add(p, r), Tl.exec.go(List.append(&2, Tl.Step, prest, s <> post), auto, Tl.free.at(List.append(&2, Tl.Step, prest, s <> post), auto), False{} <> ans), Tl.Ran{prest, Tl.Denied{Tl.Step.id(s)}}, pl.deny_go(prest, s, post, auto, ans, Tl.free.at(List.append(&2, Tl.Step, prest, s <> post), auto), {==}, pl.one_zero(Tl.auto.at(auto, p), Tl.gated(prest, auto), gf, e), held))
        case False{}:
          pl.one_nz({Tl.exec.go(p <> List.append(&2, Tl.Step, prest, s <> post), auto, False{}, False{} <> ans) == Tl.Ran{p <> prest, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}, Tl.auto.at(auto, p), Tl.gated(prest, auto), gf, e)

def pl.gate_deny_stops(+pre: List<&2, Tl.Step>, +s: Tl.Step, +post: List<&2, Tl.Step>, +auto: List<&2, Nat>, ans: List<&2, Bool>, free: {Tl.gated(pre, auto) == 0n : Nat}, held: {Tl.auto.at(auto, s) == False{} : Bool}) -> {Tl.exec(List.append(&2, Tl.Step, pre, s <> post), auto, False{} <> ans) == Tl.Ran{pre, Tl.Denied{Tl.Step.id(s)}} : Tl.Ran}:
  pl.deny_go(pre, s, post, auto, ans, Tl.free.at(List.append(&2, Tl.Step, pre, s <> post), auto), {==}, free, held)

# a run that finished ran every step, at any head test
def pl.fin_go(ss: List<&2, Tl.Step>, +auto: List<&2, Nat>, free: Bool, +ans: List<&2, Bool>, h: {Tl.End.finished(Tl.Ran.end(Tl.exec.go(ss, auto, free, ans))) == True{} : Bool}) -> {Tl.Ran.steps(Tl.exec.go(ss, auto, free, ans)) == ss : List<&2, Tl.Step>}:
  match ss:
    case Nil{}:
      {==}
    case +s <> +rest:
      match free:
        case True{}:
          %pl.steps_add(s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), ans)) : {_ == s <> rest : List<&2, Tl.Step>}
          Equal.cong(List<&2, Tl.Step>, List<&2, Tl.Step>, xs => s <> xs, Tl.Ran.steps(Tl.exec.go(rest, auto, Tl.free.at(rest, auto), ans)), rest, pl.fin_go(rest, auto, Tl.free.at(rest, auto), ans, pl.fin_add(s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), ans), h)))
        case False{}:
          match ans:
            case Nil{}:
              pl.gate_no_fin({Tl.Ran.steps(Tl.gate(False{}, s, Tl.Ran{Nil{}, Tl.Finished{}})) == s <> rest : List<&2, Tl.Step>}, s, Tl.Ran{Nil{}, Tl.Finished{}}, h)
            case +a <> +more:
              match a:
                case True{}:
                  %pl.steps_add(s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), more)) : {_ == s <> rest : List<&2, Tl.Step>}
                  Equal.cong(List<&2, Tl.Step>, List<&2, Tl.Step>, xs => s <> xs, Tl.Ran.steps(Tl.exec.go(rest, auto, Tl.free.at(rest, auto), more)), rest, pl.fin_go(rest, auto, Tl.free.at(rest, auto), more, pl.fin_add(s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), more), h)))
                case False{}:
                  pl.gate_no_fin({Tl.Ran.steps(Tl.gate(False{}, s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), more))) == s <> rest : List<&2, Tl.Step>}, s, Tl.exec.go(rest, auto, Tl.free.at(rest, auto), more), h)

def pl.gate_finish_runs_all(+ss: List<&2, Tl.Step>, +auto: List<&2, Nat>, +ans: List<&2, Bool>, fin: {Tl.End.finished(Tl.Ran.end(Tl.exec(ss, auto, ans))) == True{} : Bool}) -> {Tl.Ran.steps(Tl.exec(ss, auto, ans)) == ss : List<&2, Tl.Step>}:
  pl.fin_go(ss, auto, Tl.free.at(ss, auto), ans, fin)
