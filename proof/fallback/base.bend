# eukhe: lemmas shared by the proofs of area fallback: the model's
# membership and keep are the spec's; the first untried candidate of a
# list whose head is tried; no untried candidate; a request's Nats cut
# back into its candidates and tried models

import Base
import ../../bend/fallback.bend as Fb
import ../../bend/ffi_fallback.bend as FFb
import ../../laws/fallback.bend as Fallback
import ../base/logic/bool.bend as LLogicBool
import ../base/staging.bend as LStg

# The choice
# ----------

# the model's sameness is Nat equality
def fbb.same_eq(a: Nat, b: Nat) -> {Fb.same(a, b) == Nat.is_eq(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      fbb.same_eq(p, q)

# the model's membership is the spec's
def fbb.has_in(+m: Nat, xs: List<&2, Nat>) -> {Fb.tried_has(m, xs) == Fallback.fb_in(m, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %fbb.same_eq(m, x) : {Bool.or(Fb.same(m, x), Fb.tried_has(m, t)) == Bool.or(_, Fallback.fb_in(m, t)) : Bool}
      %fbb.has_in(m, t) : {Bool.or(Fb.same(m, x), Fb.tried_has(m, t)) == Bool.or(Fb.same(m, x), _) : Bool}
      {==}

# membership turned around: rewrites the model's into the spec's
def fbb.in_has(+m: Nat, +xs: List<&2, Nat>) -> {Fallback.fb_in(m, xs) == Fb.tried_has(m, xs) : Bool}:
  Equal.sym(Bool, Fb.tried_has(m, xs), Fallback.fb_in(m, xs), fbb.has_in(m, xs))

# a failure the spec does not keep the model does not keep
def fbb.not_kept(k: Fb.Why, hk: {Fallback.fb_keeps(k) == False{} : Bool}) -> {Fb.kept(k) == False{} : Bool}:
  match k:
    case Fb.Failed{n, retries}:
      hk
    case Fb.Login{}:
      {==}
    case Fb.Quota{until}:
      {==}
    case Fb.Unset{}:
      {==}

# the run past a keep: the next step (turned around: rewrites the choice
# into it)
def fbb.past_keep(+k: Fb.Why, +cands: List<&2, Nat>, +tried: List<&2, Nat>, hk: {Fallback.fb_keeps(k) == False{} : Bool}) -> {Fb.next(cands, tried, k) == Fb.choose(Fb.In{k, cands, tried}) : Fb.Choice}:
  %Equal.sym(Bool, Fb.kept(k), False{}, fbb.not_kept(k, hk)) : {Fb.next(cands, tried, k) == Fb.choose.if(k, cands, tried, _) : Fb.Choice}
  {==}

# with every candidate tried there is no first untried one
def fbb.first_none(cands: List<&2, Nat>, +tried: List<&2, Nat>, +h: {Fallback.fb_all_in(cands, tried) == True{} : Bool}) -> {Fb.first(cands, tried) == None{} : Maybe<&2, Nat>}:
  match cands:
    case Nil{}:
      {==}
    case +c <> +t:
      +hc = LLogicBool.wr_and_l(Fallback.fb_in(c, tried), Fallback.fb_all_in(t, tried), h)
      +ht = LLogicBool.wr_and_r(Fallback.fb_in(c, tried), Fallback.fb_all_in(t, tried), h)
      %fbb.in_has(c, tried) : {Fb.pick(c, _, Fb.first(t, tried)) == None{} : Maybe<&2, Nat>}
      %Equal.sym(Bool, Fallback.fb_in(c, tried), True{}, hc) : {Fb.pick(c, _, Fb.first(t, tried)) == None{} : Maybe<&2, Nat>}
      fbb.first_none(t, tried, ht)

# after tried candidates p, the untried c is the first untried one
def fbb.first_after(p: List<&2, Nat>, +c: Nat, +rest: List<&2, Nat>, +tried: List<&2, Nat>, +hp: {Fallback.fb_all_in(p, tried) == True{} : Bool}, hc: {Fallback.fb_in(c, tried) == False{} : Bool}) -> {Fb.first(List.append(&2, Nat, p, c <> rest), tried) == Some{c} : Maybe<&2, Nat>}:
  match p:
    case Nil{}:
      %fbb.in_has(c, tried) : {Fb.pick(c, _, Fb.first(rest, tried)) == Some{c} : Maybe<&2, Nat>}
      %Equal.sym(Bool, Fallback.fb_in(c, tried), False{}, hc) : {Fb.pick(c, _, Fb.first(rest, tried)) == Some{c} : Maybe<&2, Nat>}
      {==}
    case +x <> +t:
      +hx = LLogicBool.wr_and_l(Fallback.fb_in(x, tried), Fallback.fb_all_in(t, tried), hp)
      +ht = LLogicBool.wr_and_r(Fallback.fb_in(x, tried), Fallback.fb_all_in(t, tried), hp)
      %fbb.in_has(x, tried) : {Fb.pick(x, _, Fb.first(List.append(&2, Nat, t, c <> rest), tried)) == Some{c} : Maybe<&2, Nat>}
      %Equal.sym(Bool, Fallback.fb_in(x, tried), True{}, hx) : {Fb.pick(x, _, Fb.first(List.append(&2, Nat, t, c <> rest), tried)) == Some{c} : Maybe<&2, Nat>}
      fbb.first_after(t, c, rest, tried, ht, hc)

# with no candidate left, every failure but a usage limit ends
def fbb.none_ends(k: Fb.Why, hq: {Fallback.fb_quota(k) == False{} : Bool}) -> {Fb.none_left(k) == Fb.End{} : Fb.Choice}:
  match k:
    case Fb.Failed{n, retries}:
      {==}
    case Fb.Login{}:
      {==}
    case Fb.Quota{until}:
      LStg.stg.absurd({Fb.Hold{until} == Fb.End{} : Fb.Choice}, hq)
    case Fb.Unset{}:
      {==}

# The wire
# --------

# the reply's spelling is the spec's
def fbb.reply(c: Fb.Choice) -> {FFb.put_choice(c) == Fallback.fb_reply(c) : String}:
  match c:
    case Fb.Keep{}:
      {==}
    case Fb.Switch{m}:
      {==}
    case Fb.Hold{until}:
      {==}
    case Fb.End{}:
      {==}

# a list cut after its first count items reads back as the two parts
def fbb.split_app(c: List<&2, Nat>, +t: List<&2, Nat>) -> {FFb.split(List.length(&2, Nat, c), List.append(&2, Nat, c, t)) == Some{FFb.Parts{c, t}} : Maybe<&2, FFb.Parts>}:
  match c:
    case Nil{}:
      {==}
    case +x <> +u:
      %fbb.split_app(u, t) : {FFb.split.cons(x, FFb.split(List.length(&2, Nat, u), List.append(&2, Nat, u, t))) == FFb.split.cons(x, _) : Maybe<&2, FFb.Parts>}
      {==}

# what a cut answers: none, or two parts whose count and Nats are n, t
def fbb.SP(+n: Nat, +t: List<&2, Nat>, r: Maybe<&2, FFb.Parts>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{q}:
      match q:
        case FFb.Parts{a, b}:
          {n <> t == List.length(&2, Nat, a) <> List.append(&2, Nat, a, b) : List<&2, Nat>}

# a count, then a Nat: the count one up, then x, then the Nats
def fbb.bump(+x: Nat, ys: List<&2, Nat>) -> List<&2, Nat>:
  match ys:
    case Nil{}:
      []
    case h <> tl:
      (1n+h) <> x <> tl

def fbb.cons_sp(+p: Nat, +x: Nat, +u: List<&2, Nat>, r: Maybe<&2, FFb.Parts>, v: fbb.SP(p, u, r)) -> fbb.SP(1n+p, x <> u, FFb.split.cons(x, r)):
  match r:
    case None{}:
      Unit{}
    case Some{q}:
      match q:
        case FFb.Parts{+a, +b}:
          Equal.cong(List<&2, Nat>, List<&2, Nat>, z => fbb.bump(x, z), p <> u, List.length(&2, Nat, a) <> List.append(&2, Nat, a, b), v)

# every cut is exact: its parts spell the count and the Nats it cut
def fbb.split_sp(+n: Nat, t: List<&2, Nat>) -> fbb.SP(n, t, FFb.split(n, t)):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match t:
        case Nil{}:
          Unit{}
        case +x <> +u:
          fbb.cons_sp(p, x, u, FFb.split(p, u), fbb.split_sp(p, u))

# what a parse answers: none, or a request whose Nats are xs
def fbb.PX(+xs: List<&2, Nat>, r: Maybe<&2, Fb.In>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{x}:
      {xs == Fallback.fb_nats(x) : List<&2, Nat>}

def fbb.cut_px(+w: Fb.Why, +n: Nat, +u: List<&2, Nat>, r: Maybe<&2, FFb.Parts>, v: fbb.SP(n, u, r)) -> fbb.PX(Fallback.fb_why_nats(w, n <> u), FFb.parse.cut(w, r)):
  match r:
    case None{}:
      Unit{}
    case Some{q}:
      match q:
        case FFb.Parts{+a, +b}:
          Equal.cong(List<&2, Nat>, List<&2, Nat>, z => Fallback.fb_why_nats(w, z), n <> u, List.length(&2, Nat, a) <> List.append(&2, Nat, a, b), v)

# the candidates and the tried models parse back exactly
def fbb.lists_px(+w: Fb.Why, t: List<&2, Nat>) -> fbb.PX(Fallback.fb_why_nats(w, t), FFb.parse.lists(w, t)):
  match t:
    case Nil{}:
      Unit{}
    case +n <> +u:
      fbb.cut_px(w, n, u, FFb.split(n, u), fbb.split_sp(n, u))

def fbb.failed_px(t: List<&2, Nat>) -> fbb.PX(0n <> t, FFb.parse.failed(t)):
  match t:
    case Nil{}:
      Unit{}
    case +n <> t2:
      match t2:
        case Nil{}:
          Unit{}
        case +r <> +u:
          fbb.lists_px(Fb.Failed{n, r}, u)

def fbb.quota_px(t: List<&2, Nat>) -> fbb.PX(2n <> t, FFb.parse.quota(t)):
  match t:
    case Nil{}:
      Unit{}
    case +until <> +u:
      fbb.lists_px(Fb.Quota{until}, u)

def fbb.kind_px(k: Nat, +t: List<&2, Nat>) -> fbb.PX(k <> t, FFb.parse.kind(k, t)):
  match k:
    case 0n:
      fbb.failed_px(t)
    case 1n:
      fbb.lists_px(Fb.Login{}, t)
    case 2n:
      fbb.quota_px(t)
    case 3n:
      fbb.lists_px(Fb.Unset{}, t)
    case 4n+q:
      Unit{}

# every parse is exact: a request it answers is spelled by the Nats it read
def fbb.parse_px(xs: List<&2, Nat>) -> fbb.PX(xs, FFb.parse(xs)):
  match xs:
    case Nil{}:
      Unit{}
    case +k <> +t:
      fbb.kind_px(k, t)
