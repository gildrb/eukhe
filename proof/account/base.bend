# eukhe: lemmas shared by the proofs of area account: the model's
# usability is the spec's; the first usable account after unusable ones;
# no usable account when every one is limited past now or dead; the
# earliest limit after later ones; the model's wait is the spec's; no
# login left when every login is dead; the reply's spelling is the
# spec's; a request's Nats cut back into its marks

import Base
import ../../bend/account.bend as Ac
import ../../bend/ffi_account.bend as FAc
import ../../laws/account.bend as Account
import ../base/nat.bend as LNat
import ../base/staging.bend as LStg

# Numbers
# -------

# not a < b is b <= a
def acb.nlt_le(a: Nat, b: Nat) -> {Bool.not(Nat.is_lt(a, b)) == Nat.is_le(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      acb.nlt_le(p, q)

# a < b <= c: a < c
def acb.lt_le(a: Nat, b: Nat, c: Nat, ab: {Nat.is_lt(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n r:
      LStg.stg.absurdF({Nat.is_lt(0n, r) == True{} : Bool}, ab)
    case 0n 1n+q 0n:
      LStg.stg.absurdF({False{} == True{} : Bool}, bc)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n r:
      LStg.stg.absurdF({Nat.is_lt(1n+p, r) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      LStg.stg.absurdF({False{} == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      acb.lt_le(p, q, r, ab, bc)

# not not b: b
def acb.not_not(b: Bool, h: {Bool.not(Bool.not(b)) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      LStg.stg.absurdF({False{} == True{} : Bool}, h)

# The first usable account
# ------------------------

# an account the spec finds usable the model does
def acb.usable(+now: Nat, m: Ac.Mark, h: {Account.ac_usable(now, m) == True{} : Bool}) -> {Ac.free(now, m) == True{} : Bool}:
  match m:
    case Ac.Free{}:
      {==}
    case Ac.Until{+t}:
      %acb.nlt_le(now, t) : {_ == True{} : Bool}
      h
    case Ac.Dead{}:
      LStg.stg.absurdF({False{} == True{} : Bool}, h)

# an account the spec finds unusable the model does not use
def acb.unusable(+now: Nat, m: Ac.Mark, h: {Bool.not(Account.ac_usable(now, m)) == True{} : Bool}) -> {Ac.free(now, m) == False{} : Bool}:
  match m:
    case Ac.Free{}:
      LStg.stg.absurdF({True{} == False{} : Bool}, h)
    case Ac.Until{+t}:
      LNat.pc.lt_not_le(now, t, acb.not_not(Nat.is_lt(now, t), h))
    case Ac.Dead{}:
      {==}

# after accounts p none of which can serve, the usable m is the first
# usable one, at the place the length of p
def acb.first_at(+now: Nat, p: List<&2, Ac.Mark>, +m: Ac.Mark, +rest: List<&2, Ac.Mark>, +hp: {Account.ac_none_usable(now, p) == True{} : Bool}, hm: {Account.ac_usable(now, m) == True{} : Bool}) -> {Ac.first(now, List.append(&2, Ac.Mark, p, m <> rest)) == Some{List.length(&2, Ac.Mark, p)} : Maybe<&2, Nat>}:
  match p:
    case Nil{}:
      %Equal.sym(Bool, Ac.free(now, m), True{}, acb.usable(now, m, hm)) : {Ac.first.of(_, Ac.first(now, rest)) == Some{0n} : Maybe<&2, Nat>}
      {==}
    case +x <> +t:
      +hx = LStg.stg.and_l(Bool.not(Account.ac_usable(now, x)), Account.ac_none_usable(now, t), hp)
      +ht = LStg.stg.and_r(Bool.not(Account.ac_usable(now, x)), Account.ac_none_usable(now, t), hp)
      %Equal.sym(Bool, Ac.free(now, x), False{}, acb.unusable(now, x, hx)) : {Ac.first.of(_, Ac.first(now, List.append(&2, Ac.Mark, t, m <> rest))) == Some{1n+List.length(&2, Ac.Mark, t)} : Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Nat>, Ac.first(now, List.append(&2, Ac.Mark, t, m <> rest)), Some{List.length(&2, Ac.Mark, t)}, acb.first_at(now, t, m, rest, ht, hm)) : {Ac.first.of(False{}, _) == Some{1n+List.length(&2, Ac.Mark, t)} : Maybe<&2, Nat>}
      {==}

# No usable account
# -----------------

# accounts dead or limited until e or later, e past now: none is usable
def acb.first_none_from(+now: Nat, +e: Nat, ms: List<&2, Ac.Mark>, +he: {Nat.is_lt(now, e) == True{} : Bool}, +h: {Account.ac_all_from(e, ms) == True{} : Bool}) -> {Ac.first(now, ms) == None{} : Maybe<&2, Nat>}:
  match ms:
    case Nil{}:
      {==}
    case m <> +t:
      match m:
        case Ac.Free{}:
          LStg.stg.absurdF({Ac.first(now, Ac.Free{} <> t) == None{} : Maybe<&2, Nat>}, h)
        case Ac.Until{+u}:
          +hu = LStg.stg.and_l(Nat.is_le(e, u), Account.ac_all_from(e, t), h)
          +ht = LStg.stg.and_r(Nat.is_le(e, u), Account.ac_all_from(e, t), h)
          %Equal.sym(Bool, Nat.is_le(u, now), False{}, LNat.pc.lt_not_le(now, u, acb.lt_le(now, e, u, he, hu))) : {Ac.first.of(_, Ac.first(now, t)) == None{} : Maybe<&2, Nat>}
          %Equal.sym(Maybe<&2, Nat>, Ac.first(now, t), None{}, acb.first_none_from(now, e, t, he, ht)) : {Ac.first.of(False{}, _) == None{} : Maybe<&2, Nat>}
          {==}
        case Ac.Dead{}:
          %Equal.sym(Maybe<&2, Nat>, Ac.first(now, t), None{}, acb.first_none_from(now, e, t, he, h)) : {Ac.first.of(False{}, _) == None{} : Maybe<&2, Nat>}
          {==}

# accounts p dead or limited past e, then one limited until e (past now),
# then ones dead or limited until e or later: none is usable
def acb.first_none_at(+now: Nat, p: List<&2, Ac.Mark>, +e: Nat, +rest: List<&2, Ac.Mark>, +he: {Nat.is_lt(now, e) == True{} : Bool}, +hp: {Account.ac_all_after(e, p) == True{} : Bool}, +hr: {Account.ac_all_from(e, rest) == True{} : Bool}) -> {Ac.first(now, List.append(&2, Ac.Mark, p, Ac.Until{e} <> rest)) == None{} : Maybe<&2, Nat>}:
  match p:
    case Nil{}:
      %Equal.sym(Bool, Nat.is_le(e, now), False{}, LNat.pc.lt_not_le(now, e, he)) : {Ac.first.of(_, Ac.first(now, rest)) == None{} : Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Nat>, Ac.first(now, rest), None{}, acb.first_none_from(now, e, rest, he, hr)) : {Ac.first.of(False{}, _) == None{} : Maybe<&2, Nat>}
      {==}
    case x <> +t:
      match x:
        case Ac.Free{}:
          LStg.stg.absurdF({Ac.first(now, Ac.Free{} <> List.append(&2, Ac.Mark, t, Ac.Until{e} <> rest)) == None{} : Maybe<&2, Nat>}, hp)
        case Ac.Until{+u}:
          +hu = LStg.stg.and_l(Nat.is_lt(e, u), Account.ac_all_after(e, t), hp)
          +ht = LStg.stg.and_r(Nat.is_lt(e, u), Account.ac_all_after(e, t), hp)
          %Equal.sym(Bool, Nat.is_le(u, now), False{}, LNat.pc.lt_not_le(now, u, acb.lt_le(now, e, u, he, LNat.pc.lt_to_le(e, u, hu)))) : {Ac.first.of(_, Ac.first(now, List.append(&2, Ac.Mark, t, Ac.Until{e} <> rest))) == None{} : Maybe<&2, Nat>}
          %Equal.sym(Maybe<&2, Nat>, Ac.first(now, List.append(&2, Ac.Mark, t, Ac.Until{e} <> rest)), None{}, acb.first_none_at(now, t, e, rest, he, ht, hr)) : {Ac.first.of(False{}, _) == None{} : Maybe<&2, Nat>}
          {==}
        case Ac.Dead{}:
          %Equal.sym(Maybe<&2, Nat>, Ac.first(now, List.append(&2, Ac.Mark, t, Ac.Until{e} <> rest)), None{}, acb.first_none_at(now, t, e, rest, he, hp, hr)) : {Ac.first.of(False{}, _) == None{} : Maybe<&2, Nat>}
          {==}

# The earliest limit
# ------------------

# what the earliest limit answers: none, or a reset at e or later
def acb.SF(+e: Nat, r: Maybe<&2, Ac.Soon>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{s}:
      match s:
        case Ac.Soon{a, t}:
          {Nat.is_le(e, t) == True{} : Bool}

def acb.later_sf(+e: Nat, r: Maybe<&2, Ac.Soon>, v: acb.SF(e, r)) -> acb.SF(e, Ac.later(r)):
  match r:
    case None{}:
      Unit{}
    case Some{s}:
      match s:
        case Ac.Soon{a, t}:
          v

def acb.pick_sf(+e: Nat, b: Bool, +u: Nat, +a: Nat, +t: Nat, hu: {Nat.is_le(e, u) == True{} : Bool}, ht: {Nat.is_le(e, t) == True{} : Bool}) -> acb.SF(e, Ac.soonest.pick(b, u, a, t)):
  match b:
    case True{}:
      hu
    case False{}:
      ht

def acb.until_sf(+e: Nat, +u: Nat, r: Maybe<&2, Ac.Soon>, hu: {Nat.is_le(e, u) == True{} : Bool}, v: acb.SF(e, r)) -> acb.SF(e, Ac.soonest.until(u, r)):
  match r:
    case None{}:
      hu
    case Some{s}:
      match s:
        case Ac.Soon{+a, +t}:
          acb.pick_sf(e, Nat.is_le(u, t), u, a, t, hu, v)

# accounts dead or limited until e or later: their earliest limit, if
# any, resets at e or later
def acb.from_sf(+e: Nat, ms: List<&2, Ac.Mark>, +h: {Account.ac_all_from(e, ms) == True{} : Bool}) -> acb.SF(e, Ac.soonest(ms)):
  match ms:
    case Nil{}:
      Unit{}
    case m <> +t:
      match m:
        case Ac.Free{}:
          LStg.stg.absurdF(acb.SF(e, Ac.soonest(Ac.Free{} <> t)), h)
        case Ac.Until{+u}:
          +hu = LStg.stg.and_l(Nat.is_le(e, u), Account.ac_all_from(e, t), h)
          +ht = LStg.stg.and_r(Nat.is_le(e, u), Account.ac_all_from(e, t), h)
          acb.until_sf(e, u, Ac.soonest(t), hu, acb.from_sf(e, t, ht))
        case Ac.Dead{}:
          acb.later_sf(e, Ac.soonest(t), acb.from_sf(e, t, h))

# a limit until e before accounts whose earliest limit resets at e or
# later is the earliest (the first on a tie)
def acb.until_head(+e: Nat, r: Maybe<&2, Ac.Soon>, v: acb.SF(e, r)) -> {Ac.soonest.until(e, r) == Some{Ac.Soon{0n, e}} : Maybe<&2, Ac.Soon>}:
  match r:
    case None{}:
      {==}
    case Some{s}:
      match s:
        case Ac.Soon{+a, +t}:
          %Equal.sym(Bool, Nat.is_le(e, t), True{}, v) : {Ac.soonest.pick(_, e, a, t) == Some{Ac.Soon{0n, e}} : Maybe<&2, Ac.Soon>}
          {==}

# accounts p dead or limited past e, then one limited until e, then ones
# dead or limited until e or later: the earliest limit is that one's
def acb.soonest_at(p: List<&2, Ac.Mark>, +e: Nat, +rest: List<&2, Ac.Mark>, +hp: {Account.ac_all_after(e, p) == True{} : Bool}, hr: {Account.ac_all_from(e, rest) == True{} : Bool}) -> {Ac.soonest(List.append(&2, Ac.Mark, p, Ac.Until{e} <> rest)) == Some{Ac.Soon{List.length(&2, Ac.Mark, p), e}} : Maybe<&2, Ac.Soon>}:
  match p:
    case Nil{}:
      acb.until_head(e, Ac.soonest(rest), acb.from_sf(e, rest, hr))
    case x <> +t:
      match x:
        case Ac.Free{}:
          LStg.stg.absurdF({Ac.soonest(List.append(&2, Ac.Mark, Ac.Free{} <> t, Ac.Until{e} <> rest)) == Some{Ac.Soon{1n+List.length(&2, Ac.Mark, t), e}} : Maybe<&2, Ac.Soon>}, hp)
        case Ac.Until{+u}:
          +hu = LStg.stg.and_l(Nat.is_lt(e, u), Account.ac_all_after(e, t), hp)
          +ht = LStg.stg.and_r(Nat.is_lt(e, u), Account.ac_all_after(e, t), hp)
          %Equal.sym(Maybe<&2, Ac.Soon>, Ac.soonest(List.append(&2, Ac.Mark, t, Ac.Until{e} <> rest)), Some{Ac.Soon{List.length(&2, Ac.Mark, t), e}}, acb.soonest_at(t, e, rest, ht, hr)) : {Ac.soonest.until(u, _) == Some{Ac.Soon{1n+List.length(&2, Ac.Mark, t), e}} : Maybe<&2, Ac.Soon>}
          %Equal.sym(Bool, Nat.is_le(u, e), False{}, LNat.pc.lt_not_le(e, u, hu)) : {Ac.soonest.pick(_, u, List.length(&2, Ac.Mark, t), e) == Some{Ac.Soon{1n+List.length(&2, Ac.Mark, t), e}} : Maybe<&2, Ac.Soon>}
          {==}
        case Ac.Dead{}:
          %Equal.sym(Maybe<&2, Ac.Soon>, Ac.soonest(List.append(&2, Ac.Mark, t, Ac.Until{e} <> rest)), Some{Ac.Soon{List.length(&2, Ac.Mark, t), e}}, acb.soonest_at(t, e, rest, hp, hr)) : {Ac.later(_) == Some{Ac.Soon{1n+List.length(&2, Ac.Mark, t), e}} : Maybe<&2, Ac.Soon>}
          {==}

# the model's wait is the spec's
def acb.waits_may(+now: Nat, +cap: Nat, waits: Nat, +e: Nat) -> {Ac.waits_for(now, cap, waits, e) == Account.ac_may_wait(now, cap, waits, e) : Bool}:
  match waits:
    case 0n:
      {==}
    case 1n+w:
      Equal.sym(Bool, Bool.not(Nat.is_lt(Nat.add(now, cap), e)), Nat.is_le(e, Nat.add(now, cap)), acb.nlt_le(Nat.add(now, cap), e))

# accounts p dead or limited past e, then one limited until e (past now),
# then ones dead or limited until e or later: the run waits for that one
# or hands it on, as the spec's wait says (turned around: rewrites the
# choice into it)
def acb.limited_at(+now: Nat, +cap: Nat, +waits: Nat, +p: List<&2, Ac.Mark>, +e: Nat, +rest: List<&2, Ac.Mark>, +he: {Nat.is_lt(now, e) == True{} : Bool}, +hp: {Account.ac_all_after(e, p) == True{} : Bool}, +hr: {Account.ac_all_from(e, rest) == True{} : Bool}) -> {Ac.limited.of(Account.ac_may_wait(now, cap, waits, e), List.length(&2, Ac.Mark, p), e) == Ac.choose(Ac.In{now, cap, waits, List.append(&2, Ac.Mark, p, Ac.Until{e} <> rest)}) : Ac.Choice}:
  %Equal.sym(Maybe<&2, Nat>, Ac.first(now, List.append(&2, Ac.Mark, p, Ac.Until{e} <> rest)), None{}, acb.first_none_at(now, p, e, rest, he, hp, hr)) : {Ac.limited.of(Account.ac_may_wait(now, cap, waits, e), List.length(&2, Ac.Mark, p), e) == Ac.choose.of(now, cap, waits, List.append(&2, Ac.Mark, p, Ac.Until{e} <> rest), _) : Ac.Choice}
  %Equal.sym(Maybe<&2, Ac.Soon>, Ac.soonest(List.append(&2, Ac.Mark, p, Ac.Until{e} <> rest)), Some{Ac.Soon{List.length(&2, Ac.Mark, p), e}}, acb.soonest_at(p, e, rest, hp, hr)) : {Ac.limited.of(Account.ac_may_wait(now, cap, waits, e), List.length(&2, Ac.Mark, p), e) == Ac.limited(now, cap, waits, _) : Ac.Choice}
  %Equal.sym(Bool, Ac.waits_for(now, cap, waits, e), Account.ac_may_wait(now, cap, waits, e), acb.waits_may(now, cap, waits, e)) : {Ac.limited.of(Account.ac_may_wait(now, cap, waits, e), List.length(&2, Ac.Mark, p), e) == Ac.limited.of(_, List.length(&2, Ac.Mark, p), e) : Ac.Choice}
  {==}

# No login left
# -------------

# every login dead: none is usable
def acb.dead_first(+now: Nat, ms: List<&2, Ac.Mark>, h: {Account.ac_all_dead(ms) == True{} : Bool}) -> {Ac.first(now, ms) == None{} : Maybe<&2, Nat>}:
  match ms:
    case Nil{}:
      {==}
    case m <> +t:
      match m:
        case Ac.Free{}:
          LStg.stg.absurdF({Ac.first(now, Ac.Free{} <> t) == None{} : Maybe<&2, Nat>}, h)
        case Ac.Until{u}:
          LStg.stg.absurdF({Ac.first(now, Ac.Until{u} <> t) == None{} : Maybe<&2, Nat>}, h)
        case Ac.Dead{}:
          %Equal.sym(Maybe<&2, Nat>, Ac.first(now, t), None{}, acb.dead_first(now, t, h)) : {Ac.first.of(False{}, _) == None{} : Maybe<&2, Nat>}
          {==}

# every login dead: none is limited
def acb.dead_soonest(ms: List<&2, Ac.Mark>, h: {Account.ac_all_dead(ms) == True{} : Bool}) -> {Ac.soonest(ms) == None{} : Maybe<&2, Ac.Soon>}:
  match ms:
    case Nil{}:
      {==}
    case m <> +t:
      match m:
        case Ac.Free{}:
          LStg.stg.absurdF({Ac.soonest(Ac.Free{} <> t) == None{} : Maybe<&2, Ac.Soon>}, h)
        case Ac.Until{u}:
          LStg.stg.absurdF({Ac.soonest(Ac.Until{u} <> t) == None{} : Maybe<&2, Ac.Soon>}, h)
        case Ac.Dead{}:
          %Equal.sym(Maybe<&2, Ac.Soon>, Ac.soonest(t), None{}, acb.dead_soonest(t, h)) : {Ac.later(_) == None{} : Maybe<&2, Ac.Soon>}
          {==}

# every login dead: no login is left
def acb.login(+now: Nat, +cap: Nat, +waits: Nat, +ms: List<&2, Ac.Mark>, +h: {Account.ac_all_dead(ms) == True{} : Bool}) -> {Ac.choose(Ac.In{now, cap, waits, ms}) == Ac.Login{} : Ac.Choice}:
  %Equal.sym(Maybe<&2, Nat>, Ac.first(now, ms), None{}, acb.dead_first(now, ms, h)) : {Ac.choose.of(now, cap, waits, ms, _) == Ac.Login{} : Ac.Choice}
  %Equal.sym(Maybe<&2, Ac.Soon>, Ac.soonest(ms), None{}, acb.dead_soonest(ms, h)) : {Ac.limited(now, cap, waits, _) == Ac.Login{} : Ac.Choice}
  {==}

# The wire
# --------

# the reply's spelling is the spec's
def acb.reply(c: Ac.Choice) -> {FAc.put_choice(c) == Account.ac_reply(c) : String}:
  match c:
    case Ac.Use{a}:
      {==}
    case Ac.Hold{a, until}:
      {==}
    case Ac.Quota{a, until}:
      {==}
    case Ac.Login{}:
      {==}

# the Nats of marks read back as those marks
def acb.marks_back(ms: List<&2, Ac.Mark>) -> {FAc.marks(Account.ac_marks_nats(ms)) == Some{ms} : Maybe<&2, List<&2, Ac.Mark>>}:
  match ms:
    case Nil{}:
      {==}
    case m <> +t:
      match m:
        case Ac.Free{}:
          %Equal.sym(Maybe<&2, List<&2, Ac.Mark>>, FAc.marks(Account.ac_marks_nats(t)), Some{t}, acb.marks_back(t)) : {FAc.marks.cons(Ac.Free{}, _) == Some{Ac.Free{} <> t} : Maybe<&2, List<&2, Ac.Mark>>}
          {==}
        case Ac.Until{+u}:
          %Equal.sym(Maybe<&2, List<&2, Ac.Mark>>, FAc.marks(Account.ac_marks_nats(t)), Some{t}, acb.marks_back(t)) : {FAc.marks.cons(Ac.Until{u}, _) == Some{Ac.Until{u} <> t} : Maybe<&2, List<&2, Ac.Mark>>}
          {==}
        case Ac.Dead{}:
          %Equal.sym(Maybe<&2, List<&2, Ac.Mark>>, FAc.marks(Account.ac_marks_nats(t)), Some{t}, acb.marks_back(t)) : {FAc.marks.cons(Ac.Dead{}, _) == Some{Ac.Dead{} <> t} : Maybe<&2, List<&2, Ac.Mark>>}
          {==}

# what a read of marks answers: none, or marks whose Nats are xs
def acb.MX(+xs: List<&2, Nat>, r: Maybe<&2, List<&2, Ac.Mark>>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{ms}:
      {xs == Account.ac_marks_nats(ms) : List<&2, Nat>}

def acb.cons_mx(+m: Ac.Mark, +rest: List<&2, Nat>, r: Maybe<&2, List<&2, Ac.Mark>>, v: acb.MX(rest, r)) -> acb.MX(Account.ac_mark_nats(m, rest), FAc.marks.cons(m, r)):
  match r:
    case None{}:
      Unit{}
    case Some{+ms}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => Account.ac_mark_nats(m, z), rest, Account.ac_marks_nats(ms), v)

# every read of marks is exact: the marks it answers are spelled by the
# Nats it read
def acb.marks_mx(xs: List<&2, Nat>) -> acb.MX(xs, FAc.marks(xs)):
  match xs:
    case Nil{}:
      {==}
    case k <> +rest:
      match k:
        case 0n:
          acb.cons_mx(Ac.Free{}, rest, FAc.marks(rest), acb.marks_mx(rest))
        case 1n:
          match rest:
            case Nil{}:
              Unit{}
            case +t <> +more:
              acb.cons_mx(Ac.Until{t}, more, FAc.marks(more), acb.marks_mx(more))
        case 2n:
          acb.cons_mx(Ac.Dead{}, rest, FAc.marks(rest), acb.marks_mx(rest))
        case 3n+q:
          Unit{}

# what a parse answers: none, or a request whose Nats are xs
def acb.PX(+xs: List<&2, Nat>, r: Maybe<&2, Ac.In>) -> Type:
  match r:
    case None{}:
      Unit
    case Some{x}:
      {xs == Account.ac_nats(x) : List<&2, Nat>}

def acb.marks_px(+now: Nat, +cap: Nat, +waits: Nat, +rest: List<&2, Nat>, r: Maybe<&2, List<&2, Ac.Mark>>, v: acb.MX(rest, r)) -> acb.PX(now <> cap <> waits <> rest, FAc.parse.marks(now, cap, waits, r)):
  match r:
    case None{}:
      Unit{}
    case Some{+ms}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => now <> cap <> waits <> z, rest, Account.ac_marks_nats(ms), v)

# every parse is exact: a request it answers is spelled by the Nats it read
def acb.parse_px(xs: List<&2, Nat>) -> acb.PX(xs, FAc.parse(xs)):
  match xs:
    case Nil{}:
      Unit{}
    case +now <> t:
      match t:
        case Nil{}:
          Unit{}
        case +cap <> u:
          match u:
            case Nil{}:
              Unit{}
            case +waits <> +rest:
              acb.marks_px(now, cap, waits, rest, FAc.marks(rest), acb.marks_mx(rest))
