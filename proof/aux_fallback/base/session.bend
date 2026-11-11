# eukhe: lemmas of area aux_fallback, the session model: membership of
# keys (afh.listed_in, afh.listed_sound), the keys of events joined
# (afh.subs_app, afh.notes_app), a session run in two parts (afh.go_app)
# with the keys shown after the first part (afh.aft) being the keys its
# passes fell back with (afh.aft_listed), and a session's notices without
# a repeat and apart from the keys shown before it (afh.inv).

import Base
import ../../../bend/aux_fallback.bend as Af
import ../../../laws/aux_fallback/model.bend as AuxFallback
import ../../base/bool.bend as LBool
import ../../base/logic/bool.bend as LLogicBool
import ../../model_name/base.bend as LA
import ../fallback_is_reported.bend as PRep

# Keys
# ----

def afh.nat_eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      afh.nat_eq_refl(m)

def afh.nat_eq_sym(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+y:
      {==}
    case 1n+x 0n:
      {==}
    case 1n+x 1n+y:
      afh.nat_eq_sym(x, y)

def afh.key_eq_refl(k: Af.Key) -> {Af.Key.eq(k, k) == True{} : Bool}:
  match k:
    case Af.K{+p, +s, +r}:
      LA.mnb.and_t(Nat.is_eq(p, p), Bool.and(Nat.is_eq(s, s), Nat.is_eq(r, r)), afh.nat_eq_refl(p), LA.mnb.and_t(Nat.is_eq(s, s), Nat.is_eq(r, r), afh.nat_eq_refl(s), afh.nat_eq_refl(r)))

def afh.key_eq_sym(a: Af.Key, b: Af.Key) -> {Af.Key.eq(a, b) == Af.Key.eq(b, a) : Bool}:
  match a b:
    case Af.K{+ap, +as1, +ar} Af.K{+bp, +bs1, +br}:
      %afh.nat_eq_sym(ap, bp) : {Bool.and(Nat.is_eq(ap, bp), Bool.and(Nat.is_eq(as1, bs1), Nat.is_eq(ar, br))) == Bool.and(_, Bool.and(Nat.is_eq(bs1, as1), Nat.is_eq(br, ar))) : Bool}
      %afh.nat_eq_sym(as1, bs1) : {Bool.and(Nat.is_eq(ap, bp), Bool.and(Nat.is_eq(as1, bs1), Nat.is_eq(ar, br))) == Bool.and(Nat.is_eq(ap, bp), Bool.and(_, Nat.is_eq(br, ar))) : Bool}
      %afh.nat_eq_sym(ar, br) : {Bool.and(Nat.is_eq(ap, bp), Bool.and(Nat.is_eq(as1, bs1), Nat.is_eq(ar, br))) == Bool.and(Nat.is_eq(ap, bp), Bool.and(Nat.is_eq(as1, bs1), _)) : Bool}
      {==}

# a key that occurs in a list is listed in it
def afh.listed_in(a: List<&2, Af.Key>, +k: Af.Key, +b: List<&2, Af.Key>) -> {Af.listed(List.append(&2, Af.Key, a, k <> b), k) == True{} : Bool}:
  match a:
    case Nil{}:
      LBool.ppr.or_l(Af.Key.eq(k, k), Af.listed(b, k), afh.key_eq_refl(k))
    case +x <> +t:
      LBool.ppr.or_r(Af.Key.eq(x, k), Af.listed(List.append(&2, Af.Key, t, k <> b), k), afh.listed_in(t, k, b))

def afh.LS(ks: List<&2, Af.Key>, k: Af.Key) -> Type:
  Sigma<&1, &1, List<&2, Af.Key>, a => Sigma<&1, &1, List<&2, Af.Key>, b => {ks == List.append(&2, Af.Key, a, k <> b) : List<&2, Af.Key>}>>

def afh.ls_next(+x: Af.Key, -t: List<&2, Af.Key>, -k: Af.Key, s: afh.LS(t, k)) -> afh.LS(x <> t, k):
  (+a, (+b, e)) = s
  (x <> a, (b, Equal.cong(List<&2, Af.Key>, List<&2, Af.Key>, z => x <> z, t, List.append(&2, Af.Key, a, k <> b), e)))

def afh.ls_at(c: Bool, +x: Af.Key, +t: List<&2, Af.Key>, +k: Af.Key, ec: {Af.Key.eq(x, k) == c : Bool}, h: {Bool.or(c, Af.listed(t, k)) == True{} : Bool}, ih: {Af.listed(t, k) == True{} : Bool} -> afh.LS(t, k)) -> afh.LS(x <> t, k):
  match c:
    case True{}:
      (Nil{}, (t, Equal.cong(Af.Key, List<&2, Af.Key>, z => z <> t, x, k, PRep.ppr.key_eq_true(x, k, ec))))
    case False{}:
      afh.ls_next(x, t, k, ih(h))

# a listed key occurs in the list
def afh.listed_sound(ks: List<&2, Af.Key>, +k: Af.Key, h: {Af.listed(ks, k) == True{} : Bool}) -> afh.LS(ks, k):
  match ks:
    case Nil{}:
      LA.mnb.absurd_f(afh.LS(Nil{}, k), h)
    case +x <> +t:
      afh.ls_at(Af.Key.eq(x, k), x, t, k, {==}, h, h2 => afh.listed_sound(t, k, h2))

# The keys of events
# ------------------

def afh.subs_app(es: List<&2, Af.Ev>, +fs: List<&2, Af.Ev>) -> {Af.subs(List.append(&2, Af.Ev, es, fs)) == List.append(&2, Af.Key, Af.subs(es), Af.subs(fs)) : List<&2, Af.Key>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Af.Stay{}:
          afh.subs_app(rest, fs)
        case Af.Went{}:
          afh.subs_app(rest, fs)
        case Af.Sub{+k}:
          Equal.cong(List<&2, Af.Key>, List<&2, Af.Key>, z => k <> z, Af.subs(List.append(&2, Af.Ev, rest, fs)), List.append(&2, Af.Key, Af.subs(rest), Af.subs(fs)), afh.subs_app(rest, fs))
        case Af.Note{k}:
          afh.subs_app(rest, fs)

def afh.notes_app(es: List<&2, Af.Ev>, +fs: List<&2, Af.Ev>) -> {Af.notes(List.append(&2, Af.Ev, es, fs)) == List.append(&2, Af.Key, Af.notes(es), Af.notes(fs)) : List<&2, Af.Key>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Af.Stay{}:
          afh.notes_app(rest, fs)
        case Af.Went{}:
          afh.notes_app(rest, fs)
        case Af.Sub{k}:
          afh.notes_app(rest, fs)
        case Af.Note{+k}:
          Equal.cong(List<&2, Af.Key>, List<&2, Af.Key>, z => k <> z, Af.notes(List.append(&2, Af.Ev, rest, fs)), List.append(&2, Af.Key, Af.notes(rest), Af.notes(fs)), afh.notes_app(rest, fs))

# A session in two parts
# ----------------------

# the keys shown after the passes ps, sh shown before them
def afh.aft(ps: List<&2, Af.Pass>, sh: List<&2, Af.Key>) -> List<&2, Af.Key>:
  match ps:
    case Nil{}:
      sh
    case x <> t:
      afh.aft(t, Af.after(Af.decide(x), sh))

def afh.noted_app(b: Bool, k: Af.Key, xs: List<&2, Af.Ev>, ys: List<&2, Af.Ev>) -> {Af.noted(b, k, List.append(&2, Af.Ev, xs, ys)) == List.append(&2, Af.Ev, Af.noted(b, k, xs), ys) : List<&2, Af.Ev>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def afh.put_app(r: Af.Route, +sh: List<&2, Af.Key>, +xs: List<&2, Af.Ev>, +ys: List<&2, Af.Ev>) -> {Af.put(r, sh, List.append(&2, Af.Ev, xs, ys)) == List.append(&2, Af.Ev, Af.put(r, sh, xs), ys) : List<&2, Af.Ev>}:
  match r:
    case Af.Session{}:
      {==}
    case Af.Routed{}:
      {==}
    case Af.Fallback{+k}:
      Equal.cong(List<&2, Af.Ev>, List<&2, Af.Ev>, z => Af.Sub{k} <> z, Af.noted(Af.listed(sh, k), k, List.append(&2, Af.Ev, xs, ys)), List.append(&2, Af.Ev, Af.noted(Af.listed(sh, k), k, xs), ys), afh.noted_app(Af.listed(sh, k), k, xs, ys))

# the session ps then q is the events of ps, then those of q with the keys
# shown after ps
def afh.go_app(ps: List<&2, Af.Pass>, +q: List<&2, Af.Pass>, +sh: List<&2, Af.Key>) -> {Af.go(List.append(&2, Af.Pass, ps, q), sh) == List.append(&2, Af.Ev, Af.go(ps, sh), Af.go(q, afh.aft(ps, sh))) : List<&2, Af.Ev>}:
  match ps:
    case Nil{}:
      {==}
    case +x <> +t:
      +d = Af.decide(x)
      +a = Af.after(d, sh)
      Equal.trans(List<&2, Af.Ev>, Af.put(d, sh, Af.go(List.append(&2, Af.Pass, t, q), a)), Af.put(d, sh, List.append(&2, Af.Ev, Af.go(t, a), Af.go(q, afh.aft(t, a)))), List.append(&2, Af.Ev, Af.put(d, sh, Af.go(t, a)), Af.go(q, afh.aft(t, a))), Equal.cong(List<&2, Af.Ev>, List<&2, Af.Ev>, z => Af.put(d, sh, z), Af.go(List.append(&2, Af.Pass, t, q), a), List.append(&2, Af.Ev, Af.go(t, a), Af.go(q, afh.aft(t, a))), afh.go_app(t, q, a)), afh.put_app(d, sh, Af.go(t, a), Af.go(q, afh.aft(t, a))))

# The keys shown are the keys fallen back with
# --------------------------------------------

def afh.or_false(b: Bool) -> {Bool.or(b, False{}) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def afh.or_swap(e: Bool, s: Bool, -l: Bool) -> {Bool.or(Bool.or(e, s), l) == Bool.or(s, Bool.or(e, l)) : Bool}:
  match e:
    case True{}:
      match s:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

def afh.or_tt(s: Bool, -l: Bool, e: {s == True{} : Bool}) -> {Bool.or(s, l) == Bool.or(s, Bool.or(True{}, l)) : Bool}:
  match s:
    case True{}:
      {==}
    case False{}:
      LA.mnb.absurd_f({Bool.or(False{}, l) == Bool.or(False{}, Bool.or(True{}, l)) : Bool}, e)

def afh.seen_k(+j: Af.Key, +k: Af.Key, -sh: List<&2, Af.Key>, ee: {Af.Key.eq(j, k) == True{} : Bool}, es: {Af.listed(sh, j) == True{} : Bool}) -> {Af.listed(sh, k) == True{} : Bool}:
  %PRep.ppr.key_eq_true(j, k, ee) : {Af.listed(sh, _) == True{} : Bool}
  es

def afh.step_seen(e: Bool, +j: Af.Key, +k: Af.Key, +sh: List<&2, Af.Key>, -F: List<&2, Af.Key>, ee: {Af.Key.eq(j, k) == e : Bool}, es: {Af.listed(sh, j) == True{} : Bool}) -> {Bool.or(Af.listed(sh, k), Af.listed(F, k)) == Bool.or(Af.listed(sh, k), Bool.or(e, Af.listed(F, k))) : Bool}:
  match e:
    case True{}:
      afh.or_tt(Af.listed(sh, k), Af.listed(F, k), afh.seen_k(j, k, sh, ee, es))
    case False{}:
      {==}

def afh.step_fb(s: Bool, +j: Af.Key, +k: Af.Key, +sh: List<&2, Af.Key>, +F: List<&2, Af.Key>, es: {Af.listed(sh, j) == s : Bool}) -> {Bool.or(Af.listed(Af.shown(s, j, sh), k), Af.listed(F, k)) == Bool.or(Af.listed(sh, k), Bool.or(Af.Key.eq(j, k), Af.listed(F, k))) : Bool}:
  match s:
    case True{}:
      afh.step_seen(Af.Key.eq(j, k), j, k, sh, F, {==}, es)
    case False{}:
      afh.or_swap(Af.Key.eq(j, k), Af.listed(sh, k), Af.listed(F, k))

# one pass: a key is shown after it, or among keys F fallen back with
# later, when it was shown before it, or among the pass's fallback key and F
def afh.step(r: Af.Route, +sh: List<&2, Af.Key>, +F: List<&2, Af.Key>, +k: Af.Key) -> {Bool.or(Af.listed(Af.after(r, sh), k), Af.listed(F, k)) == Bool.or(Af.listed(sh, k), Af.listed(AuxFallback.afh_fell(r, F), k)) : Bool}:
  match r:
    case Af.Session{}:
      {==}
    case Af.Routed{}:
      {==}
    case Af.Fallback{+j}:
      afh.step_fb(Af.listed(sh, j), j, k, sh, F, {==})

# a key is shown after the passes ps when it was shown before them, or
# one of them fell back with it
def afh.aft_listed(ps: List<&2, Af.Pass>, +sh: List<&2, Af.Key>, +k: Af.Key) -> {Af.listed(afh.aft(ps, sh), k) == Bool.or(Af.listed(sh, k), Af.listed(AuxFallback.afh_fallen(ps), k)) : Bool}:
  match ps:
    case Nil{}:
      Equal.sym(Bool, Bool.or(Af.listed(sh, k), False{}), Af.listed(sh, k), afh.or_false(Af.listed(sh, k)))
    case +x <> +t:
      +a = Af.after(Af.decide(x), sh)
      Equal.trans(Bool, Af.listed(afh.aft(t, a), k), Bool.or(Af.listed(a, k), Af.listed(AuxFallback.afh_fallen(t), k)), Bool.or(Af.listed(sh, k), Af.listed(AuxFallback.afh_fell(Af.decide(x), AuxFallback.afh_fallen(t)), k)), afh.aft_listed(t, a, k), afh.step(Af.decide(x), sh, AuxFallback.afh_fallen(t), k))

def afh.notice(b: Bool, k: Af.Key) -> {Af.Sub{k} <> Af.noted(b, k, Nil{}) == Af.Sub{k} <> AuxFallback.afh_notice(b, k) : List<&2, Af.Ev>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the events of the pass after ps, the keys shown after ps being those
# shown by a session that ran ps
def afh.last(r: Af.Route, +ps: List<&2, Af.Pass>) -> {Af.put(r, afh.aft(ps, Nil{}), Nil{}) == AuxFallback.afh_events(r, AuxFallback.afh_fallen(ps)) : List<&2, Af.Ev>}:
  match r:
    case Af.Session{}:
      {==}
    case Af.Routed{}:
      {==}
    case Af.Fallback{+k}:
      +F = AuxFallback.afh_fallen(ps)
      %Equal.sym(Bool, Af.listed(afh.aft(ps, Nil{}), k), Af.listed(F, k), afh.aft_listed(ps, Nil{}, k)) : {Af.Sub{k} <> Af.noted(_, k, Nil{}) == Af.Sub{k} <> AuxFallback.afh_notice(Af.listed(F, k), k) : List<&2, Af.Ev>}
      afh.notice(Af.listed(F, k), k)

# Notices without a repeat
# ------------------------

# no key of ns is listed in sh
def afh.disj(ns: List<&2, Af.Key>, +sh: List<&2, Af.Key>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case n <> t:
      Bool.and(Bool.not(Af.listed(sh, n)), afh.disj(t, sh))

def afh.INV(t: List<&2, Af.Ev>, sh: List<&2, Af.Key>) -> Type:
  {Bool.and(AuxFallback.afh_nodup(Af.notes(t)), afh.disj(Af.notes(t), sh)) == True{} : Bool}

def afh.dc_fin(a: Bool, b: Bool, c: Bool, d: Bool, ea: {a == False{} : Bool}, eb: {b == False{} : Bool}, ec: {c == False{} : Bool}, ed: {d == True{} : Bool}) -> {Bool.or(a, b) == False{} : Bool} & {Bool.and(Bool.not(c), d) == True{} : Bool}:
  match a:
    case True{}:
      LA.mnb.absurd({Bool.or(True{}, b) == False{} : Bool} & {Bool.and(Bool.not(c), d) == True{} : Bool}, ea)
    case False{}:
      match b:
        case True{}:
          LA.mnb.absurd({Bool.or(False{}, True{}) == False{} : Bool} & {Bool.and(Bool.not(c), d) == True{} : Bool}, eb)
        case False{}:
          match c:
            case True{}:
              LA.mnb.absurd({Bool.or(False{}, False{}) == False{} : Bool} & {Bool.and(Bool.not(True{}), d) == True{} : Bool}, ec)
            case False{}:
              match d:
                case True{}:
                  ({==}, {==})
                case False{}:
                  LA.mnb.absurd_f({Bool.or(False{}, False{}) == False{} : Bool} & {Bool.and(Bool.not(False{}), False{}) == True{} : Bool}, ed)

def afh.dc_split(+a: Bool, +b: Bool, +c: Bool, +d: Bool, ea: {a == False{} : Bool}, ec: {c == False{} : Bool}, ih: {b == False{} : Bool} & {d == True{} : Bool}) -> {Bool.or(a, b) == False{} : Bool} & {Bool.and(Bool.not(c), d) == True{} : Bool}:
  (eb, ed) = ih
  afh.dc_fin(a, b, c, d, ea, eb, ec, ed)

# keys ns apart from j <> sh: j is not among them, and they are apart from
# sh
def afh.disj_cons(ns: List<&2, Af.Key>, +j: Af.Key, +sh: List<&2, Af.Key>, h: {afh.disj(ns, j <> sh) == True{} : Bool}) -> {Af.listed(ns, j) == False{} : Bool} & {afh.disj(ns, sh) == True{} : Bool}:
  match ns:
    case Nil{}:
      ({==}, {==})
    case +n <> +t:
      +hh = h
      +o = LLogicBool.ppr.not_t(Bool.or(Af.Key.eq(j, n), Af.listed(sh, n)), LLogicBool.ppr.and_l(Bool.not(Bool.or(Af.Key.eq(j, n), Af.listed(sh, n))), afh.disj(t, j <> sh), hh))
      +ejn = LA.mnb.or_fl(Af.Key.eq(j, n), Af.listed(sh, n), o)
      +enj = Equal.trans(Bool, Af.Key.eq(n, j), Af.Key.eq(j, n), False{}, afh.key_eq_sym(n, j), ejn)
      +esn = LA.mnb.or_fr(Af.Key.eq(j, n), Af.listed(sh, n), o)
      afh.dc_split(Af.Key.eq(n, j), Af.listed(t, j), Af.listed(sh, n), afh.disj(t, sh), enj, esn, afh.disj_cons(t, j, sh, LLogicBool.ppr.and_r(Bool.not(Bool.or(Af.Key.eq(j, n), Af.listed(sh, n))), afh.disj(t, j <> sh), hh)))

def afh.and4(a: Bool, b: Bool, c: Bool, d: Bool, ea: {a == False{} : Bool}, eb: {b == True{} : Bool}, ec: {c == False{} : Bool}, ed: {d == True{} : Bool}) -> {Bool.and(Bool.and(Bool.not(a), b), Bool.and(Bool.not(c), d)) == True{} : Bool}:
  match a:
    case True{}:
      LA.mnb.absurd({Bool.and(Bool.and(Bool.not(True{}), b), Bool.and(Bool.not(c), d)) == True{} : Bool}, ea)
    case False{}:
      match b:
        case False{}:
          LA.mnb.absurd_f({Bool.and(Bool.and(Bool.not(False{}), False{}), Bool.and(Bool.not(c), d)) == True{} : Bool}, eb)
        case True{}:
          match c:
            case True{}:
              LA.mnb.absurd({Bool.and(Bool.and(Bool.not(False{}), True{}), Bool.and(Bool.not(True{}), d)) == True{} : Bool}, ec)
            case False{}:
              match d:
                case False{}:
                  LA.mnb.absurd_f({Bool.and(Bool.and(Bool.not(False{}), True{}), Bool.and(Bool.not(False{}), False{})) == True{} : Bool}, ed)
                case True{}:
                  {==}

def afh.fb_fin(+j: Af.Key, +sh: List<&2, Af.Key>, +ns: List<&2, Af.Key>, es: {Af.listed(sh, j) == False{} : Bool}, nd: {AuxFallback.afh_nodup(ns) == True{} : Bool}, dc: {Af.listed(ns, j) == False{} : Bool} & {afh.disj(ns, sh) == True{} : Bool}) -> {Bool.and(AuxFallback.afh_nodup(j <> ns), afh.disj(j <> ns, sh)) == True{} : Bool}:
  (ln, ds) = dc
  afh.and4(Af.listed(ns, j), AuxFallback.afh_nodup(ns), Af.listed(sh, j), afh.disj(ns, sh), ln, nd, es, ds)

def afh.fb_new(+j: Af.Key, +sh: List<&2, Af.Key>, +ns: List<&2, Af.Key>, es: {Af.listed(sh, j) == False{} : Bool}, ih: {Bool.and(AuxFallback.afh_nodup(ns), afh.disj(ns, j <> sh)) == True{} : Bool}) -> {Bool.and(AuxFallback.afh_nodup(j <> ns), afh.disj(j <> ns, sh)) == True{} : Bool}:
  +hh = ih
  +nd = LLogicBool.ppr.and_l(AuxFallback.afh_nodup(ns), afh.disj(ns, j <> sh), hh)
  afh.fb_fin(j, sh, ns, es, nd, afh.disj_cons(ns, j, sh, LLogicBool.ppr.and_r(AuxFallback.afh_nodup(ns), afh.disj(ns, j <> sh), hh)))

# a fallback pass of key j, the session having shown j or not (s)
def afh.inv_fb(s: Bool, +j: Af.Key, +sh: List<&2, Af.Key>, +t: List<&2, Af.Ev>, es: {Af.listed(sh, j) == s : Bool}, ih: afh.INV(t, Af.shown(s, j, sh))) -> afh.INV(Af.noted(s, j, t), sh):
  match s:
    case True{}:
      ih
    case False{}:
      afh.fb_new(j, sh, Af.notes(t), es, ih)

def afh.inv_put(r: Af.Route, +sh: List<&2, Af.Key>, +t: List<&2, Af.Ev>, ih: afh.INV(t, Af.after(r, sh))) -> afh.INV(Af.put(r, sh, t), sh):
  match r:
    case Af.Session{}:
      ih
    case Af.Routed{}:
      ih
    case Af.Fallback{+j}:
      afh.inv_fb(Af.listed(sh, j), j, sh, t, {==}, ih)

# a session's notices hold no key twice, and none shown before it
def afh.inv(ps: List<&2, Af.Pass>, +sh: List<&2, Af.Key>) -> afh.INV(Af.go(ps, sh), sh):
  match ps:
    case Nil{}:
      {==}
    case +x <> +t:
      afh.inv_put(Af.decide(x), sh, Af.go(t, Af.after(Af.decide(x), sh)), afh.inv(t, Af.after(Af.decide(x), sh)))
