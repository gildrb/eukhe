# eukhe: lemmas of area agent_tree for patches, masks and halves
# (integration T3-T5, halves T1/T8)

import Base
import ../../../bend/agent_tree.bend as T
import ../../../spec/agents/agent_tree.bend as S

# Logic
# -----

# G when b is True, Unit when False
def at_patch.If(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# False is not True: anything follows
def at_patch.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : at_patch.If(_, G)
  Unit{}

def at_patch.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      at_patch.absurd({False{} == True{} : Bool}, e)

def at_patch.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      at_patch.absurd({b == True{} : Bool}, e)

def at_patch.and_intro(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

# Halves
# ------

# the larger half: n less half(n)
def at_patch.hi(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match p:
        case 0n:
          1n
        case 1n+q:
          1n+at_patch.hi(q)

def at_patch.add_succ_r(x: Nat, -y: Nat) -> {1n+Nat.add(x, y) == Nat.add(x, 1n+y) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      %at_patch.add_succ_r(p, y) : {2n+Nat.add(p, y) == 1n+_ : Nat}
      {==}

def at_patch.sub_add(h: Nat, x: Nat) -> {x == Nat.sub(Nat.add(h, x), h) : Nat}:
  match h:
    case 0n:
      match x:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case 1n+p:
      at_patch.sub_add(p, x)

def at_patch.half_hi(+c: Nat) -> {Nat.add(T.half(c), at_patch.hi(c)) == c : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          %at_patch.add_succ_r(T.half(q), at_patch.hi(q)) : {1n+_ == 2n+q : Nat}
          %at_patch.half_hi(q) : {2n+Nat.add(T.half(q), at_patch.hi(q)) == 2n+_ : Nat}
          {==}

def at_patch.hi_half(+c: Nat) -> {c == Nat.add(at_patch.hi(c), T.half(c)) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          %at_patch.add_succ_r(at_patch.hi(q), T.half(q)) : {2n+q == 1n+_ : Nat}
          %at_patch.hi_half(q) : {2n+q == 2n+_ : Nat}
          {==}

# hi(c) is c less its smaller half
def at_patch.hi_sub(+c: Nat) -> {at_patch.hi(c) == Nat.sub(c, T.half(c)) : Nat}:
  %at_patch.half_hi(c) : {at_patch.hi(c) == Nat.sub(_, T.half(c)) : Nat}
  at_patch.sub_add(T.half(c), at_patch.hi(c))

def at_patch.eq_refl(n: Nat) -> {True{} == Nat.is_eq(n, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      at_patch.eq_refl(p)

# the larger half is the smaller one or one more
def at_patch.hi_close(c: Nat) -> {Bool.or(Nat.is_eq(at_patch.hi(c), T.half(c)), Nat.is_eq(at_patch.hi(c), 1n+T.half(c))) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          at_patch.hi_close(q)

# the halves of a value are fair
def at_patch.fair(+c: Nat) -> {Bool.and(Nat.is_eq(Nat.add(Nat.sub(c, T.half(c)), T.half(c)), c), Bool.or(Nat.is_eq(Nat.sub(c, T.half(c)), T.half(c)), Nat.is_eq(Nat.sub(c, T.half(c)), 1n+T.half(c)))) == True{} : Bool}:
  %at_patch.hi_sub(c) : {Bool.and(Nat.is_eq(Nat.add(_, T.half(c)), c), Bool.or(Nat.is_eq(_, T.half(c)), Nat.is_eq(_, 1n+T.half(c)))) == True{} : Bool}
  %at_patch.hi_half(c) : {Bool.and(Nat.is_eq(_, c), Bool.or(Nat.is_eq(at_patch.hi(c), T.half(c)), Nat.is_eq(at_patch.hi(c), 1n+T.half(c)))) == True{} : Bool}
  %at_patch.eq_refl(c) : {Bool.and(_, Bool.or(Nat.is_eq(at_patch.hi(c), T.half(c)), Nat.is_eq(at_patch.hi(c), 1n+T.half(c)))) == True{} : Bool}
  at_patch.hi_close(c)

# Apply
# -----

def at_patch.app_nil(f: List<&2, Nat>) -> {f == T.apply(f, []) : List<&2, Nat>}:
  match f:
    case Nil{}:
      {==}
    case Con{x, xt}:
      {==}

def at_patch.nil_app(p: List<&2, Maybe<&2, Nat>>) -> {[] == T.apply([], p) : List<&2, Nat>}:
  match p:
    case Nil{}:
      {==}
    case Con{y, yt}:
      {==}

def at_patch.nil_app_r(p: List<&2, Maybe<&2, Nat>>) -> {T.apply([], p) == [] : List<&2, Nat>}:
  match p:
    case Nil{}:
      {==}
    case Con{y, yt}:
      {==}

# a patch with no write inside the empty scope changes nothing
def at_patch.nones(+g: List<&2, Nat>, +a: List<&2, Maybe<&2, Nat>>) -> {g == T.apply(g, S.restrict(a, [])) : List<&2, Nat>}:
  match g:
    case Nil{}:
      match a:
        case Nil{}:
          {==}
        case Con{y, yt}:
          {==}
    case Con{z, zt}:
      match a:
        case Nil{}:
          {==}
        case Con{y, yt}:
          %at_patch.nones(zt, yt) : {z <> zt == z <> _ : List<&2, Nat>}
          {==}

# T3: the integrated patch applies the parent's then the child's writes
# inside its scope
def at_patch.overlay_applies_r(+f: List<&2, Nat>, +c: List<&2, Maybe<&2, Nat>>, +a: List<&2, Maybe<&2, Nat>>, +s: List<&2, Bool>) -> {T.apply(T.apply(f, c), S.restrict(a, s)) == T.apply(f, T.overlay(c, a, s)) : List<&2, Nat>}:
  match f:
    case Nil{}:
      %at_patch.nil_app(T.overlay(c, a, s)) : {T.apply(T.apply([], c), S.restrict(a, s)) == _ : List<&2, Nat>}
      %at_patch.nil_app(c) : {T.apply(_, S.restrict(a, s)) == [] : List<&2, Nat>}
      at_patch.nil_app_r(S.restrict(a, s))
    case Con{z, zt}:
      match c:
        case Nil{}:
          match a:
            case Nil{}:
              match s:
                case Nil{}:
                  {==}
                case Con{b, bt}:
                  {==}
            case Con{y, yt}:
              match y:
                case None{}:
                  match s:
                    case Nil{}:
                      %at_patch.nones(zt, yt) : {z <> _ == z <> zt : List<&2, Nat>}
                      {==}
                    case Con{b, bt}:
                      match b:
                        case True{}:
                          %at_patch.overlay_applies_r(zt, [], yt, bt) : {z <> T.apply(zt, S.restrict(yt, bt)) == z <> _ : List<&2, Nat>}
                          %at_patch.app_nil(zt) : {z <> T.apply(zt, S.restrict(yt, bt)) == z <> T.apply(_, S.restrict(yt, bt)) : List<&2, Nat>}
                          {==}
                        case False{}:
                          %at_patch.overlay_applies_r(zt, [], yt, bt) : {z <> T.apply(zt, S.restrict(yt, bt)) == z <> _ : List<&2, Nat>}
                          %at_patch.app_nil(zt) : {z <> T.apply(zt, S.restrict(yt, bt)) == z <> T.apply(_, S.restrict(yt, bt)) : List<&2, Nat>}
                          {==}
                case Some{v}:
                  match s:
                    case Nil{}:
                      %at_patch.nones(zt, yt) : {z <> _ == z <> zt : List<&2, Nat>}
                      {==}
                    case Con{b, bt}:
                      match b:
                        case True{}:
                          %at_patch.overlay_applies_r(zt, [], yt, bt) : {v <> T.apply(zt, S.restrict(yt, bt)) == v <> _ : List<&2, Nat>}
                          %at_patch.app_nil(zt) : {v <> T.apply(zt, S.restrict(yt, bt)) == v <> T.apply(_, S.restrict(yt, bt)) : List<&2, Nat>}
                          {==}
                        case False{}:
                          %at_patch.overlay_applies_r(zt, [], yt, bt) : {z <> T.apply(zt, S.restrict(yt, bt)) == z <> _ : List<&2, Nat>}
                          %at_patch.app_nil(zt) : {z <> T.apply(zt, S.restrict(yt, bt)) == z <> T.apply(_, S.restrict(yt, bt)) : List<&2, Nat>}
                          {==}
        case Con{c0, ct}:
          match a:
            case Nil{}:
              match s:
                case Nil{}:
                  {==}
                case Con{b, bt}:
                  {==}
            case Con{y, yt}:
              match y:
                case None{}:
                  match s:
                    case Nil{}:
                      %at_patch.nones(T.apply(zt, ct), yt) : {T.land(c0, z) <> _ == T.land(c0, z) <> T.apply(zt, ct) : List<&2, Nat>}
                      {==}
                    case Con{b, bt}:
                      match b:
                        case True{}:
                          %at_patch.overlay_applies_r(zt, ct, yt, bt) : {T.land(c0, z) <> T.apply(T.apply(zt, ct), S.restrict(yt, bt)) == T.land(c0, z) <> _ : List<&2, Nat>}
                          {==}
                        case False{}:
                          %at_patch.overlay_applies_r(zt, ct, yt, bt) : {T.land(c0, z) <> T.apply(T.apply(zt, ct), S.restrict(yt, bt)) == T.land(c0, z) <> _ : List<&2, Nat>}
                          {==}
                case Some{v}:
                  match s:
                    case Nil{}:
                      %at_patch.nones(T.apply(zt, ct), yt) : {T.land(c0, z) <> _ == T.land(c0, z) <> T.apply(zt, ct) : List<&2, Nat>}
                      {==}
                    case Con{b, bt}:
                      match b:
                        case True{}:
                          %at_patch.overlay_applies_r(zt, ct, yt, bt) : {v <> T.apply(T.apply(zt, ct), S.restrict(yt, bt)) == v <> _ : List<&2, Nat>}
                          {==}
                        case False{}:
                          %at_patch.overlay_applies_r(zt, ct, yt, bt) : {T.land(c0, z) <> T.apply(T.apply(zt, ct), S.restrict(yt, bt)) == T.land(c0, z) <> _ : List<&2, Nat>}
                          {==}

def at_patch.overlay_applies(+f: List<&2, Nat>, +c: List<&2, Maybe<&2, Nat>>, +a: List<&2, Maybe<&2, Nat>>, +s: List<&2, Bool>) -> {T.apply(f, T.overlay(c, a, s)) == T.apply(T.apply(f, c), S.restrict(a, s)) : List<&2, Nat>}:
  Equal.sym(List<&2, Nat>, T.apply(T.apply(f, c), S.restrict(a, s)), T.apply(f, T.overlay(c, a, s)), at_patch.overlay_applies_r(f, c, a, s))

# Conflicts
# ---------

# T3: every write is applied or reported, and only writes are reported
def at_patch.cover(a: List<&2, Maybe<&2, Nat>>, s: List<&2, Bool>) -> {S.or_mask(S.writes(S.restrict(a, s)), T.conflicts(a, s)) == S.writes(a) : List<&2, Bool>}:
  match a:
    case Nil{}:
      match s:
        case Nil{}:
          {==}
        case Con{b, bt}:
          {==}
    case Con{x, xt}:
      match x:
        case None{}:
          match s:
            case Nil{}:
              %at_patch.cover(xt, []) : {False{} <> S.or_mask(S.writes(S.restrict(xt, [])), T.conflicts(xt, [])) == False{} <> _ : List<&2, Bool>}
              {==}
            case Con{b, bt}:
              match b:
                case True{}:
                  %at_patch.cover(xt, bt) : {False{} <> S.or_mask(S.writes(S.restrict(xt, bt)), T.conflicts(xt, bt)) == False{} <> _ : List<&2, Bool>}
                  {==}
                case False{}:
                  %at_patch.cover(xt, bt) : {False{} <> S.or_mask(S.writes(S.restrict(xt, bt)), T.conflicts(xt, bt)) == False{} <> _ : List<&2, Bool>}
                  {==}
        case Some{v}:
          match s:
            case Nil{}:
              %at_patch.cover(xt, []) : {True{} <> S.or_mask(S.writes(S.restrict(xt, [])), T.conflicts(xt, [])) == True{} <> _ : List<&2, Bool>}
              {==}
            case Con{b, bt}:
              match b:
                case True{}:
                  %at_patch.cover(xt, bt) : {True{} <> S.or_mask(S.writes(S.restrict(xt, bt)), T.conflicts(xt, bt)) == True{} <> _ : List<&2, Bool>}
                  {==}
                case False{}:
                  %at_patch.cover(xt, bt) : {True{} <> S.or_mask(S.writes(S.restrict(xt, bt)), T.conflicts(xt, bt)) == True{} <> _ : List<&2, Bool>}
                  {==}

# T3: no conflict lies inside the scope
def at_patch.outside(a: List<&2, Maybe<&2, Nat>>, s: List<&2, Bool>) -> {S.disjoint(T.conflicts(a, s), s) == True{} : Bool}:
  match a:
    case Nil{}:
      match s:
        case Nil{}:
          {==}
        case Con{b, bt}:
          {==}
    case Con{x, xt}:
      match x:
        case None{}:
          match s:
            case Nil{}:
              {==}
            case Con{b, bt}:
              at_patch.outside(xt, bt)
        case Some{v}:
          match s:
            case Nil{}:
              {==}
            case Con{b, bt}:
              match b:
                case True{}:
                  at_patch.outside(xt, bt)
                case False{}:
                  at_patch.outside(xt, bt)

# Arrival order
# -------------

# no unit written by both patches
def at_patch.dw(p: List<&2, Maybe<&2, Nat>>, q: List<&2, Maybe<&2, Nat>>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{x, xt}:
      match q:
        case Nil{}:
          True{}
        case Con{y, yt}:
          Bool.and(Bool.not(Bool.and(Maybe.is_some(&2, Nat, x), Maybe.is_some(&2, Nat, y))), at_patch.dw(xt, yt))

def at_patch.dw_nil_r(p: List<&2, Maybe<&2, Nat>>) -> {at_patch.dw(p, []) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{x, xt}:
      {==}

def at_patch.dj_nil_l(s: List<&2, Bool>) -> {S.disjoint([], s) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case Con{b, bt}:
      {==}

def at_patch.dj_nil_r(s: List<&2, Bool>) -> {S.disjoint(s, []) == True{} : Bool}:
  match s:
    case Nil{}:
      {==}
    case Con{b, bt}:
      {==}

# two patches writing disjoint units commute
def at_patch.commute(+g: List<&2, Nat>, +p: List<&2, Maybe<&2, Nat>>, +q: List<&2, Maybe<&2, Nat>>, e: {at_patch.dw(p, q) == True{} : Bool}) -> {T.apply(T.apply(g, p), q) == T.apply(T.apply(g, q), p) : List<&2, Nat>}:
  match g:
    case Nil{}:
      match p:
        case Nil{}:
          match q:
            case Nil{}:
              {==}
            case Con{y, yt}:
              {==}
        case Con{x, xt}:
          match q:
            case Nil{}:
              {==}
            case Con{y, yt}:
              {==}
    case Con{z, zt}:
      match p:
        case Nil{}:
          match q:
            case Nil{}:
              {==}
            case Con{y, yt}:
              {==}
        case Con{x, xt}:
          match x:
            case None{}:
              match q:
                case Nil{}:
                  {==}
                case Con{y, yt}:
                  match y:
                    case None{}:
                      %at_patch.commute(zt, xt, yt, e) : {z <> T.apply(T.apply(zt, xt), yt) == z <> _ : List<&2, Nat>}
                      {==}
                    case Some{v}:
                      %at_patch.commute(zt, xt, yt, e) : {v <> T.apply(T.apply(zt, xt), yt) == v <> _ : List<&2, Nat>}
                      {==}
            case Some{u}:
              match q:
                case Nil{}:
                  {==}
                case Con{y, yt}:
                  match y:
                    case None{}:
                      %at_patch.commute(zt, xt, yt, e) : {u <> T.apply(T.apply(zt, xt), yt) == u <> _ : List<&2, Nat>}
                      {==}
                    case Some{v}:
                      at_patch.absurd({v <> T.apply(T.apply(zt, xt), yt) == u <> T.apply(T.apply(zt, yt), xt) : List<&2, Nat>}, e)

# a head written over an unwritten one keeps the patches disjoint
def at_patch.dw_cons_none(y: Maybe<&2, Nat>, -p: List<&2, Maybe<&2, Nat>>, -q: List<&2, Maybe<&2, Nat>>, h: {at_patch.dw(p, q) == True{} : Bool}) -> {at_patch.dw(y <> p, None{} <> q) == True{} : Bool}:
  match y:
    case None{}:
      h
    case Some{v}:
      h

# the writes of two patches restricted to disjoint scopes are disjoint
def at_patch.dw_restrict(+a: List<&2, Maybe<&2, Nat>>, +sa: List<&2, Bool>, +x: List<&2, Maybe<&2, Nat>>, +sb: List<&2, Bool>, e: {S.disjoint(sa, sb) == True{} : Bool}) -> {at_patch.dw(S.restrict(a, sa), S.restrict(x, sb)) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{y, yt}:
      match sa:
        case Nil{}:
          match x:
            case Nil{}:
              {==}
            case Con{w, wt}:
              match sb:
                case Nil{}:
                  at_patch.dw_restrict(yt, [], wt, [], e)
                case Con{b, bt}:
                  match b:
                    case True{}:
                      at_patch.dw_restrict(yt, [], wt, bt, at_patch.dj_nil_l(bt))
                    case False{}:
                      at_patch.dw_restrict(yt, [], wt, bt, at_patch.dj_nil_l(bt))
        case Con{c, ct}:
          match c:
            case True{}:
              match x:
                case Nil{}:
                  {==}
                case Con{w, wt}:
                  match sb:
                    case Nil{}:
                      at_patch.dw_cons_none(y, S.restrict(yt, ct), S.restrict(wt, []), at_patch.dw_restrict(yt, ct, wt, [], at_patch.dj_nil_r(ct)))
                    case Con{b, bt}:
                      match b:
                        case True{}:
                          at_patch.absurd({at_patch.dw(S.restrict(y <> yt, True{} <> ct), S.restrict(w <> wt, True{} <> bt)) == True{} : Bool}, e)
                        case False{}:
                          at_patch.dw_cons_none(y, S.restrict(yt, ct), S.restrict(wt, bt), at_patch.dw_restrict(yt, ct, wt, bt, e))
            case False{}:
              match x:
                case Nil{}:
                  {==}
                case Con{w, wt}:
                  match sb:
                    case Nil{}:
                      at_patch.dw_restrict(yt, ct, wt, [], at_patch.dj_nil_r(ct))
                    case Con{b, bt}:
                      match b:
                        case True{}:
                          at_patch.dw_restrict(yt, ct, wt, bt, e)
                        case False{}:
                          at_patch.dw_restrict(yt, ct, wt, bt, e)

# T4: two children over disjoint scopes integrate in either order
def at_patch.arrival(+f: List<&2, Nat>, +c: List<&2, Maybe<&2, Nat>>, +a: List<&2, Maybe<&2, Nat>>, +sa: List<&2, Bool>, +x: List<&2, Maybe<&2, Nat>>, +sb: List<&2, Bool>, e: {S.disjoint(sa, sb) == True{} : Bool}) -> {T.apply(f, T.overlay(T.overlay(c, a, sa), x, sb)) == T.apply(f, T.overlay(T.overlay(c, x, sb), a, sa)) : List<&2, Nat>}:
  %at_patch.overlay_applies_r(f, T.overlay(c, a, sa), x, sb) : {_ == T.apply(f, T.overlay(T.overlay(c, x, sb), a, sa)) : List<&2, Nat>}
  %at_patch.overlay_applies_r(f, c, a, sa) : {T.apply(_, S.restrict(x, sb)) == T.apply(f, T.overlay(T.overlay(c, x, sb), a, sa)) : List<&2, Nat>}
  %at_patch.overlay_applies_r(f, T.overlay(c, x, sb), a, sa) : {T.apply(T.apply(T.apply(f, c), S.restrict(a, sa)), S.restrict(x, sb)) == _ : List<&2, Nat>}
  %at_patch.overlay_applies_r(f, c, x, sb) : {T.apply(T.apply(T.apply(f, c), S.restrict(a, sa)), S.restrict(x, sb)) == T.apply(_, S.restrict(a, sa)) : List<&2, Nat>}
  at_patch.commute(T.apply(f, c), S.restrict(a, sa), S.restrict(x, sb), at_patch.dw_restrict(a, sa, x, sb, e))

# Scopes
# ------

# every unit a owns, s owns (s reads False past its end)
def at_patch.incl(a: List<&2, Bool>, s: List<&2, Bool>) -> Bool:
  match a:
    case Nil{}:
      True{}
    case Con{x, xt}:
      match s:
        case Nil{}:
          Bool.and(Bool.not(x), at_patch.incl(xt, []))
        case Con{b, bt}:
          Bool.and(Bool.or(b, Bool.not(x)), at_patch.incl(xt, bt))

# every positive count sits on a unit s owns, q no longer than s
def at_patch.cov(q: List<&2, Nat>, s: List<&2, Bool>) -> Bool:
  match q:
    case Nil{}:
      True{}
    case Con{n, qt}:
      match s:
        case Nil{}:
          False{}
        case Con{b, bt}:
          Bool.and(Bool.or(b, Nat.is_eq(n, 0n)), at_patch.cov(qt, bt))

def at_patch.eq_cov(+u: List<&2, Nat>, +s: List<&2, Bool>, +e: {S.nats_eq(u, S.counts(s)) == True{} : Bool}) -> {at_patch.cov(u, s) == True{} : Bool}:
  match u:
    case Nil{}:
      {==}
    case Con{n, ut}:
      match s:
        case Nil{}:
          at_patch.absurd({at_patch.cov(n <> ut, []) == True{} : Bool}, e)
        case Con{b, bt}:
          match b:
            case True{}:
              at_patch.eq_cov(ut, bt, at_patch.and_r(Nat.is_eq(n, 1n), S.nats_eq(ut, S.counts(bt)), e))
            case False{}:
              +e2 = e
              at_patch.and_intro(Nat.is_eq(n, 0n), at_patch.cov(ut, bt), at_patch.and_l(Nat.is_eq(n, 0n), S.nats_eq(ut, S.counts(bt)), e2), at_patch.eq_cov(ut, bt, at_patch.and_r(Nat.is_eq(n, 0n), S.nats_eq(ut, S.counts(bt)), e2)))

def at_patch.zero_r(x: Nat, -y: Nat, e: {Nat.is_eq(Nat.add(x, y), 0n) == True{} : Bool}) -> {Nat.is_eq(y, 0n) == True{} : Bool}:
  match x:
    case 0n:
      e
    case 1n+p:
      at_patch.absurd({Nat.is_eq(y, 0n) == True{} : Bool}, e)

def at_patch.zero_l(x: Nat, -y: Nat, e: {Nat.is_eq(Nat.add(x, y), 0n) == True{} : Bool}) -> {Nat.is_eq(x, 0n) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      at_patch.absurd({Nat.is_eq(1n+p, 0n) == True{} : Bool}, e)

def at_patch.cov_addv_r(+p: List<&2, Nat>, +q: List<&2, Nat>, +s: List<&2, Bool>, +e: {at_patch.cov(S.addv(p, q), s) == True{} : Bool}) -> {at_patch.cov(q, s) == True{} : Bool}:
  match p:
    case Nil{}:
      match q:
        case Nil{}:
          {==}
        case Con{y, yt}:
          e
    case Con{x, xt}:
      match q:
        case Nil{}:
          {==}
        case Con{y, yt}:
          match s:
            case Nil{}:
              at_patch.absurd({at_patch.cov(y <> yt, []) == True{} : Bool}, e)
            case Con{b, bt}:
              match b:
                case True{}:
                  at_patch.cov_addv_r(xt, yt, bt, e)
                case False{}:
                  at_patch.and_intro(Nat.is_eq(y, 0n), at_patch.cov(yt, bt), at_patch.zero_r(x, y, at_patch.and_l(Nat.is_eq(Nat.add(x, y), 0n), at_patch.cov(S.addv(xt, yt), bt), e)), at_patch.cov_addv_r(xt, yt, bt, at_patch.and_r(Nat.is_eq(Nat.add(x, y), 0n), at_patch.cov(S.addv(xt, yt), bt), e)))

def at_patch.cov_addv_l(+p: List<&2, Nat>, +q: List<&2, Nat>, +s: List<&2, Bool>, +e: {at_patch.cov(S.addv(p, q), s) == True{} : Bool}) -> {at_patch.cov(p, s) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{x, xt}:
      match q:
        case Nil{}:
          e
        case Con{y, yt}:
          match s:
            case Nil{}:
              at_patch.absurd({at_patch.cov(x <> xt, []) == True{} : Bool}, e)
            case Con{b, bt}:
              match b:
                case True{}:
                  at_patch.cov_addv_l(xt, yt, bt, e)
                case False{}:
                  at_patch.and_intro(Nat.is_eq(x, 0n), at_patch.cov(xt, bt), at_patch.zero_l(x, y, at_patch.and_l(Nat.is_eq(Nat.add(x, y), 0n), at_patch.cov(S.addv(xt, yt), bt), e)), at_patch.cov_addv_l(xt, yt, bt, at_patch.and_r(Nat.is_eq(Nat.add(x, y), 0n), at_patch.cov(S.addv(xt, yt), bt), e)))

def at_patch.cov_incl(+ls: List<&2, Bool>, +s: List<&2, Bool>, e: {at_patch.cov(S.counts(ls), s) == True{} : Bool}) -> {at_patch.incl(ls, s) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{x, xt}:
      match x:
        case True{}:
          match s:
            case Nil{}:
              at_patch.absurd({at_patch.incl(True{} <> xt, []) == True{} : Bool}, e)
            case Con{b, bt}:
              match b:
                case True{}:
                  at_patch.cov_incl(xt, bt, e)
                case False{}:
                  at_patch.absurd({at_patch.incl(True{} <> xt, False{} <> bt) == True{} : Bool}, e)
        case False{}:
          match s:
            case Nil{}:
              at_patch.absurd({at_patch.incl(False{} <> xt, []) == True{} : Bool}, e)
            case Con{b, bt}:
              match b:
                case True{}:
                  at_patch.cov_incl(xt, bt, e)
                case False{}:
                  at_patch.cov_incl(xt, bt, e)

# the counts of a split cover the scope's
def at_patch.splits_cov(+s: List<&2, Bool>, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>, e: {S.splits(s, own, ls, rs) == True{} : Bool}) -> {at_patch.cov(S.addv(S.counts(ls), S.counts(rs)), s) == True{} : Bool}:
  at_patch.cov_addv_r(S.counts(own), S.addv(S.counts(ls), S.counts(rs)), s, at_patch.eq_cov(S.addv(S.counts(own), S.addv(S.counts(ls), S.counts(rs))), s, at_patch.and_r(S.same_lengths(s, own, ls, rs), S.nats_eq(S.addv(S.counts(own), S.addv(S.counts(ls), S.counts(rs))), S.counts(s)), e)))

def at_patch.splits_l(+s: List<&2, Bool>, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>, e: {S.splits(s, own, ls, rs) == True{} : Bool}) -> {at_patch.incl(ls, s) == True{} : Bool}:
  at_patch.cov_incl(ls, s, at_patch.cov_addv_l(S.counts(ls), S.counts(rs), s, at_patch.splits_cov(s, own, ls, rs, e)))

def at_patch.splits_r(+s: List<&2, Bool>, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>, e: {S.splits(s, own, ls, rs) == True{} : Bool}) -> {at_patch.incl(rs, s) == True{} : Bool}:
  at_patch.cov_incl(rs, s, at_patch.cov_addv_r(S.counts(ls), S.counts(rs), s, at_patch.splits_cov(s, own, ls, rs, e)))

# Within
# ------

# a patch within s is its own restriction to s
def at_patch.restrict_id(+a: List<&2, Maybe<&2, Nat>>, +s: List<&2, Bool>, e: {S.within(a, s) == True{} : Bool}) -> {a == S.restrict(a, s) : List<&2, Maybe<&2, Nat>>}:
  match a:
    case Nil{}:
      {==}
    case Con{x, xt}:
      match x:
        case None{}:
          match s:
            case Nil{}:
              %at_patch.restrict_id(xt, [], e) : {None{} <> xt == None{} <> _ : List<&2, Maybe<&2, Nat>>}
              {==}
            case Con{b, bt}:
              match b:
                case True{}:
                  %at_patch.restrict_id(xt, bt, e) : {None{} <> xt == None{} <> _ : List<&2, Maybe<&2, Nat>>}
                  {==}
                case False{}:
                  %at_patch.restrict_id(xt, bt, e) : {None{} <> xt == None{} <> _ : List<&2, Maybe<&2, Nat>>}
                  {==}
        case Some{v}:
          match s:
            case Nil{}:
              at_patch.absurd({Some{v} <> xt == None{} <> S.restrict(xt, []) : List<&2, Maybe<&2, Nat>>}, e)
            case Con{b, bt}:
              match b:
                case True{}:
                  %at_patch.restrict_id(xt, bt, e) : {Some{v} <> xt == Some{v} <> _ : List<&2, Maybe<&2, Nat>>}
                  {==}
                case False{}:
                  at_patch.absurd({Some{v} <> xt == None{} <> S.restrict(xt, bt) : List<&2, Maybe<&2, Nat>>}, e)

# integrating a child over a scope inside s keeps the patch within s
def at_patch.within_overlay(+a: List<&2, Maybe<&2, Nat>>, +c: List<&2, Maybe<&2, Nat>>, +sa: List<&2, Bool>, +s: List<&2, Bool>, +hc: {S.within(c, s) == True{} : Bool}, hs: {at_patch.incl(sa, s) == True{} : Bool}) -> {S.within(T.overlay(c, a, sa), s) == True{} : Bool}:
  match a:
    case Nil{}:
      match c:
        case Nil{}:
          match sa:
            case Nil{}:
              {==}
            case Con{b, bt}:
              {==}
        case Con{c0, ct}:
          match sa:
            case Nil{}:
              hc
            case Con{b, bt}:
              hc
    case Con{x, xt}:
      match c:
        case Nil{}:
          match sa:
            case Nil{}:
              {==}
            case Con{b, bt}:
              match b:
                case True{}:
                  match s:
                    case Nil{}:
                      at_patch.absurd({S.within(T.overlay([], x <> xt, True{} <> bt), []) == True{} : Bool}, hs)
                    case Con{d, dt}:
                      match d:
                        case True{}:
                          at_patch.within_overlay(xt, [], bt, dt, {==}, hs)
                        case False{}:
                          at_patch.absurd({S.within(T.overlay([], x <> xt, True{} <> bt), False{} <> dt) == True{} : Bool}, hs)
                case False{}:
                  match s:
                    case Nil{}:
                      at_patch.within_overlay(xt, [], bt, [], {==}, hs)
                    case Con{d, dt}:
                      match d:
                        case True{}:
                          at_patch.within_overlay(xt, [], bt, dt, {==}, hs)
                        case False{}:
                          at_patch.within_overlay(xt, [], bt, dt, {==}, hs)
        case Con{c0, ct}:
          match sa:
            case Nil{}:
              hc
            case Con{b, bt}:
              match b:
                case True{}:
                  match s:
                    case Nil{}:
                      at_patch.absurd({S.within(T.overlay(c0 <> ct, x <> xt, True{} <> bt), []) == True{} : Bool}, hs)
                    case Con{d, dt}:
                      match d:
                        case True{}:
                          at_patch.within_overlay(xt, ct, bt, dt, hc, hs)
                        case False{}:
                          at_patch.absurd({S.within(T.overlay(c0 <> ct, x <> xt, True{} <> bt), False{} <> dt) == True{} : Bool}, hs)
                case False{}:
                  match s:
                    case Nil{}:
                      at_patch.and_intro(Maybe.is_none(&2, Nat, c0), S.within(T.overlay(ct, xt, bt), []), at_patch.and_l(Maybe.is_none(&2, Nat, c0), S.within(ct, []), hc), at_patch.within_overlay(xt, ct, bt, [], at_patch.and_r(Maybe.is_none(&2, Nat, c0), S.within(ct, []), hc), hs))
                    case Con{d, dt}:
                      match d:
                        case True{}:
                          at_patch.within_overlay(xt, ct, bt, dt, hc, hs)
                        case False{}:
                          at_patch.and_intro(Maybe.is_none(&2, Nat, c0), S.within(T.overlay(ct, xt, bt), dt), at_patch.and_l(Maybe.is_none(&2, Nat, c0), S.within(ct, dt), hc), at_patch.within_overlay(xt, ct, bt, dt, at_patch.and_r(Maybe.is_none(&2, Nat, c0), S.within(ct, dt), hc), hs))

# a node's patch over its children's stays within s when both do
def at_patch.within_seq(+p: List<&2, Maybe<&2, Nat>>, +q: List<&2, Maybe<&2, Nat>>, +s: List<&2, Bool>, +hp: {S.within(p, s) == True{} : Bool}, hq: {S.within(q, s) == True{} : Bool}) -> {S.within(T.seq(p, q), s) == True{} : Bool}:
  match p:
    case Nil{}:
      match q:
        case Nil{}:
          {==}
        case Con{y, yt}:
          hq
    case Con{x, xt}:
      match q:
        case Nil{}:
          hp
        case Con{y, yt}:
          match y:
            case None{}:
              match s:
                case Nil{}:
                  at_patch.and_intro(Maybe.is_none(&2, Nat, x), S.within(T.seq(xt, yt), []), at_patch.and_l(Maybe.is_none(&2, Nat, x), S.within(xt, []), hp), at_patch.within_seq(xt, yt, [], at_patch.and_r(Maybe.is_none(&2, Nat, x), S.within(xt, []), hp), hq))
                case Con{d, dt}:
                  match d:
                    case True{}:
                      at_patch.within_seq(xt, yt, dt, hp, hq)
                    case False{}:
                      at_patch.and_intro(Maybe.is_none(&2, Nat, x), S.within(T.seq(xt, yt), dt), at_patch.and_l(Maybe.is_none(&2, Nat, x), S.within(xt, dt), hp), at_patch.within_seq(xt, yt, dt, at_patch.and_r(Maybe.is_none(&2, Nat, x), S.within(xt, dt), hp), hq))
            case Some{v}:
              match s:
                case Nil{}:
                  at_patch.absurd({S.within(T.seq(x <> xt, Some{v} <> yt), []) == True{} : Bool}, hq)
                case Con{d, dt}:
                  match d:
                    case True{}:
                      at_patch.within_seq(xt, yt, dt, hp, hq)
                    case False{}:
                      at_patch.absurd({S.within(T.seq(x <> xt, Some{v} <> yt), False{} <> dt) == True{} : Bool}, hq)

# a tidy subtree's integrated patch stays within its scope
def at_patch.res_within(+n: T.Node, e: {S.tidy(n) == True{} : Bool}) -> {S.within(T.result(n), T.scope_of(T.info(n))) == True{} : Bool}:
  match n:
    case T.Leaf{i}:
      e
    case T.Split{i, own, l, r}:
      +e1 = at_patch.and_l(Bool.and(S.within(T.patch_of(i), T.scope_of(i)), S.splits(T.scope_of(i), own, T.scope_of(T.info(l)), T.scope_of(T.info(r)))), Bool.and(S.tidy(l), S.tidy(r)), e)
      +hs = at_patch.and_r(S.within(T.patch_of(i), T.scope_of(i)), S.splits(T.scope_of(i), own, T.scope_of(T.info(l)), T.scope_of(T.info(r))), e1)
      hp = at_patch.and_l(S.within(T.patch_of(i), T.scope_of(i)), S.splits(T.scope_of(i), own, T.scope_of(T.info(l)), T.scope_of(T.info(r))), e1)
      x1 = at_patch.within_overlay(T.result(l), [], T.scope_of(T.info(l)), T.scope_of(i), {==}, at_patch.splits_l(T.scope_of(i), own, T.scope_of(T.info(l)), T.scope_of(T.info(r)), hs))
      x2 = at_patch.within_overlay(T.result(r), T.overlay([], T.result(l), T.scope_of(T.info(l))), T.scope_of(T.info(r)), T.scope_of(i), x1, at_patch.splits_r(T.scope_of(i), own, T.scope_of(T.info(l)), T.scope_of(T.info(r)), hs))
      at_patch.within_seq(T.overlay(T.overlay([], T.result(l), T.scope_of(T.info(l))), T.result(r), T.scope_of(T.info(r))), T.patch_of(i), T.scope_of(i), x2, hp)

# Sequence
# --------

def at_patch.seq_apply_r(+f: List<&2, Nat>, +p: List<&2, Maybe<&2, Nat>>, +q: List<&2, Maybe<&2, Nat>>) -> {T.apply(T.apply(f, p), q) == T.apply(f, T.seq(p, q)) : List<&2, Nat>}:
  match f:
    case Nil{}:
      match p:
        case Nil{}:
          match q:
            case Nil{}:
              {==}
            case Con{y, yt}:
              {==}
        case Con{x, xt}:
          match q:
            case Nil{}:
              {==}
            case Con{y, yt}:
              {==}
    case Con{z, zt}:
      match p:
        case Nil{}:
          match q:
            case Nil{}:
              {==}
            case Con{y, yt}:
              {==}
        case Con{x, xt}:
          match q:
            case Nil{}:
              {==}
            case Con{y, yt}:
              match y:
                case None{}:
                  %at_patch.seq_apply_r(zt, xt, yt) : {T.land(x, z) <> T.apply(T.apply(zt, xt), yt) == T.land(x, z) <> _ : List<&2, Nat>}
                  {==}
                case Some{v}:
                  %at_patch.seq_apply_r(zt, xt, yt) : {v <> T.apply(T.apply(zt, xt), yt) == v <> _ : List<&2, Nat>}
                  {==}

def at_patch.app_seq_r(+ps: List<&2, List<&2, Maybe<&2, Nat>>>, +qs: List<&2, List<&2, Maybe<&2, Nat>>>, +f: List<&2, Nat>) -> {S.apply_seq(qs, S.apply_seq(ps, f)) == S.apply_seq(List.append(&2, List<&2, Maybe<&2, Nat>>, ps, qs), f) : List<&2, Nat>}:
  match ps:
    case Nil{}:
      {==}
    case Con{p, pt}:
      at_patch.app_seq_r(pt, qs, T.apply(f, p))

def at_patch.seq_split(+pl: List<&2, List<&2, Maybe<&2, Nat>>>, +pr: List<&2, List<&2, Maybe<&2, Nat>>>, +p: List<&2, Maybe<&2, Nat>>, +f: List<&2, Nat>) -> {T.apply(S.apply_seq(pr, S.apply_seq(pl, f)), p) == S.apply_seq(List.append(&2, List<&2, Maybe<&2, Nat>>, pl, List.append(&2, List<&2, Maybe<&2, Nat>>, pr, [p])), f) : List<&2, Nat>}:
  %at_patch.app_seq_r(pl, List.append(&2, List<&2, Maybe<&2, Nat>>, pr, [p]), f) : {T.apply(S.apply_seq(pr, S.apply_seq(pl, f)), p) == _ : List<&2, Nat>}
  %at_patch.app_seq_r(pr, [p], S.apply_seq(pl, f)) : {T.apply(S.apply_seq(pr, S.apply_seq(pl, f)), p) == _ : List<&2, Nat>}
  {==}

# the children's patches integrated over their scopes apply as the two
# subtrees one after the other
def at_patch.par_mid(+f: List<&2, Nat>, +a: List<&2, Maybe<&2, Nat>>, +b: List<&2, Maybe<&2, Nat>>, +sl: List<&2, Bool>, +sr: List<&2, Bool>, -pl: List<&2, List<&2, Maybe<&2, Nat>>>, -pr: List<&2, List<&2, Maybe<&2, Nat>>>, ha: {S.within(a, sl) == True{} : Bool}, hb: {S.within(b, sr) == True{} : Bool}, il: {T.apply(f, a) == S.apply_seq(pl, f) : List<&2, Nat>}, ir: {T.apply(T.apply(f, a), b) == S.apply_seq(pr, T.apply(f, a)) : List<&2, Nat>}) -> {T.apply(f, T.overlay(T.overlay([], a, sl), b, sr)) == S.apply_seq(pr, S.apply_seq(pl, f)) : List<&2, Nat>}:
  %at_patch.overlay_applies_r(f, T.overlay([], a, sl), b, sr) : {_ == S.apply_seq(pr, S.apply_seq(pl, f)) : List<&2, Nat>}
  %at_patch.overlay_applies_r(f, [], a, sl) : {T.apply(_, S.restrict(b, sr)) == S.apply_seq(pr, S.apply_seq(pl, f)) : List<&2, Nat>}
  %at_patch.app_nil(f) : {T.apply(T.apply(_, S.restrict(a, sl)), S.restrict(b, sr)) == S.apply_seq(pr, S.apply_seq(pl, f)) : List<&2, Nat>}
  %at_patch.restrict_id(a, sl, ha) : {T.apply(T.apply(f, _), S.restrict(b, sr)) == S.apply_seq(pr, S.apply_seq(pl, f)) : List<&2, Nat>}
  %at_patch.restrict_id(b, sr, hb) : {T.apply(T.apply(f, a), _) == S.apply_seq(pr, S.apply_seq(pl, f)) : List<&2, Nat>}
  %il : {T.apply(T.apply(f, a), b) == S.apply_seq(pr, _) : List<&2, Nat>}
  ir

# T5: the integrated root patch applies as every node's patch in
# post-order
def at_patch.par_seq(+t: T.Node, +f: List<&2, Nat>, e: {S.tidy(t) == True{} : Bool}) -> {T.apply(f, T.result(t)) == S.apply_seq(S.patches(t), f) : List<&2, Nat>}:
  match t:
    case T.Leaf{i}:
      {==}
    case T.Split{i, own, l, r}:
      +e2 = at_patch.and_r(Bool.and(S.within(T.patch_of(i), T.scope_of(i)), S.splits(T.scope_of(i), own, T.scope_of(T.info(l)), T.scope_of(T.info(r)))), Bool.and(S.tidy(l), S.tidy(r)), e)
      +tl = at_patch.and_l(S.tidy(l), S.tidy(r), e2)
      +tr = at_patch.and_r(S.tidy(l), S.tidy(r), e2)
      %at_patch.seq_apply_r(f, T.overlay(T.overlay([], T.result(l), T.scope_of(T.info(l))), T.result(r), T.scope_of(T.info(r))), T.patch_of(i)) : {_ == S.apply_seq(List.append(&2, List<&2, Maybe<&2, Nat>>, S.patches(l), List.append(&2, List<&2, Maybe<&2, Nat>>, S.patches(r), [T.patch_of(i)])), f) : List<&2, Nat>}
      %at_patch.seq_split(S.patches(l), S.patches(r), T.patch_of(i), f) : {T.apply(T.apply(f, T.overlay(T.overlay([], T.result(l), T.scope_of(T.info(l))), T.result(r), T.scope_of(T.info(r)))), T.patch_of(i)) == _ : List<&2, Nat>}
      Equal.cong(List<&2, Nat>, List<&2, Nat>, g => T.apply(g, T.patch_of(i)), T.apply(f, T.overlay(T.overlay([], T.result(l), T.scope_of(T.info(l))), T.result(r), T.scope_of(T.info(r)))), S.apply_seq(S.patches(r), S.apply_seq(S.patches(l), f)), at_patch.par_mid(f, T.result(l), T.result(r), T.scope_of(T.info(l)), T.scope_of(T.info(r)), S.patches(l), S.patches(r), at_patch.res_within(l, tl), at_patch.res_within(r, tr), at_patch.par_seq(l, f, tl), at_patch.par_seq(r, T.apply(f, T.result(l)), tr)))
