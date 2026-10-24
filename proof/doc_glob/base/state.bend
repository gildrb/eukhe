# eukhe: one step of the glob stepper from the state of a ranking
#
# The stepper's state after the hits sent whole rank as R is St(s, k, R):
# the page (s, k), c = s + k + 1, and the first c hits of R with their
# count and oldest time. A time is answered by the spec's Wants; a hit
# sent whole moves the state to St(Put(x, R)); the page is the spec's page
# of R (only the first c of R decide it).

import Base
import ../../../bend/doc_glob.bend as Gb
import ../../../bend/ffi_doc_glob.bend as FGb
import ../../../bend/wire.bend as Wr
import ../../../laws/doc_glob.bend as DocGlob
import ../../../laws/wire.bend as Wire
import ./rank.bend as GR
import ./keep.bend as GK

# the state of the ranking R
def gp.St(+s: Nat, +k: Nat, +R: List<&2, DocGlob.glob.Hit>) -> FGb.St:
  +c = {1n+Nat.add(s, k) : Nat}
  FGb.Gl{s, k, c, DocGlob.glob.Len(DocGlob.glob.First(R, c)), DocGlob.glob.Low(DocGlob.glob.First(R, c)), GR.gp.its(DocGlob.glob.First(R, c))}

# Code and spec helpers of one shape
# ----------------------------------

def gp.when(b: Bool, +v: Nat) -> {Gb.when(b, v) == DocGlob.glob.When(b, v) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def gp.opt(m: Maybe<&2, Nat>, rest: String) -> {FGb.put_opt(m, rest) == DocGlob.glob.spell_opt(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      {==}

def gp.size(lim: Maybe<&2, Nat>) -> {Gb.size(lim) == DocGlob.glob.Size(lim) : Nat}:
  match lim:
    case None{}:
      {==}
    case Some{l}:
      {==}

def gp.step_map(w: DocGlob.glob.Hit, r: Nat & String) -> {Wr.put_list.step(~Gb.It, ~FGb.put_it, GR.gp.it(w), r) == Wr.put_list.step(~DocGlob.glob.Hit, ~DocGlob.glob.spell_hit, w, r) : Nat & String}:
  match w:
    case DocGlob.glob.Hit{m, p}:
      match r:
        case (n, t):
          {==}

def gp.go_map(W: List<&2, DocGlob.glob.Hit>, +rest: String) -> {Wr.put_list.go(~Gb.It, ~FGb.put_it, GR.gp.its(W), rest) == Wr.put_list.go(~DocGlob.glob.Hit, ~DocGlob.glob.spell_hit, W, rest) : Nat & String}:
  match W:
    case Nil{}:
      {==}
    case +w <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Gb.It, ~FGb.put_it, GR.gp.its(t), rest), Wr.put_list.go(~DocGlob.glob.Hit, ~DocGlob.glob.spell_hit, t, rest), gp.go_map(t, rest)) : {Wr.put_list.step(~Gb.It, ~FGb.put_it, GR.gp.it(w), _) == Wr.put_list.step(~DocGlob.glob.Hit, ~DocGlob.glob.spell_hit, w, Wr.put_list.go(~DocGlob.glob.Hit, ~DocGlob.glob.spell_hit, t, rest)) : Nat & String}
      gp.step_map(w, Wr.put_list.go(~DocGlob.glob.Hit, ~DocGlob.glob.spell_hit, t, rest))

# the page's paths are spelled as the spec spells its hits
def gp.list_map(+W: List<&2, DocGlob.glob.Hit>) -> {Wr.put_list(~Gb.It, ~FGb.put_it, GR.gp.its(W), "") == Wr.put_list(~DocGlob.glob.Hit, ~DocGlob.glob.spell_hit, W, "") : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Gb.It, ~FGb.put_it, GR.gp.its(W), ""), Wr.put_list.go(~DocGlob.glob.Hit, ~DocGlob.glob.spell_hit, W, ""), gp.go_map(W, "")) : {Wr.put_list.fin(_) == Wr.put_list(~DocGlob.glob.Hit, ~DocGlob.glob.spell_hit, W, "") : String}
  {==}

# Cutting
# -------

def gp.low_len(+m: Nat, F: List<&2, DocGlob.glob.Hit>) -> {Gb.low(m, DocGlob.glob.Len(F), DocGlob.glob.Low(F)) == DocGlob.glob.Low.go(F, m) : Nat}:
  match F:
    case Nil{}:
      {==}
    case z <> u:
      match z:
        case DocGlob.glob.Hit{a, q}:
          {==}

def gp.fin_cons(y: DocGlob.glob.Hit, +t: List<&2, DocGlob.glob.Hit>, +d: Nat, ih: {Gb.fin(GR.gp.its(t), d) == Gb.Fin{GR.gp.its(DocGlob.glob.First(t, d)), DocGlob.glob.Len(DocGlob.glob.First(t, d)), DocGlob.glob.Low(DocGlob.glob.First(t, d))} : Gb.Fin}) -> {Gb.fin.cons(GR.gp.it(y), Gb.fin(GR.gp.its(t), d)) == Gb.Fin{GR.gp.its(y <> DocGlob.glob.First(t, d)), DocGlob.glob.Len(y <> DocGlob.glob.First(t, d)), DocGlob.glob.Low(y <> DocGlob.glob.First(t, d))} : Gb.Fin}:
  match y:
    case DocGlob.glob.Hit{+m, +p}:
      +F = {DocGlob.glob.First(t, d) : List<&2, DocGlob.glob.Hit>}
      %Equal.sym(Gb.Fin, Gb.fin(GR.gp.its(t), d), Gb.Fin{GR.gp.its(F), DocGlob.glob.Len(F), DocGlob.glob.Low(F)}, ih) : {Gb.fin.cons(Gb.it(m, p), _) == Gb.Fin{GR.gp.its(DocGlob.glob.Hit{m, p} <> F), DocGlob.glob.Len(DocGlob.glob.Hit{m, p} <> F), DocGlob.glob.Low(DocGlob.glob.Hit{m, p} <> F)} : Gb.Fin}
      %Equal.sym(Nat, Gb.low(m, DocGlob.glob.Len(F), DocGlob.glob.Low(F)), DocGlob.glob.Low.go(F, m), gp.low_len(m, F)) : {Gb.Fin{Gb.it(m, p) <> GR.gp.its(F), 1n+DocGlob.glob.Len(F), _} == Gb.Fin{GR.gp.its(DocGlob.glob.Hit{m, p} <> F), DocGlob.glob.Len(DocGlob.glob.Hit{m, p} <> F), DocGlob.glob.Low(DocGlob.glob.Hit{m, p} <> F)} : Gb.Fin}
      {==}

# the code's cut to c is the spec's first c, their count and oldest time
def gp.fin(L: List<&2, DocGlob.glob.Hit>, c: Nat) -> {Gb.fin(GR.gp.its(L), c) == Gb.Fin{GR.gp.its(DocGlob.glob.First(L, c)), DocGlob.glob.Len(DocGlob.glob.First(L, c)), DocGlob.glob.Low(DocGlob.glob.First(L, c))} : Gb.Fin}:
  match L:
    case Nil{}:
      {==}
    case +y <> +t:
      match c:
        case 0n:
          {==}
        case 1n++d:
          gp.fin_cons(y, t, d, gp.fin(t, d))

# Pages
# -----

def gp.first_its(L: List<&2, DocGlob.glob.Hit>, k: Nat) -> {Gb.first(GR.gp.its(L), k) == GR.gp.its(DocGlob.glob.First(L, k)) : List<&2, Gb.It>}:
  match L:
    case Nil{}:
      {==}
    case +y <> t:
      match k:
        case 0n:
          {==}
        case 1n+j:
          Equal.cong(List<&2, Gb.It>, List<&2, Gb.It>, l => GR.gp.it(y) <> l, Gb.first(GR.gp.its(t), j), GR.gp.its(DocGlob.glob.First(t, j)), gp.first_its(t, j))

def gp.after_its(L: List<&2, DocGlob.glob.Hit>, s: Nat) -> {Gb.after(GR.gp.its(L), s) == GR.gp.its(DocGlob.glob.Drop(L, s)) : List<&2, Gb.It>}:
  match L:
    case Nil{}:
      {==}
    case y <> t:
      match s:
        case 0n:
          {==}
        case 1n+j:
          gp.after_its(t, j)

def gp.drop_first(s: Nat, R: List<&2, DocGlob.glob.Hit>, +k: Nat) -> {DocGlob.glob.Drop(DocGlob.glob.First(R, 1n+Nat.add(s, k)), s) == DocGlob.glob.First(DocGlob.glob.Drop(R, s), 1n+k) : List<&2, DocGlob.glob.Hit>}:
  match s:
    case 0n:
      match R:
        case Nil{}:
          {==}
        case y <> t:
          {==}
    case 1n+j:
      match R:
        case Nil{}:
          {==}
        case y <> t:
          gp.drop_first(j, t, k)

# the page of the first s + k + 1 hits is the spec's window
def gp.page(+R: List<&2, DocGlob.glob.Hit>, +s: Nat, +k: Nat) -> {Gb.page(GR.gp.its(DocGlob.glob.First(R, 1n+Nat.add(s, k))), s, k) == GR.gp.its(DocGlob.glob.Window(R, s, k)) : List<&2, Gb.It>}:
  +F = {DocGlob.glob.First(R, 1n+Nat.add(s, k)) : List<&2, DocGlob.glob.Hit>}
  %Equal.sym(List<&2, Gb.It>, Gb.after(GR.gp.its(F), s), GR.gp.its(DocGlob.glob.Drop(F, s)), gp.after_its(F, s)) : {Gb.first(_, k) == GR.gp.its(DocGlob.glob.Window(R, s, k)) : List<&2, Gb.It>}
  %Equal.sym(List<&2, DocGlob.glob.Hit>, DocGlob.glob.Drop(F, s), DocGlob.glob.First(DocGlob.glob.Drop(R, s), 1n+k), gp.drop_first(s, R, k)) : {Gb.first(GR.gp.its(_), k) == GR.gp.its(DocGlob.glob.Window(R, s, k)) : List<&2, Gb.It>}
  %Equal.sym(List<&2, Gb.It>, Gb.first(GR.gp.its(DocGlob.glob.First(DocGlob.glob.Drop(R, s), 1n+k)), k), GR.gp.its(DocGlob.glob.First(DocGlob.glob.First(DocGlob.glob.Drop(R, s), 1n+k), k)), gp.first_its(DocGlob.glob.First(DocGlob.glob.Drop(R, s), 1n+k), k)) : {_ == GR.gp.its(DocGlob.glob.Window(R, s, k)) : List<&2, Gb.It>}
  Equal.cong(List<&2, DocGlob.glob.Hit>, List<&2, Gb.It>, l => GR.gp.its(l), DocGlob.glob.First(DocGlob.glob.First(DocGlob.glob.Drop(R, s), 1n+k), k), DocGlob.glob.First(DocGlob.glob.Drop(R, s), k), GK.gp.ff1(DocGlob.glob.Drop(R, s), k))

def gp.lt_len(a: Nat, R: List<&2, DocGlob.glob.Hit>) -> {Nat.is_lt(a, DocGlob.glob.Len(DocGlob.glob.First(R, 1n+a))) == Nat.is_lt(a, DocGlob.glob.Len(R)) : Bool}:
  match a:
    case 0n:
      match R:
        case Nil{}:
          {==}
        case y <> t:
          {==}
    case 1n+b:
      match R:
        case Nil{}:
          {==}
        case y <> t:
          gp.lt_len(b, t)

# the continuation from the first s + k + 1 hits is the spec's
def gp.next(+s: Nat, k: Nat, +R: List<&2, DocGlob.glob.Hit>) -> {Gb.next(s, k, DocGlob.glob.Len(DocGlob.glob.First(R, 1n+Nat.add(s, k)))) == DocGlob.glob.More(DocGlob.glob.Len(R), s, k) : Maybe<&2, Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      +a = {Nat.add(s, 1n+j) : Nat}
      %Equal.sym(Bool, Nat.is_lt(a, DocGlob.glob.Len(DocGlob.glob.First(R, 1n+a))), Nat.is_lt(a, DocGlob.glob.Len(R)), gp.lt_len(a, R)) : {Gb.when(_, a) == DocGlob.glob.When(Nat.is_lt(a, DocGlob.glob.Len(R)), a) : Maybe<&2, Nat>}
      gp.when(Nat.is_lt(a, DocGlob.glob.Len(R)), a)

def gp.le_len(s: Nat, R: List<&2, DocGlob.glob.Hit>, +k: Nat) -> {Nat.is_le(DocGlob.glob.Len(DocGlob.glob.First(R, 1n+Nat.add(s, k))), s) == Nat.is_le(DocGlob.glob.Len(R), s) : Bool}:
  match s:
    case 0n:
      match R:
        case Nil{}:
          {==}
        case y <> t:
          {==}
    case 1n+j:
      match R:
        case Nil{}:
          {==}
        case y <> t:
          gp.le_len(j, t, k)

def gp.first_all(s: Nat, R: List<&2, DocGlob.glob.Hit>, +k: Nat, h: {Nat.is_le(DocGlob.glob.Len(R), s) == True{} : Bool}) -> {DocGlob.glob.First(R, 1n+Nat.add(s, k)) == R : List<&2, DocGlob.glob.Hit>}:
  match s:
    case 0n:
      match R:
        case Nil{}:
          {==}
        case y <> t:
          GR.gp.absurd({DocGlob.glob.First(y <> t, 1n+k) == y <> t : List<&2, DocGlob.glob.Hit>}, h)
    case 1n+j:
      match R:
        case Nil{}:
          {==}
        case +y <> +t:
          Equal.cong(List<&2, DocGlob.glob.Hit>, List<&2, DocGlob.glob.Hit>, l => y <> l, DocGlob.glob.First(t, 1n+Nat.add(j, k)), t, gp.first_all(j, t, k, h))

def gp.past_q(q: Bool, +s: Nat, +k: Nat, +R: List<&2, DocGlob.glob.Hit>, eq: {Nat.is_le(DocGlob.glob.Len(R), s) == q : Bool}) -> {Gb.past(s, DocGlob.glob.Len(DocGlob.glob.First(R, 1n+Nat.add(s, k)))) == DocGlob.glob.Past(DocGlob.glob.Len(R), s) : Maybe<&2, Nat>}:
  match q:
    case True{}:
      %Equal.sym(List<&2, DocGlob.glob.Hit>, DocGlob.glob.First(R, 1n+Nat.add(s, k)), R, gp.first_all(s, R, k, eq)) : {Gb.past(s, DocGlob.glob.Len(_)) == DocGlob.glob.Past(DocGlob.glob.Len(R), s) : Maybe<&2, Nat>}
      gp.when(Bool.and(Nat.is_le(DocGlob.glob.Len(R), s), Nat.is_lt(0n, DocGlob.glob.Len(R))), DocGlob.glob.Len(R))
    case False{}:
      %Equal.sym(Bool, Nat.is_le(DocGlob.glob.Len(DocGlob.glob.First(R, 1n+Nat.add(s, k))), s), Nat.is_le(DocGlob.glob.Len(R), s), gp.le_len(s, R, k)) : {Gb.when(Bool.and(_, Nat.is_lt(0n, DocGlob.glob.Len(DocGlob.glob.First(R, 1n+Nat.add(s, k))))), DocGlob.glob.Len(DocGlob.glob.First(R, 1n+Nat.add(s, k)))) == DocGlob.glob.Past(DocGlob.glob.Len(R), s) : Maybe<&2, Nat>}
      %Equal.sym(Bool, Nat.is_le(DocGlob.glob.Len(R), s), False{}, eq) : {Gb.when(Bool.and(_, Nat.is_lt(0n, DocGlob.glob.Len(DocGlob.glob.First(R, 1n+Nat.add(s, k))))), DocGlob.glob.Len(DocGlob.glob.First(R, 1n+Nat.add(s, k)))) == DocGlob.glob.When(Bool.and(_, Nat.is_lt(0n, DocGlob.glob.Len(R))), DocGlob.glob.Len(R)) : Maybe<&2, Nat>}
      {==}

# the past-the-end count from the first s + k + 1 hits is the spec's
def gp.past(+s: Nat, +k: Nat, +R: List<&2, DocGlob.glob.Hit>) -> {Gb.past(s, DocGlob.glob.Len(DocGlob.glob.First(R, 1n+Nat.add(s, k)))) == DocGlob.glob.Past(DocGlob.glob.Len(R), s) : Maybe<&2, Nat>}:
  gp.past_q(Nat.is_le(DocGlob.glob.Len(R), s), s, k, R, {==})
