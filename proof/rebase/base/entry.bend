# eukhe: lemmas of the entry proofs of area rebase (bend/ffi_rebase.bend):
# a spelled request reads back (fe.req_rt) and its flat edits read back
# (fe.unflat, from fe.split and the length bound fe.len_flat); the reply is
# the spelled spec answer (fe.reply); an answer that opens with 'E' is the
# one error form (fe.refuse); a decoded request was spelled (fx.*: the
# list decoders' exactness, fe.split_exact, fe.unflat_exact).

import Base
import ../../../bend/rebase.bend as R
import ../../../bend/ffi_rebase.bend as FR
import ../../../bend/wire.bend as Wr
import ../../../spec/harness/rebase.bend as RbSpec
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/rebase.bend as Rebase
import ../../base/wire.bend as PWireBase
import ../../wire/wire_list_exact.bend as PWireListExact
import ../../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../../glob/base/entry.bend as LGlobEntry
import ../base.bend as LR
import ../rebase_refines.bend as PRebaseRefines

# Flat edits
# ----------

def fe.flat(es: List<&2, R.Edit>) -> {FR.flat(es) == Rebase.rb_flat(es) : List<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case Con{e, rest}:
      match e:
        case R.Edit{+s, +t, +ls}:
          Equal.cong(List<&2, Nat>, List<&2, Nat>, z => s <> (t <> (List.length(&2, Nat, ls) <> List.append(&2, Nat, ls, z))), FR.flat(rest), Rebase.rb_flat(rest), fe.flat(rest))

def fe.le_succ_r(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      LR.rb.absurdF({Nat.is_le(1n+p, 1n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      fe.le_succ_r(p, q, e)

def fe.le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      LR.rb.le_zero(c)
    case 1n+p 0n _:
      LR.rb.absurdF({Nat.is_le(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      LR.rb.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      fe.le_trans(p, q, r, ab, bc)

# a list after ls is no shorter than it
def fe.len_app(ls: List<&2, Nat>, +y: List<&2, Nat>) -> {Nat.is_le(List.length(&2, Nat, y), List.length(&2, Nat, List.append(&2, Nat, ls, y))) == True{} : Bool}:
  match ls:
    case Nil{}:
      LR.rb.le_refl(List.length(&2, Nat, y))
    case Con{x, +t}:
      fe.le_succ_r(List.length(&2, Nat, y), List.length(&2, Nat, List.append(&2, Nat, t, y)), fe.len_app(t, y))

# the flat edits are at least as many numbers as edits
def fe.len_flat(es: List<&2, R.Edit>) -> {Nat.is_le(List.length(&2, R.Edit, es), List.length(&2, Nat, Rebase.rb_flat(es))) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case Con{e, +rest}:
      match e:
        case R.Edit{s, t, +ls}:
          +ab = fe.le_trans(List.length(&2, R.Edit, rest), List.length(&2, Nat, Rebase.rb_flat(rest)), List.length(&2, Nat, List.append(&2, Nat, ls, Rebase.rb_flat(rest))), fe.len_flat(rest), fe.len_app(ls, Rebase.rb_flat(rest)))
          fe.le_succ_r(List.length(&2, R.Edit, rest), 1n+List.length(&2, Nat, List.append(&2, Nat, ls, Rebase.rb_flat(rest))), fe.le_succ_r(List.length(&2, R.Edit, rest), List.length(&2, Nat, List.append(&2, Nat, ls, Rebase.rb_flat(rest))), ab))

# the first |ls| ids of ls ++ y are ls
def fe.split(ls: List<&2, Nat>, +y: List<&2, Nat>) -> {FR.split(List.length(&2, Nat, ls), List.append(&2, Nat, ls, y)) == Some{FR.Cut{ls, y}} : Maybe<&2, FR.Cut>}:
  match ls:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %Equal.sym(Maybe<&2, FR.Cut>, FR.split(List.length(&2, Nat, t), List.append(&2, Nat, t, y)), Some{FR.Cut{t, y}}, fe.split(t, y)) : {FR.split.cons(x, _) == Some{FR.Cut{x <> t, y}} : Maybe<&2, FR.Cut>}
      {==}

# the flat edits read back with fuel for as many edits
def fe.unflat(es: List<&2, R.Edit>, f: Nat, le: {Nat.is_le(List.length(&2, R.Edit, es), f) == True{} : Bool}) -> {FR.unflat(f, Rebase.rb_flat(es)) == Some{es} : Maybe<&2, List<&2, R.Edit>>}:
  match es:
    case Nil{}:
      match f:
        case 0n:
          {==}
        case 1n+p:
          {==}
    case Con{e, +rest}:
      match e:
        case R.Edit{+s, +t, +ls}:
          match f:
            case 0n:
              LR.rb.absurdF({FR.unflat(0n, Rebase.rb_flat(R.Edit{s, t, ls} <> rest)) == Some{R.Edit{s, t, ls} <> rest} : Maybe<&2, List<&2, R.Edit>>}, le)
            case 1n+p:
              %Equal.sym(Maybe<&2, FR.Cut>, FR.split(List.length(&2, Nat, ls), List.append(&2, Nat, ls, Rebase.rb_flat(rest))), Some{FR.Cut{ls, Rebase.rb_flat(rest)}}, fe.split(ls, Rebase.rb_flat(rest))) : {FR.unflat.at(s, t, _, z => FR.unflat(p, z)) == Some{R.Edit{s, t, ls} <> rest} : Maybe<&2, List<&2, R.Edit>>}
              %Equal.sym(Maybe<&2, List<&2, R.Edit>>, FR.unflat(p, Rebase.rb_flat(rest)), Some{rest}, fe.unflat(rest, p, le)) : {FR.unflat.cons(R.Edit{s, t, ls}, _) == Some{R.Edit{s, t, ls} <> rest} : Maybe<&2, List<&2, R.Edit>>}
              {==}

# Requests and replies
# --------------------

# a request that fits reads back whole
def fe.req_rt(+b: List<&2, Nat>, +h: List<&2, Nat>, +es: List<&2, R.Edit>, +rest: String, fit: {Rebase.rb_fit(b, h, es) == True{} : Bool}) -> {FR.get_req(Rebase.rb_w_req(b, h, es, rest)) == Wr.Got{FR.Req{b, h, Rebase.rb_flat(es)}, rest} : Wr.Dec<FR.Req>}:
  +fx = Rebase.rb_flat(es)
  +fit0 = fit
  +fb = LR.rb.and_l(Rebase.rb_nfit(b), Bool.and(Rebase.rb_nfit(h), Rebase.rb_nfit(fx)), fit0)
  +fr = LR.rb.and_r(Rebase.rb_nfit(b), Bool.and(Rebase.rb_nfit(h), Rebase.rb_nfit(fx)), fit0)
  +fh = LR.rb.and_l(Rebase.rb_nfit(h), Rebase.rb_nfit(fx), fr)
  +ff = LR.rb.and_r(Rebase.rb_nfit(h), Rebase.rb_nfit(fx), fr)
  +r2 = Wr.put_list(~Nat, ~Wr.put_nat, fx, rest)
  +r1 = Wr.put_list(~Nat, ~Wr.put_nat, h, r2)
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, b, r1)), Wr.Got{b, r1}, Wire.wire_list_round_trip(b, r1, fb)) : {FR.get_req.base(_) == Wr.Got{FR.Req{b, h, fx}, rest} : Wr.Dec<FR.Req>}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, r1), Wr.Got{h, r2}, Wire.wire_list_round_trip(h, r2, fh)) : {FR.get_req.head(b, _) == Wr.Got{FR.Req{b, h, fx}, rest} : Wr.Dec<FR.Req>}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, r2), Wr.Got{fx, rest}, Wire.wire_list_round_trip(fx, rest, ff)) : {FR.get_req.edits(b, h, _) == Wr.Got{FR.Req{b, h, fx}, rest} : Wr.Dec<FR.Req>}
  {==}

def fe.why(w: R.Why) -> {FR.put_why(w, "") == Rebase.rb_w_why(w) : String}:
  match w:
    case R.Invalid{i}:
      {==}
    case R.Moved{i}:
      {==}
    case R.Ambiguous{i}:
      {==}
    case R.Crossed{i}:
      {==}
    case R.TooLarge{}:
      {==}

# an outcome is spelled as the laws spell it
def fe.out(o: R.Outcome) -> {FR.put_outcome(o) == Rebase.rb_w_reply(o) : String}:
  match o:
    case R.Rebased{+fs}:
      %Equal.sym(List<&2, Nat>, FR.flat(fs), Rebase.rb_flat(fs), fe.flat(fs)) : {Wr.put_nat(0n, Wr.put_list(~Nat, ~Wr.put_nat, _, "")) == Rebase.rb_w_reply(R.Rebased{fs}) : String}
      {==}
    case R.Conflict{+w}:
      %Equal.sym(String, FR.put_why(w, ""), Rebase.rb_w_why(w), fe.why(w)) : {Wr.put_nat(1n, _) == Rebase.rb_w_reply(R.Conflict{w}) : String}
      {==}

def fe.bound(q: Bool, +b: List<&2, Nat>, +h: List<&2, Nat>, +es: List<&2, R.Edit>) -> {FR.put_outcome(FR.bounded.at(q, b, h, es)) == Rebase.rb_w_reply(Rebase.rb_bounded.of(q, b, h, es)) : String}:
  match q:
    case True{}:
      %Equal.sym(R.Outcome, R.rebase(b, h, es), RbSpec.rebase(b, h, es), Rebase.rebase_refines(b, h, es)) : {FR.put_outcome(_) == Rebase.rb_w_reply(RbSpec.rebase(b, h, es)) : String}
      fe.out(RbSpec.rebase(b, h, es))
    case False{}:
      {==}

# the answer to spelled edits is the spec's within the bound, spelled
def fe.reply(+b: List<&2, Nat>, +h: List<&2, Nat>, +es: List<&2, R.Edit>) -> {FR.answer(FR.Req{b, h, Rebase.rb_flat(es)}) == Rebase.rb_w_reply(Rebase.rb_answer(b, h, es)) : String}:
  +fx = Rebase.rb_flat(es)
  %Equal.sym(Maybe<&2, List<&2, R.Edit>>, FR.unflat(List.length(&2, Nat, fx), fx), Some{es}, fe.unflat(es, List.length(&2, Nat, fx), fe.len_flat(es))) : {FR.answer.of(_, b, h) == Rebase.rb_w_reply(Rebase.rb_answer(b, h, es)) : String}
  fe.bound(Nat.is_le(Nat.mul(List.length(&2, R.Edit, es), Nat.add(List.length(&2, Nat, b), List.length(&2, Nat, h))), Rebase.rb_work_max()), b, h, es)

# Errors
# ------

def fe.out_ok(o: R.Outcome) -> {LawsBase.wire_opens_err(FR.put_outcome(o)) == False{} : Bool}:
  match o:
    case R.Rebased{fs}:
      Wire.wire_nat_not_err(0n, Wr.put_list(~Nat, ~Wr.put_nat, FR.flat(fs), ""))
    case R.Conflict{w}:
      Wire.wire_nat_not_err(1n, FR.put_why(w, ""))

def fe.of_refuse(m: Maybe<&2, List<&2, R.Edit>>, +b: List<&2, Nat>, +h: List<&2, Nat>, bad: {LawsBase.wire_opens_err(FR.answer.of(m, b, h)) == True{} : Bool}) -> {FR.answer.of(m, b, h) == Wr.err("rebase: malformed request") : String}:
  match m:
    case None{}:
      {==}
    case Some{+es}:
      LR.rb.absurd({FR.put_outcome(FR.bounded(b, h, es)) == Wr.err("rebase: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FR.put_outcome(FR.bounded(b, h, es))), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FR.put_outcome(FR.bounded(b, h, es))), True{}, bad), fe.out_ok(FR.bounded(b, h, es))))

# an answer that opens with 'E' is the one error form
def fe.refuse(x: Wr.Dec<FR.Req>, bad: {LawsBase.wire_opens_err(FR.ffi.got(x)) == True{} : Bool}) -> {FR.ffi.got(x) == Wr.err("rebase: malformed request") : String}:
  match x:
    case Wr.Got{q, rest}:
      match q:
        case FR.Req{+b, +h, +xs}:
          match rest:
            case SNil{}:
              fe.of_refuse(FR.unflat(List.length(&2, Nat, xs), xs), b, h, bad)
            case SCon{y, z}:
              {==}
    case Wr.Bad{}:
      {==}

# Decoded requests were spelled
# -----------------------------

def fe.MB(m: Maybe<&2, List<&2, R.Edit>>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# None is not Some
def fe.none_some(-A: Type, -x: List<&2, R.Edit>, e: {None{} == Some{x} : Maybe<&2, List<&2, R.Edit>>}) -> A:
  %e : fe.MB(_, A)
  Unit{}

def fe.MC(m: Maybe<&2, FR.Cut>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

def fe.none_cut(-A: Type, -x: FR.Cut, e: {None{} == Some{x} : Maybe<&2, FR.Cut>}) -> A:
  %e : fe.MC(_, A)
  Unit{}

def fe.unsome(m: Maybe<&2, List<&2, R.Edit>>) -> List<&2, R.Edit>:
  match m:
    case None{}:
      Nil{}
    case Some{x}:
      x

def fe.cut_l(m: Maybe<&2, FR.Cut>) -> List<&2, Nat>:
  match m:
    case None{}:
      Nil{}
    case Some{c}:
      match c:
        case FR.Cut{l, r}:
          l

def fe.cut_r(m: Maybe<&2, FR.Cut>) -> List<&2, Nat>:
  match m:
    case None{}:
      Nil{}
    case Some{c}:
      match c:
        case FR.Cut{l, r}:
          r

def fe.se.fin(+x: Nat, -p: Nat, -t: List<&2, Nat>, +l2: List<&2, Nat>, +r2: List<&2, Nat>, -ls: List<&2, Nat>, -rest: List<&2, Nat>, el: {x <> l2 == ls : List<&2, Nat>}, er: {r2 == rest : List<&2, Nat>}, both: {t == List.append(&2, Nat, l2, r2) : List<&2, Nat>} & {p == List.length(&2, Nat, l2) : Nat})
  -> {x <> t == List.append(&2, Nat, ls, rest) : List<&2, Nat>} & {1n+p == List.length(&2, Nat, ls) : Nat}:
  (et, ep) = both
  %el : {x <> t == List.append(&2, Nat, _, rest) : List<&2, Nat>} & {1n+p == List.length(&2, Nat, _) : Nat}
  %er : {x <> t == List.append(&2, Nat, x <> l2, _) : List<&2, Nat>} & {1n+p == List.length(&2, Nat, x <> l2) : Nat}
  %Equal.sym(List<&2, Nat>, t, List.append(&2, Nat, l2, r2), et) : {x <> _ == List.append(&2, Nat, x <> l2, r2) : List<&2, Nat>} & {1n+p == List.length(&2, Nat, x <> l2) : Nat}
  %Equal.sym(Nat, p, List.length(&2, Nat, l2), ep) : {x <> List.append(&2, Nat, l2, r2) == List.append(&2, Nat, x <> l2, r2) : List<&2, Nat>} & {1n+_ == List.length(&2, Nat, x <> l2) : Nat}
  ({==}, {==})

def fe.se.cons(+x: Nat, -p: Nat, -t: List<&2, Nat>, m: Maybe<&2, FR.Cut>, em: {FR.split(p, t) == m : Maybe<&2, FR.Cut>}, +ls: List<&2, Nat>, +rest: List<&2, Nat>,
  e: {FR.split.cons(x, m) == Some{FR.Cut{ls, rest}} : Maybe<&2, FR.Cut>},
  ih: @l2: List<&2, Nat> -> @r2: List<&2, Nat> -> {FR.split(p, t) == Some{FR.Cut{l2, r2}} : Maybe<&2, FR.Cut>} -> ({t == List.append(&2, Nat, l2, r2) : List<&2, Nat>} & {p == List.length(&2, Nat, l2) : Nat}))
  -> {x <> t == List.append(&2, Nat, ls, rest) : List<&2, Nat>} & {1n+p == List.length(&2, Nat, ls) : Nat}:
  match m:
    case None{}:
      fe.none_cut({x <> t == List.append(&2, Nat, ls, rest) : List<&2, Nat>} & {1n+p == List.length(&2, Nat, ls) : Nat}, FR.Cut{ls, rest}, e)
    case Some{c}:
      match c:
        case FR.Cut{+l2, +r2}:
          +e0 = e
          +el = Equal.cong(Maybe<&2, FR.Cut>, List<&2, Nat>, fe.cut_l, Some{FR.Cut{x <> l2, r2}}, Some{FR.Cut{ls, rest}}, e0)
          +er = Equal.cong(Maybe<&2, FR.Cut>, List<&2, Nat>, fe.cut_r, Some{FR.Cut{x <> l2, r2}}, Some{FR.Cut{ls, rest}}, e0)
          fe.se.fin(x, p, t, l2, r2, ls, rest, el, er, ih(l2, r2, em))

# a split read ls then rest from what it was given
def fe.split_exact(n: Nat, xs: List<&2, Nat>, +ls: List<&2, Nat>, +rest: List<&2, Nat>, e: {FR.split(n, xs) == Some{FR.Cut{ls, rest}} : Maybe<&2, FR.Cut>}) -> {xs == List.append(&2, Nat, ls, rest) : List<&2, Nat>} & {n == List.length(&2, Nat, ls) : Nat}:
  match n xs:
    case 0n Nil{}:
      +e0 = e
      %Equal.cong(Maybe<&2, FR.Cut>, List<&2, Nat>, fe.cut_l, Some{FR.Cut{Nil{}, Nil{}}}, Some{FR.Cut{ls, rest}}, e0) : {Nil{} == List.append(&2, Nat, _, rest) : List<&2, Nat>} & {0n == List.length(&2, Nat, _) : Nat}
      %Equal.cong(Maybe<&2, FR.Cut>, List<&2, Nat>, fe.cut_r, Some{FR.Cut{Nil{}, Nil{}}}, Some{FR.Cut{ls, rest}}, e0) : {Nil{} == List.append(&2, Nat, Nil{}, _) : List<&2, Nat>} & {0n == 0n : Nat}
      ({==}, {==})
    case 0n Con{+y, +yt}:
      +e0 = e
      %Equal.cong(Maybe<&2, FR.Cut>, List<&2, Nat>, fe.cut_l, Some{FR.Cut{Nil{}, y <> yt}}, Some{FR.Cut{ls, rest}}, e0) : {y <> yt == List.append(&2, Nat, _, rest) : List<&2, Nat>} & {0n == List.length(&2, Nat, _) : Nat}
      %Equal.cong(Maybe<&2, FR.Cut>, List<&2, Nat>, fe.cut_r, Some{FR.Cut{Nil{}, y <> yt}}, Some{FR.Cut{ls, rest}}, e0) : {y <> yt == List.append(&2, Nat, Nil{}, _) : List<&2, Nat>} & {0n == 0n : Nat}
      ({==}, {==})
    case 1n+p Nil{}:
      fe.none_cut({Nil{} == List.append(&2, Nat, ls, rest) : List<&2, Nat>} & {1n+p == List.length(&2, Nat, ls) : Nat}, FR.Cut{ls, rest}, e)
    case 1n++p Con{+x, +t}:
      fe.se.cons(x, p, t, FR.split(p, t), {==}, ls, rest, e, l2 => r2 => e2 => fe.split_exact(p, t, l2, r2, e2))

def fe.ue.cons(+s: Nat, +t: Nat, -n: Nat, -r3: List<&2, Nat>, +ls: List<&2, Nat>, +rest: List<&2, Nat>, -p: Nat, m2: Maybe<&2, List<&2, R.Edit>>, em2: {FR.unflat(p, rest) == m2 : Maybe<&2, List<&2, R.Edit>>}, -es: List<&2, R.Edit>,
  e: {FR.unflat.cons(R.Edit{s, t, ls}, m2) == Some{es} : Maybe<&2, List<&2, R.Edit>>},
  sp: {r3 == List.append(&2, Nat, ls, rest) : List<&2, Nat>} & {n == List.length(&2, Nat, ls) : Nat},
  ih: @rs: List<&2, Nat> -> @es2: List<&2, R.Edit> -> {FR.unflat(p, rs) == Some{es2} : Maybe<&2, List<&2, R.Edit>>} -> {rs == Rebase.rb_flat(es2) : List<&2, Nat>})
  -> {s <> (t <> (n <> r3)) == Rebase.rb_flat(es) : List<&2, Nat>}:
  match m2:
    case None{}:
      fe.none_some({s <> (t <> (n <> r3)) == Rebase.rb_flat(es) : List<&2, Nat>}, es, e)
    case Some{+es2}:
      (er3, en) = sp
      %Equal.cong(Maybe<&2, List<&2, R.Edit>>, List<&2, R.Edit>, fe.unsome, Some{R.Edit{s, t, ls} <> es2}, Some{es}, e) : {s <> (t <> (n <> r3)) == Rebase.rb_flat(_) : List<&2, Nat>}
      %Equal.sym(Nat, n, List.length(&2, Nat, ls), en) : {s <> (t <> (_ <> r3)) == Rebase.rb_flat(R.Edit{s, t, ls} <> es2) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, r3, List.append(&2, Nat, ls, rest), er3) : {s <> (t <> (List.length(&2, Nat, ls) <> _)) == Rebase.rb_flat(R.Edit{s, t, ls} <> es2) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, rest, Rebase.rb_flat(es2), ih(rest, es2, em2)) : {s <> (t <> (List.length(&2, Nat, ls) <> List.append(&2, Nat, ls, _))) == Rebase.rb_flat(R.Edit{s, t, ls} <> es2) : List<&2, Nat>}
      {==}

def fe.ue.at(+s: Nat, +t: Nat, +n: Nat, +r3: List<&2, Nat>, +p: Nat, m: Maybe<&2, FR.Cut>, em: {FR.split(n, r3) == m : Maybe<&2, FR.Cut>}, -es: List<&2, R.Edit>,
  e: {FR.unflat.at(s, t, m, z => FR.unflat(p, z)) == Some{es} : Maybe<&2, List<&2, R.Edit>>},
  ih: @rs: List<&2, Nat> -> @es2: List<&2, R.Edit> -> {FR.unflat(p, rs) == Some{es2} : Maybe<&2, List<&2, R.Edit>>} -> {rs == Rebase.rb_flat(es2) : List<&2, Nat>})
  -> {s <> (t <> (n <> r3)) == Rebase.rb_flat(es) : List<&2, Nat>}:
  match m:
    case None{}:
      fe.none_some({s <> (t <> (n <> r3)) == Rebase.rb_flat(es) : List<&2, Nat>}, es, e)
    case Some{c}:
      match c:
        case FR.Cut{+ls, +rest}:
          fe.ue.cons(s, t, n, r3, ls, rest, p, FR.unflat(p, rest), {==}, es, e, fe.split_exact(n, r3, ls, rest, em), ih)

# flat edits read back were spelled from them
def fe.unflat_exact(f: Nat, xs: List<&2, Nat>, +es: List<&2, R.Edit>, e: {FR.unflat(f, xs) == Some{es} : Maybe<&2, List<&2, R.Edit>>}) -> {xs == Rebase.rb_flat(es) : List<&2, Nat>}:
  match f xs:
    case 0n Nil{}:
      %Equal.cong(Maybe<&2, List<&2, R.Edit>>, List<&2, R.Edit>, fe.unsome, Some{Nil{}}, Some{es}, e) : {Nil{} == Rebase.rb_flat(_) : List<&2, Nat>}
      {==}
    case 0n Con{x, xt}:
      fe.none_some({x <> xt == Rebase.rb_flat(es) : List<&2, Nat>}, es, e)
    case 1n+p Nil{}:
      %Equal.cong(Maybe<&2, List<&2, R.Edit>>, List<&2, R.Edit>, fe.unsome, Some{Nil{}}, Some{es}, e) : {Nil{} == Rebase.rb_flat(_) : List<&2, Nat>}
      {==}
    case 1n++p Con{+s, r1}:
      match r1:
        case Nil{}:
          fe.none_some({[s] == Rebase.rb_flat(es) : List<&2, Nat>}, es, e)
        case Con{+t, r2}:
          match r2:
            case Nil{}:
              fe.none_some({[s, t] == Rebase.rb_flat(es) : List<&2, Nat>}, es, e)
            case Con{+n, +r3}:
              fe.ue.at(s, t, n, r3, p, FR.split(n, r3), {==}, es, e, rs => es2 => e2 => fe.unflat_exact(p, rs, es2, e2))

def fx.T(s: String) -> Type:
  Sigma<&1, &1, Rebase.Ask, q => {s == Rebase.rb_w_ask(q) : String} & {Rebase.rb_fit_ask(q) == True{} : Bool}>

def fx.of(m: Maybe<&2, List<&2, R.Edit>>, -s: String, +b: List<&2, Nat>, +h: List<&2, Nat>, +xs: List<&2, Nat>, em: {FR.unflat(List.length(&2, Nat, xs), xs) == m : Maybe<&2, List<&2, R.Edit>>},
  pre: {s == Wr.put_list(~Nat, ~Wr.put_nat, b, Wr.put_list(~Nat, ~Wr.put_nat, h, Wr.put_list(~Nat, ~Wr.put_nat, xs, ""))) : String},
  fb: {Rebase.rb_nfit(b) == True{} : Bool}, fh: {Rebase.rb_nfit(h) == True{} : Bool}, fxs: {Rebase.rb_nfit(xs) == True{} : Bool},
  ok: {LawsBase.wire_opens_err(FR.answer.of(m, b, h)) == False{} : Bool}) -> fx.T(s):
  match m:
    case None{}:
      LR.rb.absurd(fx.T(s), ok)
    case Some{+es}:
      +ex = fe.unflat_exact(List.length(&2, Nat, xs), xs, es, em)
      +sp = Equal.trans(String, s, Wr.put_list(~Nat, ~Wr.put_nat, b, Wr.put_list(~Nat, ~Wr.put_nat, h, Wr.put_list(~Nat, ~Wr.put_nat, xs, ""))), Wr.put_list(~Nat, ~Wr.put_nat, b, Wr.put_list(~Nat, ~Wr.put_nat, h, Wr.put_list(~Nat, ~Wr.put_nat, Rebase.rb_flat(es), ""))), pre, Equal.cong(List<&2, Nat>, String, z => Wr.put_list(~Nat, ~Wr.put_nat, b, Wr.put_list(~Nat, ~Wr.put_nat, h, Wr.put_list(~Nat, ~Wr.put_nat, z, ""))), xs, Rebase.rb_flat(es), ex))
      +ff = Equal.trans(Bool, Rebase.rb_nfit(Rebase.rb_flat(es)), Rebase.rb_nfit(xs), True{}, Equal.cong(List<&2, Nat>, Bool, z => Rebase.rb_nfit(z), Rebase.rb_flat(es), xs, Equal.sym(List<&2, Nat>, xs, Rebase.rb_flat(es), ex)), fxs)
      (Rebase.Ask{b, h, es}, (sp, LR.rb.and_t(Rebase.rb_nfit(b), Bool.and(Rebase.rb_nfit(h), Rebase.rb_nfit(Rebase.rb_flat(es))), fb, LR.rb.and_t(Rebase.rb_nfit(h), Rebase.rb_nfit(Rebase.rb_flat(es)), fh, ff))))

def fx.done(-s: String, +b: List<&2, Nat>, +h: List<&2, Nat>, +xs: List<&2, Nat>, rest: String,
  pre: {s == Wr.put_list(~Nat, ~Wr.put_nat, b, Wr.put_list(~Nat, ~Wr.put_nat, h, Wr.put_list(~Nat, ~Wr.put_nat, xs, rest))) : String},
  fb: {Rebase.rb_nfit(b) == True{} : Bool}, fh: {Rebase.rb_nfit(h) == True{} : Bool}, fxs: {Rebase.rb_nfit(xs) == True{} : Bool},
  ok: {LawsBase.wire_opens_err(FR.ffi.done(FR.Req{b, h, xs}, Wr.end(rest))) == False{} : Bool}) -> fx.T(s):
  match rest:
    case SNil{}:
      fx.of(FR.unflat(List.length(&2, Nat, xs), xs), s, b, h, xs, {==}, pre, fb, fh, fxs, ok)
    case SCon{y, z}:
      LR.rb.absurd(fx.T(s), ok)

def fx.edits(-s: String, +b: List<&2, Nat>, +h: List<&2, Nat>, +s2: String,
  pre: {s == Wr.put_list(~Nat, ~Wr.put_nat, b, Wr.put_list(~Nat, ~Wr.put_nat, h, s2)) : String},
  fb: {Rebase.rb_nfit(b) == True{} : Bool}, fh: {Rebase.rb_nfit(h) == True{} : Bool},
  d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s2) == d : Wr.Dec<List<&2, Nat>>},
  ok: {LawsBase.wire_opens_err(FR.ffi.got(FR.get_req.edits(b, h, d))) == False{} : Bool}) -> fx.T(s):
  match d:
    case Wr.Got{+xs, +s3}:
      +e = ed
      +ex = Wire.wire_list_exact(s2, xs, s3, e)
      +pre2 = Equal.trans(String, s, Wr.put_list(~Nat, ~Wr.put_nat, b, Wr.put_list(~Nat, ~Wr.put_nat, h, s2)), Wr.put_list(~Nat, ~Wr.put_nat, b, Wr.put_list(~Nat, ~Wr.put_nat, h, Wr.put_list(~Nat, ~Wr.put_nat, xs, s3))), pre, Equal.cong(String, String, z => Wr.put_list(~Nat, ~Wr.put_nat, b, Wr.put_list(~Nat, ~Wr.put_nat, h, z)), s2, Wr.put_list(~Nat, ~Wr.put_nat, xs, s3), ex))
      fx.done(s, b, h, xs, s3, pre2, fb, fh, LGlobEntry.ge.nats_fit(s2, xs, s3, e), ok)
    case Wr.Bad{}:
      LR.rb.absurd(fx.T(s), ok)

def fx.head(-s: String, +b: List<&2, Nat>, +s1: String,
  pre: {s == Wr.put_list(~Nat, ~Wr.put_nat, b, s1) : String},
  fb: {Rebase.rb_nfit(b) == True{} : Bool},
  d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s1) == d : Wr.Dec<List<&2, Nat>>},
  ok: {LawsBase.wire_opens_err(FR.ffi.got(FR.get_req.head(b, d))) == False{} : Bool}) -> fx.T(s):
  match d:
    case Wr.Got{+h, +s2}:
      +e = ed
      +eh = Wire.wire_list_exact(s1, h, s2, e)
      +pre2 = Equal.trans(String, s, Wr.put_list(~Nat, ~Wr.put_nat, b, s1), Wr.put_list(~Nat, ~Wr.put_nat, b, Wr.put_list(~Nat, ~Wr.put_nat, h, s2)), pre, Equal.cong(String, String, z => Wr.put_list(~Nat, ~Wr.put_nat, b, z), s1, Wr.put_list(~Nat, ~Wr.put_nat, h, s2), eh))
      fx.edits(s, b, h, s2, pre2, fb, LGlobEntry.ge.nats_fit(s1, h, s2, e), Wr.get_list(~Nat, ~Wr.get_nat, s2), {==}, ok)
    case Wr.Bad{}:
      LR.rb.absurd(fx.T(s), ok)

# an answered input is a spelled request that fits
def fx.base(+s: String, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s) == d : Wr.Dec<List<&2, Nat>>}, ok: {LawsBase.wire_opens_err(FR.ffi.got(FR.get_req.base(d))) == False{} : Bool}) -> fx.T(s):
  match d:
    case Wr.Got{+b, +s1}:
      +e = ed
      fx.head(s, b, s1, Wire.wire_list_exact(s, b, s1, e), LGlobEntry.ge.nats_fit(s, b, s1, e), Wr.get_list(~Nat, ~Wr.get_nat, s1), {==}, ok)
    case Wr.Bad{}:
      LR.rb.absurd(fx.T(s), ok)
