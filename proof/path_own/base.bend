# eukhe: lemmas the proofs of area path_own share: what one rule answers,
# the first naming rule of two lists of rules, and the entry: a request
# read back, the reply spelled

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/path_own.bend as Po
import ../../bend/ffi_path_own.bend as FPo
import ../../bend/wire.bend as Wr
import ../../bend/wire_flat.bend as Fl
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/path_own.bend as PathOwn
import ../base/wire.bend as LWire
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip
import ../irreversible/base.bend as LIr

# One rule
# --------

# A at Own, Unit at Judged: refutes {Judged{c} == Own{i}}
def po.WM(x: Po.Wc, A: Type) -> Type:
  match x:
    case Po.Judged{c}:
      Unit
    case Po.Own{i}:
      A

# one rule answers Own only when it names the path (u: whether it does)
def po.hit(u: Bool, -c: Pp.Cls, h: {Po.of(Po.first.pick(u, 0n, None{}), c) == Po.Own{0n} : Po.Wc}) -> {u == True{} : Bool}:
  match u:
    case True{}:
      {==}
    case False{}:
      %h : po.WM(_, {False{} == True{} : Bool})
      Unit{}

# one rule answers Own at place 0 or the judge's class
def po.one(b: Bool, +c: Pp.Cls) -> {PathOwn.po_one(Po.of(Po.first.pick(b, 0n, None{}), c), c) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      LIr.irb.eq_refl(PathOwn.sp_po_code(c))

# Two lists of rules
# ------------------

# a's place, else b
def po.fthen(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match a:
    case Some{i}:
      Some{i}
    case None{}:
      b

# a place n further on
def po.mshift(n: Nat, m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{j}:
      Some{Nat.add(n, j)}

def po.shift_at(b: Bool, -rest: List<&2, Po.Rule>, -at: List<&2, Nat>, +i: Nat, +j: Nat, ih: {Po.first(rest, at, Nat.add(i, 1n+j)) == po.mshift(i, Po.first(rest, at, 1n+j)) : Maybe<&2, Nat>}) -> {Po.first.pick(b, Nat.add(i, j), Po.first(rest, at, 1n+Nat.add(i, j))) == po.mshift(i, Po.first.pick(b, j, Po.first(rest, at, 1n+j))) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      %LIr.irb.add_succ(i, j) : {Po.first(rest, at, _) == po.mshift(i, Po.first(rest, at, 1n+j)) : Maybe<&2, Nat>}
      ih

# counting from i + j is counting from j, every place i further on
def po.first_shift(ys: List<&2, Po.Rule>, +at: List<&2, Nat>, +i: Nat, +j: Nat) -> {Po.first(ys, at, Nat.add(i, j)) == po.mshift(i, Po.first(ys, at, j)) : Maybe<&2, Nat>}:
  match ys:
    case Nil{}:
      {==}
    case +r <> +rest:
      po.shift_at(Po.names(r, at), rest, at, i, j, po.first_shift(rest, at, i, 1n+j))

def po.app_at(b: Bool, -t: List<&2, Po.Rule>, -ys: List<&2, Po.Rule>, -at: List<&2, Nat>, +j: Nat, +n: Nat, ih: {Po.first(List.append(&2, Po.Rule, t, ys), at, 1n+j) == po.fthen(Po.first(t, at, 1n+j), Po.first(ys, at, Nat.add(n, 1n+j))) : Maybe<&2, Nat>}) -> {Po.first.pick(b, j, Po.first(List.append(&2, Po.Rule, t, ys), at, 1n+j)) == po.fthen(Po.first.pick(b, j, Po.first(t, at, 1n+j)), Po.first(ys, at, 1n+Nat.add(n, j))) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      %LIr.irb.add_succ(n, j) : {Po.first(List.append(&2, Po.Rule, t, ys), at, 1n+j) == po.fthen(Po.first(t, at, 1n+j), Po.first(ys, at, _)) : Maybe<&2, Nat>}
      ih

# the first naming rule of xs then ys: the one of xs, else the one of ys
# counted past xs
def po.first_app(xs: List<&2, Po.Rule>, +ys: List<&2, Po.Rule>, +at: List<&2, Nat>, +j: Nat) -> {Po.first(List.append(&2, Po.Rule, xs, ys), at, j) == po.fthen(Po.first(xs, at, j), Po.first(ys, at, Nat.add(List.length(&2, Po.Rule, xs), j))) : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +r <> +t:
      po.app_at(Po.names(r, at), t, ys, at, j, List.length(&2, Po.Rule, t), po.first_app(t, ys, at, 1n+j))

# the answer of the joined places is the spec's join of the answers
def po.then_of(a: Maybe<&2, Nat>, +n: Nat, b: Maybe<&2, Nat>, +c: Pp.Cls) -> {Po.of(po.fthen(a, po.mshift(n, b)), c) == PathOwn.po_then(Po.of(a, c), n, Po.of(b, c)) : Po.Wc}:
  match a:
    case Some{i}:
      {==}
    case None{}:
      match b:
        case None{}:
          {==}
        case Some{j}:
          {==}

# The entry: spelling
# -------------------

def po.one_flat(xs: List<&2, Nat>, +rest: List<&2, Nat>) -> {Fl.one(xs, rest) == List.append(&2, Nat, PathOwn.po_succ(xs), 0n <> rest) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => (1n+x) <> z, Fl.one(t, rest), List.append(&2, Nat, PathOwn.po_succ(t), 0n <> rest), po.one_flat(t, rest))

# the entry's flat list is the spec's
def po.flat(xss: List<&2, List<&2, Nat>>) -> {Fl.flat(xss) == PathOwn.po_flat(xss) : List<&2, Nat>}:
  match xss:
    case Nil{}:
      {==}
    case +xs <> +t:
      Equal.trans(List<&2, Nat>, Fl.one(xs, Fl.flat(t)), List.append(&2, Nat, PathOwn.po_succ(xs), 0n <> Fl.flat(t)), List.append(&2, Nat, PathOwn.po_succ(xs), 0n <> PathOwn.po_flat(t)), po.one_flat(xs, Fl.flat(t)), Equal.cong(List<&2, Nat>, List<&2, Nat>, z => List.append(&2, Nat, PathOwn.po_succ(xs), 0n <> z), Fl.flat(t), PathOwn.po_flat(t), po.flat(t)))

# the rules as Rust writes them: one flat list
def po.F(rs: List<&2, Po.Rule>) -> List<&2, Nat>:
  PathOwn.po_flat(PathOwn.sp_po_rules(rs))

def po.rule_rt(r: Po.Rule, +t: List<&2, Po.Rule>) -> {FPo.rules.cons(FPo.rule.of(PathOwn.sp_po_rule(r)), Some{t}) == Some{r <> t} : Maybe<&2, List<&2, Po.Rule>>}:
  match r:
    case Po.Tree{p}:
      {==}
    case Po.Dir{p}:
      {==}

# the rules Rust writes read back as the rules
def po.rules_rt(rs: List<&2, Po.Rule>) -> {FPo.rules.of(PathOwn.sp_po_rules(rs)) == Some{rs} : Maybe<&2, List<&2, Po.Rule>>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      %Equal.sym(Maybe<&2, List<&2, Po.Rule>>, FPo.rules.of(PathOwn.sp_po_rules(t)), Some{t}, po.rules_rt(t)) : {FPo.rules.cons(FPo.rule.of(PathOwn.sp_po_rule(r)), _) == Some{r <> t} : Maybe<&2, List<&2, Po.Rule>>}
      po.rule_rt(r, t)

def po.cls_rt(c: Pp.Cls) -> {FPo.cls.of(PathOwn.sp_po_code(c)) == Some{c} : Maybe<&2, Pp.Cls>}:
  match c:
    case Pp.Inside{}:
      {==}
    case Pp.Outside{}:
      {==}
    case Pp.Protected{}:
      {==}
    case Pp.Secret{}:
      {==}

def po.code_fits(c: Pp.Cls) -> {LawsBase.wire_fits(PathOwn.sp_po_code(c)) == True{} : Bool}:
  match c:
    case Pp.Inside{}:
      {==}
    case Pp.Outside{}:
      {==}
    case Pp.Protected{}:
      {==}
    case Pp.Secret{}:
      {==}

# the request Rust writes reads back, the rest untouched
def po.rt(q: FPo.Req, +rest: String, +fits: {PathOwn.po_req_fits(q) == True{} : Bool}) -> {FPo.get_req(PathOwn.sp_po_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FPo.Req>}:
  match q:
    case FPo.Req{+rs, +at, +c, +w}:
      +xss = PathOwn.sp_po_rules(rs)
      +ns = PathOwn.po_flat(xss)
      +k = PathOwn.sp_po_code(c)
      +r3 = Wr.put_bool(w, rest)
      +r2 = Wr.put_nat(k, r3)
      +r1 = PathOwn.sp_po_ns(at, r2)
      +fr = LIr.irb.and_l(PathOwn.po_ns_fit(ns), PathOwn.po_ns_fit(at), fits)
      +fa = LIr.irb.and_r(PathOwn.po_ns_fit(ns), PathOwn.po_ns_fit(at), fits)
      +goal = {Wr.Got{FPo.Req{rs, at, c, w}, rest} : Wr.Dec<FPo.Req>}
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, PathOwn.sp_po_ns(ns, r1)), Wr.Got{ns, r1}, Wire.wire_list_round_trip(ns, r1, fr)) : {FPo.get_req.rules(_) == goal : Wr.Dec<FPo.Req>}
      %po.flat(xss) : {FPo.get_req.rs(FPo.rules.flat(Fl.unflat(_)), r1) == goal : Wr.Dec<FPo.Req>}
      %Equal.sym(Maybe<&2, List<&2, List<&2, Nat>>>, Fl.unflat(Fl.flat(xss)), Some{xss}, LWire.fe.unflat_flat(xss)) : {FPo.get_req.rs(FPo.rules.flat(_), r1) == goal : Wr.Dec<FPo.Req>}
      %Equal.sym(Maybe<&2, List<&2, Po.Rule>>, FPo.rules.of(xss), Some{rs}, po.rules_rt(rs)) : {FPo.get_req.rs(_, r1) == goal : Wr.Dec<FPo.Req>}
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, PathOwn.sp_po_ns(at, r2)), Wr.Got{at, r2}, Wire.wire_list_round_trip(at, r2, fa)) : {FPo.get_req.at(rs, _) == goal : Wr.Dec<FPo.Req>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(k, r3)), Wr.Got{k, r3}, Wire.wire_nat_round_trip(k, r3, po.code_fits(c))) : {FPo.get_req.cls(rs, at, _) == goal : Wr.Dec<FPo.Req>}
      %Equal.sym(Maybe<&2, Pp.Cls>, FPo.cls.of(k), Some{c}, po.cls_rt(c)) : {FPo.get_req.c(rs, at, _, r3) == goal : Wr.Dec<FPo.Req>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(w, rest)), Wr.Got{w, rest}, Wire.wire_bool_round_trip(w, rest)) : {FPo.get_req.w(rs, at, c, _) == goal : Wr.Dec<FPo.Req>}
      {==}

# The entry: the reply
# --------------------

def po.wc(x: Po.Wc) -> {FPo.put_wc(x, "") == PathOwn.sp_po_wc(x) : String}:
  match x:
    case Po.Judged{c}:
      match c:
        case Pp.Inside{}:
          {==}
        case Pp.Outside{}:
          {==}
        case Pp.Protected{}:
          {==}
        case Pp.Secret{}:
          {==}
    case Po.Own{i}:
      {==}

# the entry's reply is the laws' spelling of the model's answer
def po.reply(q: FPo.Req) -> {FPo.answer(q) == PathOwn.sp_po_reply(q) : String}:
  match q:
    case FPo.Req{+rs, +at, +c, +w}:
      po.wc(Po.class(rs, at, c, w))

def po.wc_ok(x: Po.Wc) -> {LawsBase.wire_opens_err(FPo.put_wc(x, "")) == False{} : Bool}:
  match x:
    case Po.Judged{c}:
      Wire.wire_nat_not_err(0n, Wr.put_nat(FPo.cls(c), ""))
    case Po.Own{i}:
      Wire.wire_nat_not_err(1n, Wr.put_nat(i, ""))

# no answer of the model opens with the error mark
def po.answer_ok(q: FPo.Req) -> {LawsBase.wire_opens_err(FPo.answer(q)) == False{} : Bool}:
  match q:
    case FPo.Req{+rs, +at, +c, +w}:
      po.wc_ok(Po.class(rs, at, c, w))
