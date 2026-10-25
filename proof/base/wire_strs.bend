# eukhe: lemmas shared by the entry proofs (doc_commit, dash_access,
# gateway_answer): a wire list of String
#
# A spelled list of strings that fit reads back (dcw.strs.rt) and a
# decoded one is spelled, its count and every length within the wire
# (dcw.strs.list).

import Base
import ../../bend/wire.bend as Wr
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ./bool.bend as LBool
import ./logic/bool.bend as LLogicBool
import ./wire_dec.bend as LE

# One item
# --------

def dcw.strs.item_rt(+x: String, +rest: String, h: {LawsBase.wire_fits(String.length(x)) == True{} : Bool}) -> {Wr.get_str(Wr.put_str(x, rest)) == Wr.Got{x, rest} : Wr.Dec<String>}:
  Wire.wire_str_round_trip(x, rest, h)

def dcw.strs.hd(+x: String, +t: List<&2, String>, h: {DocCommit.sp_fit_strs(x <> t) == True{} : Bool}) -> {LawsBase.wire_fits(String.length(x)) == True{} : Bool}:
  LLogicBool.tree.pt.and_l(LawsBase.wire_fits(String.length(x)), DocCommit.sp_fit_strs(t), h)

def dcw.strs.tl(+x: String, +t: List<&2, String>, h: {DocCommit.sp_fit_strs(x <> t) == True{} : Bool}) -> {DocCommit.sp_fit_strs(t) == True{} : Bool}:
  LLogicBool.tree.pt.and_r(LawsBase.wire_fits(String.length(x)), DocCommit.sp_fit_strs(t), h)

def dcw.strs.cons_fit(-x: String, -t: List<&2, String>, fx: {LawsBase.wire_fits(String.length(x)) == True{} : Bool}, ft: {DocCommit.sp_fit_strs(t) == True{} : Bool}) -> {DocCommit.sp_fit_strs(x <> t) == True{} : Bool}:
  LBool.cb_and_intro(LawsBase.wire_fits(String.length(x)), DocCommit.sp_fit_strs(t), fx, ft)

# The spelling
# ------------

# the spec's items of xs, then rest
def dcw.strs.items(xs: List<&2, String>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      Wr.put_str(x, dcw.strs.items(t, rest))

def dcw.strs.put_go(xs: List<&2, String>, -rest: String) ->
  {Wr.put_list.go(~String, ~Wr.put_str, xs, rest) == (List.length(&2, String, xs), dcw.strs.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~String, ~Wr.put_str, t, rest), (List.length(&2, String, t), dcw.strs.items(t, rest)), dcw.strs.put_go(t, rest)) : {Wr.put_list.step(~String, ~Wr.put_str, x, _) == (1n+List.length(&2, String, t), Wr.put_str(x, dcw.strs.items(t, rest))) : Nat & String}
      {==}

# a list is its count, then its items
def dcw.strs.put(+xs: List<&2, String>, -rest: String) ->
  {Wr.put_list(~String, ~Wr.put_str, xs, rest) == Wr.put_nat(List.length(&2, String, xs), dcw.strs.items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~String, ~Wr.put_str, xs, rest), (List.length(&2, String, xs), dcw.strs.items(xs, rest)), dcw.strs.put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, String, xs), dcw.strs.items(xs, rest)) : String}
  {==}

# Round trip
# ----------

# the item loop reads back x then t
def dcw.strs.go_rt(+t: List<&2, String>, +x: String, +rest: String, h: {DocCommit.sp_fit_strs(x <> t) == True{} : Bool}) ->
  {Wr.get_list.go(~String, ~Wr.get_str, List.length(&2, String, t), Wr.get_str(Wr.put_str(x, dcw.strs.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, String>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, dcw.strs.item_rt(x, rest, dcw.strs.hd(x, Nil{}, h))) : {Wr.get_list.go(~String, ~Wr.get_str, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, String>>}
      {==}
    case Con{+y, +u}:
      +hh = h
      +r2 = Wr.put_str(y, dcw.strs.items(u, rest))
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, r2)), Wr.Got{x, r2}, dcw.strs.item_rt(x, r2, dcw.strs.hd(x, y <> u, hh))) : {Wr.get_list.go(~String, ~Wr.get_str, 1n+List.length(&2, String, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, String>>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list.go(~String, ~Wr.get_str, List.length(&2, String, u), Wr.get_str(r2)), Wr.Got{y <> u, rest}, dcw.strs.go_rt(u, y, rest, dcw.strs.tl(x, y <> u, hh))) : {Wr.get_list.cons(String, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, String>>}
      {==}

# a spelled list whose count and items fit reads back, and the rest is
# untouched
def dcw.strs.rt(xs: List<&2, String>, +rest: String, hn: {LawsBase.wire_fits(List.length(&2, String, xs)) == True{} : Bool}, hf: {DocCommit.sp_fit_strs(xs) == True{} : Bool}) ->
  {Wr.get_list(~String, ~Wr.get_str, Wr.put_list(~String, ~Wr.put_str, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, String>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, hn)) : {Wr.get_list.start(~String, ~Wr.get_str, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, String>>}
      {==}
    case Con{+x, +t}:
      +items = dcw.strs.items(x <> t, rest)
      %Equal.sym(String, Wr.put_list(~String, ~Wr.put_str, x <> t, rest), Wr.put_nat(List.length(&2, String, x <> t), items), dcw.strs.put(x <> t, rest)) : {Wr.get_list(~String, ~Wr.get_str, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, String>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, String, x <> t), items)), Wr.Got{List.length(&2, String, x <> t), items}, Wire.wire_nat_round_trip(List.length(&2, String, x <> t), items, hn)) : {Wr.get_list.start(~String, ~Wr.get_str, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, String>>}
      dcw.strs.go_rt(t, x, rest, hf)

# the round trip, turned around
def dcw.strs.back(+xs: List<&2, String>, +rest: String, hn: {LawsBase.wire_fits(List.length(&2, String, xs)) == True{} : Bool}, hf: {DocCommit.sp_fit_strs(xs) == True{} : Bool}) ->
  {Wr.Got{xs, rest} == Wr.get_list(~String, ~Wr.get_str, Wr.put_list(~String, ~Wr.put_str, xs, rest)) : Wr.Dec<List<&2, String>>}:
  Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, Wr.put_list(~String, ~Wr.put_str, xs, rest)), Wr.Got{xs, rest}, dcw.strs.rt(xs, rest, hn, hf))

# Exactness
# ---------

# what the item loop's answer says about its input s (m + 1 items)
def dcw.strs.PL(s: String, m: Nat, d: Wr.Dec<List<&2, String>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == dcw.strs.items(xs, r) : String} & ({List.length(&2, String, xs) == 1n+m : Nat} & {DocCommit.sp_fit_strs(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def dcw.strs.step(-s: String, +x: String, +s3: String, -k: Nat, ex: {s == Wr.put_str(x, s3) : String}, fx: {LawsBase.wire_fits(String.length(x)) == True{} : Bool},
  d: Wr.Dec<List<&2, String>>, ih: dcw.strs.PL(s3, k, d)) -> dcw.strs.PL(s, 1n+k, Wr.get_list.cons(String, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (Equal.trans(String, s, Wr.put_str(x, s3), Wr.put_str(x, dcw.strs.items(ys, r)), ex,
          Equal.cong(String, String, z => Wr.put_str(x, z), s3, dcw.strs.items(ys, r), e1)),
        (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, String, ys), 1n+k, e2), dcw.strs.cons_fit(x, ys, fx, e3)))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only spelled items that fit
def dcw.strs.loop(m: Nat, cur: Wr.Dec<String>, +s: String, pc: LE.dcw.SP(s, cur)) ->
  dcw.strs.PL(s, m, Wr.get_list.go(~String, ~Wr.get_str, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, dcw.strs.cons_fit(x, Nil{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      dcw.strs.step(s, x, s3, k, e, f, Wr.get_list.go(~String, ~Wr.get_str, k, Wr.get_str(s3)),
        dcw.strs.loop(k, Wr.get_str(s3), s3, LE.dcw.str(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder's answer says about its input s
def dcw.strs.LS(s: String, d: Wr.Dec<List<&2, String>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_list(~String, ~Wr.put_str, xs, r) : String} & ({LawsBase.wire_fits(List.length(&2, String, xs)) == True{} : Bool} & {DocCommit.sp_fit_strs(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def dcw.strs.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, String>, -r: String,
  en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == dcw.strs.items(xs, r) : String},
  e2: {List.length(&2, String, xs) == 1n+m : Nat}) -> {s == Wr.put_list(~String, ~Wr.put_str, xs, r) : String}:
  %Equal.sym(String, Wr.put_list(~String, ~Wr.put_str, xs, r), Wr.put_nat(List.length(&2, String, xs), dcw.strs.items(xs, r)), dcw.strs.put(xs, r)) : {s == _ : String}
  %Equal.sym(Nat, List.length(&2, String, xs), 1n+m, e2) : {s == Wr.put_nat(_, dcw.strs.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def dcw.strs.conv_f(-m: Nat, -xs: List<&2, String>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  e2: {List.length(&2, String, xs) == 1n+m : Nat}) -> {LawsBase.wire_fits(List.length(&2, String, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, String, xs), 1n+m, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
  fn

def dcw.strs.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String},
  fn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  d: Wr.Dec<List<&2, String>>, pl: dcw.strs.PL(s2, m, d)) -> dcw.strs.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      (dcw.strs.conv_s(s, s2, m, xs, r, en, e1, e2), (dcw.strs.conv_f(m, xs, fn, e2), e3))
    case Wr.Bad{}:
      Unit{}

def dcw.strs.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String},
  fn: {LawsBase.wire_fits(n) == True{} : Bool}) ->
  dcw.strs.LS(s, Wr.get_list.start(~String, ~Wr.get_str, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, (fn, {==}))
    case 1n++m:
      dcw.strs.conv(s, s2, m, en, fn, Wr.get_list.go(~String, ~Wr.get_str, m, Wr.get_str(s2)),
        dcw.strs.loop(m, Wr.get_str(s2), s2, LE.dcw.str(s2)))

def dcw.strs.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) ->
  dcw.strs.LS(s, Wr.get_list.start(~String, ~Wr.get_str, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      dcw.strs.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a list decoded is spelled, and what it holds fits the wire
def dcw.strs.list(+s: String) -> dcw.strs.LS(s, Wr.get_list(~String, ~Wr.get_str, s)):
  dcw.strs.top(s, Wr.get_nat(s), {==})
