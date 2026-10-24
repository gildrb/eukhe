# eukhe: lemmas of the doc_commit entry proofs: the list of Ent (sweep)
#
# A spelled list of entries whose names fit reads back (dcw.ents.rt) and
# a decoded one is spelled, its count and every name within the wire
# (dcw.ents.list).

import Base
import ../../../bend/doc_commit.bend as Cm
import ../../../bend/ffi_doc_commit.bend as FCm
import ../../../bend/wire.bend as Wr
import ../../../laws/doc_commit.bend as DocCommit
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../base.bend as LA
import ./wire.bend as LE

# One item
# --------

# the name of an entry fits the wire
def dcw.ents.ifit(e: Cm.Ent) -> Bool:
  match e:
    case Cm.Ent{n, h}:
      LawsBase.wire_fits(String.length(n))

def dcw.ents.item_rt(x: Cm.Ent, +rest: String, h: {dcw.ents.ifit(x) == True{} : Bool}) -> {FCm.get_ent(DocCommit.sp_w_ent(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Cm.Ent>}:
  match x:
    case Cm.Ent{+n, +b}:
      %LE.dcw.str_back(n, Wr.put_bool(b, rest), h) : {FCm.get_ent.name(_) == Wr.Got{Cm.Ent{n, b}, rest} : Wr.Dec<Cm.Ent>}
      %LE.dcw.bool_back(b, rest) : {FCm.get_ent.held(n, _) == Wr.Got{Cm.Ent{n, b}, rest} : Wr.Dec<Cm.Ent>}
      {==}

def dcw.ents.hd(x: Cm.Ent, +t: List<&2, Cm.Ent>, h: {DocCommit.sp_fit_ents(x <> t) == True{} : Bool}) -> {dcw.ents.ifit(x) == True{} : Bool}:
  match x:
    case Cm.Ent{+n, b}:
      LA.dcw.and_l(LawsBase.wire_fits(String.length(n)), DocCommit.sp_fit_ents(t), h)

def dcw.ents.tl(x: Cm.Ent, +t: List<&2, Cm.Ent>, h: {DocCommit.sp_fit_ents(x <> t) == True{} : Bool}) -> {DocCommit.sp_fit_ents(t) == True{} : Bool}:
  match x:
    case Cm.Ent{+n, b}:
      LA.dcw.and_r(LawsBase.wire_fits(String.length(n)), DocCommit.sp_fit_ents(t), h)

def dcw.ents.cons_fit(x: Cm.Ent, -t: List<&2, Cm.Ent>, fx: {dcw.ents.ifit(x) == True{} : Bool}, ft: {DocCommit.sp_fit_ents(t) == True{} : Bool}) -> {DocCommit.sp_fit_ents(x <> t) == True{} : Bool}:
  match x:
    case Cm.Ent{n, b}:
      LA.dcw.and_tt(LawsBase.wire_fits(String.length(n)), DocCommit.sp_fit_ents(t), fx, ft)

def dcw.ents.IP(s: String, d: Wr.Dec<Cm.Ent>) -> Type:
  match d:
    case Wr.Got{e, r}:
      {s == DocCommit.sp_w_ent(e, r) : String} & {dcw.ents.ifit(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dcw.ent.held(-s: String, +n: String, +s1: String, pre: {s == Wr.put_str(n, s1) : String}, fn: {LawsBase.wire_fits(String.length(n)) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}) -> dcw.ents.IP(s, FCm.get_ent.held(n, d)):
  match d:
    case Wr.Got{+h, +s2}:
      (Equal.trans(String, s, Wr.put_str(n, s1), Wr.put_str(n, Wr.put_bool(h, s2)), pre, Equal.cong(String, String, z => Wr.put_str(n, z), s1, Wr.put_bool(h, s2), Wire.wire_bool_exact(s1, h, s2, ed))), fn)
    case Wr.Bad{}:
      Unit{}

def dcw.ent.name(-s: String, d: Wr.Dec<String>, sp: LE.dcw.SP(s, d)) -> dcw.ents.IP(s, FCm.get_ent.name(d)):
  match d:
    case Wr.Got{+n, +s1}:
      (e, f) = sp
      dcw.ent.held(s, n, s1, e, f, Wr.get_bool(s1), {==})
    case Wr.Bad{}:
      Unit{}

# an Ent decoded is spelled, and its name fits
def dcw.ents.item(+s: String) -> dcw.ents.IP(s, FCm.get_ent(s)):
  dcw.ent.name(s, Wr.get_str(s), LE.dcw.str(s))

# The spelling
# ------------

# the spec's items of xs, then rest
def dcw.ents.items(xs: List<&2, Cm.Ent>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      DocCommit.sp_w_ent(x, dcw.ents.items(t, rest))

def dcw.ents.put_go(xs: List<&2, Cm.Ent>, -rest: String) ->
  {Wr.put_list.go(~Cm.Ent, ~DocCommit.sp_w_ent, xs, rest) == (List.length(&2, Cm.Ent, xs), dcw.ents.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Cm.Ent, ~DocCommit.sp_w_ent, t, rest), (List.length(&2, Cm.Ent, t), dcw.ents.items(t, rest)), dcw.ents.put_go(t, rest)) : {Wr.put_list.step(~Cm.Ent, ~DocCommit.sp_w_ent, x, _) == (1n+List.length(&2, Cm.Ent, t), DocCommit.sp_w_ent(x, dcw.ents.items(t, rest))) : Nat & String}
      {==}

# a list is its count, then its items
def dcw.ents.put(+xs: List<&2, Cm.Ent>, -rest: String) ->
  {Wr.put_list(~Cm.Ent, ~DocCommit.sp_w_ent, xs, rest) == Wr.put_nat(List.length(&2, Cm.Ent, xs), dcw.ents.items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Cm.Ent, ~DocCommit.sp_w_ent, xs, rest), (List.length(&2, Cm.Ent, xs), dcw.ents.items(xs, rest)), dcw.ents.put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Cm.Ent, xs), dcw.ents.items(xs, rest)) : String}
  {==}

# Round trip
# ----------

# the item loop reads back x then t
def dcw.ents.go_rt(+t: List<&2, Cm.Ent>, +x: Cm.Ent, +rest: String, h: {DocCommit.sp_fit_ents(x <> t) == True{} : Bool}) ->
  {Wr.get_list.go(~Cm.Ent, ~FCm.get_ent, List.length(&2, Cm.Ent, t), FCm.get_ent(DocCommit.sp_w_ent(x, dcw.ents.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Cm.Ent>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Cm.Ent>, FCm.get_ent(DocCommit.sp_w_ent(x, rest)), Wr.Got{x, rest}, dcw.ents.item_rt(x, rest, dcw.ents.hd(x, Nil{}, h))) : {Wr.get_list.go(~Cm.Ent, ~FCm.get_ent, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Cm.Ent>>}
      {==}
    case Con{+y, +u}:
      +hh = h
      +r2 = DocCommit.sp_w_ent(y, dcw.ents.items(u, rest))
      %Equal.sym(Wr.Dec<Cm.Ent>, FCm.get_ent(DocCommit.sp_w_ent(x, r2)), Wr.Got{x, r2}, dcw.ents.item_rt(x, r2, dcw.ents.hd(x, y <> u, hh))) : {Wr.get_list.go(~Cm.Ent, ~FCm.get_ent, 1n+List.length(&2, Cm.Ent, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Cm.Ent>>}
      %Equal.sym(Wr.Dec<List<&2, Cm.Ent>>, Wr.get_list.go(~Cm.Ent, ~FCm.get_ent, List.length(&2, Cm.Ent, u), FCm.get_ent(r2)), Wr.Got{y <> u, rest}, dcw.ents.go_rt(u, y, rest, dcw.ents.tl(x, y <> u, hh))) : {Wr.get_list.cons(Cm.Ent, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Cm.Ent>>}
      {==}

# a spelled list whose count and items fit reads back, and the rest is
# untouched
def dcw.ents.rt(xs: List<&2, Cm.Ent>, +rest: String, hn: {LawsBase.wire_fits(List.length(&2, Cm.Ent, xs)) == True{} : Bool}, hf: {DocCommit.sp_fit_ents(xs) == True{} : Bool}) ->
  {Wr.get_list(~Cm.Ent, ~FCm.get_ent, Wr.put_list(~Cm.Ent, ~DocCommit.sp_w_ent, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Cm.Ent>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, hn)) : {Wr.get_list.start(~Cm.Ent, ~FCm.get_ent, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Cm.Ent>>}
      {==}
    case Con{+x, +t}:
      +items = dcw.ents.items(x <> t, rest)
      %Equal.sym(String, Wr.put_list(~Cm.Ent, ~DocCommit.sp_w_ent, x <> t, rest), Wr.put_nat(List.length(&2, Cm.Ent, x <> t), items), dcw.ents.put(x <> t, rest)) : {Wr.get_list(~Cm.Ent, ~FCm.get_ent, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Cm.Ent>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Cm.Ent, x <> t), items)), Wr.Got{List.length(&2, Cm.Ent, x <> t), items}, Wire.wire_nat_round_trip(List.length(&2, Cm.Ent, x <> t), items, hn)) : {Wr.get_list.start(~Cm.Ent, ~FCm.get_ent, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Cm.Ent>>}
      dcw.ents.go_rt(t, x, rest, hf)

# the round trip, turned around
def dcw.ents.back(+xs: List<&2, Cm.Ent>, +rest: String, hn: {LawsBase.wire_fits(List.length(&2, Cm.Ent, xs)) == True{} : Bool}, hf: {DocCommit.sp_fit_ents(xs) == True{} : Bool}) ->
  {Wr.Got{xs, rest} == Wr.get_list(~Cm.Ent, ~FCm.get_ent, Wr.put_list(~Cm.Ent, ~DocCommit.sp_w_ent, xs, rest)) : Wr.Dec<List<&2, Cm.Ent>>}:
  Equal.sym(Wr.Dec<List<&2, Cm.Ent>>, Wr.get_list(~Cm.Ent, ~FCm.get_ent, Wr.put_list(~Cm.Ent, ~DocCommit.sp_w_ent, xs, rest)), Wr.Got{xs, rest}, dcw.ents.rt(xs, rest, hn, hf))

# Exactness
# ---------

# what the item loop's answer says about its input s (m + 1 items)
def dcw.ents.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Cm.Ent>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == dcw.ents.items(xs, r) : String} & ({List.length(&2, Cm.Ent, xs) == 1n+m : Nat} & {DocCommit.sp_fit_ents(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def dcw.ents.step(-s: String, +x: Cm.Ent, +s3: String, -k: Nat, ex: {s == DocCommit.sp_w_ent(x, s3) : String}, fx: {dcw.ents.ifit(x) == True{} : Bool},
  d: Wr.Dec<List<&2, Cm.Ent>>, ih: dcw.ents.PL(s3, k, d)) -> dcw.ents.PL(s, 1n+k, Wr.get_list.cons(Cm.Ent, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (Equal.trans(String, s, DocCommit.sp_w_ent(x, s3), DocCommit.sp_w_ent(x, dcw.ents.items(ys, r)), ex,
          Equal.cong(String, String, z => DocCommit.sp_w_ent(x, z), s3, dcw.ents.items(ys, r), e1)),
        (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Cm.Ent, ys), 1n+k, e2), dcw.ents.cons_fit(x, ys, fx, e3)))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only spelled items that fit
def dcw.ents.loop(m: Nat, cur: Wr.Dec<Cm.Ent>, +s: String, pc: dcw.ents.IP(s, cur)) ->
  dcw.ents.PL(s, m, Wr.get_list.go(~Cm.Ent, ~FCm.get_ent, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, dcw.ents.cons_fit(x, Nil{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      dcw.ents.step(s, x, s3, k, e, f, Wr.get_list.go(~Cm.Ent, ~FCm.get_ent, k, FCm.get_ent(s3)),
        dcw.ents.loop(k, FCm.get_ent(s3), s3, dcw.ents.item(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder's answer says about its input s
def dcw.ents.LS(s: String, d: Wr.Dec<List<&2, Cm.Ent>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_list(~Cm.Ent, ~DocCommit.sp_w_ent, xs, r) : String} & ({LawsBase.wire_fits(List.length(&2, Cm.Ent, xs)) == True{} : Bool} & {DocCommit.sp_fit_ents(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def dcw.ents.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Cm.Ent>, -r: String,
  en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == dcw.ents.items(xs, r) : String},
  e2: {List.length(&2, Cm.Ent, xs) == 1n+m : Nat}) -> {s == Wr.put_list(~Cm.Ent, ~DocCommit.sp_w_ent, xs, r) : String}:
  %Equal.sym(String, Wr.put_list(~Cm.Ent, ~DocCommit.sp_w_ent, xs, r), Wr.put_nat(List.length(&2, Cm.Ent, xs), dcw.ents.items(xs, r)), dcw.ents.put(xs, r)) : {s == _ : String}
  %Equal.sym(Nat, List.length(&2, Cm.Ent, xs), 1n+m, e2) : {s == Wr.put_nat(_, dcw.ents.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def dcw.ents.conv_f(-m: Nat, -xs: List<&2, Cm.Ent>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  e2: {List.length(&2, Cm.Ent, xs) == 1n+m : Nat}) -> {LawsBase.wire_fits(List.length(&2, Cm.Ent, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Cm.Ent, xs), 1n+m, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
  fn

def dcw.ents.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String},
  fn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  d: Wr.Dec<List<&2, Cm.Ent>>, pl: dcw.ents.PL(s2, m, d)) -> dcw.ents.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      (dcw.ents.conv_s(s, s2, m, xs, r, en, e1, e2), (dcw.ents.conv_f(m, xs, fn, e2), e3))
    case Wr.Bad{}:
      Unit{}

def dcw.ents.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String},
  fn: {LawsBase.wire_fits(n) == True{} : Bool}) ->
  dcw.ents.LS(s, Wr.get_list.start(~Cm.Ent, ~FCm.get_ent, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, (fn, {==}))
    case 1n++m:
      dcw.ents.conv(s, s2, m, en, fn, Wr.get_list.go(~Cm.Ent, ~FCm.get_ent, m, FCm.get_ent(s2)),
        dcw.ents.loop(m, FCm.get_ent(s2), s2, dcw.ents.item(s2)))

def dcw.ents.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) ->
  dcw.ents.LS(s, Wr.get_list.start(~Cm.Ent, ~FCm.get_ent, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      dcw.ents.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a list decoded is spelled, and what it holds fits the wire
def dcw.ents.list(+s: String) -> dcw.ents.LS(s, Wr.get_list(~Cm.Ent, ~FCm.get_ent, s)):
  dcw.ents.top(s, Wr.get_nat(s), {==})
