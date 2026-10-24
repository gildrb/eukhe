# eukhe: lemmas of the doc_commit entry proofs: the list of Met (check)
#
# A spelled list of Met reads back (dcw.mets.rt) and a decoded one is
# spelled with a count that fits (dcw.mets.list): item by item with
# wire_bool_exact, the count with wire_nat_exact and wire_nat_decoded_fits.

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

# a spelled Met reads back
def dcw.mets.item_rt(x: Cm.Met, +rest: String) -> {FCm.get_met(DocCommit.sp_w_met(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Cm.Met>}:
  match x:
    case Cm.Met{c, t}:
      match c t:
        case True{} True{}:
          {==}
        case True{} False{}:
          {==}
        case False{} True{}:
          {==}
        case False{} False{}:
          {==}

def dcw.mets.IP(s: String, d: Wr.Dec<Cm.Met>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == DocCommit.sp_w_met(m, r) : String}
    case Wr.Bad{}:
      Unit

def dcw.met.taken(-s: String, +c: Bool, +s1: String, pre: {s == Wr.put_bool(c, s1) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}) -> dcw.mets.IP(s, FCm.get_met.taken(c, d)):
  match d:
    case Wr.Got{+t, +s2}:
      Equal.trans(String, s, Wr.put_bool(c, s1), Wr.put_bool(c, Wr.put_bool(t, s2)), pre, Equal.cong(String, String, z => Wr.put_bool(c, z), s1, Wr.put_bool(t, s2), Wire.wire_bool_exact(s1, t, s2, ed)))
    case Wr.Bad{}:
      Unit{}

def dcw.met.changed(+s: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> dcw.mets.IP(s, FCm.get_met.changed(d)):
  match d:
    case Wr.Got{+c, +s1}:
      +e = ed
      dcw.met.taken(s, c, s1, Wire.wire_bool_exact(s, c, s1, e), Wr.get_bool(s1), {==})
    case Wr.Bad{}:
      Unit{}

# a Met decoded is spelled
def dcw.mets.item(+s: String) -> dcw.mets.IP(s, FCm.get_met(s)):
  dcw.met.changed(s, Wr.get_bool(s), {==})

# The spelling
# ------------

# the spec's items of xs, then rest
def dcw.mets.items(xs: List<&2, Cm.Met>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      DocCommit.sp_w_met(x, dcw.mets.items(t, rest))

def dcw.mets.put_go(xs: List<&2, Cm.Met>, -rest: String) ->
  {Wr.put_list.go(~Cm.Met, ~DocCommit.sp_w_met, xs, rest) == (List.length(&2, Cm.Met, xs), dcw.mets.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Cm.Met, ~DocCommit.sp_w_met, t, rest), (List.length(&2, Cm.Met, t), dcw.mets.items(t, rest)), dcw.mets.put_go(t, rest)) : {Wr.put_list.step(~Cm.Met, ~DocCommit.sp_w_met, x, _) == (1n+List.length(&2, Cm.Met, t), DocCommit.sp_w_met(x, dcw.mets.items(t, rest))) : Nat & String}
      {==}

# a list is its count, then its items
def dcw.mets.put(+xs: List<&2, Cm.Met>, -rest: String) ->
  {Wr.put_list(~Cm.Met, ~DocCommit.sp_w_met, xs, rest) == Wr.put_nat(List.length(&2, Cm.Met, xs), dcw.mets.items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Cm.Met, ~DocCommit.sp_w_met, xs, rest), (List.length(&2, Cm.Met, xs), dcw.mets.items(xs, rest)), dcw.mets.put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Cm.Met, xs), dcw.mets.items(xs, rest)) : String}
  {==}

# Round trip
# ----------

# the item loop reads back x then t
def dcw.mets.go_rt(+t: List<&2, Cm.Met>, +x: Cm.Met, +rest: String) ->
  {Wr.get_list.go(~Cm.Met, ~FCm.get_met, List.length(&2, Cm.Met, t), FCm.get_met(DocCommit.sp_w_met(x, dcw.mets.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Cm.Met>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Cm.Met>, FCm.get_met(DocCommit.sp_w_met(x, rest)), Wr.Got{x, rest}, dcw.mets.item_rt(x, rest)) : {Wr.get_list.go(~Cm.Met, ~FCm.get_met, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Cm.Met>>}
      {==}
    case Con{+y, +u}:
      +r2 = DocCommit.sp_w_met(y, dcw.mets.items(u, rest))
      %Equal.sym(Wr.Dec<Cm.Met>, FCm.get_met(DocCommit.sp_w_met(x, r2)), Wr.Got{x, r2}, dcw.mets.item_rt(x, r2)) : {Wr.get_list.go(~Cm.Met, ~FCm.get_met, 1n+List.length(&2, Cm.Met, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Cm.Met>>}
      %Equal.sym(Wr.Dec<List<&2, Cm.Met>>, Wr.get_list.go(~Cm.Met, ~FCm.get_met, List.length(&2, Cm.Met, u), FCm.get_met(r2)), Wr.Got{y <> u, rest}, dcw.mets.go_rt(u, y, rest)) : {Wr.get_list.cons(Cm.Met, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Cm.Met>>}
      {==}

# a spelled list whose count fits reads back, and the rest is untouched
def dcw.mets.rt(xs: List<&2, Cm.Met>, +rest: String, hn: {LawsBase.wire_fits(List.length(&2, Cm.Met, xs)) == True{} : Bool}) ->
  {Wr.get_list(~Cm.Met, ~FCm.get_met, Wr.put_list(~Cm.Met, ~DocCommit.sp_w_met, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Cm.Met>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, hn)) : {Wr.get_list.start(~Cm.Met, ~FCm.get_met, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Cm.Met>>}
      {==}
    case Con{+x, +t}:
      +items = dcw.mets.items(x <> t, rest)
      %Equal.sym(String, Wr.put_list(~Cm.Met, ~DocCommit.sp_w_met, x <> t, rest), Wr.put_nat(List.length(&2, Cm.Met, x <> t), items), dcw.mets.put(x <> t, rest)) : {Wr.get_list(~Cm.Met, ~FCm.get_met, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Cm.Met>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Cm.Met, x <> t), items)), Wr.Got{List.length(&2, Cm.Met, x <> t), items}, Wire.wire_nat_round_trip(List.length(&2, Cm.Met, x <> t), items, hn)) : {Wr.get_list.start(~Cm.Met, ~FCm.get_met, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Cm.Met>>}
      dcw.mets.go_rt(t, x, rest)

# the round trip, turned around
def dcw.mets.back(+xs: List<&2, Cm.Met>, +rest: String, hn: {LawsBase.wire_fits(List.length(&2, Cm.Met, xs)) == True{} : Bool}) ->
  {Wr.Got{xs, rest} == Wr.get_list(~Cm.Met, ~FCm.get_met, Wr.put_list(~Cm.Met, ~DocCommit.sp_w_met, xs, rest)) : Wr.Dec<List<&2, Cm.Met>>}:
  Equal.sym(Wr.Dec<List<&2, Cm.Met>>, Wr.get_list(~Cm.Met, ~FCm.get_met, Wr.put_list(~Cm.Met, ~DocCommit.sp_w_met, xs, rest)), Wr.Got{xs, rest}, dcw.mets.rt(xs, rest, hn))

# Exactness
# ---------

# what the item loop's answer says about its input s (m + 1 items)
def dcw.mets.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Cm.Met>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == dcw.mets.items(xs, r) : String} & {List.length(&2, Cm.Met, xs) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def dcw.mets.step(-s: String, +x: Cm.Met, +s3: String, -k: Nat, ex: {s == DocCommit.sp_w_met(x, s3) : String},
  d: Wr.Dec<List<&2, Cm.Met>>, ih: dcw.mets.PL(s3, k, d)) -> dcw.mets.PL(s, 1n+k, Wr.get_list.cons(Cm.Met, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e2) = ih
      (Equal.trans(String, s, DocCommit.sp_w_met(x, s3), DocCommit.sp_w_met(x, dcw.mets.items(ys, r)), ex,
          Equal.cong(String, String, z => DocCommit.sp_w_met(x, z), s3, dcw.mets.items(ys, r), e1)),
        Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Cm.Met, ys), 1n+k, e2))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only spelled items
def dcw.mets.loop(m: Nat, cur: Wr.Dec<Cm.Met>, +s: String, pc: dcw.mets.IP(s, cur)) ->
  dcw.mets.PL(s, m, Wr.get_list.go(~Cm.Met, ~FCm.get_met, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (pc, {==})
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      dcw.mets.step(s, x, s3, k, pc, Wr.get_list.go(~Cm.Met, ~FCm.get_met, k, FCm.get_met(s3)),
        dcw.mets.loop(k, FCm.get_met(s3), s3, dcw.mets.item(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder's answer says about its input s
def dcw.mets.LS(s: String, d: Wr.Dec<List<&2, Cm.Met>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_list(~Cm.Met, ~DocCommit.sp_w_met, xs, r) : String} & {LawsBase.wire_fits(List.length(&2, Cm.Met, xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dcw.mets.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Cm.Met>, -r: String,
  en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == dcw.mets.items(xs, r) : String},
  e2: {List.length(&2, Cm.Met, xs) == 1n+m : Nat}) -> {s == Wr.put_list(~Cm.Met, ~DocCommit.sp_w_met, xs, r) : String}:
  %Equal.sym(String, Wr.put_list(~Cm.Met, ~DocCommit.sp_w_met, xs, r), Wr.put_nat(List.length(&2, Cm.Met, xs), dcw.mets.items(xs, r)), dcw.mets.put(xs, r)) : {s == _ : String}
  %Equal.sym(Nat, List.length(&2, Cm.Met, xs), 1n+m, e2) : {s == Wr.put_nat(_, dcw.mets.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def dcw.mets.conv_f(-m: Nat, -xs: List<&2, Cm.Met>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  e2: {List.length(&2, Cm.Met, xs) == 1n+m : Nat}) -> {LawsBase.wire_fits(List.length(&2, Cm.Met, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Cm.Met, xs), 1n+m, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
  fn

def dcw.mets.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String},
  fn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  d: Wr.Dec<List<&2, Cm.Met>>, pl: dcw.mets.PL(s2, m, d)) -> dcw.mets.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, +e2) = pl
      (dcw.mets.conv_s(s, s2, m, xs, r, en, e1, e2), dcw.mets.conv_f(m, xs, fn, e2))
    case Wr.Bad{}:
      Unit{}

def dcw.mets.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String},
  fn: {LawsBase.wire_fits(n) == True{} : Bool}) ->
  dcw.mets.LS(s, Wr.get_list.start(~Cm.Met, ~FCm.get_met, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, fn)
    case 1n++m:
      dcw.mets.conv(s, s2, m, en, fn, Wr.get_list.go(~Cm.Met, ~FCm.get_met, m, FCm.get_met(s2)),
        dcw.mets.loop(m, FCm.get_met(s2), s2, dcw.mets.item(s2)))

def dcw.mets.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) ->
  dcw.mets.LS(s, Wr.get_list.start(~Cm.Met, ~FCm.get_met, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      dcw.mets.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a list decoded is spelled, and what it holds fits the wire
def dcw.mets.list(+s: String) -> dcw.mets.LS(s, Wr.get_list(~Cm.Met, ~FCm.get_met, s)):
  dcw.mets.top(s, Wr.get_nat(s), {==})
