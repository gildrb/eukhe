# eukhe: lemmas of the doc_commit entry proofs: the list of Fate (answer)
#
# A spelled list of Fate reads back (dcw.fates.rt) and a decoded one is
# spelled with a count that fits (dcw.fates.list): each Fate and its
# Outcome tag by tag with wire_nat_exact.

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

# a spelled Fate reads back
def dcw.fates.item_rt(x: Cm.Fate, +rest: String) -> {FCm.get_fate(DocCommit.sp_w_fate(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Cm.Fate>}:
  match x:
    case Cm.Noop{}:
      {==}
    case Cm.Wrote{o}:
      match o:
        case Cm.Lands{w}:
          match w:
            case Cm.NoWarn{}:
              {==}
            case Cm.SyncWarn{}:
              {==}
            case Cm.RemoveWarn{}:
              {==}
        case Cm.Fails{}:
          {==}
    case Cm.Untried{}:
      {==}

def dcw.OP(s: String, d: Wr.Dec<Cm.Outcome>) -> Type:
  match d:
    case Wr.Got{o, r}:
      {s == DocCommit.sp_w_outcome(o, r) : String}
    case Wr.Bad{}:
      Unit

def dcw.out.warn(t: Nat, +s2: String, -s: String, pre: {s == Wr.put_nat(0n, Wr.put_nat(t, s2)) : String}) -> dcw.OP(s, FCm.get_outcome.warn(FCm.get_warn.tag(t, s2))):
  match t:
    case 0n:
      pre
    case 1n:
      pre
    case 2n:
      pre
    case 3n+u:
      Unit{}

def dcw.out.lands(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Nat>, np: LE.dcw.NP(s1, d)) -> dcw.OP(s, FCm.get_outcome.lands(d)):
  match d:
    case Wr.Got{+t, +s2}:
      dcw.out.warn(t, s2, s, LE.dcw.after(s, 0n, s1, Wr.put_nat(t, s2), pre, np))
    case Wr.Bad{}:
      Unit{}

def dcw.out.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> dcw.OP(s, FCm.get_outcome.tag(t, s1)):
  match t:
    case 0n:
      dcw.out.lands(s, s1, pre, Wr.get_nat(s1), LE.dcw.nat(s1))
    case 1n:
      pre
    case 2n+u:
      Unit{}

def dcw.out.go(-s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> dcw.OP(s, FCm.get_outcome(d)):
  match d:
    case Wr.Got{t, s1}:
      dcw.out.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

def dcw.fates.IP(s: String, d: Wr.Dec<Cm.Fate>) -> Type:
  match d:
    case Wr.Got{f, r}:
      {s == DocCommit.sp_w_fate(f, r) : String}
    case Wr.Bad{}:
      Unit

def dcw.fate.wrote(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Cm.Outcome>, op: dcw.OP(s1, d)) -> dcw.fates.IP(s, FCm.get_fate.wrote(d)):
  match d:
    case Wr.Got{+o, +r}:
      LE.dcw.after(s, 1n, s1, DocCommit.sp_w_outcome(o, r), pre, op)
    case Wr.Bad{}:
      Unit{}

def dcw.fate.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> dcw.fates.IP(s, FCm.get_fate.tag(t, s1)):
  match t:
    case 0n:
      pre
    case 1n:
      dcw.fate.wrote(s, s1, pre, FCm.get_outcome(Wr.get_nat(s1)), dcw.out.go(s1, Wr.get_nat(s1), LE.dcw.nat(s1)))
    case 2n:
      pre
    case 3n+u:
      Unit{}

def dcw.fate.start(-s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> dcw.fates.IP(s, FCm.get_fate.start(d)):
  match d:
    case Wr.Got{t, s1}:
      dcw.fate.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

# a Fate decoded is spelled
def dcw.fates.item(+s: String) -> dcw.fates.IP(s, FCm.get_fate(s)):
  dcw.fate.start(s, Wr.get_nat(s), LE.dcw.nat(s))

# The spelling
# ------------

# the spec's items of xs, then rest
def dcw.fates.items(xs: List<&2, Cm.Fate>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      DocCommit.sp_w_fate(x, dcw.fates.items(t, rest))

def dcw.fates.put_go(xs: List<&2, Cm.Fate>, -rest: String) ->
  {Wr.put_list.go(~Cm.Fate, ~DocCommit.sp_w_fate, xs, rest) == (List.length(&2, Cm.Fate, xs), dcw.fates.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Cm.Fate, ~DocCommit.sp_w_fate, t, rest), (List.length(&2, Cm.Fate, t), dcw.fates.items(t, rest)), dcw.fates.put_go(t, rest)) : {Wr.put_list.step(~Cm.Fate, ~DocCommit.sp_w_fate, x, _) == (1n+List.length(&2, Cm.Fate, t), DocCommit.sp_w_fate(x, dcw.fates.items(t, rest))) : Nat & String}
      {==}

# a list is its count, then its items
def dcw.fates.put(+xs: List<&2, Cm.Fate>, -rest: String) ->
  {Wr.put_list(~Cm.Fate, ~DocCommit.sp_w_fate, xs, rest) == Wr.put_nat(List.length(&2, Cm.Fate, xs), dcw.fates.items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Cm.Fate, ~DocCommit.sp_w_fate, xs, rest), (List.length(&2, Cm.Fate, xs), dcw.fates.items(xs, rest)), dcw.fates.put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Cm.Fate, xs), dcw.fates.items(xs, rest)) : String}
  {==}

# Round trip
# ----------

# the item loop reads back x then t
def dcw.fates.go_rt(+t: List<&2, Cm.Fate>, +x: Cm.Fate, +rest: String) ->
  {Wr.get_list.go(~Cm.Fate, ~FCm.get_fate, List.length(&2, Cm.Fate, t), FCm.get_fate(DocCommit.sp_w_fate(x, dcw.fates.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Cm.Fate>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Cm.Fate>, FCm.get_fate(DocCommit.sp_w_fate(x, rest)), Wr.Got{x, rest}, dcw.fates.item_rt(x, rest)) : {Wr.get_list.go(~Cm.Fate, ~FCm.get_fate, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Cm.Fate>>}
      {==}
    case Con{+y, +u}:
      +r2 = DocCommit.sp_w_fate(y, dcw.fates.items(u, rest))
      %Equal.sym(Wr.Dec<Cm.Fate>, FCm.get_fate(DocCommit.sp_w_fate(x, r2)), Wr.Got{x, r2}, dcw.fates.item_rt(x, r2)) : {Wr.get_list.go(~Cm.Fate, ~FCm.get_fate, 1n+List.length(&2, Cm.Fate, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Cm.Fate>>}
      %Equal.sym(Wr.Dec<List<&2, Cm.Fate>>, Wr.get_list.go(~Cm.Fate, ~FCm.get_fate, List.length(&2, Cm.Fate, u), FCm.get_fate(r2)), Wr.Got{y <> u, rest}, dcw.fates.go_rt(u, y, rest)) : {Wr.get_list.cons(Cm.Fate, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Cm.Fate>>}
      {==}

# a spelled list whose count fits reads back, and the rest is untouched
def dcw.fates.rt(xs: List<&2, Cm.Fate>, +rest: String, hn: {LawsBase.wire_fits(List.length(&2, Cm.Fate, xs)) == True{} : Bool}) ->
  {Wr.get_list(~Cm.Fate, ~FCm.get_fate, Wr.put_list(~Cm.Fate, ~DocCommit.sp_w_fate, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Cm.Fate>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, hn)) : {Wr.get_list.start(~Cm.Fate, ~FCm.get_fate, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Cm.Fate>>}
      {==}
    case Con{+x, +t}:
      +items = dcw.fates.items(x <> t, rest)
      %Equal.sym(String, Wr.put_list(~Cm.Fate, ~DocCommit.sp_w_fate, x <> t, rest), Wr.put_nat(List.length(&2, Cm.Fate, x <> t), items), dcw.fates.put(x <> t, rest)) : {Wr.get_list(~Cm.Fate, ~FCm.get_fate, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Cm.Fate>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Cm.Fate, x <> t), items)), Wr.Got{List.length(&2, Cm.Fate, x <> t), items}, Wire.wire_nat_round_trip(List.length(&2, Cm.Fate, x <> t), items, hn)) : {Wr.get_list.start(~Cm.Fate, ~FCm.get_fate, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Cm.Fate>>}
      dcw.fates.go_rt(t, x, rest)

# the round trip, turned around
def dcw.fates.back(+xs: List<&2, Cm.Fate>, +rest: String, hn: {LawsBase.wire_fits(List.length(&2, Cm.Fate, xs)) == True{} : Bool}) ->
  {Wr.Got{xs, rest} == Wr.get_list(~Cm.Fate, ~FCm.get_fate, Wr.put_list(~Cm.Fate, ~DocCommit.sp_w_fate, xs, rest)) : Wr.Dec<List<&2, Cm.Fate>>}:
  Equal.sym(Wr.Dec<List<&2, Cm.Fate>>, Wr.get_list(~Cm.Fate, ~FCm.get_fate, Wr.put_list(~Cm.Fate, ~DocCommit.sp_w_fate, xs, rest)), Wr.Got{xs, rest}, dcw.fates.rt(xs, rest, hn))

# Exactness
# ---------

# what the item loop's answer says about its input s (m + 1 items)
def dcw.fates.PL(s: String, m: Nat, d: Wr.Dec<List<&2, Cm.Fate>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == dcw.fates.items(xs, r) : String} & {List.length(&2, Cm.Fate, xs) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def dcw.fates.step(-s: String, +x: Cm.Fate, +s3: String, -k: Nat, ex: {s == DocCommit.sp_w_fate(x, s3) : String},
  d: Wr.Dec<List<&2, Cm.Fate>>, ih: dcw.fates.PL(s3, k, d)) -> dcw.fates.PL(s, 1n+k, Wr.get_list.cons(Cm.Fate, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e2) = ih
      (Equal.trans(String, s, DocCommit.sp_w_fate(x, s3), DocCommit.sp_w_fate(x, dcw.fates.items(ys, r)), ex,
          Equal.cong(String, String, z => DocCommit.sp_w_fate(x, z), s3, dcw.fates.items(ys, r), e1)),
        Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Cm.Fate, ys), 1n+k, e2))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only spelled items
def dcw.fates.loop(m: Nat, cur: Wr.Dec<Cm.Fate>, +s: String, pc: dcw.fates.IP(s, cur)) ->
  dcw.fates.PL(s, m, Wr.get_list.go(~Cm.Fate, ~FCm.get_fate, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (pc, {==})
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      dcw.fates.step(s, x, s3, k, pc, Wr.get_list.go(~Cm.Fate, ~FCm.get_fate, k, FCm.get_fate(s3)),
        dcw.fates.loop(k, FCm.get_fate(s3), s3, dcw.fates.item(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder's answer says about its input s
def dcw.fates.LS(s: String, d: Wr.Dec<List<&2, Cm.Fate>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_list(~Cm.Fate, ~DocCommit.sp_w_fate, xs, r) : String} & {LawsBase.wire_fits(List.length(&2, Cm.Fate, xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def dcw.fates.conv_s(-s: String, -s2: String, -m: Nat, +xs: List<&2, Cm.Fate>, -r: String,
  en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == dcw.fates.items(xs, r) : String},
  e2: {List.length(&2, Cm.Fate, xs) == 1n+m : Nat}) -> {s == Wr.put_list(~Cm.Fate, ~DocCommit.sp_w_fate, xs, r) : String}:
  %Equal.sym(String, Wr.put_list(~Cm.Fate, ~DocCommit.sp_w_fate, xs, r), Wr.put_nat(List.length(&2, Cm.Fate, xs), dcw.fates.items(xs, r)), dcw.fates.put(xs, r)) : {s == _ : String}
  %Equal.sym(Nat, List.length(&2, Cm.Fate, xs), 1n+m, e2) : {s == Wr.put_nat(_, dcw.fates.items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def dcw.fates.conv_f(-m: Nat, -xs: List<&2, Cm.Fate>, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  e2: {List.length(&2, Cm.Fate, xs) == 1n+m : Nat}) -> {LawsBase.wire_fits(List.length(&2, Cm.Fate, xs)) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Cm.Fate, xs), 1n+m, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
  fn

def dcw.fates.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String},
  fn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  d: Wr.Dec<List<&2, Cm.Fate>>, pl: dcw.fates.PL(s2, m, d)) -> dcw.fates.LS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, +e2) = pl
      (dcw.fates.conv_s(s, s2, m, xs, r, en, e1, e2), dcw.fates.conv_f(m, xs, fn, e2))
    case Wr.Bad{}:
      Unit{}

def dcw.fates.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String},
  fn: {LawsBase.wire_fits(n) == True{} : Bool}) ->
  dcw.fates.LS(s, Wr.get_list.start(~Cm.Fate, ~FCm.get_fate, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, fn)
    case 1n++m:
      dcw.fates.conv(s, s2, m, en, fn, Wr.get_list.go(~Cm.Fate, ~FCm.get_fate, m, FCm.get_fate(s2)),
        dcw.fates.loop(m, FCm.get_fate(s2), s2, dcw.fates.item(s2)))

def dcw.fates.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) ->
  dcw.fates.LS(s, Wr.get_list.start(~Cm.Fate, ~FCm.get_fate, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      dcw.fates.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a list decoded is spelled, and what it holds fits the wire
def dcw.fates.list(+s: String) -> dcw.fates.LS(s, Wr.get_list(~Cm.Fate, ~FCm.get_fate, s)):
  dcw.fates.top(s, Wr.get_nat(s), {==})
