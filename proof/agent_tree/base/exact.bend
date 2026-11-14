# eukhe: lemmas of the entry proofs of area agent_tree
# (bend/ffi_agent_tree.bend): the request decoder answers Got{q, rest} only
# for an input that is the spelling of q before rest, every number and
# count within the wire (atx.req). Per decoder, a predicate on its answer
# (what it says about its input), carried stage by stage on the wire's
# exactness laws wire_nat_exact, wire_nat_decoded_fits, wire_bool_exact and
# wire_list_reads_items; the node reader by induction on its fuel
# (atx.go), whatever the fuel.

import Base
import ../../../bend/agent_crown.bend as C
import ../../../bend/agent_tree.bend as T
import ../../../bend/ffi_agent_tree.bend as FAt
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/agent_tree.bend as AgentTree
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../../wire/wire_list_reads_items.bend as PWireListReadsItems
import ./entry.bend as ATE

# s is P(a), and a is b: s is P(b)
def atx.ext(P: String -> String, -s: String, -a: String, -b: String, pre: {s == P(a) : String}, e: {a == b : String}) -> {s == P(b) : String}:
  Equal.trans(String, s, P(a), P(b), pre, Equal.cong(String, String, P, a, b, e))

# Numbers, Bools
# --------------

# what a Nat reader's answer says about its input s
def atx.NP(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def atx.nat.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> atx.NP(s, d):
  match d:
    case Wr.Got{+n, +r}:
      +e2 = ed
      (Wire.wire_nat_exact(s, n, r, e2), Wire.wire_nat_decoded_fits(s, n, r, e2))
    case Wr.Bad{}:
      Unit{}

def atx.nat(+s: String) -> atx.NP(s, Wr.get_nat(s)):
  atx.nat.at(s, Wr.get_nat(s), {==})

def atx.BP(s: String, d: Wr.Dec<Bool>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {s == Wr.put_bool(b, r) : String}
    case Wr.Bad{}:
      Unit

def atx.bool.at(+s: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> atx.BP(s, d):
  match d:
    case Wr.Got{+b, +r}:
      Wire.wire_bool_exact(s, b, r, ed)
    case Wr.Bad{}:
      Unit{}

def atx.bool(+s: String) -> atx.BP(s, Wr.get_bool(s)):
  atx.bool.at(s, Wr.get_bool(s), {==})

# Tags: Maybe Nat, Dir, Lim, Status
# ---------------------------------

def atx.MP(s: String, d: Wr.Dec<Maybe<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == AgentTree.w_mnat(m, r) : String} & {LawsBase.wire_mfits(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def atx.mnat_some(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, np: atx.NP(s1, d)) -> atx.MP(s, FAt.get_mnat.some(d)):
  match d:
    case Wr.Got{+n, +r}:
      (e, f) = np
      (atx.ext(z => Wr.put_nat(1n, z), s, s1, Wr.put_nat(n, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def atx.mnat_of(t: Nat, -s: String, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> atx.MP(s, FAt.get_mnat.of(t, s1)):
  match t:
    case 0n:
      (pre, {==})
    case 1n+a:
      match a:
        case 0n:
          atx.mnat_some(s, s1, pre, Wr.get_nat(s1), atx.nat(s1))
        case 1n+b:
          Unit{}

def atx.mnat_tag(-s: String, d: Wr.Dec<Nat>, np: atx.NP(s, d)) -> atx.MP(s, FAt.get_mnat.tag(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = np
      atx.mnat_of(t, s, s1, e)
    case Wr.Bad{}:
      Unit{}

def atx.mnat(+s: String) -> atx.MP(s, FAt.get_mnat(s)):
  atx.mnat_tag(s, Wr.get_nat(s), atx.nat(s))

def atx.DP(s: String, d: Wr.Dec<T.Dir>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Wr.put_nat(AgentTree.dir_tag(x), r) : String}
    case Wr.Bad{}:
      Unit

def atx.dir_of(t: Nat, -s: String, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> atx.DP(s, FAt.get_dir.of(t, s1)):
  match t:
    case 0n:
      pre
    case 1n+a:
      match a:
        case 0n:
          pre
        case 1n+b:
          Unit{}

def atx.dir_tag(-s: String, d: Wr.Dec<Nat>, np: atx.NP(s, d)) -> atx.DP(s, FAt.get_dir.tag(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = np
      atx.dir_of(t, s, s1, e)
    case Wr.Bad{}:
      Unit{}

def atx.dir(+s: String) -> atx.DP(s, FAt.get_dir(s)):
  atx.dir_tag(s, Wr.get_nat(s), atx.nat(s))

def atx.LmP(s: String, d: Wr.Dec<T.Lim>) -> Type:
  match d:
    case Wr.Got{l, r}:
      {s == AgentTree.w_lim(l, r) : String} & {AgentTree.fit_lim(l) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def atx.lim_value(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, np: atx.NP(s1, d)) -> atx.LmP(s, FAt.get_lim.value(d)):
  match d:
    case Wr.Got{+n, +r}:
      (e, f) = np
      (atx.ext(z => Wr.put_nat(1n, z), s, s1, Wr.put_nat(n, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def atx.lim_of(t: Nat, -s: String, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> atx.LmP(s, FAt.get_lim.of(t, s1)):
  match t:
    case 0n:
      (pre, {==})
    case 1n+a:
      match a:
        case 0n:
          atx.lim_value(s, s1, pre, Wr.get_nat(s1), atx.nat(s1))
        case 1n+b:
          Unit{}

def atx.lim_tag(-s: String, d: Wr.Dec<Nat>, np: atx.NP(s, d)) -> atx.LmP(s, FAt.get_lim.tag(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = np
      atx.lim_of(t, s, s1, e)
    case Wr.Bad{}:
      Unit{}

def atx.lim(+s: String) -> atx.LmP(s, FAt.get_lim(s)):
  atx.lim_tag(s, Wr.get_nat(s), atx.nat(s))

def atx.SP(s: String, d: Wr.Dec<T.Status>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Wr.put_nat(AgentTree.status_tag(x), r) : String}
    case Wr.Bad{}:
      Unit

def atx.status_of(t: Nat, -s: String, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> atx.SP(s, FAt.get_status.of(t, s1)):
  match t:
    case 0n:
      pre
    case 1n+a:
      match a:
        case 0n:
          pre
        case 1n+b:
          match b:
            case 0n:
              pre
            case 1n+c:
              match c:
                case 0n:
                  pre
                case 1n+d:
                  Unit{}

def atx.status_tag(-s: String, d: Wr.Dec<Nat>, np: atx.NP(s, d)) -> atx.SP(s, FAt.get_status.tag(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = np
      atx.status_of(t, s, s1, e)
    case Wr.Bad{}:
      Unit{}

def atx.status(+s: String) -> atx.SP(s, FAt.get_status(s)):
  atx.status_tag(s, Wr.get_nat(s), atx.nat(s))

# Lists: Bools, patches, paths
# ----------------------------

# what the item reader's answer says about its input s (k items)
def atx.BIP(s: String, k: Nat, d: Wr.Dec<List<&2, Bool>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == AgentTree.w_bools.items(xs, r) : String} & {List.length(&2, Bool, xs) == k : Nat}
    case Wr.Bad{}:
      Unit

def atx.bool_at(+s: String, -d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> atx.BP(s, d):
  %ed : atx.BP(s, _)
  atx.bool(s)

# an item before items read
def atx.bool_cons(-s: String, +c: Bool, +r1: String, -k: Nat, d: Wr.Dec<List<&2, Bool>>, ih: atx.BIP(r1, k, d), cp: atx.BP(s, Wr.Got{c, r1})) -> atx.BIP(s, 1n+k, LawsBase.wire_items.cons(Bool, c, d)):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e2) = ih
      (atx.ext(z => Wr.put_bool(c, z), s, r1, AgentTree.w_bools.items(xs, r), cp, e1), Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Bool, xs), k, e2))
    case Wr.Bad{}:
      Unit{}

# mm + 1 items, the first read from s as cur
def atx.bool_items(mm: Nat, cur: Wr.Dec<Bool>, +s: String, er: {Wr.get_bool(s) == cur : Wr.Dec<Bool>}) -> atx.BIP(s, 1n+mm, LawsBase.wire_items.then(Bool, cur, r => LawsBase.wire_items(~Bool, ~Wr.get_bool, mm, r))):
  match mm cur:
    case 0n Wr.Got{+c, +r1}:
      atx.bool_cons(s, c, r1, 0n, Wr.Got{Nil{}, r1}, ({==}, {==}), atx.bool_at(s, Wr.Got{c, r1}, er))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+c, +r1}:
      atx.bool_cons(s, c, r1, 1n+k, LawsBase.wire_items.then(Bool, Wr.get_bool(r1), r => LawsBase.wire_items(~Bool, ~Wr.get_bool, k, r)), atx.bool_items(k, Wr.get_bool(r1), r1, {==}), atx.bool_at(s, Wr.Got{c, r1}, er))
    case 1n++k Wr.Bad{}:
      Unit{}

def atx.bool_items_of(k: Nat, +s: String) -> atx.BIP(s, k, LawsBase.wire_items(~Bool, ~Wr.get_bool, k, s)):
  match k:
    case 0n:
      ({==}, {==})
    case 1n+mm:
      atx.bool_items(mm, Wr.get_bool(s), s, {==})

# what the Bool list reader's answer says about its input s
def atx.LB(s: String, d: Wr.Dec<List<&2, Bool>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == AgentTree.w_bools(xs, r) : String} & {AgentTree.fit_bools(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def atx.bool_list(-s: String, +k: Nat, +s1: String, en: {s == Wr.put_nat(k, s1) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<List<&2, Bool>>, ip: atx.BIP(s1, k, d)) -> atx.LB(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e2) = ip
      +ln = e2
      +n = List.length(&2, Bool, xs)
      +w = AgentTree.w_bools.items(xs, r)
      +es = atx.ext(z => Wr.put_nat(k, z), s, s1, w, en, e1)
      +el = Equal.cong(Nat, String, z => Wr.put_nat(z, w), k, n, Equal.sym(Nat, n, k, ln))
      (Equal.trans(String, s, Wr.put_nat(k, w), Wr.put_nat(n, w), es, el), Equal.trans(Bool, LawsBase.wire_fits(n), LawsBase.wire_fits(k), True{}, Equal.cong(Nat, Bool, z => LawsBase.wire_fits(z), n, k, ln), fk))
    case Wr.Bad{}:
      Unit{}

def atx.bool_count(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> atx.LB(s, LawsBase.wire_read_list.count(~Bool, ~Wr.get_bool, d)):
  match d:
    case Wr.Got{+k, +s1}:
      +e = ed
      atx.bool_list(s, k, s1, Wire.wire_nat_exact(s, k, s1, e), Wire.wire_nat_decoded_fits(s, k, s1, e), LawsBase.wire_items(~Bool, ~Wr.get_bool, k, s1), atx.bool_items_of(k, s1))
    case Wr.Bad{}:
      Unit{}

def atx.bools(+s: String) -> atx.LB(s, FAt.get_bools(s)):
  %Equal.sym(Wr.Dec<List<&2, Bool>>, Wr.get_list(~Bool, ~Wr.get_bool, s), LawsBase.wire_read_list(~Bool, ~Wr.get_bool, s), Wire.wire_list_reads_items(~Bool, ~Wr.get_bool, s)) : atx.LB(s, _)
  atx.bool_count(s, Wr.get_nat(s), {==})

def atx.MIP(s: String, k: Nat, d: Wr.Dec<List<&2, Maybe<&2, Nat>>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == AgentTree.w_patch.items(xs, r) : String} & ({List.length(&2, Maybe<&2, Nat>, xs) == k : Nat} & {AgentTree.fit_patch.items(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def atx.mnat_at(+s: String, -d: Wr.Dec<Maybe<&2, Nat>>, ed: {FAt.get_mnat(s) == d : Wr.Dec<Maybe<&2, Nat>>}) -> atx.MP(s, d):
  %ed : atx.MP(s, _)
  atx.mnat(s)

def atx.mnat_cons(-s: String, +c: Maybe<&2, Nat>, +r1: String, -k: Nat, d: Wr.Dec<List<&2, Maybe<&2, Nat>>>, ih: atx.MIP(r1, k, d), cp: atx.MP(s, Wr.Got{c, r1})) -> atx.MIP(s, 1n+k, LawsBase.wire_items.cons(Maybe<&2, Nat>, c, d)):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, (e2, e3)) = ih
      (ec, fc) = cp
      (atx.ext(z => AgentTree.w_mnat(c, z), s, r1, AgentTree.w_patch.items(xs, r), ec, e1), (Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Maybe<&2, Nat>, xs), k, e2), ATE.ate.and_t(LawsBase.wire_mfits(c), AgentTree.fit_patch.items(xs), fc, e3)))
    case Wr.Bad{}:
      Unit{}

def atx.mnat_items(mm: Nat, cur: Wr.Dec<Maybe<&2, Nat>>, +s: String, er: {FAt.get_mnat(s) == cur : Wr.Dec<Maybe<&2, Nat>>}) -> atx.MIP(s, 1n+mm, LawsBase.wire_items.then(Maybe<&2, Nat>, cur, r => LawsBase.wire_items(~Maybe<&2, Nat>, ~FAt.get_mnat, mm, r))):
  match mm cur:
    case 0n Wr.Got{+c, +r1}:
      atx.mnat_cons(s, c, r1, 0n, Wr.Got{Nil{}, r1}, ({==}, ({==}, {==})), atx.mnat_at(s, Wr.Got{c, r1}, er))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+c, +r1}:
      atx.mnat_cons(s, c, r1, 1n+k, LawsBase.wire_items.then(Maybe<&2, Nat>, FAt.get_mnat(r1), r => LawsBase.wire_items(~Maybe<&2, Nat>, ~FAt.get_mnat, k, r)), atx.mnat_items(k, FAt.get_mnat(r1), r1, {==}), atx.mnat_at(s, Wr.Got{c, r1}, er))
    case 1n++k Wr.Bad{}:
      Unit{}

def atx.mnat_items_of(k: Nat, +s: String) -> atx.MIP(s, k, LawsBase.wire_items(~Maybe<&2, Nat>, ~FAt.get_mnat, k, s)):
  match k:
    case 0n:
      ({==}, ({==}, {==}))
    case 1n+mm:
      atx.mnat_items(mm, FAt.get_mnat(s), s, {==})

def atx.LM(s: String, d: Wr.Dec<List<&2, Maybe<&2, Nat>>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == AgentTree.w_patch(xs, r) : String} & {AgentTree.fit_patch(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def atx.mnat_list(-s: String, +k: Nat, +s1: String, en: {s == Wr.put_nat(k, s1) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<List<&2, Maybe<&2, Nat>>>, ip: atx.MIP(s1, k, d)) -> atx.LM(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, (e2, e3)) = ip
      +ln = e2
      +n = List.length(&2, Maybe<&2, Nat>, xs)
      +w = AgentTree.w_patch.items(xs, r)
      +es = atx.ext(z => Wr.put_nat(k, z), s, s1, w, en, e1)
      +el = Equal.cong(Nat, String, z => Wr.put_nat(z, w), k, n, Equal.sym(Nat, n, k, ln))
      +fl = Equal.trans(Bool, LawsBase.wire_fits(n), LawsBase.wire_fits(k), True{}, Equal.cong(Nat, Bool, z => LawsBase.wire_fits(z), n, k, ln), fk)
      (Equal.trans(String, s, Wr.put_nat(k, w), Wr.put_nat(n, w), es, el), ATE.ate.and_t(LawsBase.wire_fits(n), AgentTree.fit_patch.items(xs), fl, e3))
    case Wr.Bad{}:
      Unit{}

def atx.mnat_count(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> atx.LM(s, LawsBase.wire_read_list.count(~Maybe<&2, Nat>, ~FAt.get_mnat, d)):
  match d:
    case Wr.Got{+k, +s1}:
      +e = ed
      atx.mnat_list(s, k, s1, Wire.wire_nat_exact(s, k, s1, e), Wire.wire_nat_decoded_fits(s, k, s1, e), LawsBase.wire_items(~Maybe<&2, Nat>, ~FAt.get_mnat, k, s1), atx.mnat_items_of(k, s1))
    case Wr.Bad{}:
      Unit{}

def atx.patch(+s: String) -> atx.LM(s, FAt.get_patch(s)):
  %Equal.sym(Wr.Dec<List<&2, Maybe<&2, Nat>>>, Wr.get_list(~Maybe<&2, Nat>, ~FAt.get_mnat, s), LawsBase.wire_read_list(~Maybe<&2, Nat>, ~FAt.get_mnat, s), Wire.wire_list_reads_items(~Maybe<&2, Nat>, ~FAt.get_mnat, s)) : atx.LM(s, _)
  atx.mnat_count(s, Wr.get_nat(s), {==})

def atx.DIP(s: String, k: Nat, d: Wr.Dec<List<&2, T.Dir>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == AgentTree.w_path.items(xs, r) : String} & {List.length(&2, T.Dir, xs) == k : Nat}
    case Wr.Bad{}:
      Unit

def atx.dir_at(+s: String, -d: Wr.Dec<T.Dir>, ed: {FAt.get_dir(s) == d : Wr.Dec<T.Dir>}) -> atx.DP(s, d):
  %ed : atx.DP(s, _)
  atx.dir(s)

def atx.dir_cons(-s: String, +c: T.Dir, +r1: String, -k: Nat, d: Wr.Dec<List<&2, T.Dir>>, ih: atx.DIP(r1, k, d), cp: atx.DP(s, Wr.Got{c, r1})) -> atx.DIP(s, 1n+k, LawsBase.wire_items.cons(T.Dir, c, d)):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e2) = ih
      (atx.ext(z => Wr.put_nat(AgentTree.dir_tag(c), z), s, r1, AgentTree.w_path.items(xs, r), cp, e1), Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, T.Dir, xs), k, e2))
    case Wr.Bad{}:
      Unit{}

def atx.dir_items(mm: Nat, cur: Wr.Dec<T.Dir>, +s: String, er: {FAt.get_dir(s) == cur : Wr.Dec<T.Dir>}) -> atx.DIP(s, 1n+mm, LawsBase.wire_items.then(T.Dir, cur, r => LawsBase.wire_items(~T.Dir, ~FAt.get_dir, mm, r))):
  match mm cur:
    case 0n Wr.Got{+c, +r1}:
      atx.dir_cons(s, c, r1, 0n, Wr.Got{Nil{}, r1}, ({==}, {==}), atx.dir_at(s, Wr.Got{c, r1}, er))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+c, +r1}:
      atx.dir_cons(s, c, r1, 1n+k, LawsBase.wire_items.then(T.Dir, FAt.get_dir(r1), r => LawsBase.wire_items(~T.Dir, ~FAt.get_dir, k, r)), atx.dir_items(k, FAt.get_dir(r1), r1, {==}), atx.dir_at(s, Wr.Got{c, r1}, er))
    case 1n++k Wr.Bad{}:
      Unit{}

def atx.dir_items_of(k: Nat, +s: String) -> atx.DIP(s, k, LawsBase.wire_items(~T.Dir, ~FAt.get_dir, k, s)):
  match k:
    case 0n:
      ({==}, {==})
    case 1n+mm:
      atx.dir_items(mm, FAt.get_dir(s), s, {==})

def atx.LP(s: String, d: Wr.Dec<List<&2, T.Dir>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == AgentTree.w_path(xs, r) : String} & {AgentTree.fit_path(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def atx.dir_list(-s: String, +k: Nat, +s1: String, en: {s == Wr.put_nat(k, s1) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<List<&2, T.Dir>>, ip: atx.DIP(s1, k, d)) -> atx.LP(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e2) = ip
      +ln = e2
      +n = List.length(&2, T.Dir, xs)
      +w = AgentTree.w_path.items(xs, r)
      +es = atx.ext(z => Wr.put_nat(k, z), s, s1, w, en, e1)
      +el = Equal.cong(Nat, String, z => Wr.put_nat(z, w), k, n, Equal.sym(Nat, n, k, ln))
      (Equal.trans(String, s, Wr.put_nat(k, w), Wr.put_nat(n, w), es, el), Equal.trans(Bool, LawsBase.wire_fits(n), LawsBase.wire_fits(k), True{}, Equal.cong(Nat, Bool, z => LawsBase.wire_fits(z), n, k, ln), fk))
    case Wr.Bad{}:
      Unit{}

def atx.dir_count(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> atx.LP(s, LawsBase.wire_read_list.count(~T.Dir, ~FAt.get_dir, d)):
  match d:
    case Wr.Got{+k, +s1}:
      +e = ed
      atx.dir_list(s, k, s1, Wire.wire_nat_exact(s, k, s1, e), Wire.wire_nat_decoded_fits(s, k, s1, e), LawsBase.wire_items(~T.Dir, ~FAt.get_dir, k, s1), atx.dir_items_of(k, s1))
    case Wr.Bad{}:
      Unit{}

def atx.path(+s: String) -> atx.LP(s, FAt.get_path(s)):
  %Equal.sym(Wr.Dec<List<&2, T.Dir>>, Wr.get_list(~T.Dir, ~FAt.get_dir, s), LawsBase.wire_read_list(~T.Dir, ~FAt.get_dir, s), Wire.wire_list_reads_items(~T.Dir, ~FAt.get_dir, s)) : atx.LP(s, _)
  atx.dir_count(s, Wr.get_nat(s), {==})

# Info
# ----
# field by field (a stage calls the next)

def atx.IP(s: String, d: Wr.Dec<T.Info>) -> Type:
  match d:
    case Wr.Got{i, r}:
      {s == AgentTree.w_info(i, r) : String} & {AgentTree.fit_info(i) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def atx.info_patch(-s: String, +st: T.Status, +sc: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +s5: String, pre: {s == Wr.put_nat(AgentTree.status_tag(st), AgentTree.w_bools(sc, AgentTree.w_lim(lim, Wr.put_nat(sp, AgentTree.w_lim(dl, s5))))) : String}, fsc: {AgentTree.fit_bools(sc) == True{} : Bool}, flim: {AgentTree.fit_lim(lim) == True{} : Bool}, fsp: {LawsBase.wire_fits(sp) == True{} : Bool}, fdl: {AgentTree.fit_lim(dl) == True{} : Bool}, d: Wr.Dec<List<&2, Maybe<&2, Nat>>>, lp: atx.LM(s5, d)) -> atx.IP(s, FAt.get_info.patch(st, sc, lim, sp, dl, d)):
  match d:
    case Wr.Got{+p, +r}:
      (e, fp) = lp
      (atx.ext(z => Wr.put_nat(AgentTree.status_tag(st), AgentTree.w_bools(sc, AgentTree.w_lim(lim, Wr.put_nat(sp, AgentTree.w_lim(dl, z))))), s, s5, AgentTree.w_patch(p, r), pre, e), ATE.ate.and_t(AgentTree.fit_bools(sc), Bool.and(AgentTree.fit_lim(lim), Bool.and(LawsBase.wire_fits(sp), Bool.and(AgentTree.fit_lim(dl), AgentTree.fit_patch(p)))), fsc, ATE.ate.and_t(AgentTree.fit_lim(lim), Bool.and(LawsBase.wire_fits(sp), Bool.and(AgentTree.fit_lim(dl), AgentTree.fit_patch(p))), flim, ATE.ate.and_t(LawsBase.wire_fits(sp), Bool.and(AgentTree.fit_lim(dl), AgentTree.fit_patch(p)), fsp, ATE.ate.and_t(AgentTree.fit_lim(dl), AgentTree.fit_patch(p), fdl, fp)))))
    case Wr.Bad{}:
      Unit{}

def atx.info_deadline(-s: String, +st: T.Status, +sc: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +s4: String, pre: {s == Wr.put_nat(AgentTree.status_tag(st), AgentTree.w_bools(sc, AgentTree.w_lim(lim, Wr.put_nat(sp, s4)))) : String}, fsc: {AgentTree.fit_bools(sc) == True{} : Bool}, flim: {AgentTree.fit_lim(lim) == True{} : Bool}, fsp: {LawsBase.wire_fits(sp) == True{} : Bool}, d: Wr.Dec<T.Lim>, lp: atx.LmP(s4, d)) -> atx.IP(s, FAt.get_info.deadline(st, sc, lim, sp, d)):
  match d:
    case Wr.Got{+dl, +s5}:
      (e, f) = lp
      atx.info_patch(s, st, sc, lim, sp, dl, s5, atx.ext(z => Wr.put_nat(AgentTree.status_tag(st), AgentTree.w_bools(sc, AgentTree.w_lim(lim, Wr.put_nat(sp, z)))), s, s4, AgentTree.w_lim(dl, s5), pre, e), fsc, flim, fsp, f, FAt.get_patch(s5), atx.patch(s5))
    case Wr.Bad{}:
      Unit{}

def atx.info_spent(-s: String, +st: T.Status, +sc: List<&2, Bool>, +lim: T.Lim, +s3: String, pre: {s == Wr.put_nat(AgentTree.status_tag(st), AgentTree.w_bools(sc, AgentTree.w_lim(lim, s3))) : String}, fsc: {AgentTree.fit_bools(sc) == True{} : Bool}, flim: {AgentTree.fit_lim(lim) == True{} : Bool}, d: Wr.Dec<Nat>, np: atx.NP(s3, d)) -> atx.IP(s, FAt.get_info.spent(st, sc, lim, d)):
  match d:
    case Wr.Got{+sp, +s4}:
      (e, f) = np
      atx.info_deadline(s, st, sc, lim, sp, s4, atx.ext(z => Wr.put_nat(AgentTree.status_tag(st), AgentTree.w_bools(sc, AgentTree.w_lim(lim, z))), s, s3, Wr.put_nat(sp, s4), pre, e), fsc, flim, f, FAt.get_lim(s4), atx.lim(s4))
    case Wr.Bad{}:
      Unit{}

def atx.info_limit(-s: String, +st: T.Status, +sc: List<&2, Bool>, +s2: String, pre: {s == Wr.put_nat(AgentTree.status_tag(st), AgentTree.w_bools(sc, s2)) : String}, fsc: {AgentTree.fit_bools(sc) == True{} : Bool}, d: Wr.Dec<T.Lim>, lp: atx.LmP(s2, d)) -> atx.IP(s, FAt.get_info.limit(st, sc, d)):
  match d:
    case Wr.Got{+lim, +s3}:
      (e, f) = lp
      atx.info_spent(s, st, sc, lim, s3, atx.ext(z => Wr.put_nat(AgentTree.status_tag(st), AgentTree.w_bools(sc, z)), s, s2, AgentTree.w_lim(lim, s3), pre, e), fsc, f, Wr.get_nat(s3), atx.nat(s3))
    case Wr.Bad{}:
      Unit{}

def atx.info_scope(-s: String, +st: T.Status, +s1: String, pre: {s == Wr.put_nat(AgentTree.status_tag(st), s1) : String}, d: Wr.Dec<List<&2, Bool>>, lp: atx.LB(s1, d)) -> atx.IP(s, FAt.get_info.scope(st, d)):
  match d:
    case Wr.Got{+sc, +s2}:
      (e, f) = lp
      atx.info_limit(s, st, sc, s2, atx.ext(z => Wr.put_nat(AgentTree.status_tag(st), z), s, s1, AgentTree.w_bools(sc, s2), pre, e), f, FAt.get_lim(s2), atx.lim(s2))
    case Wr.Bad{}:
      Unit{}

def atx.info_status(-s: String, d: Wr.Dec<T.Status>, sp: atx.SP(s, d)) -> atx.IP(s, FAt.get_info.status(d)):
  match d:
    case Wr.Got{+st, +s1}:
      atx.info_scope(s, st, s1, sp, FAt.get_bools(s1), atx.bools(s1))
    case Wr.Bad{}:
      Unit{}

def atx.info(+s: String) -> atx.IP(s, FAt.get_info(s)):
  atx.info_status(s, FAt.get_status(s), atx.status(s))

# Node
# ----

# a node's head before r
def atx.w_head(h: FAt.Head, r: String) -> String:
  match h:
    case FAt.HLeaf{i}:
      Wr.put_nat(0n, AgentTree.w_info(i, r))
    case FAt.HSplit{i, own}:
      Wr.put_nat(1n, AgentTree.w_info(i, AgentTree.w_bools(own, r)))

def atx.fit_head(h: FAt.Head) -> Bool:
  match h:
    case FAt.HLeaf{i}:
      AgentTree.fit_info(i)
    case FAt.HSplit{i, +own}:
      Bool.and(AgentTree.fit_info(i), AgentTree.fit_bools(own))

def atx.HP(s: String, d: Wr.Dec<FAt.Head>) -> Type:
  match d:
    case Wr.Got{h, r}:
      {s == atx.w_head(h, r) : String} & {atx.fit_head(h) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def atx.head_own(-s: String, +i: T.Info, +sk: String, pre: {s == Wr.put_nat(1n, AgentTree.w_info(i, sk)) : String}, fi: {AgentTree.fit_info(i) == True{} : Bool}, d: Wr.Dec<List<&2, Bool>>, lp: atx.LB(sk, d)) -> atx.HP(s, FAt.get_head.own(i, d)):
  match d:
    case Wr.Got{+own, +r}:
      (e, f) = lp
      (atx.ext(z => Wr.put_nat(1n, AgentTree.w_info(i, z)), s, sk, AgentTree.w_bools(own, r), pre, e), ATE.ate.and_t(AgentTree.fit_info(i), AgentTree.fit_bools(own), fi, f))
    case Wr.Bad{}:
      Unit{}

def atx.head_split(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<T.Info>, ip: atx.IP(s1, d)) -> atx.HP(s, FAt.get_head.split(d)):
  match d:
    case Wr.Got{+i, +sk}:
      (e, f) = ip
      atx.head_own(s, i, sk, atx.ext(z => Wr.put_nat(1n, z), s, s1, AgentTree.w_info(i, sk), pre, e), f, FAt.get_bools(sk), atx.bools(sk))
    case Wr.Bad{}:
      Unit{}

def atx.head_leaf(-s: String, +s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<T.Info>, ip: atx.IP(s1, d)) -> atx.HP(s, FAt.get_head.leaf(d)):
  match d:
    case Wr.Got{+i, +r}:
      (e, f) = ip
      (atx.ext(z => Wr.put_nat(0n, z), s, s1, AgentTree.w_info(i, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def atx.head_of(t: Nat, -s: String, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> atx.HP(s, FAt.get_head.of(t, s1)):
  match t:
    case 0n:
      atx.head_leaf(s, s1, pre, FAt.get_info(s1), atx.info(s1))
    case 1n+a:
      match a:
        case 0n:
          atx.head_split(s, s1, pre, FAt.get_info(s1), atx.info(s1))
        case 1n+b:
          Unit{}

def atx.head_tag(-s: String, d: Wr.Dec<Nat>, np: atx.NP(s, d)) -> atx.HP(s, FAt.get_head.tag(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = np
      atx.head_of(t, s, s1, e)
    case Wr.Bad{}:
      Unit{}

def atx.head(+s: String) -> atx.HP(s, FAt.get_head(s)):
  atx.head_tag(s, Wr.get_nat(s), atx.nat(s))

# what the node reader's answer says about its input s
def atx.NdP(s: String, d: Wr.Dec<T.Node>) -> Type:
  match d:
    case Wr.Got{t, r}:
      {s == AgentTree.w_node(t, r) : String} & {AgentTree.fit_node(t) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# past a split's head and its left child l: what the left child's answer
# says about the input s
def atx.RP(s: String, i: T.Info, own: List<&2, Bool>, l: Wr.Dec<T.Node>) -> Type:
  match l:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(1n, AgentTree.w_info(i, AgentTree.w_bools(own, AgentTree.w_node(n, r)))) : String} & ({AgentTree.fit_info(i) == True{} : Bool} & ({AgentTree.fit_bools(own) == True{} : Bool} & {AgentTree.fit_node(n) == True{} : Bool}))
    case Wr.Bad{}:
      Unit

# what the node reader at m says about its input s
def atx.AtP(s: String, m: FAt.At) -> Type:
  match m:
    case FAt.AtHead{d}:
      atx.HP(s, d)
    case FAt.AtRight{i, own, l}:
      atx.RP(s, i, own, l)

def atx.right_of(-s: String, +i: T.Info, +own: List<&2, Bool>, +r0: String, pre: {s == Wr.put_nat(1n, AgentTree.w_info(i, AgentTree.w_bools(own, r0))) : String}, fi: {AgentTree.fit_info(i) == True{} : Bool}, fo: {AgentTree.fit_bools(own) == True{} : Bool}, d: Wr.Dec<T.Node>, np: atx.NdP(r0, d)) -> atx.RP(s, i, own, d):
  match d:
    case Wr.Got{+n, +r}:
      (e, f) = np
      (atx.ext(z => Wr.put_nat(1n, AgentTree.w_info(i, AgentTree.w_bools(own, z))), s, r0, AgentTree.w_node(n, r), pre, e), (fi, (fo, f)))
    case Wr.Bad{}:
      Unit{}

def atx.join(-s: String, +i: T.Info, +own: List<&2, Bool>, +l: T.Node, +r0: String, pre: {s == Wr.put_nat(1n, AgentTree.w_info(i, AgentTree.w_bools(own, AgentTree.w_node(l, r0)))) : String}, fi: {AgentTree.fit_info(i) == True{} : Bool}, fo: {AgentTree.fit_bools(own) == True{} : Bool}, fl: {AgentTree.fit_node(l) == True{} : Bool}, d: Wr.Dec<T.Node>, np: atx.NdP(r0, d)) -> atx.NdP(s, FAt.get_node.join(i, own, l, d)):
  match d:
    case Wr.Got{+n, +r}:
      (e, f) = np
      (atx.ext(z => Wr.put_nat(1n, AgentTree.w_info(i, AgentTree.w_bools(own, AgentTree.w_node(l, z)))), s, r0, AgentTree.w_node(n, r), pre, e), ATE.ate.and_t(AgentTree.fit_info(i), Bool.and(AgentTree.fit_bools(own), Bool.and(AgentTree.fit_node(l), AgentTree.fit_node(n))), fi, ATE.ate.and_t(AgentTree.fit_bools(own), Bool.and(AgentTree.fit_node(l), AgentTree.fit_node(n)), fo, ATE.ate.and_t(AgentTree.fit_node(l), AgentTree.fit_node(n), fl, f))))
    case Wr.Bad{}:
      Unit{}

# the node reader accepts only spelled nodes that fit, whatever its fuel
def atx.go(f: Nat, -s: String, m: FAt.At, mp: atx.AtP(s, m)) -> atx.NdP(s, FAt.get_node.go(f, m)):
  match f:
    case 0n:
      Unit{}
    case 1n++g:
      match m:
        case FAt.AtHead{d}:
          match d:
            case Wr.Got{+h, +r}:
              match h:
                case FAt.HLeaf{+i}:
                  mp
                case FAt.HSplit{+i, +own}:
                  (e, fh) = mp
                  +fh0 = fh
                  +fi = ATE.ate.and_l(AgentTree.fit_info(i), AgentTree.fit_bools(own), fh0)
                  +fo = ATE.ate.and_r(AgentTree.fit_info(i), AgentTree.fit_bools(own), fh0)
                  +inner = FAt.get_node.go(g, FAt.AtHead{FAt.get_head(r)})
                  atx.go(g, s, FAt.AtRight{i, own, inner}, atx.right_of(s, i, own, r, e, fi, fo, inner, atx.go(g, r, FAt.AtHead{FAt.get_head(r)}, atx.head(r))))
            case Wr.Bad{}:
              Unit{}
        case FAt.AtRight{+i, +own, l}:
          match l:
            case Wr.Got{+n, +r}:
              (e, rest) = mp
              (fi, rest2) = rest
              (fo, fl) = rest2
              atx.join(s, i, own, n, r, e, fi, fo, fl, FAt.get_node.go(g, FAt.AtHead{FAt.get_head(r)}), atx.go(g, r, FAt.AtHead{FAt.get_head(r)}, atx.head(r)))
            case Wr.Bad{}:
              Unit{}

def atx.node(+s: String) -> atx.NdP(s, FAt.get_node(s)):
  atx.go(String.length(s), s, FAt.AtHead{FAt.get_head(s)}, atx.head(s))

# Bounds, view
# ------------

def atx.BdP(s: String, d: Wr.Dec<T.Bounds>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {s == AgentTree.w_bounds(b, r) : String} & {AgentTree.fit_bounds(b) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def atx.bounds_margin(-s: String, +dd: Nat, +n: Nat, +sk: String, pre: {s == Wr.put_nat(dd, Wr.put_nat(n, sk)) : String}, fd: {LawsBase.wire_fits(dd) == True{} : Bool}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<Nat>, np: atx.NP(sk, d)) -> atx.BdP(s, FAt.get_bounds.margin(dd, n, d)):
  match d:
    case Wr.Got{+m, +r}:
      (e, f) = np
      (atx.ext(z => Wr.put_nat(dd, Wr.put_nat(n, z)), s, sk, Wr.put_nat(m, r), pre, e), ATE.ate.and_t(LawsBase.wire_fits(dd), Bool.and(LawsBase.wire_fits(n), LawsBase.wire_fits(m)), fd, ATE.ate.and_t(LawsBase.wire_fits(n), LawsBase.wire_fits(m), fn, f)))
    case Wr.Bad{}:
      Unit{}

def atx.bounds_nodes(-s: String, +dd: Nat, +sk: String, pre: {s == Wr.put_nat(dd, sk) : String}, fd: {LawsBase.wire_fits(dd) == True{} : Bool}, d: Wr.Dec<Nat>, np: atx.NP(sk, d)) -> atx.BdP(s, FAt.get_bounds.nodes(dd, d)):
  match d:
    case Wr.Got{+n, +r}:
      (e, f) = np
      atx.bounds_margin(s, dd, n, r, atx.ext(z => Wr.put_nat(dd, z), s, sk, Wr.put_nat(n, r), pre, e), fd, f, Wr.get_nat(r), atx.nat(r))
    case Wr.Bad{}:
      Unit{}

def atx.bounds_depth(-s: String, d: Wr.Dec<Nat>, np: atx.NP(s, d)) -> atx.BdP(s, FAt.get_bounds.depth(d)):
  match d:
    case Wr.Got{+dd, +r}:
      (e, f) = np
      atx.bounds_nodes(s, dd, r, e, f, Wr.get_nat(r), atx.nat(r))
    case Wr.Bad{}:
      Unit{}

def atx.bounds(+s: String) -> atx.BdP(s, FAt.get_bounds(s)):
  atx.bounds_depth(s, Wr.get_nat(s), atx.nat(s))

def atx.VP(s: String, d: Wr.Dec<T.View>) -> Type:
  match d:
    case Wr.Got{v, r}:
      {s == AgentTree.w_view(v, r) : String} & {AgentTree.fit_view(v) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def atx.view_work(-s: String, +m: Bool, +n: Nat, +sk: String, pre: {s == Wr.put_bool(m, Wr.put_nat(n, sk)) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<Bool>, bp: atx.BP(sk, d)) -> atx.VP(s, FAt.get_view.work(m, n, d)):
  match d:
    case Wr.Got{+w, +r}:
      (atx.ext(z => Wr.put_bool(m, Wr.put_nat(n, z)), s, sk, Wr.put_bool(w, r), pre, bp), fn)
    case Wr.Bad{}:
      Unit{}

def atx.view_arrived(-s: String, +m: Bool, +sk: String, pre: {s == Wr.put_bool(m, sk) : String}, d: Wr.Dec<Nat>, np: atx.NP(sk, d)) -> atx.VP(s, FAt.get_view.arrived(m, d)):
  match d:
    case Wr.Got{+n, +r}:
      (e, f) = np
      atx.view_work(s, m, n, r, atx.ext(z => Wr.put_bool(m, z), s, sk, Wr.put_nat(n, r), pre, e), f, Wr.get_bool(r), atx.bool(r))
    case Wr.Bad{}:
      Unit{}

def atx.view_message(-s: String, d: Wr.Dec<Bool>, bp: atx.BP(s, d)) -> atx.VP(s, FAt.get_view.message(d)):
  match d:
    case Wr.Got{+m, +r}:
      atx.view_arrived(s, m, r, bp, Wr.get_nat(r), atx.nat(r))
    case Wr.Bad{}:
      Unit{}

def atx.view(+s: String) -> atx.VP(s, FAt.get_view(s)):
  atx.view_message(s, Wr.get_bool(s), atx.bool(s))

# Event
# -----

def atx.EP(s: String, d: Wr.Dec<T.Ev>) -> Type:
  match d:
    case Wr.Got{e, r}:
      {s == AgentTree.w_ev(e, r) : String} & {AgentTree.fit_ev(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def atx.split_hold(-s: String, +at: List<&2, T.Dir>, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>, +sk: String, pre: {s == Wr.put_nat(0n, AgentTree.w_path(at, AgentTree.w_bools(own, AgentTree.w_bools(ls, AgentTree.w_bools(rs, sk))))) : String}, fa: {AgentTree.fit_path(at) == True{} : Bool}, fo: {AgentTree.fit_bools(own) == True{} : Bool}, fl: {AgentTree.fit_bools(ls) == True{} : Bool}, fr: {AgentTree.fit_bools(rs) == True{} : Bool}, d: Wr.Dec<Nat>, np: atx.NP(sk, d)) -> atx.EP(s, FAt.get_ev.split_hold(at, own, ls, rs, d)):
  match d:
    case Wr.Got{+hold, +r}:
      (e, f) = np
      (atx.ext(z => Wr.put_nat(0n, AgentTree.w_path(at, AgentTree.w_bools(own, AgentTree.w_bools(ls, AgentTree.w_bools(rs, z))))), s, sk, Wr.put_nat(hold, r), pre, e), ATE.ate.and_t(AgentTree.fit_path(at), Bool.and(AgentTree.fit_bools(own), Bool.and(AgentTree.fit_bools(ls), Bool.and(AgentTree.fit_bools(rs), LawsBase.wire_fits(hold)))), fa, ATE.ate.and_t(AgentTree.fit_bools(own), Bool.and(AgentTree.fit_bools(ls), Bool.and(AgentTree.fit_bools(rs), LawsBase.wire_fits(hold))), fo, ATE.ate.and_t(AgentTree.fit_bools(ls), Bool.and(AgentTree.fit_bools(rs), LawsBase.wire_fits(hold)), fl, ATE.ate.and_t(AgentTree.fit_bools(rs), LawsBase.wire_fits(hold), fr, f)))))
    case Wr.Bad{}:
      Unit{}

def atx.split_rs(-s: String, +at: List<&2, T.Dir>, +own: List<&2, Bool>, +ls: List<&2, Bool>, +sk: String, pre: {s == Wr.put_nat(0n, AgentTree.w_path(at, AgentTree.w_bools(own, AgentTree.w_bools(ls, sk)))) : String}, fa: {AgentTree.fit_path(at) == True{} : Bool}, fo: {AgentTree.fit_bools(own) == True{} : Bool}, fl: {AgentTree.fit_bools(ls) == True{} : Bool}, d: Wr.Dec<List<&2, Bool>>, lp: atx.LB(sk, d)) -> atx.EP(s, FAt.get_ev.split_rs(at, own, ls, d)):
  match d:
    case Wr.Got{+rs, +r}:
      (e, f) = lp
      atx.split_hold(s, at, own, ls, rs, r, atx.ext(z => Wr.put_nat(0n, AgentTree.w_path(at, AgentTree.w_bools(own, AgentTree.w_bools(ls, z)))), s, sk, AgentTree.w_bools(rs, r), pre, e), fa, fo, fl, f, Wr.get_nat(r), atx.nat(r))
    case Wr.Bad{}:
      Unit{}

def atx.split_ls(-s: String, +at: List<&2, T.Dir>, +own: List<&2, Bool>, +sk: String, pre: {s == Wr.put_nat(0n, AgentTree.w_path(at, AgentTree.w_bools(own, sk))) : String}, fa: {AgentTree.fit_path(at) == True{} : Bool}, fo: {AgentTree.fit_bools(own) == True{} : Bool}, d: Wr.Dec<List<&2, Bool>>, lp: atx.LB(sk, d)) -> atx.EP(s, FAt.get_ev.split_ls(at, own, d)):
  match d:
    case Wr.Got{+ls, +r}:
      (e, f) = lp
      atx.split_rs(s, at, own, ls, r, atx.ext(z => Wr.put_nat(0n, AgentTree.w_path(at, AgentTree.w_bools(own, z))), s, sk, AgentTree.w_bools(ls, r), pre, e), fa, fo, f, FAt.get_bools(r), atx.bools(r))
    case Wr.Bad{}:
      Unit{}

def atx.split_own(-s: String, +at: List<&2, T.Dir>, +sk: String, pre: {s == Wr.put_nat(0n, AgentTree.w_path(at, sk)) : String}, fa: {AgentTree.fit_path(at) == True{} : Bool}, d: Wr.Dec<List<&2, Bool>>, lp: atx.LB(sk, d)) -> atx.EP(s, FAt.get_ev.split_own(at, d)):
  match d:
    case Wr.Got{+own, +r}:
      (e, f) = lp
      atx.split_ls(s, at, own, r, atx.ext(z => Wr.put_nat(0n, AgentTree.w_path(at, z)), s, sk, AgentTree.w_bools(own, r), pre, e), fa, f, FAt.get_bools(r), atx.bools(r))
    case Wr.Bad{}:
      Unit{}

def atx.spend(-s: String, +at: List<&2, T.Dir>, +sk: String, pre: {s == Wr.put_nat(1n, AgentTree.w_path(at, sk)) : String}, fa: {AgentTree.fit_path(at) == True{} : Bool}, d: Wr.Dec<Nat>, np: atx.NP(sk, d)) -> atx.EP(s, FAt.get_ev.spend(at, d)):
  match d:
    case Wr.Got{+n, +r}:
      (e, f) = np
      (atx.ext(z => Wr.put_nat(1n, AgentTree.w_path(at, z)), s, sk, Wr.put_nat(n, r), pre, e), ATE.ate.and_t(AgentTree.fit_path(at), LawsBase.wire_fits(n), fa, f))
    case Wr.Bad{}:
      Unit{}

def atx.finish(-s: String, +at: List<&2, T.Dir>, +sk: String, pre: {s == Wr.put_nat(2n, AgentTree.w_path(at, sk)) : String}, fa: {AgentTree.fit_path(at) == True{} : Bool}, d: Wr.Dec<List<&2, Maybe<&2, Nat>>>, lp: atx.LM(sk, d)) -> atx.EP(s, FAt.get_ev.finish(at, d)):
  match d:
    case Wr.Got{+p, +r}:
      (e, f) = lp
      (atx.ext(z => Wr.put_nat(2n, AgentTree.w_path(at, z)), s, sk, AgentTree.w_patch(p, r), pre, e), ATE.ate.and_t(AgentTree.fit_path(at), AgentTree.fit_patch(p), fa, f))
    case Wr.Bad{}:
      Unit{}

def atx.fail(-s: String, +at: List<&2, T.Dir>, +sk: String, pre: {s == Wr.put_nat(3n, AgentTree.w_path(at, sk)) : String}, fa: {AgentTree.fit_path(at) == True{} : Bool}, d: Wr.Dec<List<&2, Maybe<&2, Nat>>>, lp: atx.LM(sk, d)) -> atx.EP(s, FAt.get_ev.fail(at, d)):
  match d:
    case Wr.Got{+p, +r}:
      (e, f) = lp
      (atx.ext(z => Wr.put_nat(3n, AgentTree.w_path(at, z)), s, sk, AgentTree.w_patch(p, r), pre, e), ATE.ate.and_t(AgentTree.fit_path(at), AgentTree.fit_patch(p), fa, f))
    case Wr.Bad{}:
      Unit{}

def atx.redo_extra(-s: String, +at: List<&2, T.Dir>, +side: T.Dir, +sk: String, pre: {s == Wr.put_nat(5n, AgentTree.w_path(at, Wr.put_nat(AgentTree.dir_tag(side), sk))) : String}, fa: {AgentTree.fit_path(at) == True{} : Bool}, d: Wr.Dec<Nat>, np: atx.NP(sk, d)) -> atx.EP(s, FAt.get_ev.redo_extra(at, side, d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, f) = np
      (atx.ext(z => Wr.put_nat(5n, AgentTree.w_path(at, Wr.put_nat(AgentTree.dir_tag(side), z))), s, sk, Wr.put_nat(x, r), pre, e), ATE.ate.and_t(AgentTree.fit_path(at), LawsBase.wire_fits(x), fa, f))
    case Wr.Bad{}:
      Unit{}

def atx.redo_side(-s: String, +at: List<&2, T.Dir>, +sk: String, pre: {s == Wr.put_nat(5n, AgentTree.w_path(at, sk)) : String}, fa: {AgentTree.fit_path(at) == True{} : Bool}, d: Wr.Dec<T.Dir>, dp: atx.DP(sk, d)) -> atx.EP(s, FAt.get_ev.redo_side(at, d)):
  match d:
    case Wr.Got{+side, +r}:
      atx.redo_extra(s, at, side, r, atx.ext(z => Wr.put_nat(5n, AgentTree.w_path(at, z)), s, sk, Wr.put_nat(AgentTree.dir_tag(side), r), pre, dp), fa, Wr.get_nat(r), atx.nat(r))
    case Wr.Bad{}:
      Unit{}

def atx.ev_of(t: Nat, -s: String, +at: List<&2, T.Dir>, +sk: String, pre: {s == Wr.put_nat(t, AgentTree.w_path(at, sk)) : String}, fa: {AgentTree.fit_path(at) == True{} : Bool}) -> atx.EP(s, FAt.get_ev.of(t, at, sk)):
  match t:
    case 0n:
      atx.split_own(s, at, sk, pre, fa, FAt.get_bools(sk), atx.bools(sk))
    case 1n+a:
      match a:
        case 0n:
          atx.spend(s, at, sk, pre, fa, Wr.get_nat(sk), atx.nat(sk))
        case 1n+b:
          match b:
            case 0n:
              atx.finish(s, at, sk, pre, fa, FAt.get_patch(sk), atx.patch(sk))
            case 1n+c:
              match c:
                case 0n:
                  atx.fail(s, at, sk, pre, fa, FAt.get_patch(sk), atx.patch(sk))
                case 1n+d:
                  match d:
                    case 0n:
                      (pre, fa)
                    case 1n+e:
                      match e:
                        case 0n:
                          atx.redo_side(s, at, sk, pre, fa, FAt.get_dir(sk), atx.dir(sk))
                        case 1n+g:
                          Unit{}

def atx.ev_at(+t: Nat, -s: String, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}, d: Wr.Dec<List<&2, T.Dir>>, lp: atx.LP(s1, d)) -> atx.EP(s, FAt.get_ev.at(t, d)):
  match d:
    case Wr.Got{+at, +sk}:
      (e, f) = lp
      atx.ev_of(t, s, at, sk, atx.ext(z => Wr.put_nat(t, z), s, s1, AgentTree.w_path(at, sk), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def atx.tick(-s: String, +s1: String, pre: {s == Wr.put_nat(6n, s1) : String}, d: Wr.Dec<Nat>, np: atx.NP(s1, d)) -> atx.EP(s, FAt.get_ev.tick(d)):
  match d:
    case Wr.Got{+n, +r}:
      (e, f) = np
      (atx.ext(z => Wr.put_nat(6n, z), s, s1, Wr.put_nat(n, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def atx.ev_tagged(t: Nat, -s: String, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> atx.EP(s, FAt.get_ev.tagged(t, s1)):
  match t:
    case 0n:
      atx.ev_at(0n, s, s1, pre, FAt.get_path(s1), atx.path(s1))
    case 1n+a:
      match a:
        case 0n:
          atx.ev_at(1n, s, s1, pre, FAt.get_path(s1), atx.path(s1))
        case 1n+b:
          match b:
            case 0n:
              atx.ev_at(2n, s, s1, pre, FAt.get_path(s1), atx.path(s1))
            case 1n+c:
              match c:
                case 0n:
                  atx.ev_at(3n, s, s1, pre, FAt.get_path(s1), atx.path(s1))
                case 1n+d:
                  match d:
                    case 0n:
                      atx.ev_at(4n, s, s1, pre, FAt.get_path(s1), atx.path(s1))
                    case 1n+e:
                      match e:
                        case 0n:
                          atx.ev_at(5n, s, s1, pre, FAt.get_path(s1), atx.path(s1))
                        case 1n+f:
                          match f:
                            case 0n:
                              atx.tick(s, s1, pre, Wr.get_nat(s1), atx.nat(s1))
                            case 1n+g:
                              Unit{}

def atx.ev_tag(-s: String, d: Wr.Dec<Nat>, np: atx.NP(s, d)) -> atx.EP(s, FAt.get_ev.tag(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = np
      atx.ev_tagged(t, s, s1, e)
    case Wr.Bad{}:
      Unit{}

def atx.ev(+s: String) -> atx.EP(s, FAt.get_ev(s)):
  atx.ev_tag(s, Wr.get_nat(s), atx.nat(s))

# Help leaves, crown, crown event
# -------------------------------

def atx.HlP(s: String, d: Wr.Dec<C.Help>) -> Type:
  match d:
    case Wr.Got{h, r}:
      {s == AgentTree.w_help(h, r) : String} & {AgentTree.fit_help(h) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def atx.help_deadline(-s: String, +at: List<&2, T.Dir>, +st: T.Status, +lim: T.Lim, +sp: Nat, +sk: String, pre: {s == AgentTree.w_path(at, Wr.put_nat(AgentTree.status_tag(st), AgentTree.w_lim(lim, Wr.put_nat(sp, sk)))) : String}, fa: {AgentTree.fit_path(at) == True{} : Bool}, fl: {AgentTree.fit_lim(lim) == True{} : Bool}, fs: {LawsBase.wire_fits(sp) == True{} : Bool}, d: Wr.Dec<T.Lim>, lp: atx.LmP(sk, d)) -> atx.HlP(s, FAt.get_help.deadline(at, st, lim, sp, d)):
  match d:
    case Wr.Got{+dl, +r}:
      (e, f) = lp
      (atx.ext(z => AgentTree.w_path(at, Wr.put_nat(AgentTree.status_tag(st), AgentTree.w_lim(lim, Wr.put_nat(sp, z)))), s, sk, AgentTree.w_lim(dl, r), pre, e), ATE.ate.and_t(AgentTree.fit_path(at), Bool.and(AgentTree.fit_lim(lim), Bool.and(LawsBase.wire_fits(sp), AgentTree.fit_lim(dl))), fa, ATE.ate.and_t(AgentTree.fit_lim(lim), Bool.and(LawsBase.wire_fits(sp), AgentTree.fit_lim(dl)), fl, ATE.ate.and_t(LawsBase.wire_fits(sp), AgentTree.fit_lim(dl), fs, f))))
    case Wr.Bad{}:
      Unit{}

def atx.help_spent(-s: String, +at: List<&2, T.Dir>, +st: T.Status, +lim: T.Lim, +sk: String, pre: {s == AgentTree.w_path(at, Wr.put_nat(AgentTree.status_tag(st), AgentTree.w_lim(lim, sk))) : String}, fa: {AgentTree.fit_path(at) == True{} : Bool}, fl: {AgentTree.fit_lim(lim) == True{} : Bool}, d: Wr.Dec<Nat>, np: atx.NP(sk, d)) -> atx.HlP(s, FAt.get_help.spent(at, st, lim, d)):
  match d:
    case Wr.Got{+sp, +r}:
      (e, f) = np
      atx.help_deadline(s, at, st, lim, sp, r, atx.ext(z => AgentTree.w_path(at, Wr.put_nat(AgentTree.status_tag(st), AgentTree.w_lim(lim, z))), s, sk, Wr.put_nat(sp, r), pre, e), fa, fl, f, FAt.get_lim(r), atx.lim(r))
    case Wr.Bad{}:
      Unit{}

def atx.help_limit(-s: String, +at: List<&2, T.Dir>, +st: T.Status, +sk: String, pre: {s == AgentTree.w_path(at, Wr.put_nat(AgentTree.status_tag(st), sk)) : String}, fa: {AgentTree.fit_path(at) == True{} : Bool}, d: Wr.Dec<T.Lim>, lp: atx.LmP(sk, d)) -> atx.HlP(s, FAt.get_help.limit(at, st, d)):
  match d:
    case Wr.Got{+lim, +r}:
      (e, f) = lp
      atx.help_spent(s, at, st, lim, r, atx.ext(z => AgentTree.w_path(at, Wr.put_nat(AgentTree.status_tag(st), z)), s, sk, AgentTree.w_lim(lim, r), pre, e), fa, f, Wr.get_nat(r), atx.nat(r))
    case Wr.Bad{}:
      Unit{}

def atx.help_status(-s: String, +at: List<&2, T.Dir>, +sk: String, pre: {s == AgentTree.w_path(at, sk) : String}, fa: {AgentTree.fit_path(at) == True{} : Bool}, d: Wr.Dec<T.Status>, sp: atx.SP(sk, d)) -> atx.HlP(s, FAt.get_help.status(at, d)):
  match d:
    case Wr.Got{+st, +r}:
      atx.help_limit(s, at, st, r, atx.ext(z => AgentTree.w_path(at, z), s, sk, Wr.put_nat(AgentTree.status_tag(st), r), pre, sp), fa, FAt.get_lim(r), atx.lim(r))
    case Wr.Bad{}:
      Unit{}

def atx.help_path(-s: String, d: Wr.Dec<List<&2, T.Dir>>, lp: atx.LP(s, d)) -> atx.HlP(s, FAt.get_help.at(d)):
  match d:
    case Wr.Got{+at, +r}:
      (e, f) = lp
      atx.help_status(s, at, r, e, f, FAt.get_status(r), atx.status(r))
    case Wr.Bad{}:
      Unit{}

def atx.help(+s: String) -> atx.HlP(s, FAt.get_help(s)):
  atx.help_path(s, FAt.get_path(s), atx.path(s))

def atx.HIP(s: String, k: Nat, d: Wr.Dec<List<&2, C.Help>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == AgentTree.w_helps.items(xs, r) : String} & ({List.length(&2, C.Help, xs) == k : Nat} & {AgentTree.fit_helps.items(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def atx.hl_at(+s: String, -d: Wr.Dec<C.Help>, ed: {FAt.get_help(s) == d : Wr.Dec<C.Help>}) -> atx.HlP(s, d):
  %ed : atx.HlP(s, _)
  atx.help(s)

def atx.hl_cons(-s: String, +c: C.Help, +r1: String, -k: Nat, d: Wr.Dec<List<&2, C.Help>>, ih: atx.HIP(r1, k, d), cp: atx.HlP(s, Wr.Got{c, r1})) -> atx.HIP(s, 1n+k, LawsBase.wire_items.cons(C.Help, c, d)):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, (e2, e3)) = ih
      (ec, fc) = cp
      (atx.ext(z => AgentTree.w_help(c, z), s, r1, AgentTree.w_helps.items(xs, r), ec, e1), (Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, C.Help, xs), k, e2), ATE.ate.and_t(AgentTree.fit_help(c), AgentTree.fit_helps.items(xs), fc, e3)))
    case Wr.Bad{}:
      Unit{}

def atx.hl_items(mm: Nat, cur: Wr.Dec<C.Help>, +s: String, er: {FAt.get_help(s) == cur : Wr.Dec<C.Help>}) -> atx.HIP(s, 1n+mm, LawsBase.wire_items.then(C.Help, cur, r => LawsBase.wire_items(~C.Help, ~FAt.get_help, mm, r))):
  match mm cur:
    case 0n Wr.Got{+c, +r1}:
      atx.hl_cons(s, c, r1, 0n, Wr.Got{Nil{}, r1}, ({==}, ({==}, {==})), atx.hl_at(s, Wr.Got{c, r1}, er))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+c, +r1}:
      atx.hl_cons(s, c, r1, 1n+k, LawsBase.wire_items.then(C.Help, FAt.get_help(r1), r => LawsBase.wire_items(~C.Help, ~FAt.get_help, k, r)), atx.hl_items(k, FAt.get_help(r1), r1, {==}), atx.hl_at(s, Wr.Got{c, r1}, er))
    case 1n++k Wr.Bad{}:
      Unit{}

def atx.hl_items_of(k: Nat, +s: String) -> atx.HIP(s, k, LawsBase.wire_items(~C.Help, ~FAt.get_help, k, s)):
  match k:
    case 0n:
      ({==}, ({==}, {==}))
    case 1n+mm:
      atx.hl_items(mm, FAt.get_help(s), s, {==})

def atx.LH(s: String, d: Wr.Dec<List<&2, C.Help>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == AgentTree.w_helps(xs, r) : String} & {AgentTree.fit_helps(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def atx.hl_list(-s: String, +k: Nat, +s1: String, en: {s == Wr.put_nat(k, s1) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<List<&2, C.Help>>, ip: atx.HIP(s1, k, d)) -> atx.LH(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, (e2, e3)) = ip
      +ln = e2
      +n = List.length(&2, C.Help, xs)
      +w = AgentTree.w_helps.items(xs, r)
      +es = atx.ext(z => Wr.put_nat(k, z), s, s1, w, en, e1)
      +el = Equal.cong(Nat, String, z => Wr.put_nat(z, w), k, n, Equal.sym(Nat, n, k, ln))
      +fl = Equal.trans(Bool, LawsBase.wire_fits(n), LawsBase.wire_fits(k), True{}, Equal.cong(Nat, Bool, z => LawsBase.wire_fits(z), n, k, ln), fk)
      (Equal.trans(String, s, Wr.put_nat(k, w), Wr.put_nat(n, w), es, el), ATE.ate.and_t(LawsBase.wire_fits(n), AgentTree.fit_helps.items(xs), fl, e3))
    case Wr.Bad{}:
      Unit{}

def atx.hl_count(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> atx.LH(s, LawsBase.wire_read_list.count(~C.Help, ~FAt.get_help, d)):
  match d:
    case Wr.Got{+k, +s1}:
      +e = ed
      atx.hl_list(s, k, s1, Wire.wire_nat_exact(s, k, s1, e), Wire.wire_nat_decoded_fits(s, k, s1, e), LawsBase.wire_items(~C.Help, ~FAt.get_help, k, s1), atx.hl_items_of(k, s1))
    case Wr.Bad{}:
      Unit{}

def atx.helps(+s: String) -> atx.LH(s, FAt.get_helps(s)):
  %Equal.sym(Wr.Dec<List<&2, C.Help>>, Wr.get_list(~C.Help, ~FAt.get_help, s), LawsBase.wire_read_list(~C.Help, ~FAt.get_help, s), Wire.wire_list_reads_items(~C.Help, ~FAt.get_help, s)) : atx.LH(s, _)
  atx.hl_count(s, Wr.get_nat(s), {==})

def atx.CrP(s: String, d: Wr.Dec<C.Crown>) -> Type:
  match d:
    case Wr.Got{c, r}:
      {s == AgentTree.w_crown(c, r) : String} & {AgentTree.fit_crown(c) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def atx.crown_helps(-s: String, +t: T.Node, +sk: String, pre: {s == AgentTree.w_node(t, sk) : String}, ft: {AgentTree.fit_node(t) == True{} : Bool}, d: Wr.Dec<List<&2, C.Help>>, lp: atx.LH(sk, d)) -> atx.CrP(s, FAt.get_crown.helps(t, d)):
  match d:
    case Wr.Got{+hs, +r}:
      (e, f) = lp
      (atx.ext(z => AgentTree.w_node(t, z), s, sk, AgentTree.w_helps(hs, r), pre, e), ATE.ate.and_t(AgentTree.fit_node(t), AgentTree.fit_helps(hs), ft, f))
    case Wr.Bad{}:
      Unit{}

def atx.crown_node(-s: String, d: Wr.Dec<T.Node>, np: atx.NdP(s, d)) -> atx.CrP(s, FAt.get_crown.node(d)):
  match d:
    case Wr.Got{+t, +r}:
      (e, f) = np
      atx.crown_helps(s, t, r, e, f, FAt.get_helps(r), atx.helps(r))
    case Wr.Bad{}:
      Unit{}

def atx.crown(+s: String) -> atx.CrP(s, FAt.get_crown(s)):
  atx.crown_node(s, FAt.get_node(s), atx.node(s))

def atx.CvP(s: String, d: Wr.Dec<C.CEv>) -> Type:
  match d:
    case Wr.Got{e, r}:
      {s == AgentTree.w_cev(e, r) : String} & {AgentTree.fit_cev(e) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def atx.cev_on(-s: String, +s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<T.Ev>, ep: atx.EP(s1, d)) -> atx.CvP(s, FAt.get_cev.on(d)):
  match d:
    case Wr.Got{+x, +r}:
      (e, f) = ep
      (atx.ext(z => Wr.put_nat(0n, z), s, s1, AgentTree.w_ev(x, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def atx.cev_help_n(-s: String, +at: List<&2, T.Dir>, +sk: String, pre: {s == Wr.put_nat(1n, AgentTree.w_path(at, sk)) : String}, fa: {AgentTree.fit_path(at) == True{} : Bool}, d: Wr.Dec<Nat>, np: atx.NP(sk, d)) -> atx.CvP(s, FAt.get_cev.help_n(at, d)):
  match d:
    case Wr.Got{+n, +r}:
      (e, f) = np
      (atx.ext(z => Wr.put_nat(1n, AgentTree.w_path(at, z)), s, sk, Wr.put_nat(n, r), pre, e), ATE.ate.and_t(AgentTree.fit_path(at), LawsBase.wire_fits(n), fa, f))
    case Wr.Bad{}:
      Unit{}

def atx.cev_help_at(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<List<&2, T.Dir>>, lp: atx.LP(s1, d)) -> atx.CvP(s, FAt.get_cev.help_at(d)):
  match d:
    case Wr.Got{+at, +r}:
      (e, f) = lp
      atx.cev_help_n(s, at, r, atx.ext(z => Wr.put_nat(1n, z), s, s1, AgentTree.w_path(at, r), pre, e), f, Wr.get_nat(r), atx.nat(r))
    case Wr.Bad{}:
      Unit{}

def atx.cev_spend_n(-s: String, +k: Nat, +sk: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(k, sk)) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<Nat>, np: atx.NP(sk, d)) -> atx.CvP(s, FAt.get_cev.spend_n(k, d)):
  match d:
    case Wr.Got{+n, +r}:
      (e, f) = np
      (atx.ext(z => Wr.put_nat(2n, Wr.put_nat(k, z)), s, sk, Wr.put_nat(n, r), pre, e), ATE.ate.and_t(LawsBase.wire_fits(k), LawsBase.wire_fits(n), fk, f))
    case Wr.Bad{}:
      Unit{}

def atx.cev_spend_k(-s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Nat>, np: atx.NP(s1, d)) -> atx.CvP(s, FAt.get_cev.spend_k(d)):
  match d:
    case Wr.Got{+k, +r}:
      (e, f) = np
      atx.cev_spend_n(s, k, r, atx.ext(z => Wr.put_nat(2n, z), s, s1, Wr.put_nat(k, r), pre, e), f, Wr.get_nat(r), atx.nat(r))
    case Wr.Bad{}:
      Unit{}

def atx.cev_end_ok(-s: String, +k: Nat, +sk: String, pre: {s == Wr.put_nat(3n, Wr.put_nat(k, sk)) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<Bool>, bp: atx.BP(sk, d)) -> atx.CvP(s, FAt.get_cev.end_ok(k, d)):
  match d:
    case Wr.Got{+ok, +r}:
      (atx.ext(z => Wr.put_nat(3n, Wr.put_nat(k, z)), s, sk, Wr.put_bool(ok, r), pre, bp), fk)
    case Wr.Bad{}:
      Unit{}

def atx.cev_end_k(-s: String, +s1: String, pre: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<Nat>, np: atx.NP(s1, d)) -> atx.CvP(s, FAt.get_cev.end_k(d)):
  match d:
    case Wr.Got{+k, +r}:
      (e, f) = np
      atx.cev_end_ok(s, k, r, atx.ext(z => Wr.put_nat(3n, z), s, s1, Wr.put_nat(k, r), pre, e), f, Wr.get_bool(r), atx.bool(r))
    case Wr.Bad{}:
      Unit{}

def atx.cev_of(t: Nat, -s: String, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> atx.CvP(s, FAt.get_cev.of(t, s1)):
  match t:
    case 0n:
      atx.cev_on(s, s1, pre, FAt.get_ev(s1), atx.ev(s1))
    case 1n+a:
      match a:
        case 0n:
          atx.cev_help_at(s, s1, pre, FAt.get_path(s1), atx.path(s1))
        case 1n+b:
          match b:
            case 0n:
              atx.cev_spend_k(s, s1, pre, Wr.get_nat(s1), atx.nat(s1))
            case 1n+c:
              match c:
                case 0n:
                  atx.cev_end_k(s, s1, pre, Wr.get_nat(s1), atx.nat(s1))
                case 1n+d:
                  Unit{}

def atx.cev_tag(-s: String, d: Wr.Dec<Nat>, np: atx.NP(s, d)) -> atx.CvP(s, FAt.get_cev.tag(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = np
      atx.cev_of(t, s, s1, e)
    case Wr.Bad{}:
      Unit{}

def atx.cev(+s: String) -> atx.CvP(s, FAt.get_cev(s)):
  atx.cev_tag(s, Wr.get_nat(s), atx.nat(s))

# The request
# -----------

# what the request reader's answer says about its input s
def atx.QP(s: String, d: Wr.Dec<FAt.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == AgentTree.w_req(q, r) : String} & {AgentTree.fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def atx.step_ev(-s: String, +b: T.Bounds, +c: C.Crown, +sk: String, pre: {s == Wr.put_nat(0n, AgentTree.w_bounds(b, AgentTree.w_crown(c, sk))) : String}, fb: {AgentTree.fit_bounds(b) == True{} : Bool}, fc: {AgentTree.fit_crown(c) == True{} : Bool}, d: Wr.Dec<C.CEv>, ep: atx.CvP(sk, d)) -> atx.QP(s, FAt.get_req.step_ev(b, c, d)):
  match d:
    case Wr.Got{+ev, +r}:
      (e, f) = ep
      (atx.ext(z => Wr.put_nat(0n, AgentTree.w_bounds(b, AgentTree.w_crown(c, z))), s, sk, AgentTree.w_cev(ev, r), pre, e), ATE.ate.and_t(AgentTree.fit_bounds(b), Bool.and(AgentTree.fit_crown(c), AgentTree.fit_cev(ev)), fb, ATE.ate.and_t(AgentTree.fit_crown(c), AgentTree.fit_cev(ev), fc, f)))
    case Wr.Bad{}:
      Unit{}

def atx.step_crown(-s: String, +b: T.Bounds, +sk: String, pre: {s == Wr.put_nat(0n, AgentTree.w_bounds(b, sk)) : String}, fb: {AgentTree.fit_bounds(b) == True{} : Bool}, d: Wr.Dec<C.Crown>, cp: atx.CrP(sk, d)) -> atx.QP(s, FAt.get_req.step_crown(b, d)):
  match d:
    case Wr.Got{+c, +r}:
      (e, f) = cp
      atx.step_ev(s, b, c, r, atx.ext(z => Wr.put_nat(0n, AgentTree.w_bounds(b, z)), s, sk, AgentTree.w_crown(c, r), pre, e), fb, f, FAt.get_cev(r), atx.cev(r))
    case Wr.Bad{}:
      Unit{}

def atx.step(-s: String, +s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<T.Bounds>, bp: atx.BdP(s1, d)) -> atx.QP(s, FAt.get_req.step(d)):
  match d:
    case Wr.Got{+b, +r}:
      (e, f) = bp
      atx.step_crown(s, b, r, atx.ext(z => Wr.put_nat(0n, z), s, s1, AgentTree.w_bounds(b, r), pre, e), f, FAt.get_crown(r), atx.crown(r))
    case Wr.Bad{}:
      Unit{}

def atx.overlay_s(-s: String, +cur: List<&2, Maybe<&2, Nat>>, +a: List<&2, Maybe<&2, Nat>>, +sk: String, pre: {s == Wr.put_nat(1n, AgentTree.w_patch(cur, AgentTree.w_patch(a, sk))) : String}, fc: {AgentTree.fit_patch(cur) == True{} : Bool}, fa: {AgentTree.fit_patch(a) == True{} : Bool}, d: Wr.Dec<List<&2, Bool>>, lp: atx.LB(sk, d)) -> atx.QP(s, FAt.get_req.overlay_s(cur, a, d)):
  match d:
    case Wr.Got{+sc, +r}:
      (e, f) = lp
      (atx.ext(z => Wr.put_nat(1n, AgentTree.w_patch(cur, AgentTree.w_patch(a, z))), s, sk, AgentTree.w_bools(sc, r), pre, e), ATE.ate.and_t(AgentTree.fit_patch(cur), Bool.and(AgentTree.fit_patch(a), AgentTree.fit_bools(sc)), fc, ATE.ate.and_t(AgentTree.fit_patch(a), AgentTree.fit_bools(sc), fa, f)))
    case Wr.Bad{}:
      Unit{}

def atx.overlay_a(-s: String, +cur: List<&2, Maybe<&2, Nat>>, +sk: String, pre: {s == Wr.put_nat(1n, AgentTree.w_patch(cur, sk)) : String}, fc: {AgentTree.fit_patch(cur) == True{} : Bool}, d: Wr.Dec<List<&2, Maybe<&2, Nat>>>, lp: atx.LM(sk, d)) -> atx.QP(s, FAt.get_req.overlay_a(cur, d)):
  match d:
    case Wr.Got{+a, +r}:
      (e, f) = lp
      atx.overlay_s(s, cur, a, r, atx.ext(z => Wr.put_nat(1n, AgentTree.w_patch(cur, z)), s, sk, AgentTree.w_patch(a, r), pre, e), fc, f, FAt.get_bools(r), atx.bools(r))
    case Wr.Bad{}:
      Unit{}

def atx.overlay(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<List<&2, Maybe<&2, Nat>>>, lp: atx.LM(s1, d)) -> atx.QP(s, FAt.get_req.overlay(d)):
  match d:
    case Wr.Got{+cur, +r}:
      (e, f) = lp
      atx.overlay_a(s, cur, r, atx.ext(z => Wr.put_nat(1n, z), s, s1, AgentTree.w_patch(cur, r), pre, e), f, FAt.get_patch(r), atx.patch(r))
    case Wr.Bad{}:
      Unit{}

def atx.next(-s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<T.View>, vp: atx.VP(s1, d)) -> atx.QP(s, FAt.get_req.next(d)):
  match d:
    case Wr.Got{+v, +r}:
      (e, f) = vp
      (atx.ext(z => Wr.put_nat(2n, z), s, s1, AgentTree.w_view(v, r), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def atx.free_path(-s: String, +c: C.Crown, +sk: String, pre: {s == Wr.put_nat(3n, AgentTree.w_crown(c, sk)) : String}, fc: {AgentTree.fit_crown(c) == True{} : Bool}, d: Wr.Dec<List<&2, T.Dir>>, lp: atx.LP(sk, d)) -> atx.QP(s, FAt.get_req.free_path(c, d)):
  match d:
    case Wr.Got{+p, +r}:
      (e, f) = lp
      (atx.ext(z => Wr.put_nat(3n, AgentTree.w_crown(c, z)), s, sk, AgentTree.w_path(p, r), pre, e), ATE.ate.and_t(AgentTree.fit_crown(c), AgentTree.fit_path(p), fc, f))
    case Wr.Bad{}:
      Unit{}

def atx.free(-s: String, +s1: String, pre: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<C.Crown>, cp: atx.CrP(s1, d)) -> atx.QP(s, FAt.get_req.free(d)):
  match d:
    case Wr.Got{+c, +r}:
      (e, f) = cp
      atx.free_path(s, c, r, atx.ext(z => Wr.put_nat(3n, z), s, s1, AgentTree.w_crown(c, r), pre, e), f, FAt.get_path(r), atx.path(r))
    case Wr.Bad{}:
      Unit{}

def atx.req_of(t: Nat, -s: String, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> atx.QP(s, FAt.get_req.of(t, s1)):
  match t:
    case 0n:
      atx.step(s, s1, pre, FAt.get_bounds(s1), atx.bounds(s1))
    case 1n+a:
      match a:
        case 0n:
          atx.overlay(s, s1, pre, FAt.get_patch(s1), atx.patch(s1))
        case 1n+b:
          match b:
            case 0n:
              atx.next(s, s1, pre, FAt.get_view(s1), atx.view(s1))
            case 1n+c:
              match c:
                case 0n:
                  atx.free(s, s1, pre, FAt.get_crown(s1), atx.crown(s1))
                case 1n+d:
                  Unit{}

def atx.req_tag(-s: String, d: Wr.Dec<Nat>, np: atx.NP(s, d)) -> atx.QP(s, FAt.get_req.tag(d)):
  match d:
    case Wr.Got{+t, +s1}:
      (e, f) = np
      atx.req_of(t, s, s1, e)
    case Wr.Bad{}:
      Unit{}

# the request reader accepts only spelled requests that fit
def atx.req(+s: String) -> atx.QP(s, FAt.get_req(s)):
  atx.req_tag(s, Wr.get_nat(s), atx.nat(s))
