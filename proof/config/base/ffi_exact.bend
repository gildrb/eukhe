# eukhe: lemmas the proofs of the config entry share (bend/ffi_config.bend):
# what the reader of spec/settings/config.bend reads is spelled: an input
# it reads whole is a request as the laws' speller writes it. Each field
# read is its wire spelling (Wire.wire_nat_exact, Wire.wire_str_exact,
# Wire.wire_list_exact); a list of items read is its count, then each
# item's spelling (pxe.list, by induction on the items).

import Base
import ../../../bend/config.bend as Cf
import ../../../bend/ffi_config.bend as FC
import ../../../bend/wire.bend as Wr
import ../../../spec/settings/config.bend as CS
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../base/logic/logic.bend as LLogicLogic
import ./ffi_spell.bend as LFS

# Lists
# -----

# what a decoder's answer d at s says: s is the item read, spelled by
# put, then the rest
def pxe.I(~A: Data, ~put: A -> String -> String, s: String, d: Wr.Dec<A>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == put(x, r) : String}
    case Wr.Bad{}:
      Unit

# what the item loop's answer says about its input s (m + 1 items)
def pxe.L(~A: Data, ~put: A -> String -> String, s: String, m: Nat, d: Wr.Dec<List<&2, A>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == LawsBase.wire_put_items(~A, ~put, xs, r) : String} & {List.length(&2, A, xs) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def pxe.step(~A: Data, ~put: A -> String -> String, -s: String, +x: A, +s3: String, -k: Nat, ex: {s == put(x, s3) : String},
  d: Wr.Dec<List<&2, A>>, ih: pxe.L(~A, ~put, s3, k, d)) -> pxe.L(~A, ~put, s, 1n+k, Wr.get_list.cons(A, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e2) = ih
      (Equal.trans(String, s, put(x, s3), put(x, LawsBase.wire_put_items(~A, ~put, ys, r)), ex,
          Equal.cong(String, String, z => put(x, z), s3, LawsBase.wire_put_items(~A, ~put, ys, r), e1)),
        Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, A, ys), 1n+k, e2))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only items that are spellings
def pxe.loop(~A: Data, ~get: String -> Wr.Dec<A>, ~put: A -> String -> String, ~h: @+s: String -> pxe.I(~A, ~put, s, get(s)),
  m: Nat, cur: Wr.Dec<A>, +s: String, pc: pxe.I(~A, ~put, s, cur)) -> pxe.L(~A, ~put, s, m, Wr.get_list.go(~A, ~get, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (pc, {==})
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      pxe.step(~A, ~put, s, x, s3, k, pc, Wr.get_list.go(~A, ~get, k, get(s3)), pxe.loop(~A, ~get, ~put, ~h, k, get(s3), s3, h(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder's answer says about its input s
def pxe.LS(~A: Data, ~put: A -> String -> String, s: String, d: Wr.Dec<List<&2, A>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == Wr.put_nat(List.length(&2, A, xs), LawsBase.wire_put_items(~A, ~put, xs, r)) : String}
    case Wr.Bad{}:
      Unit

def pxe.conv(~A: Data, ~put: A -> String -> String, +s: String, +s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String},
  d: Wr.Dec<List<&2, A>>, pl: pxe.L(~A, ~put, s2, m, d)) -> pxe.LS(~A, ~put, s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e2) = pl
      %Equal.sym(Nat, List.length(&2, A, xs), 1n+m, e2) : {s == Wr.put_nat(_, LawsBase.wire_put_items(~A, ~put, xs, r)) : String}
      %e1 : {s == Wr.put_nat(1n+m, _) : String}
      en
    case Wr.Bad{}:
      Unit{}

def pxe.nat(~A: Data, ~get: String -> Wr.Dec<A>, ~put: A -> String -> String, ~h: @+s: String -> pxe.I(~A, ~put, s, get(s)),
  +s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}) -> pxe.LS(~A, ~put, s, Wr.get_list.start(~A, ~get, Wr.Got{n, s2})):
  match n:
    case 0n:
      en
    case 1n++m:
      pxe.conv(~A, ~put, s, s2, m, en, Wr.get_list.go(~A, ~get, m, get(s2)), pxe.loop(~A, ~get, ~put, ~h, m, get(s2), s2, h(s2)))

def pxe.top(~A: Data, ~get: String -> Wr.Dec<A>, ~put: A -> String -> String, ~h: @+s: String -> pxe.I(~A, ~put, s, get(s)),
  +s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> pxe.LS(~A, ~put, s, Wr.get_list.start(~A, ~get, r)):
  match r:
    case Wr.Got{+n, +s2}:
      pxe.nat(~A, ~get, ~put, ~h, s, n, s2, Wire.wire_nat_exact(s, n, s2, er))
    case Wr.Bad{}:
      Unit{}

# a list read is its count, then the spelling of each item
def pxe.list(~A: Data, ~get: String -> Wr.Dec<A>, ~put: A -> String -> String, ~h: @+s: String -> pxe.I(~A, ~put, s, get(s)), +s: String) ->
  pxe.LS(~A, ~put, s, Wr.get_list(~A, ~get, s)):
  pxe.top(~A, ~get, ~put, ~h, s, Wr.get_nat(s), {==})

# Fields
# ------

def pxe.str.d(+s: String, d: Wr.Dec<String>, ed: {Wr.get_str(s) == d : Wr.Dec<String>}) -> pxe.I(~String, ~Wr.put_str, s, d):
  match d:
    case Wr.Got{+a, +r}:
      Wire.wire_str_exact(s, a, r, ed)
    case Wr.Bad{}:
      Unit{}

def pxe.str(+s: String) -> pxe.I(~String, ~Wr.put_str, s, Wr.get_str(s)):
  pxe.str.d(s, Wr.get_str(s), {==})

def pxe.ss_items(xs: List<&2, String>, -r: String) -> {LawsBase.wire_put_items(~String, ~Wr.put_str, xs, r) == LFS.pfs.ss_items(xs, r) : String}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      %pxe.ss_items(t, r) : {Wr.put_str(x, LawsBase.wire_put_items(~String, ~Wr.put_str, t, r)) == Wr.put_str(x, _) : String}
      {==}

# a path read is the list of its names
def pxe.path(+s1: String, +p: List<&2, String>, +s2: String, h: pxe.LS(~String, ~Wr.put_str, s1, Wr.Got{p, s2})) -> {s1 == Wr.put_list(~String, ~Wr.put_str, p, s2) : String}:
  %LFS.pfs.ss_put(p, s2) : {s1 == _ : String}
  %pxe.ss_items(p, s2) : {s1 == Wr.put_nat(List.length(&2, String, p), _) : String}
  h

# an entry read is its key, then its value
def pxe.entry.v(+s: String, +k: Nat, +s1: String, ek: {s == Wr.put_nat(k, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> pxe.I(~Cf.Entry, ~CS.cf_w_entry, s, CS.cf_r_entry.v(k, d)):
  match d:
    case Wr.Got{+v, +r}:
      %Wire.wire_nat_exact(s1, v, r, ed) : {s == Wr.put_nat(k, _) : String}
      ek
    case Wr.Bad{}:
      Unit{}

def pxe.entry.k(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> pxe.I(~Cf.Entry, ~CS.cf_w_entry, s, CS.cf_r_entry.k(d)):
  match d:
    case Wr.Got{+k, +s1}:
      pxe.entry.v(s, k, s1, Wire.wire_nat_exact(s, k, s1, ed), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

def pxe.entry(+s: String) -> pxe.I(~Cf.Entry, ~CS.cf_w_entry, s, CS.cf_r_entry(s)):
  pxe.entry.k(s, Wr.get_nat(s), {==})

def pxe.entries_items(d: List<&2, Cf.Entry>, -r: String) -> {LawsBase.wire_put_items(~Cf.Entry, ~CS.cf_w_entry, d, r) == CS.cf_w_entries.items(d, r) : String}:
  match d:
    case Nil{}:
      {==}
    case +e <> t:
      %pxe.entries_items(t, r) : {CS.cf_w_entry(e, LawsBase.wire_put_items(~Cf.Entry, ~CS.cf_w_entry, t, r)) == CS.cf_w_entry(e, _) : String}
      {==}

def pxe.Ents(s: String, d: Wr.Dec<List<&2, Cf.Entry>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == CS.cf_w_entries(xs, r) : String}
    case Wr.Bad{}:
      Unit

def pxe.ents.of(+s: String, d: Wr.Dec<List<&2, Cf.Entry>>, h: pxe.LS(~Cf.Entry, ~CS.cf_w_entry, s, d)) -> pxe.Ents(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      %pxe.entries_items(xs, r) : {s == Wr.put_nat(List.length(&2, Cf.Entry, xs), _) : String}
      h
    case Wr.Bad{}:
      Unit{}

# a list of entries read is its count, then each entry
def pxe.entries(+s: String) -> pxe.Ents(s, CS.cf_r_entries(s)):
  pxe.ents.of(s, CS.cf_r_entries(s), pxe.list(~Cf.Entry, ~CS.cf_r_entry, ~CS.cf_w_entry, ~pxe.entry, s))

# a leaf read is its path, then its outcome's tag
def pxe.leaf.tag(+s: String, +p: Nat, +s1: String, ep: {s == Wr.put_nat(p, s1) : String}, t: Nat, +s2: String, et: {s1 == Wr.put_nat(t, s2) : String}) -> pxe.I(~Cf.Leaf, ~CS.cf_w_leaf, s, CS.cf_r_leaf.tag(p, t, s2)):
  match t:
    case 0n:
      %et : {s == Wr.put_nat(p, _) : String}
      ep
    case 1n:
      %et : {s == Wr.put_nat(p, _) : String}
      ep
    case 2n:
      %et : {s == Wr.put_nat(p, _) : String}
      ep
    case 3n+q:
      Unit{}

def pxe.leaf.o(+s: String, +p: Nat, +s1: String, ep: {s == Wr.put_nat(p, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> pxe.I(~Cf.Leaf, ~CS.cf_w_leaf, s, CS.cf_r_leaf.o(p, d)):
  match d:
    case Wr.Got{+t, +s2}:
      pxe.leaf.tag(s, p, s1, ep, t, s2, Wire.wire_nat_exact(s1, t, s2, ed))
    case Wr.Bad{}:
      Unit{}

def pxe.leaf.p(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> pxe.I(~Cf.Leaf, ~CS.cf_w_leaf, s, CS.cf_r_leaf.p(d)):
  match d:
    case Wr.Got{+p, +s1}:
      pxe.leaf.o(s, p, s1, Wire.wire_nat_exact(s, p, s1, ed), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

def pxe.leaf(+s: String) -> pxe.I(~Cf.Leaf, ~CS.cf_w_leaf, s, CS.cf_r_leaf(s)):
  pxe.leaf.p(s, Wr.get_nat(s), {==})

def pxe.leaves_items(ls: List<&2, Cf.Leaf>, -r: String) -> {LawsBase.wire_put_items(~Cf.Leaf, ~CS.cf_w_leaf, ls, r) == CS.cf_w_leaves(ls, r) : String}:
  match ls:
    case Nil{}:
      {==}
    case +l <> t:
      %pxe.leaves_items(t, r) : {CS.cf_w_leaf(l, LawsBase.wire_put_items(~Cf.Leaf, ~CS.cf_w_leaf, t, r)) == CS.cf_w_leaf(l, _) : String}
      {==}

# a slot read is its provider, then its value's tag (and a whole number)
def pxe.slot.num(+s: String, +p: Nat, +s1: String, ep: {s == Wr.put_nat(p, s1) : String}, +s2: String, et: {s1 == Wr.put_nat(0n, s2) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> pxe.I(~Cf.Slot, ~CS.cf_w_slot, s, CS.cf_r_slot.num(p, d)):
  match d:
    case Wr.Got{+n, +s3}:
      %Wire.wire_nat_exact(s2, n, s3, ed) : {s == Wr.put_nat(p, Wr.put_nat(0n, _)) : String}
      %et : {s == Wr.put_nat(p, _) : String}
      ep
    case Wr.Bad{}:
      Unit{}

def pxe.slot.tag(+s: String, +p: Nat, +s1: String, ep: {s == Wr.put_nat(p, s1) : String}, t: Nat, +s2: String, et: {s1 == Wr.put_nat(t, s2) : String}) -> pxe.I(~Cf.Slot, ~CS.cf_w_slot, s, CS.cf_r_slot.tag(p, t, s2)):
  match t:
    case 0n:
      pxe.slot.num(s, p, s1, ep, s2, et, Wr.get_nat(s2), {==})
    case 1n:
      %et : {s == Wr.put_nat(p, _) : String}
      ep
    case 2n+q:
      Unit{}

def pxe.slot.v(+s: String, +p: Nat, +s1: String, ep: {s == Wr.put_nat(p, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> pxe.I(~Cf.Slot, ~CS.cf_w_slot, s, CS.cf_r_slot.v(p, d)):
  match d:
    case Wr.Got{+t, +s2}:
      pxe.slot.tag(s, p, s1, ep, t, s2, Wire.wire_nat_exact(s1, t, s2, ed))
    case Wr.Bad{}:
      Unit{}

def pxe.slot.p(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> pxe.I(~Cf.Slot, ~CS.cf_w_slot, s, CS.cf_r_slot.p(d)):
  match d:
    case Wr.Got{+p, +s1}:
      pxe.slot.v(s, p, s1, Wire.wire_nat_exact(s, p, s1, ed), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

def pxe.slot(+s: String) -> pxe.I(~Cf.Slot, ~CS.cf_w_slot, s, CS.cf_r_slot(s)):
  pxe.slot.p(s, Wr.get_nat(s), {==})

def pxe.slots_items(xs: List<&2, Cf.Slot>, -r: String) -> {LawsBase.wire_put_items(~Cf.Slot, ~CS.cf_w_slot, xs, r) == CS.cf_w_slots(xs, r) : String}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      %pxe.slots_items(t, r) : {CS.cf_w_slot(x, LawsBase.wire_put_items(~Cf.Slot, ~CS.cf_w_slot, t, r)) == CS.cf_w_slot(x, _) : String}
      {==}

# a key of a project read is its place, its path, then its value
def pxe.pkey.v(+s: String, +k: Nat, +s1: String, ek: {s == Wr.put_nat(k, s1) : String}, +p: List<&2, String>, +s2: String, epp: {s1 == Wr.put_list(~String, ~Wr.put_str, p, s2) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> pxe.I(~Cf.PKey, ~CS.cf_w_pkey, s, CS.cf_r_pkey.v(k, p, d)):
  match d:
    case Wr.Got{+v, +s3}:
      %Wire.wire_nat_exact(s2, v, s3, ed) : {s == Wr.put_nat(k, Wr.put_list(~String, ~Wr.put_str, p, _)) : String}
      %epp : {s == Wr.put_nat(k, _) : String}
      ek
    case Wr.Bad{}:
      Unit{}

def pxe.pkey.p(+s: String, +k: Nat, +s1: String, ek: {s == Wr.put_nat(k, s1) : String}, d: Wr.Dec<List<&2, String>>, h: pxe.LS(~String, ~Wr.put_str, s1, d)) -> pxe.I(~Cf.PKey, ~CS.cf_w_pkey, s, CS.cf_r_pkey.p(k, d)):
  match d:
    case Wr.Got{+p, +s2}:
      pxe.pkey.v(s, k, s1, ek, p, s2, pxe.path(s1, p, s2, h), Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def pxe.pkey.k(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> pxe.I(~Cf.PKey, ~CS.cf_w_pkey, s, CS.cf_r_pkey.k(d)):
  match d:
    case Wr.Got{+k, +s1}:
      pxe.pkey.p(s, k, s1, Wire.wire_nat_exact(s, k, s1, ed), Wr.get_list(~String, ~Wr.get_str, s1), pxe.list(~String, ~Wr.get_str, ~Wr.put_str, ~pxe.str, s1))
    case Wr.Bad{}:
      Unit{}

def pxe.pkey(+s: String) -> pxe.I(~Cf.PKey, ~CS.cf_w_pkey, s, CS.cf_r_pkey(s)):
  pxe.pkey.k(s, Wr.get_nat(s), {==})

def pxe.pkeys_items(xs: List<&2, Cf.PKey>, -r: String) -> {LawsBase.wire_put_items(~Cf.PKey, ~CS.cf_w_pkey, xs, r) == CS.cf_w_pkeys(xs, r) : String}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      %pxe.pkeys_items(t, r) : {CS.cf_w_pkey(x, LawsBase.wire_put_items(~Cf.PKey, ~CS.cf_w_pkey, t, r)) == CS.cf_w_pkey(x, _) : String}
      {==}

# a named entry read is its name, then its entries
def pxe.named.fs(+s: String, +n: Nat, +s1: String, en: {s == Wr.put_nat(n, s1) : String}, d: Wr.Dec<List<&2, Cf.Entry>>, h: pxe.Ents(s1, d)) -> pxe.I(~Cf.Named, ~CS.cf_w_named, s, CS.cf_r_named.fs(n, d)):
  match d:
    case Wr.Got{+fs, +r}:
      %h : {s == Wr.put_nat(n, _) : String}
      en
    case Wr.Bad{}:
      Unit{}

def pxe.named.n(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> pxe.I(~Cf.Named, ~CS.cf_w_named, s, CS.cf_r_named.n(d)):
  match d:
    case Wr.Got{+n, +s1}:
      pxe.named.fs(s, n, s1, Wire.wire_nat_exact(s, n, s1, ed), CS.cf_r_entries(s1), pxe.entries(s1))
    case Wr.Bad{}:
      Unit{}

def pxe.named(+s: String) -> pxe.I(~Cf.Named, ~CS.cf_w_named, s, CS.cf_r_named(s)):
  pxe.named.n(s, Wr.get_nat(s), {==})

def pxe.nameds_items(xs: List<&2, Cf.Named>, -r: String) -> {LawsBase.wire_put_items(~Cf.Named, ~CS.cf_w_named, xs, r) == CS.cf_w_nameds(xs, r) : String}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      %pxe.nameds_items(t, r) : {CS.cf_w_named(x, LawsBase.wire_put_items(~Cf.Named, ~CS.cf_w_named, t, r)) == CS.cf_w_named(x, _) : String}
      {==}

def pxe.Nds(s: String, d: Wr.Dec<List<&2, Cf.Named>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == Wr.put_nat(List.length(&2, Cf.Named, xs), CS.cf_w_nameds(xs, r)) : String}
    case Wr.Bad{}:
      Unit

def pxe.nds.of(+s: String, d: Wr.Dec<List<&2, Cf.Named>>, h: pxe.LS(~Cf.Named, ~CS.cf_w_named, s, d)) -> pxe.Nds(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      %pxe.nameds_items(xs, r) : {s == Wr.put_nat(List.length(&2, Cf.Named, xs), _) : String}
      h
    case Wr.Bad{}:
      Unit{}

# a list of named entries read is its count, then each entry
def pxe.nameds(+s: String) -> pxe.Nds(s, CS.cf_r_nameds(s)):
  pxe.nds.of(s, CS.cf_r_nameds(s), pxe.list(~Cf.Named, ~CS.cf_r_named, ~CS.cf_w_named, ~pxe.named, s))

# a read of a document read
def pxe.Rd(s: String, d: Wr.Dec<Cf.Read>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == CS.cf_w_read(x, r) : String}
    case Wr.Bad{}:
      Unit

def pxe.read.parsed(+s: String, +s1: String, es: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<List<&2, Cf.Entry>>, h: pxe.Ents(s1, d)) -> pxe.Rd(s, CS.cf_r_read.parsed(d)):
  match d:
    case Wr.Got{+xs, +r}:
      %h : {s == Wr.put_nat(1n, _) : String}
      es
    case Wr.Bad{}:
      Unit{}

def pxe.read.tag(+s: String, t: Nat, +s1: String, es: {s == Wr.put_nat(t, s1) : String}) -> pxe.Rd(s, CS.cf_r_read.tag(t, s1)):
  match t:
    case 0n:
      es
    case 1n:
      pxe.read.parsed(s, s1, es, CS.cf_r_entries(s1), pxe.entries(s1))
    case 2n:
      es
    case 3n+p:
      Unit{}

def pxe.read(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> pxe.Rd(s, CS.cf_r_read(d)):
  match d:
    case Wr.Got{+t, +s1}:
      pxe.read.tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, ed))
    case Wr.Bad{}:
      Unit{}

# an edit, then rest
def pxe.w_edit(e: Cf.Edit, rest: String) -> String:
  match e:
    case Cf.Set{k, v}:
      Wr.put_nat(0n, Wr.put_nat(k, Wr.put_nat(v, rest)))
    case Cf.Del{k}:
      Wr.put_nat(1n, Wr.put_nat(k, rest))

def pxe.Ed(s: String, d: Wr.Dec<Cf.Edit>) -> Type:
  match d:
    case Wr.Got{e, r}:
      {s == pxe.w_edit(e, r) : String}
    case Wr.Bad{}:
      Unit

def pxe.edit.set(+s: String, +s1: String, es: {s == Wr.put_nat(0n, s1) : String}, +k: Nat, +s2: String, ek: {s1 == Wr.put_nat(k, s2) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> pxe.Ed(s, CS.cf_r_edit.set(k, d)):
  match d:
    case Wr.Got{+v, +r}:
      %Wire.wire_nat_exact(s2, v, r, ed) : {s == Wr.put_nat(0n, Wr.put_nat(k, _)) : String}
      %ek : {s == Wr.put_nat(0n, _) : String}
      es
    case Wr.Bad{}:
      Unit{}

def pxe.edit.setk(+s: String, +s1: String, es: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> pxe.Ed(s, CS.cf_r_edit.setk(d)):
  match d:
    case Wr.Got{+k, +s2}:
      pxe.edit.set(s, s1, es, k, s2, Wire.wire_nat_exact(s1, k, s2, ed), Wr.get_nat(s2), {==})
    case Wr.Bad{}:
      Unit{}

def pxe.edit.del(+s: String, +s1: String, es: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> pxe.Ed(s, CS.cf_r_edit.del(d)):
  match d:
    case Wr.Got{+k, +r}:
      %Wire.wire_nat_exact(s1, k, r, ed) : {s == Wr.put_nat(1n, _) : String}
      es
    case Wr.Bad{}:
      Unit{}

def pxe.edit.tag(+s: String, t: Nat, +s1: String, es: {s == Wr.put_nat(t, s1) : String}) -> pxe.Ed(s, CS.cf_r_edit.tag(t, s1)):
  match t:
    case 0n:
      pxe.edit.setk(s, s1, es, Wr.get_nat(s1), {==})
    case 1n:
      pxe.edit.del(s, s1, es, Wr.get_nat(s1), {==})
    case 2n+p:
      Unit{}

def pxe.edit(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> pxe.Ed(s, CS.cf_r_edit(d)):
  match d:
    case Wr.Got{+t, +s1}:
      pxe.edit.tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, ed))
    case Wr.Bad{}:
      Unit{}

# the in-flight limits read
def pxe.Inf(s: String, d: Wr.Dec<Cf.InFlight>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == CS.cf_w_inflight(x, r) : String}
    case Wr.Bad{}:
      Unit

def pxe.inf.map(+s: String, +s1: String, es: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<List<&2, Cf.Slot>>, h: pxe.LS(~Cf.Slot, ~CS.cf_w_slot, s1, d)) -> pxe.Inf(s, CS.cf_r_inflight.map(d)):
  match d:
    case Wr.Got{+xs, +r}:
      %pxe.slots_items(xs, r) : {s == Wr.put_nat(1n, Wr.put_nat(List.length(&2, Cf.Slot, xs), _)) : String}
      %h : {s == Wr.put_nat(1n, _) : String}
      es
    case Wr.Bad{}:
      Unit{}

def pxe.inf.tag(+s: String, t: Nat, +s1: String, es: {s == Wr.put_nat(t, s1) : String}) -> pxe.Inf(s, CS.cf_r_inflight.tag(t, s1)):
  match t:
    case 0n:
      es
    case 1n:
      pxe.inf.map(s, s1, es, Wr.get_list(~Cf.Slot, ~CS.cf_r_slot, s1), pxe.list(~Cf.Slot, ~CS.cf_r_slot, ~CS.cf_w_slot, ~pxe.slot, s1))
    case 2n:
      es
    case 3n+p:
      Unit{}

def pxe.inf(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> pxe.Inf(s, CS.cf_r_inflight(d)):
  match d:
    case Wr.Got{+t, +s1}:
      pxe.inf.tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, ed))
    case Wr.Bad{}:
      Unit{}

# Requests
# --------

# a request, then rest (CS.cf_w_ask is this with an empty rest)
def pxe.w_ask(a: FC.Ask, rest: String) -> String:
  match a:
    case FC.AskRmw{r, e}:
      Wr.put_nat(0n, CS.cf_w_read(r, pxe.w_edit(e, rest)))
    case FC.AskLeaves{+ls}:
      Wr.put_nat(1n, Wr.put_nat(List.length(&2, Cf.Leaf, ls), CS.cf_w_leaves(ls, rest)))
    case FC.AskLimits{s, qs}:
      Wr.put_nat(2n, CS.cf_w_inflight(s, Wr.put_list(~Nat, ~Wr.put_nat, qs, rest)))
    case FC.AskTrust{t, +ks}:
      Wr.put_nat(3n, Wr.put_nat(CS.cf_w_trust(t), Wr.put_nat(List.length(&2, Cf.PKey, ks), CS.cf_w_pkeys(ks, rest))))
    case FC.AskMerge{+g, +p, qs}:
      Wr.put_nat(4n, Wr.put_nat(List.length(&2, Cf.Named, g), CS.cf_w_nameds(g, Wr.put_nat(List.length(&2, Cf.Named, p), CS.cf_w_nameds(p, Wr.put_list(~Nat, ~Wr.put_nat, qs, rest))))))

def pxe.w_ask_nil(a: FC.Ask) -> {pxe.w_ask(a, "") == CS.cf_w_ask(a) : String}:
  match a:
    case FC.AskRmw{r, e}:
      match e:
        case Cf.Set{k, v}:
          {==}
        case Cf.Del{k}:
          {==}
    case FC.AskLeaves{ls}:
      {==}
    case FC.AskLimits{s, qs}:
      {==}
    case FC.AskTrust{t, ks}:
      {==}
    case FC.AskMerge{g, p, qs}:
      {==}

def pxe.Ask(s: String, d: Wr.Dec<FC.Ask>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {s == pxe.w_ask(a, r) : String}
    case Wr.Bad{}:
      Unit

def pxe.rmw.e(+s: String, +rd: Cf.Read, +s1: String, +s2: String, es: {s == Wr.put_nat(0n, s1) : String}, hr: {s1 == CS.cf_w_read(rd, s2) : String}, d: Wr.Dec<Cf.Edit>, h: pxe.Ed(s2, d)) -> pxe.Ask(s, CS.cf_r_rmw.e(rd, d)):
  match d:
    case Wr.Got{+e, +r}:
      %h : {s == Wr.put_nat(0n, CS.cf_w_read(rd, _)) : String}
      %hr : {s == Wr.put_nat(0n, _) : String}
      es
    case Wr.Bad{}:
      Unit{}

def pxe.rmw(+s: String, +s1: String, es: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Cf.Read>, h: pxe.Rd(s1, d)) -> pxe.Ask(s, CS.cf_r_rmw(d)):
  match d:
    case Wr.Got{+rd, +s2}:
      pxe.rmw.e(s, rd, s1, s2, es, h, CS.cf_r_edit(Wr.get_nat(s2)), pxe.edit(s2, Wr.get_nat(s2), {==}))
    case Wr.Bad{}:
      Unit{}

def pxe.leaves(+s: String, +s1: String, es: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<List<&2, Cf.Leaf>>, h: pxe.LS(~Cf.Leaf, ~CS.cf_w_leaf, s1, d)) -> pxe.Ask(s, CS.cf_r_leaves(d)):
  match d:
    case Wr.Got{+ls, +r}:
      %pxe.leaves_items(ls, r) : {s == Wr.put_nat(1n, Wr.put_nat(List.length(&2, Cf.Leaf, ls), _)) : String}
      %h : {s == Wr.put_nat(1n, _) : String}
      es
    case Wr.Bad{}:
      Unit{}

def pxe.limits.qs(+s: String, +f: Cf.InFlight, +s1: String, +s2: String, es: {s == Wr.put_nat(2n, s1) : String}, hf: {s1 == CS.cf_w_inflight(f, s2) : String}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s2) == d : Wr.Dec<List<&2, Nat>>}) -> pxe.Ask(s, CS.cf_r_limits.qs(f, d)):
  match d:
    case Wr.Got{+qs, +r}:
      %Wire.wire_list_exact(s2, qs, r, ed) : {s == Wr.put_nat(2n, CS.cf_w_inflight(f, _)) : String}
      %hf : {s == Wr.put_nat(2n, _) : String}
      es
    case Wr.Bad{}:
      Unit{}

def pxe.limits(+s: String, +s1: String, es: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Cf.InFlight>, h: pxe.Inf(s1, d)) -> pxe.Ask(s, CS.cf_r_limits(d)):
  match d:
    case Wr.Got{+f, +s2}:
      pxe.limits.qs(s, f, s1, s2, es, h, Wr.get_list(~Nat, ~Wr.get_nat, s2), {==})
    case Wr.Bad{}:
      Unit{}

def pxe.trust.ks(+s: String, +tr: Cf.Trust, +s1: String, +s2: String, es: {s == Wr.put_nat(3n, s1) : String}, et: {s1 == Wr.put_nat(CS.cf_w_trust(tr), s2) : String}, d: Wr.Dec<List<&2, Cf.PKey>>, h: pxe.LS(~Cf.PKey, ~CS.cf_w_pkey, s2, d)) -> pxe.Ask(s, CS.cf_r_trust.ks(tr, d)):
  match d:
    case Wr.Got{+ks, +r}:
      %pxe.pkeys_items(ks, r) : {s == Wr.put_nat(3n, Wr.put_nat(CS.cf_w_trust(tr), Wr.put_nat(List.length(&2, Cf.PKey, ks), _))) : String}
      %h : {s == Wr.put_nat(3n, Wr.put_nat(CS.cf_w_trust(tr), _)) : String}
      %et : {s == Wr.put_nat(3n, _) : String}
      es
    case Wr.Bad{}:
      Unit{}

def pxe.trust.tag(+s: String, +s1: String, es: {s == Wr.put_nat(3n, s1) : String}, t: Nat, +s2: String, et: {s1 == Wr.put_nat(t, s2) : String}) -> pxe.Ask(s, CS.cf_r_trust.tag(t, s2)):
  match t:
    case 0n:
      pxe.trust.ks(s, Cf.Trusted{}, s1, s2, es, et, Wr.get_list(~Cf.PKey, ~CS.cf_r_pkey, s2), pxe.list(~Cf.PKey, ~CS.cf_r_pkey, ~CS.cf_w_pkey, ~pxe.pkey, s2))
    case 1n:
      pxe.trust.ks(s, Cf.Untrusted{}, s1, s2, es, et, Wr.get_list(~Cf.PKey, ~CS.cf_r_pkey, s2), pxe.list(~Cf.PKey, ~CS.cf_r_pkey, ~CS.cf_w_pkey, ~pxe.pkey, s2))
    case 2n+p:
      Unit{}

def pxe.trust(+s: String, +s1: String, es: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> pxe.Ask(s, CS.cf_r_trust(d)):
  match d:
    case Wr.Got{+t, +s2}:
      pxe.trust.tag(s, s1, es, t, s2, Wire.wire_nat_exact(s1, t, s2, ed))
    case Wr.Bad{}:
      Unit{}

def pxe.merge.qs(+s: String, +g: List<&2, Cf.Named>, +p: List<&2, Cf.Named>, +s1: String, +s2: String, +s3: String, es: {s == Wr.put_nat(4n, s1) : String}, hg: {s1 == Wr.put_nat(List.length(&2, Cf.Named, g), CS.cf_w_nameds(g, s2)) : String}, hp: {s2 == Wr.put_nat(List.length(&2, Cf.Named, p), CS.cf_w_nameds(p, s3)) : String}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s3) == d : Wr.Dec<List<&2, Nat>>}) -> pxe.Ask(s, CS.cf_r_merge.qs(g, p, d)):
  match d:
    case Wr.Got{+qs, +r}:
      %Wire.wire_list_exact(s3, qs, r, ed) : {s == Wr.put_nat(4n, Wr.put_nat(List.length(&2, Cf.Named, g), CS.cf_w_nameds(g, Wr.put_nat(List.length(&2, Cf.Named, p), CS.cf_w_nameds(p, _))))) : String}
      %hp : {s == Wr.put_nat(4n, Wr.put_nat(List.length(&2, Cf.Named, g), CS.cf_w_nameds(g, _))) : String}
      %hg : {s == Wr.put_nat(4n, _) : String}
      es
    case Wr.Bad{}:
      Unit{}

def pxe.merge.p(+s: String, +g: List<&2, Cf.Named>, +s1: String, +s2: String, es: {s == Wr.put_nat(4n, s1) : String}, hg: {s1 == Wr.put_nat(List.length(&2, Cf.Named, g), CS.cf_w_nameds(g, s2)) : String}, d: Wr.Dec<List<&2, Cf.Named>>, h: pxe.Nds(s2, d)) -> pxe.Ask(s, CS.cf_r_merge.p(g, d)):
  match d:
    case Wr.Got{+p, +s3}:
      pxe.merge.qs(s, g, p, s1, s2, s3, es, hg, h, Wr.get_list(~Nat, ~Wr.get_nat, s3), {==})
    case Wr.Bad{}:
      Unit{}

def pxe.merge(+s: String, +s1: String, es: {s == Wr.put_nat(4n, s1) : String}, d: Wr.Dec<List<&2, Cf.Named>>, h: pxe.Nds(s1, d)) -> pxe.Ask(s, CS.cf_r_merge(d)):
  match d:
    case Wr.Got{+g, +s2}:
      pxe.merge.p(s, g, s1, s2, es, h, CS.cf_r_nameds(s2), pxe.nameds(s2))
    case Wr.Bad{}:
      Unit{}

def pxe.ask.tag(+s: String, t: Nat, +s1: String, es: {s == Wr.put_nat(t, s1) : String}) -> pxe.Ask(s, CS.cf_r_ask.tag(t, s1)):
  match t:
    case 0n:
      pxe.rmw(s, s1, es, CS.cf_r_read(Wr.get_nat(s1)), pxe.read(s1, Wr.get_nat(s1), {==}))
    case 1n:
      pxe.leaves(s, s1, es, Wr.get_list(~Cf.Leaf, ~CS.cf_r_leaf, s1), pxe.list(~Cf.Leaf, ~CS.cf_r_leaf, ~CS.cf_w_leaf, ~pxe.leaf, s1))
    case 2n:
      pxe.limits(s, s1, es, CS.cf_r_inflight(Wr.get_nat(s1)), pxe.inf(s1, Wr.get_nat(s1), {==}))
    case 3n:
      pxe.trust(s, s1, es, Wr.get_nat(s1), {==})
    case 4n:
      pxe.merge(s, s1, es, CS.cf_r_nameds(s1), pxe.nameds(s1))
    case 5n+p:
      Unit{}

def pxe.ask(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> pxe.Ask(s, CS.cf_r_ask(d)):
  match d:
    case Wr.Got{+t, +s1}:
      pxe.ask.tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, ed))
    case Wr.Bad{}:
      Unit{}

# Whole requests
# --------------

# what the reader's verdict on s says: a request read whole is s spelled
def pxe.Whole(s: String, m: Maybe<&2, FC.Ask>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{a}:
      {s == CS.cf_w_ask(a) : String}

def pxe.empty(r: String, e: {String.is_empty(r) == True{} : Bool}) -> {r == "" : String}:
  match r:
    case SNil{}:
      {==}
    case SCon{c, t}:
      LLogicLogic.ppr.absurdF({SCon{c, t} == "" : String}, e)

def pxe.end(+s: String, b: Bool, +a: FC.Ask, +r: String, eb: {String.is_empty(r) == b : Bool}, h: {s == pxe.w_ask(a, r) : String}) -> pxe.Whole(s, CS.cf_r_end(b, a)):
  match b:
    case True{}:
      %pxe.w_ask_nil(a) : {s == _ : String}
      %pxe.empty(r, eb) : {s == pxe.w_ask(a, _) : String}
      h
    case False{}:
      Unit{}

def pxe.whole(+s: String, d: Wr.Dec<FC.Ask>, h: pxe.Ask(s, d)) -> pxe.Whole(s, CS.cf_r_whole(d)):
  match d:
    case Wr.Got{+a, +r}:
      pxe.end(s, String.is_empty(r), a, r, {==}, h)
    case Wr.Bad{}:
      Unit{}

# an input the reader reads whole is a spelled request
def pxe.read_exact(+s: String) -> pxe.Whole(s, CS.cf_read(s)):
  pxe.whole(s, CS.cf_r_ask(Wr.get_nat(s)), pxe.ask(s, Wr.get_nat(s), {==}))
