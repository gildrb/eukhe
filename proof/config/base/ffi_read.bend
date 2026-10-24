# eukhe: lemmas the proofs of the config entry share (bend/ffi_config.bend),
# its reader: the entry reads every input as the laws' reader does (one
# lemma per stage, each a case split on the stage's input; a list by
# induction on its count).

import Base
import ../../../bend/config.bend as Cf
import ../../../bend/ffi_config.bend as FC
import ../../../bend/wire.bend as Wr
import ../../../spec/config.bend as CS

# Logic
# -----

def pfc.if_none(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

# a claim that Some is None proves anything
def pfc.some_none(-A: Data, -x: A, -G: Type, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  %e : pfc.if_none(A, _, G)
  Unit{}

# The reader, stage by stage
# --------------------------

def pfc.entry_v(k: Nat, r: Wr.Dec<Nat>) -> {FC.get_entry.v(k, r) == CS.cf_r_entry.v(k, r) : Wr.Dec<Cf.Entry>}:
  match r:
    case Wr.Got{v, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pfc.entry_k(r: Wr.Dec<Nat>) -> {FC.get_entry.k(r) == CS.cf_r_entry.k(r) : Wr.Dec<Cf.Entry>}:
  match r:
    case Wr.Got{k, s}:
      pfc.entry_v(k, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def pfc.entry(s: String) -> {FC.get_entry(s) == CS.cf_r_entry(s) : Wr.Dec<Cf.Entry>}:
  pfc.entry_k(Wr.get_nat(s))

def pfc.leaf_tag(p: Nat, t: Nat, s: String) -> {FC.get_leaf.tag(p, t, s) == CS.cf_r_leaf.tag(p, t, s) : Wr.Dec<Cf.Leaf>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n+q:
      {==}

def pfc.leaf_o(p: Nat, r: Wr.Dec<Nat>) -> {FC.get_leaf.o(p, r) == CS.cf_r_leaf.o(p, r) : Wr.Dec<Cf.Leaf>}:
  match r:
    case Wr.Got{t, s}:
      pfc.leaf_tag(p, t, s)
    case Wr.Bad{}:
      {==}

def pfc.leaf_p(r: Wr.Dec<Nat>) -> {FC.get_leaf.p(r) == CS.cf_r_leaf.p(r) : Wr.Dec<Cf.Leaf>}:
  match r:
    case Wr.Got{p, s}:
      pfc.leaf_o(p, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def pfc.leaf(s: String) -> {FC.get_leaf(s) == CS.cf_r_leaf(s) : Wr.Dec<Cf.Leaf>}:
  pfc.leaf_p(Wr.get_nat(s))

def pfc.slot_num(p: Nat, r: Wr.Dec<Nat>) -> {FC.get_slot.num(p, r) == CS.cf_r_slot.num(p, r) : Wr.Dec<Cf.Slot>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pfc.slot_tag(p: Nat, t: Nat, s: String) -> {FC.get_slot.tag(p, t, s) == CS.cf_r_slot.tag(p, t, s) : Wr.Dec<Cf.Slot>}:
  match t:
    case 0n:
      pfc.slot_num(p, Wr.get_nat(s))
    case 1n:
      {==}
    case 2n+q:
      {==}

def pfc.slot_v(p: Nat, r: Wr.Dec<Nat>) -> {FC.get_slot.v(p, r) == CS.cf_r_slot.v(p, r) : Wr.Dec<Cf.Slot>}:
  match r:
    case Wr.Got{t, s}:
      pfc.slot_tag(p, t, s)
    case Wr.Bad{}:
      {==}

def pfc.slot_p(r: Wr.Dec<Nat>) -> {FC.get_slot.p(r) == CS.cf_r_slot.p(r) : Wr.Dec<Cf.Slot>}:
  match r:
    case Wr.Got{p, s}:
      pfc.slot_v(p, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def pfc.slot(s: String) -> {FC.get_slot(s) == CS.cf_r_slot(s) : Wr.Dec<Cf.Slot>}:
  pfc.slot_p(Wr.get_nat(s))

def pfc.pkey_v(k: Nat, p: List<&2, String>, r: Wr.Dec<Nat>) -> {FC.get_pkey.v(k, p, r) == CS.cf_r_pkey.v(k, p, r) : Wr.Dec<Cf.PKey>}:
  match r:
    case Wr.Got{v, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pfc.pkey_p(k: Nat, r: Wr.Dec<List<&2, String>>) -> {FC.get_pkey.p(k, r) == CS.cf_r_pkey.p(k, r) : Wr.Dec<Cf.PKey>}:
  match r:
    case Wr.Got{p, s}:
      pfc.pkey_v(k, p, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def pfc.pkey_k(r: Wr.Dec<Nat>) -> {FC.get_pkey.k(r) == CS.cf_r_pkey.k(r) : Wr.Dec<Cf.PKey>}:
  match r:
    case Wr.Got{k, s}:
      pfc.pkey_p(k, Wr.get_list(~String, ~Wr.get_str, s))
    case Wr.Bad{}:
      {==}

def pfc.pkey(s: String) -> {FC.get_pkey(s) == CS.cf_r_pkey(s) : Wr.Dec<Cf.PKey>}:
  pfc.pkey_k(Wr.get_nat(s))

def pfc.entries_cons(x: Cf.Entry, r: Wr.Dec<List<&2, Cf.Entry>>) -> {FC.get_entries.cons(x, r) == Wr.get_list.cons(Cf.Entry, x, r) : Wr.Dec<List<&2, Cf.Entry>>}:
  match r:
    case Wr.Got{xs, s}:
      {==}
    case Wr.Bad{}:
      {==}

# the entry's loop over the items reads as the wire's
def pfc.entries_go(n: Nat, cur: Wr.Dec<Cf.Entry>) -> {FC.get_entries.go(n, cur) == Wr.get_list.go(~Cf.Entry, ~CS.cf_r_entry, n, cur) : Wr.Dec<List<&2, Cf.Entry>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n++m:
      match cur:
        case Wr.Got{+x, +s}:
          %pfc.entry(s) : {FC.get_entries.cons(x, FC.get_entries.go(m, FC.get_entry(s))) == Wr.get_list.cons(Cf.Entry, x, Wr.get_list.go(~Cf.Entry, ~CS.cf_r_entry, m, _)) : Wr.Dec<List<&2, Cf.Entry>>}
          %pfc.entries_go(m, FC.get_entry(s)) : {FC.get_entries.cons(x, FC.get_entries.go(m, FC.get_entry(s))) == Wr.get_list.cons(Cf.Entry, x, _) : Wr.Dec<List<&2, Cf.Entry>>}
          pfc.entries_cons(x, FC.get_entries.go(m, FC.get_entry(s)))
        case Wr.Bad{}:
          {==}

def pfc.entries_start(r: Wr.Dec<Nat>) -> {FC.get_entries.start(r) == Wr.get_list.start(~Cf.Entry, ~CS.cf_r_entry, r) : Wr.Dec<List<&2, Cf.Entry>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n++m:
          %pfc.entry(s) : {FC.get_entries.go(m, FC.get_entry(s)) == Wr.get_list.go(~Cf.Entry, ~CS.cf_r_entry, m, _) : Wr.Dec<List<&2, Cf.Entry>>}
          pfc.entries_go(m, FC.get_entry(s))
    case Wr.Bad{}:
      {==}

def pfc.leaves_cons(x: Cf.Leaf, r: Wr.Dec<List<&2, Cf.Leaf>>) -> {FC.get_leaves.cons(x, r) == Wr.get_list.cons(Cf.Leaf, x, r) : Wr.Dec<List<&2, Cf.Leaf>>}:
  match r:
    case Wr.Got{xs, s}:
      {==}
    case Wr.Bad{}:
      {==}

# the entry's loop over the items reads as the wire's
def pfc.leaves_go(n: Nat, cur: Wr.Dec<Cf.Leaf>) -> {FC.get_leaves.go(n, cur) == Wr.get_list.go(~Cf.Leaf, ~CS.cf_r_leaf, n, cur) : Wr.Dec<List<&2, Cf.Leaf>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n++m:
      match cur:
        case Wr.Got{+x, +s}:
          %pfc.leaf(s) : {FC.get_leaves.cons(x, FC.get_leaves.go(m, FC.get_leaf(s))) == Wr.get_list.cons(Cf.Leaf, x, Wr.get_list.go(~Cf.Leaf, ~CS.cf_r_leaf, m, _)) : Wr.Dec<List<&2, Cf.Leaf>>}
          %pfc.leaves_go(m, FC.get_leaf(s)) : {FC.get_leaves.cons(x, FC.get_leaves.go(m, FC.get_leaf(s))) == Wr.get_list.cons(Cf.Leaf, x, _) : Wr.Dec<List<&2, Cf.Leaf>>}
          pfc.leaves_cons(x, FC.get_leaves.go(m, FC.get_leaf(s)))
        case Wr.Bad{}:
          {==}

def pfc.leaves_start(r: Wr.Dec<Nat>) -> {FC.get_leaves.start(r) == Wr.get_list.start(~Cf.Leaf, ~CS.cf_r_leaf, r) : Wr.Dec<List<&2, Cf.Leaf>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n++m:
          %pfc.leaf(s) : {FC.get_leaves.go(m, FC.get_leaf(s)) == Wr.get_list.go(~Cf.Leaf, ~CS.cf_r_leaf, m, _) : Wr.Dec<List<&2, Cf.Leaf>>}
          pfc.leaves_go(m, FC.get_leaf(s))
    case Wr.Bad{}:
      {==}

def pfc.slots_cons(x: Cf.Slot, r: Wr.Dec<List<&2, Cf.Slot>>) -> {FC.get_slots.cons(x, r) == Wr.get_list.cons(Cf.Slot, x, r) : Wr.Dec<List<&2, Cf.Slot>>}:
  match r:
    case Wr.Got{xs, s}:
      {==}
    case Wr.Bad{}:
      {==}

# the entry's loop over the items reads as the wire's
def pfc.slots_go(n: Nat, cur: Wr.Dec<Cf.Slot>) -> {FC.get_slots.go(n, cur) == Wr.get_list.go(~Cf.Slot, ~CS.cf_r_slot, n, cur) : Wr.Dec<List<&2, Cf.Slot>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n++m:
      match cur:
        case Wr.Got{+x, +s}:
          %pfc.slot(s) : {FC.get_slots.cons(x, FC.get_slots.go(m, FC.get_slot(s))) == Wr.get_list.cons(Cf.Slot, x, Wr.get_list.go(~Cf.Slot, ~CS.cf_r_slot, m, _)) : Wr.Dec<List<&2, Cf.Slot>>}
          %pfc.slots_go(m, FC.get_slot(s)) : {FC.get_slots.cons(x, FC.get_slots.go(m, FC.get_slot(s))) == Wr.get_list.cons(Cf.Slot, x, _) : Wr.Dec<List<&2, Cf.Slot>>}
          pfc.slots_cons(x, FC.get_slots.go(m, FC.get_slot(s)))
        case Wr.Bad{}:
          {==}

def pfc.slots_start(r: Wr.Dec<Nat>) -> {FC.get_slots.start(r) == Wr.get_list.start(~Cf.Slot, ~CS.cf_r_slot, r) : Wr.Dec<List<&2, Cf.Slot>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n++m:
          %pfc.slot(s) : {FC.get_slots.go(m, FC.get_slot(s)) == Wr.get_list.go(~Cf.Slot, ~CS.cf_r_slot, m, _) : Wr.Dec<List<&2, Cf.Slot>>}
          pfc.slots_go(m, FC.get_slot(s))
    case Wr.Bad{}:
      {==}

def pfc.pkeys_cons(x: Cf.PKey, r: Wr.Dec<List<&2, Cf.PKey>>) -> {FC.get_pkeys.cons(x, r) == Wr.get_list.cons(Cf.PKey, x, r) : Wr.Dec<List<&2, Cf.PKey>>}:
  match r:
    case Wr.Got{xs, s}:
      {==}
    case Wr.Bad{}:
      {==}

# the entry's loop over the items reads as the wire's
def pfc.pkeys_go(n: Nat, cur: Wr.Dec<Cf.PKey>) -> {FC.get_pkeys.go(n, cur) == Wr.get_list.go(~Cf.PKey, ~CS.cf_r_pkey, n, cur) : Wr.Dec<List<&2, Cf.PKey>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n++m:
      match cur:
        case Wr.Got{+x, +s}:
          %pfc.pkey(s) : {FC.get_pkeys.cons(x, FC.get_pkeys.go(m, FC.get_pkey(s))) == Wr.get_list.cons(Cf.PKey, x, Wr.get_list.go(~Cf.PKey, ~CS.cf_r_pkey, m, _)) : Wr.Dec<List<&2, Cf.PKey>>}
          %pfc.pkeys_go(m, FC.get_pkey(s)) : {FC.get_pkeys.cons(x, FC.get_pkeys.go(m, FC.get_pkey(s))) == Wr.get_list.cons(Cf.PKey, x, _) : Wr.Dec<List<&2, Cf.PKey>>}
          pfc.pkeys_cons(x, FC.get_pkeys.go(m, FC.get_pkey(s)))
        case Wr.Bad{}:
          {==}

def pfc.pkeys_start(r: Wr.Dec<Nat>) -> {FC.get_pkeys.start(r) == Wr.get_list.start(~Cf.PKey, ~CS.cf_r_pkey, r) : Wr.Dec<List<&2, Cf.PKey>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n++m:
          %pfc.pkey(s) : {FC.get_pkeys.go(m, FC.get_pkey(s)) == Wr.get_list.go(~Cf.PKey, ~CS.cf_r_pkey, m, _) : Wr.Dec<List<&2, Cf.PKey>>}
          pfc.pkeys_go(m, FC.get_pkey(s))
    case Wr.Bad{}:
      {==}

def pfc.named_fs(n: Nat, r: Wr.Dec<List<&2, Cf.Entry>>) -> {FC.get_named.fs(n, r) == CS.cf_r_named.fs(n, r) : Wr.Dec<Cf.Named>}:
  match r:
    case Wr.Got{fs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pfc.named_n(r: Wr.Dec<Nat>) -> {FC.get_named.n(r) == CS.cf_r_named.n(r) : Wr.Dec<Cf.Named>}:
  match r:
    case Wr.Got{n, +s}:
      %pfc.entries_start(Wr.get_nat(s)) : {FC.get_named.fs(n, FC.get_entries.start(Wr.get_nat(s))) == CS.cf_r_named.fs(n, _) : Wr.Dec<Cf.Named>}
      pfc.named_fs(n, FC.get_entries.start(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def pfc.named(s: String) -> {FC.get_named(s) == CS.cf_r_named(s) : Wr.Dec<Cf.Named>}:
  pfc.named_n(Wr.get_nat(s))

def pfc.nameds_cons(x: Cf.Named, r: Wr.Dec<List<&2, Cf.Named>>) -> {FC.get_nameds.cons(x, r) == Wr.get_list.cons(Cf.Named, x, r) : Wr.Dec<List<&2, Cf.Named>>}:
  match r:
    case Wr.Got{xs, s}:
      {==}
    case Wr.Bad{}:
      {==}

# the entry's loop over the items reads as the wire's
def pfc.nameds_go(n: Nat, cur: Wr.Dec<Cf.Named>) -> {FC.get_nameds.go(n, cur) == Wr.get_list.go(~Cf.Named, ~CS.cf_r_named, n, cur) : Wr.Dec<List<&2, Cf.Named>>}:
  match n:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          {==}
        case Wr.Bad{}:
          {==}
    case 1n++m:
      match cur:
        case Wr.Got{+x, +s}:
          %pfc.named(s) : {FC.get_nameds.cons(x, FC.get_nameds.go(m, FC.get_named(s))) == Wr.get_list.cons(Cf.Named, x, Wr.get_list.go(~Cf.Named, ~CS.cf_r_named, m, _)) : Wr.Dec<List<&2, Cf.Named>>}
          %pfc.nameds_go(m, FC.get_named(s)) : {FC.get_nameds.cons(x, FC.get_nameds.go(m, FC.get_named(s))) == Wr.get_list.cons(Cf.Named, x, _) : Wr.Dec<List<&2, Cf.Named>>}
          pfc.nameds_cons(x, FC.get_nameds.go(m, FC.get_named(s)))
        case Wr.Bad{}:
          {==}

def pfc.nameds_start(r: Wr.Dec<Nat>) -> {FC.get_nameds.start(r) == Wr.get_list.start(~Cf.Named, ~CS.cf_r_named, r) : Wr.Dec<List<&2, Cf.Named>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n++m:
          %pfc.named(s) : {FC.get_nameds.go(m, FC.get_named(s)) == Wr.get_list.go(~Cf.Named, ~CS.cf_r_named, m, _) : Wr.Dec<List<&2, Cf.Named>>}
          pfc.nameds_go(m, FC.get_named(s))
    case Wr.Bad{}:
      {==}

def pfc.read_parsed(r: Wr.Dec<List<&2, Cf.Entry>>) -> {FC.get_read.parsed(r) == CS.cf_r_read.parsed(r) : Wr.Dec<Cf.Read>}:
  match r:
    case Wr.Got{d, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pfc.read_tag(t: Nat, +s: String) -> {FC.get_read.tag(t, s) == CS.cf_r_read.tag(t, s) : Wr.Dec<Cf.Read>}:
  match t:
    case 0n:
      {==}
    case 1n:
      %pfc.entries_start(Wr.get_nat(s)) : {FC.get_read.parsed(FC.get_entries.start(Wr.get_nat(s))) == CS.cf_r_read.parsed(_) : Wr.Dec<Cf.Read>}
      pfc.read_parsed(FC.get_entries.start(Wr.get_nat(s)))
    case 2n:
      {==}
    case 3n+p:
      {==}

def pfc.read(r: Wr.Dec<Nat>) -> {FC.get_read(r) == CS.cf_r_read(r) : Wr.Dec<Cf.Read>}:
  match r:
    case Wr.Got{t, s}:
      pfc.read_tag(t, s)
    case Wr.Bad{}:
      {==}

def pfc.edit_set(k: Nat, r: Wr.Dec<Nat>) -> {FC.get_edit.set(k, r) == CS.cf_r_edit.set(k, r) : Wr.Dec<Cf.Edit>}:
  match r:
    case Wr.Got{v, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pfc.edit_setk(r: Wr.Dec<Nat>) -> {FC.get_edit.setk(r) == CS.cf_r_edit.setk(r) : Wr.Dec<Cf.Edit>}:
  match r:
    case Wr.Got{k, s}:
      pfc.edit_set(k, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def pfc.edit_del(r: Wr.Dec<Nat>) -> {FC.get_edit.del(r) == CS.cf_r_edit.del(r) : Wr.Dec<Cf.Edit>}:
  match r:
    case Wr.Got{k, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pfc.edit_tag(t: Nat, s: String) -> {FC.get_edit.tag(t, s) == CS.cf_r_edit.tag(t, s) : Wr.Dec<Cf.Edit>}:
  match t:
    case 0n:
      pfc.edit_setk(Wr.get_nat(s))
    case 1n:
      pfc.edit_del(Wr.get_nat(s))
    case 2n+p:
      {==}

def pfc.edit(r: Wr.Dec<Nat>) -> {FC.get_edit(r) == CS.cf_r_edit(r) : Wr.Dec<Cf.Edit>}:
  match r:
    case Wr.Got{t, s}:
      pfc.edit_tag(t, s)
    case Wr.Bad{}:
      {==}

def pfc.inflight_map(r: Wr.Dec<List<&2, Cf.Slot>>) -> {FC.get_inflight.map(r) == CS.cf_r_inflight.map(r) : Wr.Dec<Cf.InFlight>}:
  match r:
    case Wr.Got{es, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pfc.inflight_tag(t: Nat, +s: String) -> {FC.get_inflight.tag(t, s) == CS.cf_r_inflight.tag(t, s) : Wr.Dec<Cf.InFlight>}:
  match t:
    case 0n:
      {==}
    case 1n:
      %pfc.slots_start(Wr.get_nat(s)) : {FC.get_inflight.map(FC.get_slots.start(Wr.get_nat(s))) == CS.cf_r_inflight.map(_) : Wr.Dec<Cf.InFlight>}
      pfc.inflight_map(FC.get_slots.start(Wr.get_nat(s)))
    case 2n:
      {==}
    case 3n+p:
      {==}

def pfc.inflight(r: Wr.Dec<Nat>) -> {FC.get_inflight(r) == CS.cf_r_inflight(r) : Wr.Dec<Cf.InFlight>}:
  match r:
    case Wr.Got{t, s}:
      pfc.inflight_tag(t, s)
    case Wr.Bad{}:
      {==}

def pfc.rmw_e(r: Cf.Read, d: Wr.Dec<Cf.Edit>) -> {FC.get_rmw.e(r, d) == CS.cf_r_rmw.e(r, d) : Wr.Dec<FC.Ask>}:
  match d:
    case Wr.Got{e, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pfc.rmw(d: Wr.Dec<Cf.Read>) -> {FC.get_rmw(d) == CS.cf_r_rmw(d) : Wr.Dec<FC.Ask>}:
  match d:
    case Wr.Got{+r, +s}:
      %pfc.edit(Wr.get_nat(s)) : {FC.get_rmw.e(r, FC.get_edit(Wr.get_nat(s))) == CS.cf_r_rmw.e(r, _) : Wr.Dec<FC.Ask>}
      pfc.rmw_e(r, FC.get_edit(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def pfc.leaves_ask(d: Wr.Dec<List<&2, Cf.Leaf>>) -> {FC.get_leaves(d) == CS.cf_r_leaves(d) : Wr.Dec<FC.Ask>}:
  match d:
    case Wr.Got{ls, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pfc.limits_qs(f: Cf.InFlight, d: Wr.Dec<List<&2, Nat>>) -> {FC.get_limits.qs(f, d) == CS.cf_r_limits.qs(f, d) : Wr.Dec<FC.Ask>}:
  match d:
    case Wr.Got{qs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pfc.limits(d: Wr.Dec<Cf.InFlight>) -> {FC.get_limits(d) == CS.cf_r_limits(d) : Wr.Dec<FC.Ask>}:
  match d:
    case Wr.Got{f, s}:
      pfc.limits_qs(f, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      {==}

def pfc.trust_ks(t: Cf.Trust, d: Wr.Dec<List<&2, Cf.PKey>>) -> {FC.get_trust.ks(t, d) == CS.cf_r_trust.ks(t, d) : Wr.Dec<FC.Ask>}:
  match d:
    case Wr.Got{ks, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pfc.trust_tag(t: Nat, +s: String) -> {FC.get_trust.tag(t, s) == CS.cf_r_trust.tag(t, s) : Wr.Dec<FC.Ask>}:
  match t:
    case 0n:
      %pfc.pkeys_start(Wr.get_nat(s)) : {FC.get_trust.ks(Cf.Trusted{}, FC.get_pkeys.start(Wr.get_nat(s))) == CS.cf_r_trust.ks(Cf.Trusted{}, _) : Wr.Dec<FC.Ask>}
      pfc.trust_ks(Cf.Trusted{}, FC.get_pkeys.start(Wr.get_nat(s)))
    case 1n:
      %pfc.pkeys_start(Wr.get_nat(s)) : {FC.get_trust.ks(Cf.Untrusted{}, FC.get_pkeys.start(Wr.get_nat(s))) == CS.cf_r_trust.ks(Cf.Untrusted{}, _) : Wr.Dec<FC.Ask>}
      pfc.trust_ks(Cf.Untrusted{}, FC.get_pkeys.start(Wr.get_nat(s)))
    case 2n+p:
      {==}

def pfc.trust(r: Wr.Dec<Nat>) -> {FC.get_trust(r) == CS.cf_r_trust(r) : Wr.Dec<FC.Ask>}:
  match r:
    case Wr.Got{t, s}:
      pfc.trust_tag(t, s)
    case Wr.Bad{}:
      {==}

def pfc.merge_qs(g: List<&2, Cf.Named>, p: List<&2, Cf.Named>, d: Wr.Dec<List<&2, Nat>>) -> {FC.get_merge.qs(g, p, d) == CS.cf_r_merge.qs(g, p, d) : Wr.Dec<FC.Ask>}:
  match d:
    case Wr.Got{qs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def pfc.merge_p(g: List<&2, Cf.Named>, d: Wr.Dec<List<&2, Cf.Named>>) -> {FC.get_merge.p(g, d) == CS.cf_r_merge.p(g, d) : Wr.Dec<FC.Ask>}:
  match d:
    case Wr.Got{p, s}:
      pfc.merge_qs(g, p, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      {==}

def pfc.merge(d: Wr.Dec<List<&2, Cf.Named>>) -> {FC.get_merge(d) == CS.cf_r_merge(d) : Wr.Dec<FC.Ask>}:
  match d:
    case Wr.Got{+g, +s}:
      %pfc.nameds_start(Wr.get_nat(s)) : {FC.get_merge.p(g, FC.get_nameds.start(Wr.get_nat(s))) == CS.cf_r_merge.p(g, _) : Wr.Dec<FC.Ask>}
      pfc.merge_p(g, FC.get_nameds.start(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def pfc.ask_tag(t: Nat, +s: String) -> {FC.get_ask.tag(t, s) == CS.cf_r_ask.tag(t, s) : Wr.Dec<FC.Ask>}:
  match t:
    case 0n:
      %pfc.read(Wr.get_nat(s)) : {FC.get_rmw(FC.get_read(Wr.get_nat(s))) == CS.cf_r_rmw(_) : Wr.Dec<FC.Ask>}
      pfc.rmw(FC.get_read(Wr.get_nat(s)))
    case 1n:
      %pfc.leaves_start(Wr.get_nat(s)) : {FC.get_leaves(FC.get_leaves.start(Wr.get_nat(s))) == CS.cf_r_leaves(_) : Wr.Dec<FC.Ask>}
      pfc.leaves_ask(FC.get_leaves.start(Wr.get_nat(s)))
    case 2n:
      %pfc.inflight(Wr.get_nat(s)) : {FC.get_limits(FC.get_inflight(Wr.get_nat(s))) == CS.cf_r_limits(_) : Wr.Dec<FC.Ask>}
      pfc.limits(FC.get_inflight(Wr.get_nat(s)))
    case 3n:
      pfc.trust(Wr.get_nat(s))
    case 4n:
      %pfc.nameds_start(Wr.get_nat(s)) : {FC.get_merge(FC.get_nameds.start(Wr.get_nat(s))) == CS.cf_r_merge(_) : Wr.Dec<FC.Ask>}
      pfc.merge(FC.get_nameds.start(Wr.get_nat(s)))
    case 5n+p:
      {==}

# the entry reads every input as the laws' reader does
def pfc.ask(r: Wr.Dec<Nat>) -> {FC.get_ask(r) == CS.cf_r_ask(r) : Wr.Dec<FC.Ask>}:
  match r:
    case Wr.Got{t, s}:
      pfc.ask_tag(t, s)
    case Wr.Bad{}:
      {==}
