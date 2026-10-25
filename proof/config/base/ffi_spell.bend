# eukhe: lemmas the proofs of the config entry share (bend/ffi_config.bend),
# its requests: the laws' reader reads back every request the laws'
# spellers write that fits the wire (the wire's round trips, item by
# item, each list by induction on its items).

import Base
import ../../../bend/config.bend as Cf
import ../../../bend/ffi_config.bend as FC
import ../../../bend/wire.bend as Wr
import ../../../spec/config.bend as CS
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../base/wire.bend as LWire
import ../../base/logic/bool.bend as LLogicBool

# Paths: lists of strings
# -----------------------

# the items of a list of strings, then rest
def pfs.ss_items(xs: List<&2, String>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      Wr.put_str(x, pfs.ss_items(t, rest))

def pfs.ss_go(xs: List<&2, String>, -rest: String) -> {Wr.put_list.go(~String, ~Wr.put_str, xs, rest) == (List.length(&2, String, xs), pfs.ss_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~String, ~Wr.put_str, t, rest), (List.length(&2, String, t), pfs.ss_items(t, rest)), pfs.ss_go(t, rest)) : {Wr.put_list.step(~String, ~Wr.put_str, x, _) == (1n+List.length(&2, String, t), Wr.put_str(x, pfs.ss_items(t, rest))) : Nat & String}
      {==}

# a list of strings is its count, then its items
def pfs.ss_put(+xs: List<&2, String>, -rest: String) -> {Wr.put_nat(List.length(&2, String, xs), pfs.ss_items(xs, rest)) == Wr.put_list(~String, ~Wr.put_str, xs, rest) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~String, ~Wr.put_str, xs, rest), (List.length(&2, String, xs), pfs.ss_items(xs, rest)), pfs.ss_go(xs, rest)) : {Wr.put_nat(List.length(&2, String, xs), pfs.ss_items(xs, rest)) == Wr.put_list.fin(_) : String}
  {==}

# the strings u after x read back, x first
def pfs.ss_go_rt(u: List<&2, String>, +x: String, +rest: String, +hf: {CS.cf_fit_path(x <> u) == True{} : Bool}) -> {Wr.get_list.go(~String, ~Wr.get_str, List.length(&2, String, u), Wr.get_str(Wr.put_str(x, pfs.ss_items(u, rest)))) == Wr.Got{x <> u, rest} : Wr.Dec<List<&2, String>>}:
  match u:
    case Nil{}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, LLogicBool.wr_and_l(LawsBase.wire_fits(String.length(x)), True{}, hf))) : {Wr.get_list.go(~String, ~Wr.get_str, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, String>>}
      {==}
    case +y <> +v:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, Wr.put_str(y, pfs.ss_items(v, rest)))), Wr.Got{x, Wr.put_str(y, pfs.ss_items(v, rest))}, Wire.wire_str_round_trip(x, Wr.put_str(y, pfs.ss_items(v, rest)), LLogicBool.wr_and_l(LawsBase.wire_fits(String.length(x)), CS.cf_fit_path(y <> v), hf))) : {Wr.get_list.go(~String, ~Wr.get_str, 1n+List.length(&2, String, v), _) == Wr.Got{x <> y <> v, rest} : Wr.Dec<List<&2, String>>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list.go(~String, ~Wr.get_str, List.length(&2, String, v), Wr.get_str(Wr.put_str(y, pfs.ss_items(v, rest)))), Wr.Got{y <> v, rest}, pfs.ss_go_rt(v, y, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(String.length(x)), CS.cf_fit_path(y <> v), hf))) : {Wr.get_list.cons(String, x, _) == Wr.Got{x <> y <> v, rest} : Wr.Dec<List<&2, String>>}
      {==}

def pfs.ss_items_rt(+xs: List<&2, String>, +rest: String, +hf: {CS.cf_fit_path(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list.start(~String, ~Wr.get_str, Wr.Got{List.length(&2, String, xs), pfs.ss_items(xs, rest)}) : Wr.Dec<List<&2, String>>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +u:
      Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list.go(~String, ~Wr.get_str, List.length(&2, String, u), Wr.get_str(Wr.put_str(x, pfs.ss_items(u, rest)))), Wr.Got{x <> u, rest}, pfs.ss_go_rt(u, x, rest, hf))

# a path that fits reads back
def pfs.path_rt(+p: List<&2, String>, +rest: String, +hl: {LawsBase.wire_fits(List.length(&2, String, p)) == True{} : Bool}, +hp: {CS.cf_fit_path(p) == True{} : Bool}) -> {Wr.Got{p, rest} == Wr.get_list(~String, ~Wr.get_str, Wr.put_list(~String, ~Wr.put_str, p, rest)) : Wr.Dec<List<&2, String>>}:
  %pfs.ss_put(p, rest) : {Wr.Got{p, rest} == Wr.get_list(~String, ~Wr.get_str, _) : Wr.Dec<List<&2, String>>}
  %LWire.pw6.nat(List.length(&2, String, p), pfs.ss_items(p, rest), hl) : {Wr.Got{p, rest} == Wr.get_list.start(~String, ~Wr.get_str, _) : Wr.Dec<List<&2, String>>}
  pfs.ss_items_rt(p, rest, hp)

# Items
# -----

# an entry reads back, whatever follows it
def pfs.entry_rt(e: Cf.Entry, -t: List<&2, Cf.Entry>, +rest: String, +h: {CS.cf_fit_entries.all(e <> t) == True{} : Bool}) -> {Wr.Got{e, rest} == CS.cf_r_entry(CS.cf_w_entry(e, rest)) : Wr.Dec<Cf.Entry>}:
  match e:
    case Cf.Entry{+k, +v}:
      +hv = LLogicBool.wr_and_r(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(v), CS.cf_fit_entries.all(t)), h)
      %LWire.pw6.nat(k, Wr.put_nat(v, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(v), CS.cf_fit_entries.all(t)), h)) : {Wr.Got{Cf.Entry{k, v}, rest} == CS.cf_r_entry.k(_) : Wr.Dec<Cf.Entry>}
      %LWire.pw6.nat(v, rest, LLogicBool.wr_and_l(LawsBase.wire_fits(v), CS.cf_fit_entries.all(t), hv)) : {Wr.Got{Cf.Entry{k, v}, rest} == CS.cf_r_entry.v(k, _) : Wr.Dec<Cf.Entry>}
      {==}

def pfs.entry_tail(e: Cf.Entry, +t: List<&2, Cf.Entry>, +h: {CS.cf_fit_entries.all(e <> t) == True{} : Bool}) -> {CS.cf_fit_entries.all(t) == True{} : Bool}:
  match e:
    case Cf.Entry{+k, +v}:
      LLogicBool.wr_and_r(LawsBase.wire_fits(v), CS.cf_fit_entries.all(t), LLogicBool.wr_and_r(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(v), CS.cf_fit_entries.all(t)), h))

# a leaf reads back, whatever follows it
def pfs.leaf_rt(l: Cf.Leaf, -t: List<&2, Cf.Leaf>, +rest: String, +h: {CS.cf_fit_leaves(l <> t) == True{} : Bool}) -> {Wr.Got{l, rest} == CS.cf_r_leaf(CS.cf_w_leaf(l, rest)) : Wr.Dec<Cf.Leaf>}:
  match l:
    case Cf.Leaf{+p, o}:
      match o:
        case Cf.Good{}:
          %LWire.pw6.nat(p, Wr.put_nat(0n, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(p), CS.cf_fit_leaves(t), h)) : {Wr.Got{Cf.Leaf{p, Cf.Good{}}, rest} == CS.cf_r_leaf.p(_) : Wr.Dec<Cf.Leaf>}
          %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{Cf.Leaf{p, Cf.Good{}}, rest} == CS.cf_r_leaf.o(p, _) : Wr.Dec<Cf.Leaf>}
          {==}
        case Cf.BadType{}:
          %LWire.pw6.nat(p, Wr.put_nat(1n, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(p), CS.cf_fit_leaves(t), h)) : {Wr.Got{Cf.Leaf{p, Cf.BadType{}}, rest} == CS.cf_r_leaf.p(_) : Wr.Dec<Cf.Leaf>}
          %LWire.pw6.nat(1n, rest, {==}) : {Wr.Got{Cf.Leaf{p, Cf.BadType{}}, rest} == CS.cf_r_leaf.o(p, _) : Wr.Dec<Cf.Leaf>}
          {==}
        case Cf.Undeclared{}:
          %LWire.pw6.nat(p, Wr.put_nat(2n, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(p), CS.cf_fit_leaves(t), h)) : {Wr.Got{Cf.Leaf{p, Cf.Undeclared{}}, rest} == CS.cf_r_leaf.p(_) : Wr.Dec<Cf.Leaf>}
          %LWire.pw6.nat(2n, rest, {==}) : {Wr.Got{Cf.Leaf{p, Cf.Undeclared{}}, rest} == CS.cf_r_leaf.o(p, _) : Wr.Dec<Cf.Leaf>}
          {==}

def pfs.leaf_tail(l: Cf.Leaf, +t: List<&2, Cf.Leaf>, +h: {CS.cf_fit_leaves(l <> t) == True{} : Bool}) -> {CS.cf_fit_leaves(t) == True{} : Bool}:
  match l:
    case Cf.Leaf{+p, o}:
      LLogicBool.wr_and_r(LawsBase.wire_fits(p), CS.cf_fit_leaves(t), h)

# a slot reads back, whatever follows it
def pfs.slot_rt(x: Cf.Slot, -t: List<&2, Cf.Slot>, +rest: String, +h: {CS.cf_fit_slots(x <> t) == True{} : Bool}) -> {Wr.Got{x, rest} == CS.cf_r_slot(CS.cf_w_slot(x, rest)) : Wr.Dec<Cf.Slot>}:
  match x:
    case Cf.Slot{+p, v}:
      match v:
        case Cf.Num{+n}:
          +hv = LLogicBool.wr_and_r(LawsBase.wire_fits(p), Bool.and(LawsBase.wire_fits(n), CS.cf_fit_slots(t)), h)
          %LWire.pw6.nat(p, Wr.put_nat(0n, Wr.put_nat(n, rest)), LLogicBool.wr_and_l(LawsBase.wire_fits(p), Bool.and(LawsBase.wire_fits(n), CS.cf_fit_slots(t)), h)) : {Wr.Got{Cf.Slot{p, Cf.Num{n}}, rest} == CS.cf_r_slot.p(_) : Wr.Dec<Cf.Slot>}
          %LWire.pw6.nat(0n, Wr.put_nat(n, rest), {==}) : {Wr.Got{Cf.Slot{p, Cf.Num{n}}, rest} == CS.cf_r_slot.v(p, _) : Wr.Dec<Cf.Slot>}
          %LWire.pw6.nat(n, rest, LLogicBool.wr_and_l(LawsBase.wire_fits(n), CS.cf_fit_slots(t), hv)) : {Wr.Got{Cf.Slot{p, Cf.Num{n}}, rest} == CS.cf_r_slot.num(p, _) : Wr.Dec<Cf.Slot>}
          {==}
        case Cf.Malformed{}:
          %LWire.pw6.nat(p, Wr.put_nat(1n, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(p), Bool.and(True{}, CS.cf_fit_slots(t)), h)) : {Wr.Got{Cf.Slot{p, Cf.Malformed{}}, rest} == CS.cf_r_slot.p(_) : Wr.Dec<Cf.Slot>}
          %LWire.pw6.nat(1n, rest, {==}) : {Wr.Got{Cf.Slot{p, Cf.Malformed{}}, rest} == CS.cf_r_slot.v(p, _) : Wr.Dec<Cf.Slot>}
          {==}

def pfs.slot_tail(x: Cf.Slot, +t: List<&2, Cf.Slot>, +h: {CS.cf_fit_slots(x <> t) == True{} : Bool}) -> {CS.cf_fit_slots(t) == True{} : Bool}:
  match x:
    case Cf.Slot{+p, +v}:
      LLogicBool.wr_and_r(CS.cf_fit_val(v), CS.cf_fit_slots(t), LLogicBool.wr_and_r(LawsBase.wire_fits(p), Bool.and(CS.cf_fit_val(v), CS.cf_fit_slots(t)), h))

# a key of a project document reads back, whatever follows it
def pfs.pkey_rt(x: Cf.PKey, -t: List<&2, Cf.PKey>, +rest: String, +h: {CS.cf_fit_pkeys(x <> t) == True{} : Bool}) -> {Wr.Got{x, rest} == CS.cf_r_pkey(CS.cf_w_pkey(x, rest)) : Wr.Dec<Cf.PKey>}:
  match x:
    case Cf.PKey{+k, +p, +v}:
      +h1 = LLogicBool.wr_and_r(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(List.length(&2, String, p)), Bool.and(CS.cf_fit_path(p), Bool.and(LawsBase.wire_fits(v), CS.cf_fit_pkeys(t)))), h)
      +h2 = LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, String, p)), Bool.and(CS.cf_fit_path(p), Bool.and(LawsBase.wire_fits(v), CS.cf_fit_pkeys(t))), h1)
      +h3 = LLogicBool.wr_and_r(CS.cf_fit_path(p), Bool.and(LawsBase.wire_fits(v), CS.cf_fit_pkeys(t)), h2)
      %LWire.pw6.nat(k, Wr.put_list(~String, ~Wr.put_str, p, Wr.put_nat(v, rest)), LLogicBool.wr_and_l(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(List.length(&2, String, p)), Bool.and(CS.cf_fit_path(p), Bool.and(LawsBase.wire_fits(v), CS.cf_fit_pkeys(t)))), h)) : {Wr.Got{Cf.PKey{k, p, v}, rest} == CS.cf_r_pkey.k(_) : Wr.Dec<Cf.PKey>}
      %pfs.path_rt(p, Wr.put_nat(v, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, String, p)), Bool.and(CS.cf_fit_path(p), Bool.and(LawsBase.wire_fits(v), CS.cf_fit_pkeys(t))), h1), LLogicBool.wr_and_l(CS.cf_fit_path(p), Bool.and(LawsBase.wire_fits(v), CS.cf_fit_pkeys(t)), h2)) : {Wr.Got{Cf.PKey{k, p, v}, rest} == CS.cf_r_pkey.p(k, _) : Wr.Dec<Cf.PKey>}
      %LWire.pw6.nat(v, rest, LLogicBool.wr_and_l(LawsBase.wire_fits(v), CS.cf_fit_pkeys(t), h3)) : {Wr.Got{Cf.PKey{k, p, v}, rest} == CS.cf_r_pkey.v(k, p, _) : Wr.Dec<Cf.PKey>}
      {==}

def pfs.pkey_tail(x: Cf.PKey, +t: List<&2, Cf.PKey>, +h: {CS.cf_fit_pkeys(x <> t) == True{} : Bool}) -> {CS.cf_fit_pkeys(t) == True{} : Bool}:
  match x:
    case Cf.PKey{+k, +p, +v}:
      +h1 = LLogicBool.wr_and_r(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(List.length(&2, String, p)), Bool.and(CS.cf_fit_path(p), Bool.and(LawsBase.wire_fits(v), CS.cf_fit_pkeys(t)))), h)
      +h2 = LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, String, p)), Bool.and(CS.cf_fit_path(p), Bool.and(LawsBase.wire_fits(v), CS.cf_fit_pkeys(t))), h1)
      +h3 = LLogicBool.wr_and_r(CS.cf_fit_path(p), Bool.and(LawsBase.wire_fits(v), CS.cf_fit_pkeys(t)), h2)
      LLogicBool.wr_and_r(LawsBase.wire_fits(v), CS.cf_fit_pkeys(t), h3)

# the entries t after x read back, x first
def pfs.entries_go_rt(t: List<&2, Cf.Entry>, +x: Cf.Entry, +rest: String, +h: {CS.cf_fit_entries.all(x <> t) == True{} : Bool}) -> {Wr.Got{x <> t, rest} == Wr.get_list.go(~Cf.Entry, ~CS.cf_r_entry, List.length(&2, Cf.Entry, t), CS.cf_r_entry(CS.cf_w_entry(x, CS.cf_w_entries.items(t, rest)))) : Wr.Dec<List<&2, Cf.Entry>>}:
  match t:
    case Nil{}:
      %pfs.entry_rt(x, Nil{}, rest, h) : {Wr.Got{[x], rest} == Wr.get_list.go(~Cf.Entry, ~CS.cf_r_entry, 0n, _) : Wr.Dec<List<&2, Cf.Entry>>}
      {==}
    case +y <> +u:
      %pfs.entry_rt(x, y <> u, CS.cf_w_entry(y, CS.cf_w_entries.items(u, rest)), h) : {Wr.Got{x <> y <> u, rest} == Wr.get_list.go(~Cf.Entry, ~CS.cf_r_entry, 1n+List.length(&2, Cf.Entry, u), _) : Wr.Dec<List<&2, Cf.Entry>>}
      %pfs.entries_go_rt(u, y, rest, pfs.entry_tail(x, y <> u, h)) : {Wr.Got{x <> y <> u, rest} == Wr.get_list.cons(Cf.Entry, x, _) : Wr.Dec<List<&2, Cf.Entry>>}
      {==}

def pfs.entries_items_rt(+xs: List<&2, Cf.Entry>, +rest: String, +h: {CS.cf_fit_entries.all(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list.start(~Cf.Entry, ~CS.cf_r_entry, Wr.Got{List.length(&2, Cf.Entry, xs), CS.cf_w_entries.items(xs, rest)}) : Wr.Dec<List<&2, Cf.Entry>>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +u:
      pfs.entries_go_rt(u, x, rest, h)

# entries that fit read back, whatever follows them
def pfs.entries_rt(+xs: List<&2, Cf.Entry>, +rest: String, +hl: {LawsBase.wire_fits(List.length(&2, Cf.Entry, xs)) == True{} : Bool}, +h: {CS.cf_fit_entries.all(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list(~Cf.Entry, ~CS.cf_r_entry, Wr.put_nat(List.length(&2, Cf.Entry, xs), CS.cf_w_entries.items(xs, rest))) : Wr.Dec<List<&2, Cf.Entry>>}:
  %LWire.pw6.nat(List.length(&2, Cf.Entry, xs), CS.cf_w_entries.items(xs, rest), hl) : {Wr.Got{xs, rest} == Wr.get_list.start(~Cf.Entry, ~CS.cf_r_entry, _) : Wr.Dec<List<&2, Cf.Entry>>}
  pfs.entries_items_rt(xs, rest, h)

# a named entry reads back, whatever follows it
def pfs.named_rt(x: Cf.Named, -t: List<&2, Cf.Named>, +rest: String, +h: {CS.cf_fit_nameds(x <> t) == True{} : Bool}) -> {Wr.Got{x, rest} == CS.cf_r_named(CS.cf_w_named(x, rest)) : Wr.Dec<Cf.Named>}:
  match x:
    case Cf.Named{+n, +fs}:
      +h1 = LLogicBool.wr_and_r(LawsBase.wire_fits(n), Bool.and(CS.cf_fit_entries(fs), CS.cf_fit_nameds(t)), h)
      +hf = LLogicBool.wr_and_l(CS.cf_fit_entries(fs), CS.cf_fit_nameds(t), h1)
      %LWire.pw6.nat(n, CS.cf_w_entries(fs, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(n), Bool.and(CS.cf_fit_entries(fs), CS.cf_fit_nameds(t)), h)) : {Wr.Got{Cf.Named{n, fs}, rest} == CS.cf_r_named.n(_) : Wr.Dec<Cf.Named>}
      %pfs.entries_rt(fs, rest, LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Cf.Entry, fs)), CS.cf_fit_entries.all(fs), hf), LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Cf.Entry, fs)), CS.cf_fit_entries.all(fs), hf)) : {Wr.Got{Cf.Named{n, fs}, rest} == CS.cf_r_named.fs(n, _) : Wr.Dec<Cf.Named>}
      {==}

def pfs.named_tail(x: Cf.Named, +t: List<&2, Cf.Named>, +h: {CS.cf_fit_nameds(x <> t) == True{} : Bool}) -> {CS.cf_fit_nameds(t) == True{} : Bool}:
  match x:
    case Cf.Named{+n, +fs}:
      LLogicBool.wr_and_r(CS.cf_fit_entries(fs), CS.cf_fit_nameds(t), LLogicBool.wr_and_r(LawsBase.wire_fits(n), Bool.and(CS.cf_fit_entries(fs), CS.cf_fit_nameds(t)), h))

# the leaves t after x read back, x first
def pfs.leaves_go_rt(t: List<&2, Cf.Leaf>, +x: Cf.Leaf, +rest: String, +h: {CS.cf_fit_leaves(x <> t) == True{} : Bool}) -> {Wr.Got{x <> t, rest} == Wr.get_list.go(~Cf.Leaf, ~CS.cf_r_leaf, List.length(&2, Cf.Leaf, t), CS.cf_r_leaf(CS.cf_w_leaf(x, CS.cf_w_leaves(t, rest)))) : Wr.Dec<List<&2, Cf.Leaf>>}:
  match t:
    case Nil{}:
      %pfs.leaf_rt(x, Nil{}, rest, h) : {Wr.Got{[x], rest} == Wr.get_list.go(~Cf.Leaf, ~CS.cf_r_leaf, 0n, _) : Wr.Dec<List<&2, Cf.Leaf>>}
      {==}
    case +y <> +u:
      %pfs.leaf_rt(x, y <> u, CS.cf_w_leaf(y, CS.cf_w_leaves(u, rest)), h) : {Wr.Got{x <> y <> u, rest} == Wr.get_list.go(~Cf.Leaf, ~CS.cf_r_leaf, 1n+List.length(&2, Cf.Leaf, u), _) : Wr.Dec<List<&2, Cf.Leaf>>}
      %pfs.leaves_go_rt(u, y, rest, pfs.leaf_tail(x, y <> u, h)) : {Wr.Got{x <> y <> u, rest} == Wr.get_list.cons(Cf.Leaf, x, _) : Wr.Dec<List<&2, Cf.Leaf>>}
      {==}

def pfs.leaves_items_rt(+xs: List<&2, Cf.Leaf>, +rest: String, +h: {CS.cf_fit_leaves(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list.start(~Cf.Leaf, ~CS.cf_r_leaf, Wr.Got{List.length(&2, Cf.Leaf, xs), CS.cf_w_leaves(xs, rest)}) : Wr.Dec<List<&2, Cf.Leaf>>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +u:
      pfs.leaves_go_rt(u, x, rest, h)

# leaves that fit read back, whatever follows them
def pfs.leaves_rt(+xs: List<&2, Cf.Leaf>, +rest: String, +hl: {LawsBase.wire_fits(List.length(&2, Cf.Leaf, xs)) == True{} : Bool}, +h: {CS.cf_fit_leaves(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list(~Cf.Leaf, ~CS.cf_r_leaf, Wr.put_nat(List.length(&2, Cf.Leaf, xs), CS.cf_w_leaves(xs, rest))) : Wr.Dec<List<&2, Cf.Leaf>>}:
  %LWire.pw6.nat(List.length(&2, Cf.Leaf, xs), CS.cf_w_leaves(xs, rest), hl) : {Wr.Got{xs, rest} == Wr.get_list.start(~Cf.Leaf, ~CS.cf_r_leaf, _) : Wr.Dec<List<&2, Cf.Leaf>>}
  pfs.leaves_items_rt(xs, rest, h)

# the slots t after x read back, x first
def pfs.slots_go_rt(t: List<&2, Cf.Slot>, +x: Cf.Slot, +rest: String, +h: {CS.cf_fit_slots(x <> t) == True{} : Bool}) -> {Wr.Got{x <> t, rest} == Wr.get_list.go(~Cf.Slot, ~CS.cf_r_slot, List.length(&2, Cf.Slot, t), CS.cf_r_slot(CS.cf_w_slot(x, CS.cf_w_slots(t, rest)))) : Wr.Dec<List<&2, Cf.Slot>>}:
  match t:
    case Nil{}:
      %pfs.slot_rt(x, Nil{}, rest, h) : {Wr.Got{[x], rest} == Wr.get_list.go(~Cf.Slot, ~CS.cf_r_slot, 0n, _) : Wr.Dec<List<&2, Cf.Slot>>}
      {==}
    case +y <> +u:
      %pfs.slot_rt(x, y <> u, CS.cf_w_slot(y, CS.cf_w_slots(u, rest)), h) : {Wr.Got{x <> y <> u, rest} == Wr.get_list.go(~Cf.Slot, ~CS.cf_r_slot, 1n+List.length(&2, Cf.Slot, u), _) : Wr.Dec<List<&2, Cf.Slot>>}
      %pfs.slots_go_rt(u, y, rest, pfs.slot_tail(x, y <> u, h)) : {Wr.Got{x <> y <> u, rest} == Wr.get_list.cons(Cf.Slot, x, _) : Wr.Dec<List<&2, Cf.Slot>>}
      {==}

def pfs.slots_items_rt(+xs: List<&2, Cf.Slot>, +rest: String, +h: {CS.cf_fit_slots(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list.start(~Cf.Slot, ~CS.cf_r_slot, Wr.Got{List.length(&2, Cf.Slot, xs), CS.cf_w_slots(xs, rest)}) : Wr.Dec<List<&2, Cf.Slot>>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +u:
      pfs.slots_go_rt(u, x, rest, h)

# slots that fit read back, whatever follows them
def pfs.slots_rt(+xs: List<&2, Cf.Slot>, +rest: String, +hl: {LawsBase.wire_fits(List.length(&2, Cf.Slot, xs)) == True{} : Bool}, +h: {CS.cf_fit_slots(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list(~Cf.Slot, ~CS.cf_r_slot, Wr.put_nat(List.length(&2, Cf.Slot, xs), CS.cf_w_slots(xs, rest))) : Wr.Dec<List<&2, Cf.Slot>>}:
  %LWire.pw6.nat(List.length(&2, Cf.Slot, xs), CS.cf_w_slots(xs, rest), hl) : {Wr.Got{xs, rest} == Wr.get_list.start(~Cf.Slot, ~CS.cf_r_slot, _) : Wr.Dec<List<&2, Cf.Slot>>}
  pfs.slots_items_rt(xs, rest, h)

# the pkeys t after x read back, x first
def pfs.pkeys_go_rt(t: List<&2, Cf.PKey>, +x: Cf.PKey, +rest: String, +h: {CS.cf_fit_pkeys(x <> t) == True{} : Bool}) -> {Wr.Got{x <> t, rest} == Wr.get_list.go(~Cf.PKey, ~CS.cf_r_pkey, List.length(&2, Cf.PKey, t), CS.cf_r_pkey(CS.cf_w_pkey(x, CS.cf_w_pkeys(t, rest)))) : Wr.Dec<List<&2, Cf.PKey>>}:
  match t:
    case Nil{}:
      %pfs.pkey_rt(x, Nil{}, rest, h) : {Wr.Got{[x], rest} == Wr.get_list.go(~Cf.PKey, ~CS.cf_r_pkey, 0n, _) : Wr.Dec<List<&2, Cf.PKey>>}
      {==}
    case +y <> +u:
      %pfs.pkey_rt(x, y <> u, CS.cf_w_pkey(y, CS.cf_w_pkeys(u, rest)), h) : {Wr.Got{x <> y <> u, rest} == Wr.get_list.go(~Cf.PKey, ~CS.cf_r_pkey, 1n+List.length(&2, Cf.PKey, u), _) : Wr.Dec<List<&2, Cf.PKey>>}
      %pfs.pkeys_go_rt(u, y, rest, pfs.pkey_tail(x, y <> u, h)) : {Wr.Got{x <> y <> u, rest} == Wr.get_list.cons(Cf.PKey, x, _) : Wr.Dec<List<&2, Cf.PKey>>}
      {==}

def pfs.pkeys_items_rt(+xs: List<&2, Cf.PKey>, +rest: String, +h: {CS.cf_fit_pkeys(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list.start(~Cf.PKey, ~CS.cf_r_pkey, Wr.Got{List.length(&2, Cf.PKey, xs), CS.cf_w_pkeys(xs, rest)}) : Wr.Dec<List<&2, Cf.PKey>>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +u:
      pfs.pkeys_go_rt(u, x, rest, h)

# pkeys that fit read back, whatever follows them
def pfs.pkeys_rt(+xs: List<&2, Cf.PKey>, +rest: String, +hl: {LawsBase.wire_fits(List.length(&2, Cf.PKey, xs)) == True{} : Bool}, +h: {CS.cf_fit_pkeys(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list(~Cf.PKey, ~CS.cf_r_pkey, Wr.put_nat(List.length(&2, Cf.PKey, xs), CS.cf_w_pkeys(xs, rest))) : Wr.Dec<List<&2, Cf.PKey>>}:
  %LWire.pw6.nat(List.length(&2, Cf.PKey, xs), CS.cf_w_pkeys(xs, rest), hl) : {Wr.Got{xs, rest} == Wr.get_list.start(~Cf.PKey, ~CS.cf_r_pkey, _) : Wr.Dec<List<&2, Cf.PKey>>}
  pfs.pkeys_items_rt(xs, rest, h)

# the nameds t after x read back, x first
def pfs.nameds_go_rt(t: List<&2, Cf.Named>, +x: Cf.Named, +rest: String, +h: {CS.cf_fit_nameds(x <> t) == True{} : Bool}) -> {Wr.Got{x <> t, rest} == Wr.get_list.go(~Cf.Named, ~CS.cf_r_named, List.length(&2, Cf.Named, t), CS.cf_r_named(CS.cf_w_named(x, CS.cf_w_nameds(t, rest)))) : Wr.Dec<List<&2, Cf.Named>>}:
  match t:
    case Nil{}:
      %pfs.named_rt(x, Nil{}, rest, h) : {Wr.Got{[x], rest} == Wr.get_list.go(~Cf.Named, ~CS.cf_r_named, 0n, _) : Wr.Dec<List<&2, Cf.Named>>}
      {==}
    case +y <> +u:
      %pfs.named_rt(x, y <> u, CS.cf_w_named(y, CS.cf_w_nameds(u, rest)), h) : {Wr.Got{x <> y <> u, rest} == Wr.get_list.go(~Cf.Named, ~CS.cf_r_named, 1n+List.length(&2, Cf.Named, u), _) : Wr.Dec<List<&2, Cf.Named>>}
      %pfs.nameds_go_rt(u, y, rest, pfs.named_tail(x, y <> u, h)) : {Wr.Got{x <> y <> u, rest} == Wr.get_list.cons(Cf.Named, x, _) : Wr.Dec<List<&2, Cf.Named>>}
      {==}

def pfs.nameds_items_rt(+xs: List<&2, Cf.Named>, +rest: String, +h: {CS.cf_fit_nameds(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list.start(~Cf.Named, ~CS.cf_r_named, Wr.Got{List.length(&2, Cf.Named, xs), CS.cf_w_nameds(xs, rest)}) : Wr.Dec<List<&2, Cf.Named>>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +u:
      pfs.nameds_go_rt(u, x, rest, h)

# nameds that fit read back, whatever follows them
def pfs.nameds_rt(+xs: List<&2, Cf.Named>, +rest: String, +hl: {LawsBase.wire_fits(List.length(&2, Cf.Named, xs)) == True{} : Bool}, +h: {CS.cf_fit_nameds(xs) == True{} : Bool}) -> {Wr.Got{xs, rest} == Wr.get_list(~Cf.Named, ~CS.cf_r_named, Wr.put_nat(List.length(&2, Cf.Named, xs), CS.cf_w_nameds(xs, rest))) : Wr.Dec<List<&2, Cf.Named>>}:
  %LWire.pw6.nat(List.length(&2, Cf.Named, xs), CS.cf_w_nameds(xs, rest), hl) : {Wr.Got{xs, rest} == Wr.get_list.start(~Cf.Named, ~CS.cf_r_named, _) : Wr.Dec<List<&2, Cf.Named>>}
  pfs.nameds_items_rt(xs, rest, h)

# Requests
# --------

# a read reads back, whatever follows it
def pfs.read_rt(r: Cf.Read, +rest: String, +h: {CS.cf_fit_read(r) == True{} : Bool}) -> {Wr.Got{r, rest} == CS.cf_r_read(Wr.get_nat(CS.cf_w_read(r, rest))) : Wr.Dec<Cf.Read>}:
  match r:
    case Cf.Missing{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{Cf.Missing{}, rest} == CS.cf_r_read(_) : Wr.Dec<Cf.Read>}
      {==}
    case Cf.Parsed{+d}:
      %LWire.pw6.nat(1n, CS.cf_w_entries(d, rest), {==}) : {Wr.Got{Cf.Parsed{d}, rest} == CS.cf_r_read(_) : Wr.Dec<Cf.Read>}
      %pfs.entries_rt(d, rest, LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Cf.Entry, d)), CS.cf_fit_entries.all(d), h), LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Cf.Entry, d)), CS.cf_fit_entries.all(d), h)) : {Wr.Got{Cf.Parsed{d}, rest} == CS.cf_r_read.parsed(_) : Wr.Dec<Cf.Read>}
      {==}
    case Cf.Broken{}:
      %LWire.pw6.nat(2n, rest, {==}) : {Wr.Got{Cf.Broken{}, rest} == CS.cf_r_read(_) : Wr.Dec<Cf.Read>}
      {==}

# an edit reads back
def pfs.edit_rt(e: Cf.Edit, +h: {CS.cf_fit_edit(e) == True{} : Bool}) -> {Wr.Got{e, ""} == CS.cf_r_edit(Wr.get_nat(CS.cf_w_edit(e))) : Wr.Dec<Cf.Edit>}:
  match e:
    case Cf.Set{+k, +v}:
      %LWire.pw6.nat(0n, Wr.put_nat(k, Wr.put_nat(v, "")), {==}) : {Wr.Got{Cf.Set{k, v}, ""} == CS.cf_r_edit(_) : Wr.Dec<Cf.Edit>}
      %LWire.pw6.nat(k, Wr.put_nat(v, ""), LLogicBool.wr_and_l(LawsBase.wire_fits(k), LawsBase.wire_fits(v), h)) : {Wr.Got{Cf.Set{k, v}, ""} == CS.cf_r_edit.setk(_) : Wr.Dec<Cf.Edit>}
      %LWire.pw6.nat(v, "", LLogicBool.wr_and_r(LawsBase.wire_fits(k), LawsBase.wire_fits(v), h)) : {Wr.Got{Cf.Set{k, v}, ""} == CS.cf_r_edit.set(k, _) : Wr.Dec<Cf.Edit>}
      {==}
    case Cf.Del{+k}:
      %LWire.pw6.nat(1n, Wr.put_nat(k, ""), {==}) : {Wr.Got{Cf.Del{k}, ""} == CS.cf_r_edit(_) : Wr.Dec<Cf.Edit>}
      %LWire.pw6.nat(k, "", h) : {Wr.Got{Cf.Del{k}, ""} == CS.cf_r_edit.del(_) : Wr.Dec<Cf.Edit>}
      {==}

# providerMaxInFlight as written reads back, whatever follows it
def pfs.inflight_rt(s: Cf.InFlight, +rest: String, +h: {CS.cf_fit_inflight(s) == True{} : Bool}) -> {Wr.Got{s, rest} == CS.cf_r_inflight(Wr.get_nat(CS.cf_w_inflight(s, rest))) : Wr.Dec<Cf.InFlight>}:
  match s:
    case Cf.Unset{}:
      %LWire.pw6.nat(0n, rest, {==}) : {Wr.Got{Cf.Unset{}, rest} == CS.cf_r_inflight(_) : Wr.Dec<Cf.InFlight>}
      {==}
    case Cf.Entries{+es}:
      %LWire.pw6.nat(1n, Wr.put_nat(List.length(&2, Cf.Slot, es), CS.cf_w_slots(es, rest)), {==}) : {Wr.Got{Cf.Entries{es}, rest} == CS.cf_r_inflight(_) : Wr.Dec<Cf.InFlight>}
      %pfs.slots_rt(es, rest, LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Cf.Slot, es)), CS.cf_fit_slots(es), h), LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Cf.Slot, es)), CS.cf_fit_slots(es), h)) : {Wr.Got{Cf.Entries{es}, rest} == CS.cf_r_inflight.map(_) : Wr.Dec<Cf.InFlight>}
      {==}
    case Cf.NotMap{}:
      %LWire.pw6.nat(2n, rest, {==}) : {Wr.Got{Cf.NotMap{}, rest} == CS.cf_r_inflight(_) : Wr.Dec<Cf.InFlight>}
      {==}

# a list of numbers that fits reads back
def pfs.qs_rt(+qs: List<&2, Nat>, +h: {CS.cf_fit_qs(qs) == True{} : Bool}) -> {Wr.Got{qs, ""} == Wr.get_list(~Nat, ~Wr.get_nat, CS.cf_w_qs(qs)) : Wr.Dec<List<&2, Nat>>}:
  Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, qs, "")), Wr.Got{qs, ""}, Wire.wire_list_round_trip(qs, "", h))

def pfs.trust_rt(t: Cf.Trust, +ks: List<&2, Cf.PKey>, +hl: {LawsBase.wire_fits(List.length(&2, Cf.PKey, ks)) == True{} : Bool}, +hk: {CS.cf_fit_pkeys(ks) == True{} : Bool}) -> {Wr.Got{FC.AskTrust{t, ks}, ""} == CS.cf_r_ask(Wr.get_nat(CS.cf_w_ask(FC.AskTrust{t, ks}))) : Wr.Dec<FC.Ask>}:
  match t:
    case Cf.Trusted{}:
      %LWire.pw6.nat(3n, Wr.put_nat(0n, Wr.put_nat(List.length(&2, Cf.PKey, ks), CS.cf_w_pkeys(ks, ""))), {==}) : {Wr.Got{FC.AskTrust{Cf.Trusted{}, ks}, ""} == CS.cf_r_ask(_) : Wr.Dec<FC.Ask>}
      %LWire.pw6.nat(0n, Wr.put_nat(List.length(&2, Cf.PKey, ks), CS.cf_w_pkeys(ks, "")), {==}) : {Wr.Got{FC.AskTrust{Cf.Trusted{}, ks}, ""} == CS.cf_r_trust(_) : Wr.Dec<FC.Ask>}
      %pfs.pkeys_rt(ks, "", hl, hk) : {Wr.Got{FC.AskTrust{Cf.Trusted{}, ks}, ""} == CS.cf_r_trust.ks(Cf.Trusted{}, _) : Wr.Dec<FC.Ask>}
      {==}
    case Cf.Untrusted{}:
      %LWire.pw6.nat(3n, Wr.put_nat(1n, Wr.put_nat(List.length(&2, Cf.PKey, ks), CS.cf_w_pkeys(ks, ""))), {==}) : {Wr.Got{FC.AskTrust{Cf.Untrusted{}, ks}, ""} == CS.cf_r_ask(_) : Wr.Dec<FC.Ask>}
      %LWire.pw6.nat(1n, Wr.put_nat(List.length(&2, Cf.PKey, ks), CS.cf_w_pkeys(ks, "")), {==}) : {Wr.Got{FC.AskTrust{Cf.Untrusted{}, ks}, ""} == CS.cf_r_trust(_) : Wr.Dec<FC.Ask>}
      %pfs.pkeys_rt(ks, "", hl, hk) : {Wr.Got{FC.AskTrust{Cf.Untrusted{}, ks}, ""} == CS.cf_r_trust.ks(Cf.Untrusted{}, _) : Wr.Dec<FC.Ask>}
      {==}

# every request that fits reads back whole
def pfs.ask_rt(a: FC.Ask, +h: {CS.cf_fit_ask(a) == True{} : Bool}) -> {Wr.Got{a, ""} == CS.cf_r_ask(Wr.get_nat(CS.cf_w_ask(a))) : Wr.Dec<FC.Ask>}:
  match a:
    case FC.AskRmw{+r, +e}:
      %LWire.pw6.nat(0n, CS.cf_w_read(r, CS.cf_w_edit(e)), {==}) : {Wr.Got{FC.AskRmw{r, e}, ""} == CS.cf_r_ask(_) : Wr.Dec<FC.Ask>}
      %pfs.read_rt(r, CS.cf_w_edit(e), LLogicBool.wr_and_l(CS.cf_fit_read(r), CS.cf_fit_edit(e), h)) : {Wr.Got{FC.AskRmw{r, e}, ""} == CS.cf_r_rmw(_) : Wr.Dec<FC.Ask>}
      %pfs.edit_rt(e, LLogicBool.wr_and_r(CS.cf_fit_read(r), CS.cf_fit_edit(e), h)) : {Wr.Got{FC.AskRmw{r, e}, ""} == CS.cf_r_rmw.e(r, _) : Wr.Dec<FC.Ask>}
      {==}
    case FC.AskLeaves{+ls}:
      %LWire.pw6.nat(1n, Wr.put_nat(List.length(&2, Cf.Leaf, ls), CS.cf_w_leaves(ls, "")), {==}) : {Wr.Got{FC.AskLeaves{ls}, ""} == CS.cf_r_ask(_) : Wr.Dec<FC.Ask>}
      %pfs.leaves_rt(ls, "", LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Cf.Leaf, ls)), CS.cf_fit_leaves(ls), h), LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Cf.Leaf, ls)), CS.cf_fit_leaves(ls), h)) : {Wr.Got{FC.AskLeaves{ls}, ""} == CS.cf_r_leaves(_) : Wr.Dec<FC.Ask>}
      {==}
    case FC.AskLimits{+s, +qs}:
      %LWire.pw6.nat(2n, CS.cf_w_inflight(s, CS.cf_w_qs(qs)), {==}) : {Wr.Got{FC.AskLimits{s, qs}, ""} == CS.cf_r_ask(_) : Wr.Dec<FC.Ask>}
      %pfs.inflight_rt(s, CS.cf_w_qs(qs), LLogicBool.wr_and_l(CS.cf_fit_inflight(s), CS.cf_fit_qs(qs), h)) : {Wr.Got{FC.AskLimits{s, qs}, ""} == CS.cf_r_limits(_) : Wr.Dec<FC.Ask>}
      %pfs.qs_rt(qs, LLogicBool.wr_and_r(CS.cf_fit_inflight(s), CS.cf_fit_qs(qs), h)) : {Wr.Got{FC.AskLimits{s, qs}, ""} == CS.cf_r_limits.qs(s, _) : Wr.Dec<FC.Ask>}
      {==}
    case FC.AskTrust{t, +ks}:
      pfs.trust_rt(t, ks, LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Cf.PKey, ks)), CS.cf_fit_pkeys(ks), h), LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Cf.PKey, ks)), CS.cf_fit_pkeys(ks), h))
    case FC.AskMerge{+g, +p, +qs}:
      +h1 = LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Cf.Named, g)), Bool.and(CS.cf_fit_nameds(g), Bool.and(LawsBase.wire_fits(List.length(&2, Cf.Named, p)), Bool.and(CS.cf_fit_nameds(p), CS.cf_fit_qs(qs)))), h)
      +h2 = LLogicBool.wr_and_r(CS.cf_fit_nameds(g), Bool.and(LawsBase.wire_fits(List.length(&2, Cf.Named, p)), Bool.and(CS.cf_fit_nameds(p), CS.cf_fit_qs(qs))), h1)
      +h3 = LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Cf.Named, p)), Bool.and(CS.cf_fit_nameds(p), CS.cf_fit_qs(qs)), h2)
      +X = Wr.put_nat(List.length(&2, Cf.Named, p), CS.cf_w_nameds(p, CS.cf_w_qs(qs)))
      %LWire.pw6.nat(4n, Wr.put_nat(List.length(&2, Cf.Named, g), CS.cf_w_nameds(g, X)), {==}) : {Wr.Got{FC.AskMerge{g, p, qs}, ""} == CS.cf_r_ask(_) : Wr.Dec<FC.Ask>}
      %pfs.nameds_rt(g, X, LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Cf.Named, g)), Bool.and(CS.cf_fit_nameds(g), Bool.and(LawsBase.wire_fits(List.length(&2, Cf.Named, p)), Bool.and(CS.cf_fit_nameds(p), CS.cf_fit_qs(qs)))), h), LLogicBool.wr_and_l(CS.cf_fit_nameds(g), Bool.and(LawsBase.wire_fits(List.length(&2, Cf.Named, p)), Bool.and(CS.cf_fit_nameds(p), CS.cf_fit_qs(qs))), h1)) : {Wr.Got{FC.AskMerge{g, p, qs}, ""} == CS.cf_r_merge(_) : Wr.Dec<FC.Ask>}
      %pfs.nameds_rt(p, CS.cf_w_qs(qs), LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Cf.Named, p)), Bool.and(CS.cf_fit_nameds(p), CS.cf_fit_qs(qs)), h2), LLogicBool.wr_and_l(CS.cf_fit_nameds(p), CS.cf_fit_qs(qs), h3)) : {Wr.Got{FC.AskMerge{g, p, qs}, ""} == CS.cf_r_merge.p(g, _) : Wr.Dec<FC.Ask>}
      %pfs.qs_rt(qs, LLogicBool.wr_and_r(CS.cf_fit_nameds(p), CS.cf_fit_qs(qs), h3)) : {Wr.Got{FC.AskMerge{g, p, qs}, ""} == CS.cf_r_merge.qs(g, p, _) : Wr.Dec<FC.Ask>}
      {==}
