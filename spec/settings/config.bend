# config (spec): the spec helpers of the laws of area config
# (laws/config.bend): independent restatements of what the config rules
# decide (bend/config.bend), and the wire spellers, reader and bounds of
# its entry (bend/ffi_config.bend). A spec: the shipped code never calls
# it.

import Base
import ../../bend/config.bend as Cf
import ../../bend/ffi_config.bend as FC
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
# Spellers: a request as Rust writes it

def cf_w_entry(e: Cf.Entry, rest: String) -> String:
  match e:
    case Cf.Entry{k, v}:
      Wr.put_nat(k, Wr.put_nat(v, rest))

def cf_w_entries.items(d: List<&2, Cf.Entry>, rest: String) -> String:
  match d:
    case Nil{}:
      rest
    case e <> t:
      cf_w_entry(e, cf_w_entries.items(t, rest))

def cf_w_entries(+d: List<&2, Cf.Entry>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Cf.Entry, d), cf_w_entries.items(d, rest))

def cf_w_leaf(l: Cf.Leaf, rest: String) -> String:
  match l:
    case Cf.Leaf{p, o}:
      match o:
        case Cf.Good{}:
          Wr.put_nat(p, Wr.put_nat(0n, rest))
        case Cf.BadType{}:
          Wr.put_nat(p, Wr.put_nat(1n, rest))
        case Cf.Undeclared{}:
          Wr.put_nat(p, Wr.put_nat(2n, rest))

def cf_w_leaves(ls: List<&2, Cf.Leaf>, rest: String) -> String:
  match ls:
    case Nil{}:
      rest
    case l <> t:
      cf_w_leaf(l, cf_w_leaves(t, rest))

def cf_w_slot(x: Cf.Slot, rest: String) -> String:
  match x:
    case Cf.Slot{p, v}:
      match v:
        case Cf.Num{n}:
          Wr.put_nat(p, Wr.put_nat(0n, Wr.put_nat(n, rest)))
        case Cf.Malformed{}:
          Wr.put_nat(p, Wr.put_nat(1n, rest))

def cf_w_slots(xs: List<&2, Cf.Slot>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      cf_w_slot(x, cf_w_slots(t, rest))

def cf_w_pkey(x: Cf.PKey, rest: String) -> String:
  match x:
    case Cf.PKey{k, p, v}:
      Wr.put_nat(k, Wr.put_list(~String, ~Wr.put_str, p, Wr.put_nat(v, rest)))

def cf_w_pkeys(xs: List<&2, Cf.PKey>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      cf_w_pkey(x, cf_w_pkeys(t, rest))

def cf_w_named(x: Cf.Named, rest: String) -> String:
  match x:
    case Cf.Named{n, fs}:
      Wr.put_nat(n, cf_w_entries(fs, rest))

def cf_w_nameds(xs: List<&2, Cf.Named>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      cf_w_named(x, cf_w_nameds(t, rest))

def cf_w_read(r: Cf.Read, rest: String) -> String:
  match r:
    case Cf.Missing{}:
      Wr.put_nat(0n, rest)
    case Cf.Parsed{d}:
      Wr.put_nat(1n, cf_w_entries(d, rest))
    case Cf.Broken{}:
      Wr.put_nat(2n, rest)

def cf_w_edit(e: Cf.Edit) -> String:
  match e:
    case Cf.Set{k, v}:
      Wr.put_nat(0n, Wr.put_nat(k, Wr.put_nat(v, "")))
    case Cf.Del{k}:
      Wr.put_nat(1n, Wr.put_nat(k, ""))

def cf_w_inflight(s: Cf.InFlight, rest: String) -> String:
  match s:
    case Cf.Unset{}:
      Wr.put_nat(0n, rest)
    case Cf.Entries{+es}:
      Wr.put_nat(1n, Wr.put_nat(List.length(&2, Cf.Slot, es), cf_w_slots(es, rest)))
    case Cf.NotMap{}:
      Wr.put_nat(2n, rest)

def cf_w_trust(t: Cf.Trust) -> Nat:
  match t:
    case Cf.Trusted{}:
      0n
    case Cf.Untrusted{}:
      1n

def cf_w_qs(qs: List<&2, Nat>) -> String:
  Wr.put_list(~Nat, ~Wr.put_nat, qs, "")

# a request, as Rust writes it
def cf_w_ask(a: FC.Ask) -> String:
  match a:
    case FC.AskRmw{r, e}:
      Wr.put_nat(0n, cf_w_read(r, cf_w_edit(e)))
    case FC.AskLeaves{+ls}:
      Wr.put_nat(1n, Wr.put_nat(List.length(&2, Cf.Leaf, ls), cf_w_leaves(ls, "")))
    case FC.AskLimits{s, qs}:
      Wr.put_nat(2n, cf_w_inflight(s, cf_w_qs(qs)))
    case FC.AskTrust{t, +ks}:
      Wr.put_nat(3n, Wr.put_nat(cf_w_trust(t), Wr.put_nat(List.length(&2, Cf.PKey, ks), cf_w_pkeys(ks, ""))))
    case FC.AskMerge{+g, +p, qs}:
      Wr.put_nat(4n, Wr.put_nat(List.length(&2, Cf.Named, g), cf_w_nameds(g, Wr.put_nat(List.length(&2, Cf.Named, p), cf_w_nameds(p, cf_w_qs(qs))))))

# Spellers: the reply, as Rust reads it

def cf_w_write(w: Cf.Write) -> String:
  match w:
    case Cf.Refused{}:
      Wr.put_nat(0n, "")
    case Cf.Wrote{d}:
      Wr.put_nat(1n, cf_w_entries(d, ""))

def cf_w_lims(ls: List<&2, Cf.Lim>, rest: String) -> String:
  match ls:
    case Nil{}:
      rest
    case l <> t:
      match l:
        case Cf.Unlimited{}:
          Wr.put_nat(0n, cf_w_lims(t, rest))
        case Cf.Cap{n}:
          Wr.put_nat(1n, Wr.put_nat(n, cf_w_lims(t, rest)))

def cf_w_founds(ms: List<&2, Maybe<&2, List<&2, Cf.Entry>>>, rest: String) -> String:
  match ms:
    case Nil{}:
      rest
    case m <> t:
      match m:
        case None{}:
          Wr.put_nat(0n, cf_w_founds(t, rest))
        case Some{fs}:
          Wr.put_nat(1n, cf_w_entries(fs, cf_w_founds(t, rest)))

def cf_w_limits(+ls: List<&2, Cf.Lim>) -> String:
  Wr.put_nat(List.length(&2, Cf.Lim, ls), cf_w_lims(ls, ""))

def cf_w_merged(+ms: List<&2, Maybe<&2, List<&2, Cf.Entry>>>) -> String:
  Wr.put_nat(List.length(&2, Maybe<&2, List<&2, Cf.Entry>>, ms), cf_w_founds(ms, ""))

# the reply to a request: the model's decision, spelled as Rust reads it
def cf_w_reply(a: FC.Ask) -> String:
  match a:
    case FC.AskRmw{r, e}:
      cf_w_write(Cf.rmw(r, e))
    case FC.AskLeaves{+ls}:
      Wr.put_list(~Nat, ~Wr.put_nat, Cf.applied(ls), Wr.put_list(~Nat, ~Wr.put_nat, Cf.reported(ls), ""))
    case FC.AskLimits{s, qs}:
      cf_w_limits(Cf.limits(s, qs))
    case FC.AskTrust{+t, +ks}:
      cf_w_entries(Cf.project(t, Nil{}, ks), Wr.put_list(~String, ~Wr.put_str, Cf.withheld(t, ks), ""))
    case FC.AskMerge{g, p, qs}:
      cf_w_merged(Cf.finds(Cf.merge(g, p), qs))

# what fits the wire: every Nat, length and count of a request
def cf_fit_entries.all(d: List<&2, Cf.Entry>) -> Bool:
  match d:
    case Nil{}:
      True{}
    case e <> t:
      match e:
        case Cf.Entry{k, v}:
          Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(v), cf_fit_entries.all(t)))

def cf_fit_entries(+d: List<&2, Cf.Entry>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Cf.Entry, d)), cf_fit_entries.all(d))

def cf_fit_leaves(ls: List<&2, Cf.Leaf>) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case l <> t:
      match l:
        case Cf.Leaf{p, o}:
          Bool.and(LawsBase.wire_fits(p), cf_fit_leaves(t))

def cf_fit_val(v: Cf.Val) -> Bool:
  match v:
    case Cf.Num{n}:
      LawsBase.wire_fits(n)
    case Cf.Malformed{}:
      True{}

def cf_fit_slots(xs: List<&2, Cf.Slot>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      match x:
        case Cf.Slot{p, v}:
          Bool.and(LawsBase.wire_fits(p), Bool.and(cf_fit_val(v), cf_fit_slots(t)))

def cf_fit_path(p: List<&2, String>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case +n <> t:
      Bool.and(LawsBase.wire_fits(String.length(n)), cf_fit_path(t))

def cf_fit_pkeys(xs: List<&2, Cf.PKey>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      match x:
        case Cf.PKey{k, +p, v}:
          Bool.and(LawsBase.wire_fits(k), Bool.and(LawsBase.wire_fits(List.length(&2, String, p)), Bool.and(cf_fit_path(p), Bool.and(LawsBase.wire_fits(v), cf_fit_pkeys(t)))))

def cf_fit_nameds(xs: List<&2, Cf.Named>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      match x:
        case Cf.Named{n, fs}:
          Bool.and(LawsBase.wire_fits(n), Bool.and(cf_fit_entries(fs), cf_fit_nameds(t)))

def cf_fit_read(r: Cf.Read) -> Bool:
  match r:
    case Cf.Missing{}:
      True{}
    case Cf.Parsed{d}:
      cf_fit_entries(d)
    case Cf.Broken{}:
      True{}

def cf_fit_edit(e: Cf.Edit) -> Bool:
  match e:
    case Cf.Set{k, v}:
      Bool.and(LawsBase.wire_fits(k), LawsBase.wire_fits(v))
    case Cf.Del{k}:
      LawsBase.wire_fits(k)

def cf_fit_inflight(s: Cf.InFlight) -> Bool:
  match s:
    case Cf.Unset{}:
      True{}
    case Cf.Entries{+es}:
      Bool.and(LawsBase.wire_fits(List.length(&2, Cf.Slot, es)), cf_fit_slots(es))
    case Cf.NotMap{}:
      True{}

def cf_fit_qs(+qs: List<&2, Nat>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Nat, qs)), LawsBase.wire_nats_fit(qs))

def cf_fit_ask(a: FC.Ask) -> Bool:
  match a:
    case FC.AskRmw{r, e}:
      Bool.and(cf_fit_read(r), cf_fit_edit(e))
    case FC.AskLeaves{+ls}:
      Bool.and(LawsBase.wire_fits(List.length(&2, Cf.Leaf, ls)), cf_fit_leaves(ls))
    case FC.AskLimits{s, qs}:
      Bool.and(cf_fit_inflight(s), cf_fit_qs(qs))
    case FC.AskTrust{t, +ks}:
      Bool.and(LawsBase.wire_fits(List.length(&2, Cf.PKey, ks)), cf_fit_pkeys(ks))
    case FC.AskMerge{+g, +p, qs}:
      Bool.and(LawsBase.wire_fits(List.length(&2, Cf.Named, g)), Bool.and(cf_fit_nameds(g), Bool.and(LawsBase.wire_fits(List.length(&2, Cf.Named, p)), Bool.and(cf_fit_nameds(p), cf_fit_qs(qs)))))

# Reader: the requests the entry accepts, read with the wire primitives

def cf_r_entry.v(k: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Cf.Entry>:
  match r:
    case Wr.Got{v, s}:
      Wr.Got{Cf.Entry{k, v}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_entry.k(r: Wr.Dec<Nat>) -> Wr.Dec<Cf.Entry>:
  match r:
    case Wr.Got{k, s}:
      cf_r_entry.v(k, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_entry(s: String) -> Wr.Dec<Cf.Entry>:
  cf_r_entry.k(Wr.get_nat(s))

def cf_r_entries(s: String) -> Wr.Dec<List<&2, Cf.Entry>>:
  Wr.get_list(~Cf.Entry, ~cf_r_entry, s)

def cf_r_read.parsed(r: Wr.Dec<List<&2, Cf.Entry>>) -> Wr.Dec<Cf.Read>:
  match r:
    case Wr.Got{d, s}:
      Wr.Got{Cf.Parsed{d}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_read.tag(t: Nat, s: String) -> Wr.Dec<Cf.Read>:
  match t:
    case 0n:
      Wr.Got{Cf.Missing{}, s}
    case 1n:
      cf_r_read.parsed(cf_r_entries(s))
    case 2n:
      Wr.Got{Cf.Broken{}, s}
    case 3n+p:
      Wr.Bad{}

def cf_r_read(r: Wr.Dec<Nat>) -> Wr.Dec<Cf.Read>:
  match r:
    case Wr.Got{t, s}:
      cf_r_read.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_edit.set(k: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Cf.Edit>:
  match r:
    case Wr.Got{v, s}:
      Wr.Got{Cf.Set{k, v}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_edit.setk(r: Wr.Dec<Nat>) -> Wr.Dec<Cf.Edit>:
  match r:
    case Wr.Got{k, s}:
      cf_r_edit.set(k, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_edit.del(r: Wr.Dec<Nat>) -> Wr.Dec<Cf.Edit>:
  match r:
    case Wr.Got{k, s}:
      Wr.Got{Cf.Del{k}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_edit.tag(t: Nat, s: String) -> Wr.Dec<Cf.Edit>:
  match t:
    case 0n:
      cf_r_edit.setk(Wr.get_nat(s))
    case 1n:
      cf_r_edit.del(Wr.get_nat(s))
    case 2n+p:
      Wr.Bad{}

def cf_r_edit(r: Wr.Dec<Nat>) -> Wr.Dec<Cf.Edit>:
  match r:
    case Wr.Got{t, s}:
      cf_r_edit.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_leaf.tag(p: Nat, t: Nat, s: String) -> Wr.Dec<Cf.Leaf>:
  match t:
    case 0n:
      Wr.Got{Cf.Leaf{p, Cf.Good{}}, s}
    case 1n:
      Wr.Got{Cf.Leaf{p, Cf.BadType{}}, s}
    case 2n:
      Wr.Got{Cf.Leaf{p, Cf.Undeclared{}}, s}
    case 3n+q:
      Wr.Bad{}

def cf_r_leaf.o(p: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Cf.Leaf>:
  match r:
    case Wr.Got{t, s}:
      cf_r_leaf.tag(p, t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_leaf.p(r: Wr.Dec<Nat>) -> Wr.Dec<Cf.Leaf>:
  match r:
    case Wr.Got{p, s}:
      cf_r_leaf.o(p, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_leaf(s: String) -> Wr.Dec<Cf.Leaf>:
  cf_r_leaf.p(Wr.get_nat(s))

def cf_r_slot.num(p: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Cf.Slot>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{Cf.Slot{p, Cf.Num{n}}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_slot.tag(p: Nat, t: Nat, s: String) -> Wr.Dec<Cf.Slot>:
  match t:
    case 0n:
      cf_r_slot.num(p, Wr.get_nat(s))
    case 1n:
      Wr.Got{Cf.Slot{p, Cf.Malformed{}}, s}
    case 2n+q:
      Wr.Bad{}

def cf_r_slot.v(p: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Cf.Slot>:
  match r:
    case Wr.Got{t, s}:
      cf_r_slot.tag(p, t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_slot.p(r: Wr.Dec<Nat>) -> Wr.Dec<Cf.Slot>:
  match r:
    case Wr.Got{p, s}:
      cf_r_slot.v(p, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_slot(s: String) -> Wr.Dec<Cf.Slot>:
  cf_r_slot.p(Wr.get_nat(s))

def cf_r_inflight.map(r: Wr.Dec<List<&2, Cf.Slot>>) -> Wr.Dec<Cf.InFlight>:
  match r:
    case Wr.Got{es, s}:
      Wr.Got{Cf.Entries{es}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_inflight.tag(t: Nat, s: String) -> Wr.Dec<Cf.InFlight>:
  match t:
    case 0n:
      Wr.Got{Cf.Unset{}, s}
    case 1n:
      cf_r_inflight.map(Wr.get_list(~Cf.Slot, ~cf_r_slot, s))
    case 2n:
      Wr.Got{Cf.NotMap{}, s}
    case 3n+p:
      Wr.Bad{}

def cf_r_inflight(r: Wr.Dec<Nat>) -> Wr.Dec<Cf.InFlight>:
  match r:
    case Wr.Got{t, s}:
      cf_r_inflight.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_pkey.v(k: Nat, p: List<&2, String>, r: Wr.Dec<Nat>) -> Wr.Dec<Cf.PKey>:
  match r:
    case Wr.Got{v, s}:
      Wr.Got{Cf.PKey{k, p, v}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_pkey.p(k: Nat, r: Wr.Dec<List<&2, String>>) -> Wr.Dec<Cf.PKey>:
  match r:
    case Wr.Got{p, s}:
      cf_r_pkey.v(k, p, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_pkey.k(r: Wr.Dec<Nat>) -> Wr.Dec<Cf.PKey>:
  match r:
    case Wr.Got{k, s}:
      cf_r_pkey.p(k, Wr.get_list(~String, ~Wr.get_str, s))
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_pkey(s: String) -> Wr.Dec<Cf.PKey>:
  cf_r_pkey.k(Wr.get_nat(s))

def cf_r_named.fs(n: Nat, r: Wr.Dec<List<&2, Cf.Entry>>) -> Wr.Dec<Cf.Named>:
  match r:
    case Wr.Got{fs, s}:
      Wr.Got{Cf.Named{n, fs}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_named.n(r: Wr.Dec<Nat>) -> Wr.Dec<Cf.Named>:
  match r:
    case Wr.Got{n, s}:
      cf_r_named.fs(n, cf_r_entries(s))
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_named(s: String) -> Wr.Dec<Cf.Named>:
  cf_r_named.n(Wr.get_nat(s))

def cf_r_nameds(s: String) -> Wr.Dec<List<&2, Cf.Named>>:
  Wr.get_list(~Cf.Named, ~cf_r_named, s)

def cf_r_rmw.e(r: Cf.Read, d: Wr.Dec<Cf.Edit>) -> Wr.Dec<FC.Ask>:
  match d:
    case Wr.Got{e, s}:
      Wr.Got{FC.AskRmw{r, e}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_rmw(d: Wr.Dec<Cf.Read>) -> Wr.Dec<FC.Ask>:
  match d:
    case Wr.Got{r, s}:
      cf_r_rmw.e(r, cf_r_edit(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_leaves(d: Wr.Dec<List<&2, Cf.Leaf>>) -> Wr.Dec<FC.Ask>:
  match d:
    case Wr.Got{ls, s}:
      Wr.Got{FC.AskLeaves{ls}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_limits.qs(f: Cf.InFlight, d: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FC.Ask>:
  match d:
    case Wr.Got{qs, s}:
      Wr.Got{FC.AskLimits{f, qs}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_limits(d: Wr.Dec<Cf.InFlight>) -> Wr.Dec<FC.Ask>:
  match d:
    case Wr.Got{f, s}:
      cf_r_limits.qs(f, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_trust.ks(t: Cf.Trust, d: Wr.Dec<List<&2, Cf.PKey>>) -> Wr.Dec<FC.Ask>:
  match d:
    case Wr.Got{ks, s}:
      Wr.Got{FC.AskTrust{t, ks}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_trust.tag(t: Nat, s: String) -> Wr.Dec<FC.Ask>:
  match t:
    case 0n:
      cf_r_trust.ks(Cf.Trusted{}, Wr.get_list(~Cf.PKey, ~cf_r_pkey, s))
    case 1n:
      cf_r_trust.ks(Cf.Untrusted{}, Wr.get_list(~Cf.PKey, ~cf_r_pkey, s))
    case 2n+p:
      Wr.Bad{}

def cf_r_trust(d: Wr.Dec<Nat>) -> Wr.Dec<FC.Ask>:
  match d:
    case Wr.Got{t, s}:
      cf_r_trust.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_merge.qs(g: List<&2, Cf.Named>, p: List<&2, Cf.Named>, d: Wr.Dec<List<&2, Nat>>) -> Wr.Dec<FC.Ask>:
  match d:
    case Wr.Got{qs, s}:
      Wr.Got{FC.AskMerge{g, p, qs}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_merge.p(g: List<&2, Cf.Named>, d: Wr.Dec<List<&2, Cf.Named>>) -> Wr.Dec<FC.Ask>:
  match d:
    case Wr.Got{p, s}:
      cf_r_merge.qs(g, p, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_merge(d: Wr.Dec<List<&2, Cf.Named>>) -> Wr.Dec<FC.Ask>:
  match d:
    case Wr.Got{g, s}:
      cf_r_merge.p(g, cf_r_nameds(s))
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_ask.tag(t: Nat, s: String) -> Wr.Dec<FC.Ask>:
  match t:
    case 0n:
      cf_r_rmw(cf_r_read(Wr.get_nat(s)))
    case 1n:
      cf_r_leaves(Wr.get_list(~Cf.Leaf, ~cf_r_leaf, s))
    case 2n:
      cf_r_limits(cf_r_inflight(Wr.get_nat(s)))
    case 3n:
      cf_r_trust(Wr.get_nat(s))
    case 4n:
      cf_r_merge(cf_r_nameds(s))
    case 5n+p:
      Wr.Bad{}

def cf_r_ask(r: Wr.Dec<Nat>) -> Wr.Dec<FC.Ask>:
  match r:
    case Wr.Got{t, s}:
      cf_r_ask.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def cf_r_end(whole: Bool, a: FC.Ask) -> Maybe<&2, FC.Ask>:
  match whole:
    case True{}:
      Some{a}
    case False{}:
      None{}

def cf_r_whole(r: Wr.Dec<FC.Ask>) -> Maybe<&2, FC.Ask>:
  match r:
    case Wr.Got{a, s}:
      cf_r_end(String.is_empty(s), a)
    case Wr.Bad{}:
      None{}

# the request s is, when s is exactly one request
def cf_read(s: String) -> Maybe<&2, FC.Ask>:
  cf_r_whole(cf_r_ask(Wr.get_nat(s)))
