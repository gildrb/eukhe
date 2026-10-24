# ffi_config: the entry of the compiled Bend core for the config rules
# (the model bend/config.bend runs; crates/eukhe-bend/src/rules/config.rs
# is the Rust side). The Rust reads and writes the files and
# turns their bytes into the facts below; this entry decides. The wire
# format is bend/wire.bend; malformed input, or input left over, answers
# the error form "config: malformed request". A request is a tag and its
# body:
#
#   0 rmw     Read Edit                     -> Write
#   1 leaves  List<Leaf>                    -> List<Nat> applied,
#                                              List<Nat> reported
#   2 limits  InFlight List<Nat> providers  -> List<Lim>, one per provider
#   3 trust   Trust List<PKey>              -> List<Entry> applied,
#                                              List<String> withheld names
#   4 merge   List<Named> global, List<Named> project, List<Nat> names
#                                           -> List<Maybe<List<Entry>>>
#
#   Entry     Nat key, Nat value
#   Read      0 missing | 1 List<Entry> (parsed) | 2 broken
#   Edit      0 set Nat key, Nat value | 1 delete Nat key
#   Write     0 refused | 1 List<Entry> (written)
#   Leaf      Nat path, outcome: 0 good | 1 bad type | 2 undeclared
#   InFlight  0 unset | 1 List<Slot> (a map) | 2 not a map
#   Slot      Nat provider, Val: 0 Nat (a whole number) | 1 (malformed)
#   Lim       0 unlimited | 1 Nat cap
#   Trust     0 trusted | 1 untrusted
#   PKey      Nat key, List<String> path, Nat value
#   Named     Nat name, List<Entry> fields
#   Maybe     0 none | 1 the value

import Base
import ./wire.bend as W
import ./config.bend as Cf

# Requests
# --------

type Ask is Data:
  AskRmw{r: Cf.Read, e: Cf.Edit}
  AskLeaves{ls: List<&2, Cf.Leaf>}
  AskLimits{s: Cf.InFlight, qs: List<&2, Nat>}
  AskTrust{t: Cf.Trust, ks: List<&2, Cf.PKey>}
  AskMerge{g: List<&2, Cf.Named>, p: List<&2, Cf.Named>, qs: List<&2, Nat>}

# an entry: its key, then its value
def get_entry.v(k: Nat, r: W.Dec<Nat>) -> W.Dec<Cf.Entry>:
  match r:
    case W.Got{v, s}:
      W.Got{Cf.Entry{k, v}, s}
    case W.Bad{}:
      W.Bad{}

def get_entry.k(r: W.Dec<Nat>) -> W.Dec<Cf.Entry>:
  match r:
    case W.Got{k, s}:
      get_entry.v(k, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_entry(s: String) -> W.Dec<Cf.Entry>:
  get_entry.k(W.get_nat(s))

def get_entries.cons(e: Cf.Entry, r: W.Dec<List<&2, Cf.Entry>>) -> W.Dec<List<&2, Cf.Entry>>:
  match r:
    case W.Got{es, s}:
      W.Got{e <> es, s}
    case W.Bad{}:
      W.Bad{}

# n more entries after the one cur answers
def get_entries.go(n: Nat, cur: W.Dec<Cf.Entry>) -> W.Dec<List<&2, Cf.Entry>>:
  match n:
    case 0n:
      match cur:
        case W.Got{e, s}:
          W.Got{[e], s}
        case W.Bad{}:
          W.Bad{}
    case 1n+m:
      match cur:
        case W.Got{e, s}:
          get_entries.cons(e, get_entries.go(m, get_entry(s)))
        case W.Bad{}:
          W.Bad{}

def get_entries.start(r: W.Dec<Nat>) -> W.Dec<List<&2, Cf.Entry>>:
  match r:
    case W.Got{n, s}:
      match n:
        case 0n:
          W.Got{Nil{}, s}
        case 1n+m:
          get_entries.go(m, get_entry(s))
    case W.Bad{}:
      W.Bad{}

def get_entries(s: String) -> W.Dec<List<&2, Cf.Entry>>:
  get_entries.start(W.get_nat(s))

# a read: missing, parsed (its entries) or broken
def get_read.parsed(r: W.Dec<List<&2, Cf.Entry>>) -> W.Dec<Cf.Read>:
  match r:
    case W.Got{d, s}:
      W.Got{Cf.Parsed{d}, s}
    case W.Bad{}:
      W.Bad{}

def get_read.tag(t: Nat, s: String) -> W.Dec<Cf.Read>:
  match t:
    case 0n:
      W.Got{Cf.Missing{}, s}
    case 1n:
      get_read.parsed(get_entries(s))
    case 2n:
      W.Got{Cf.Broken{}, s}
    case 3n+p:
      W.Bad{}

def get_read(r: W.Dec<Nat>) -> W.Dec<Cf.Read>:
  match r:
    case W.Got{t, s}:
      get_read.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# an edit: a set of a key to a value, or a delete of a key
def get_edit.set(k: Nat, r: W.Dec<Nat>) -> W.Dec<Cf.Edit>:
  match r:
    case W.Got{v, s}:
      W.Got{Cf.Set{k, v}, s}
    case W.Bad{}:
      W.Bad{}

def get_edit.setk(r: W.Dec<Nat>) -> W.Dec<Cf.Edit>:
  match r:
    case W.Got{k, s}:
      get_edit.set(k, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_edit.del(r: W.Dec<Nat>) -> W.Dec<Cf.Edit>:
  match r:
    case W.Got{k, s}:
      W.Got{Cf.Del{k}, s}
    case W.Bad{}:
      W.Bad{}

def get_edit.tag(t: Nat, s: String) -> W.Dec<Cf.Edit>:
  match t:
    case 0n:
      get_edit.setk(W.get_nat(s))
    case 1n:
      get_edit.del(W.get_nat(s))
    case 2n+p:
      W.Bad{}

def get_edit(r: W.Dec<Nat>) -> W.Dec<Cf.Edit>:
  match r:
    case W.Got{t, s}:
      get_edit.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# a leaf: its path, then its outcome
def get_leaf.tag(p: Nat, t: Nat, s: String) -> W.Dec<Cf.Leaf>:
  match t:
    case 0n:
      W.Got{Cf.Leaf{p, Cf.Good{}}, s}
    case 1n:
      W.Got{Cf.Leaf{p, Cf.BadType{}}, s}
    case 2n:
      W.Got{Cf.Leaf{p, Cf.Undeclared{}}, s}
    case 3n+q:
      W.Bad{}

def get_leaf.o(p: Nat, r: W.Dec<Nat>) -> W.Dec<Cf.Leaf>:
  match r:
    case W.Got{t, s}:
      get_leaf.tag(p, t, s)
    case W.Bad{}:
      W.Bad{}

def get_leaf.p(r: W.Dec<Nat>) -> W.Dec<Cf.Leaf>:
  match r:
    case W.Got{p, s}:
      get_leaf.o(p, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_leaf(s: String) -> W.Dec<Cf.Leaf>:
  get_leaf.p(W.get_nat(s))

def get_leaves.cons(l: Cf.Leaf, r: W.Dec<List<&2, Cf.Leaf>>) -> W.Dec<List<&2, Cf.Leaf>>:
  match r:
    case W.Got{ls, s}:
      W.Got{l <> ls, s}
    case W.Bad{}:
      W.Bad{}

# n more leaves after the one cur answers
def get_leaves.go(n: Nat, cur: W.Dec<Cf.Leaf>) -> W.Dec<List<&2, Cf.Leaf>>:
  match n:
    case 0n:
      match cur:
        case W.Got{l, s}:
          W.Got{[l], s}
        case W.Bad{}:
          W.Bad{}
    case 1n+m:
      match cur:
        case W.Got{l, s}:
          get_leaves.cons(l, get_leaves.go(m, get_leaf(s)))
        case W.Bad{}:
          W.Bad{}

def get_leaves.start(r: W.Dec<Nat>) -> W.Dec<List<&2, Cf.Leaf>>:
  match r:
    case W.Got{n, s}:
      match n:
        case 0n:
          W.Got{Nil{}, s}
        case 1n+m:
          get_leaves.go(m, get_leaf(s))
    case W.Bad{}:
      W.Bad{}

# a slot of providerMaxInFlight: its provider, then a whole number or a
# malformed value
def get_slot.num(p: Nat, r: W.Dec<Nat>) -> W.Dec<Cf.Slot>:
  match r:
    case W.Got{n, s}:
      W.Got{Cf.Slot{p, Cf.Num{n}}, s}
    case W.Bad{}:
      W.Bad{}

def get_slot.tag(p: Nat, t: Nat, s: String) -> W.Dec<Cf.Slot>:
  match t:
    case 0n:
      get_slot.num(p, W.get_nat(s))
    case 1n:
      W.Got{Cf.Slot{p, Cf.Malformed{}}, s}
    case 2n+q:
      W.Bad{}

def get_slot.v(p: Nat, r: W.Dec<Nat>) -> W.Dec<Cf.Slot>:
  match r:
    case W.Got{t, s}:
      get_slot.tag(p, t, s)
    case W.Bad{}:
      W.Bad{}

def get_slot.p(r: W.Dec<Nat>) -> W.Dec<Cf.Slot>:
  match r:
    case W.Got{p, s}:
      get_slot.v(p, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_slot(s: String) -> W.Dec<Cf.Slot>:
  get_slot.p(W.get_nat(s))

def get_slots.cons(x: Cf.Slot, r: W.Dec<List<&2, Cf.Slot>>) -> W.Dec<List<&2, Cf.Slot>>:
  match r:
    case W.Got{xs, s}:
      W.Got{x <> xs, s}
    case W.Bad{}:
      W.Bad{}

# n more slots after the one cur answers
def get_slots.go(n: Nat, cur: W.Dec<Cf.Slot>) -> W.Dec<List<&2, Cf.Slot>>:
  match n:
    case 0n:
      match cur:
        case W.Got{x, s}:
          W.Got{[x], s}
        case W.Bad{}:
          W.Bad{}
    case 1n+m:
      match cur:
        case W.Got{x, s}:
          get_slots.cons(x, get_slots.go(m, get_slot(s)))
        case W.Bad{}:
          W.Bad{}

def get_slots.start(r: W.Dec<Nat>) -> W.Dec<List<&2, Cf.Slot>>:
  match r:
    case W.Got{n, s}:
      match n:
        case 0n:
          W.Got{Nil{}, s}
        case 1n+m:
          get_slots.go(m, get_slot(s))
    case W.Bad{}:
      W.Bad{}

# providerMaxInFlight: unset, a map (its slots) or not a map
def get_inflight.map(r: W.Dec<List<&2, Cf.Slot>>) -> W.Dec<Cf.InFlight>:
  match r:
    case W.Got{es, s}:
      W.Got{Cf.Entries{es}, s}
    case W.Bad{}:
      W.Bad{}

def get_inflight.tag(t: Nat, s: String) -> W.Dec<Cf.InFlight>:
  match t:
    case 0n:
      W.Got{Cf.Unset{}, s}
    case 1n:
      get_inflight.map(get_slots.start(W.get_nat(s)))
    case 2n:
      W.Got{Cf.NotMap{}, s}
    case 3n+p:
      W.Bad{}

def get_inflight(r: W.Dec<Nat>) -> W.Dec<Cf.InFlight>:
  match r:
    case W.Got{t, s}:
      get_inflight.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# a key of a project document: its place, its path, its value's place
def get_pkey.v(k: Nat, p: List<&2, String>, r: W.Dec<Nat>) -> W.Dec<Cf.PKey>:
  match r:
    case W.Got{v, s}:
      W.Got{Cf.PKey{k, p, v}, s}
    case W.Bad{}:
      W.Bad{}

def get_pkey.p(k: Nat, r: W.Dec<List<&2, String>>) -> W.Dec<Cf.PKey>:
  match r:
    case W.Got{p, s}:
      get_pkey.v(k, p, W.get_nat(s))
    case W.Bad{}:
      W.Bad{}

def get_pkey.k(r: W.Dec<Nat>) -> W.Dec<Cf.PKey>:
  match r:
    case W.Got{k, s}:
      get_pkey.p(k, W.get_list(~String, ~W.get_str, s))
    case W.Bad{}:
      W.Bad{}

def get_pkey(s: String) -> W.Dec<Cf.PKey>:
  get_pkey.k(W.get_nat(s))

def get_pkeys.cons(x: Cf.PKey, r: W.Dec<List<&2, Cf.PKey>>) -> W.Dec<List<&2, Cf.PKey>>:
  match r:
    case W.Got{xs, s}:
      W.Got{x <> xs, s}
    case W.Bad{}:
      W.Bad{}

# n more keys after the one cur answers
def get_pkeys.go(n: Nat, cur: W.Dec<Cf.PKey>) -> W.Dec<List<&2, Cf.PKey>>:
  match n:
    case 0n:
      match cur:
        case W.Got{x, s}:
          W.Got{[x], s}
        case W.Bad{}:
          W.Bad{}
    case 1n+m:
      match cur:
        case W.Got{x, s}:
          get_pkeys.cons(x, get_pkeys.go(m, get_pkey(s)))
        case W.Bad{}:
          W.Bad{}

def get_pkeys.start(r: W.Dec<Nat>) -> W.Dec<List<&2, Cf.PKey>>:
  match r:
    case W.Got{n, s}:
      match n:
        case 0n:
          W.Got{Nil{}, s}
        case 1n+m:
          get_pkeys.go(m, get_pkey(s))
    case W.Bad{}:
      W.Bad{}

# a named entry: its name, then its fields
def get_named.fs(n: Nat, r: W.Dec<List<&2, Cf.Entry>>) -> W.Dec<Cf.Named>:
  match r:
    case W.Got{fs, s}:
      W.Got{Cf.Named{n, fs}, s}
    case W.Bad{}:
      W.Bad{}

def get_named.n(r: W.Dec<Nat>) -> W.Dec<Cf.Named>:
  match r:
    case W.Got{n, s}:
      get_named.fs(n, get_entries(s))
    case W.Bad{}:
      W.Bad{}

def get_named(s: String) -> W.Dec<Cf.Named>:
  get_named.n(W.get_nat(s))

def get_nameds.cons(x: Cf.Named, r: W.Dec<List<&2, Cf.Named>>) -> W.Dec<List<&2, Cf.Named>>:
  match r:
    case W.Got{xs, s}:
      W.Got{x <> xs, s}
    case W.Bad{}:
      W.Bad{}

# n more named entries after the one cur answers
def get_nameds.go(n: Nat, cur: W.Dec<Cf.Named>) -> W.Dec<List<&2, Cf.Named>>:
  match n:
    case 0n:
      match cur:
        case W.Got{x, s}:
          W.Got{[x], s}
        case W.Bad{}:
          W.Bad{}
    case 1n+m:
      match cur:
        case W.Got{x, s}:
          get_nameds.cons(x, get_nameds.go(m, get_named(s)))
        case W.Bad{}:
          W.Bad{}

def get_nameds.start(r: W.Dec<Nat>) -> W.Dec<List<&2, Cf.Named>>:
  match r:
    case W.Got{n, s}:
      match n:
        case 0n:
          W.Got{Nil{}, s}
        case 1n+m:
          get_nameds.go(m, get_named(s))
    case W.Bad{}:
      W.Bad{}

# the bodies of the requests
def get_rmw.e(r: Cf.Read, d: W.Dec<Cf.Edit>) -> W.Dec<Ask>:
  match d:
    case W.Got{e, s}:
      W.Got{AskRmw{r, e}, s}
    case W.Bad{}:
      W.Bad{}

def get_rmw(d: W.Dec<Cf.Read>) -> W.Dec<Ask>:
  match d:
    case W.Got{r, s}:
      get_rmw.e(r, get_edit(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_leaves(d: W.Dec<List<&2, Cf.Leaf>>) -> W.Dec<Ask>:
  match d:
    case W.Got{ls, s}:
      W.Got{AskLeaves{ls}, s}
    case W.Bad{}:
      W.Bad{}

def get_limits.qs(f: Cf.InFlight, d: W.Dec<List<&2, Nat>>) -> W.Dec<Ask>:
  match d:
    case W.Got{qs, s}:
      W.Got{AskLimits{f, qs}, s}
    case W.Bad{}:
      W.Bad{}

def get_limits(d: W.Dec<Cf.InFlight>) -> W.Dec<Ask>:
  match d:
    case W.Got{f, s}:
      get_limits.qs(f, W.get_list(~Nat, ~W.get_nat, s))
    case W.Bad{}:
      W.Bad{}

def get_trust.ks(t: Cf.Trust, d: W.Dec<List<&2, Cf.PKey>>) -> W.Dec<Ask>:
  match d:
    case W.Got{ks, s}:
      W.Got{AskTrust{t, ks}, s}
    case W.Bad{}:
      W.Bad{}

def get_trust.tag(t: Nat, s: String) -> W.Dec<Ask>:
  match t:
    case 0n:
      get_trust.ks(Cf.Trusted{}, get_pkeys.start(W.get_nat(s)))
    case 1n:
      get_trust.ks(Cf.Untrusted{}, get_pkeys.start(W.get_nat(s)))
    case 2n+p:
      W.Bad{}

def get_trust(d: W.Dec<Nat>) -> W.Dec<Ask>:
  match d:
    case W.Got{t, s}:
      get_trust.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_merge.qs(g: List<&2, Cf.Named>, p: List<&2, Cf.Named>, d: W.Dec<List<&2, Nat>>) -> W.Dec<Ask>:
  match d:
    case W.Got{qs, s}:
      W.Got{AskMerge{g, p, qs}, s}
    case W.Bad{}:
      W.Bad{}

def get_merge.p(g: List<&2, Cf.Named>, d: W.Dec<List<&2, Cf.Named>>) -> W.Dec<Ask>:
  match d:
    case W.Got{p, s}:
      get_merge.qs(g, p, W.get_list(~Nat, ~W.get_nat, s))
    case W.Bad{}:
      W.Bad{}

def get_merge(d: W.Dec<List<&2, Cf.Named>>) -> W.Dec<Ask>:
  match d:
    case W.Got{g, s}:
      get_merge.p(g, get_nameds.start(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_ask.tag(t: Nat, s: String) -> W.Dec<Ask>:
  match t:
    case 0n:
      get_rmw(get_read(W.get_nat(s)))
    case 1n:
      get_leaves(get_leaves.start(W.get_nat(s)))
    case 2n:
      get_limits(get_inflight(W.get_nat(s)))
    case 3n:
      get_trust(W.get_nat(s))
    case 4n:
      get_merge(get_nameds.start(W.get_nat(s)))
    case 5n+p:
      W.Bad{}

def get_ask(r: W.Dec<Nat>) -> W.Dec<Ask>:
  match r:
    case W.Got{t, s}:
      get_ask.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# Replies
# -------

def put_entry(e: Cf.Entry, rest: String) -> String:
  match e:
    case Cf.Entry{k, v}:
      W.put_nat(k, W.put_nat(v, rest))

def put_entries.items(d: List<&2, Cf.Entry>, rest: String) -> String:
  match d:
    case Nil{}:
      rest
    case e <> t:
      put_entry(e, put_entries.items(t, rest))

# a list of entries: its count, then each entry
def put_entries(+d: List<&2, Cf.Entry>, rest: String) -> String:
  W.put_nat(List.length(&2, Cf.Entry, d), put_entries.items(d, rest))

def put_write(w: Cf.Write, rest: String) -> String:
  match w:
    case Cf.Refused{}:
      W.put_nat(0n, rest)
    case Cf.Wrote{d}:
      W.put_nat(1n, put_entries(d, rest))

def put_lim(l: Cf.Lim, rest: String) -> String:
  match l:
    case Cf.Unlimited{}:
      W.put_nat(0n, rest)
    case Cf.Cap{n}:
      W.put_nat(1n, W.put_nat(n, rest))

def put_lims.items(ls: List<&2, Cf.Lim>, rest: String) -> String:
  match ls:
    case Nil{}:
      rest
    case l <> t:
      put_lim(l, put_lims.items(t, rest))

def put_found(m: Maybe<&2, List<&2, Cf.Entry>>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{fs}:
      W.put_nat(1n, put_entries(fs, rest))

def put_founds.items(ms: List<&2, Maybe<&2, List<&2, Cf.Entry>>>, rest: String) -> String:
  match ms:
    case Nil{}:
      rest
    case m <> t:
      put_found(m, put_founds.items(t, rest))

def put_limits(+ls: List<&2, Cf.Lim>) -> String:
  W.put_nat(List.length(&2, Cf.Lim, ls), put_lims.items(ls, ""))

def put_merged(+ms: List<&2, Maybe<&2, List<&2, Cf.Entry>>>) -> String:
  W.put_nat(List.length(&2, Maybe<&2, List<&2, Cf.Entry>>, ms), put_founds.items(ms, ""))

# the reply to a request: the model's decision
def answer(a: Ask) -> String:
  match a:
    case AskRmw{r, e}:
      put_write(Cf.rmw(r, e), "")
    case AskLeaves{+ls}:
      W.put_list(~Nat, ~W.put_nat, Cf.applied(ls), W.put_list(~Nat, ~W.put_nat, Cf.reported(ls), ""))
    case AskLimits{s, qs}:
      put_limits(Cf.limits(s, qs))
    case AskTrust{+t, +ks}:
      put_entries(Cf.project(t, Nil{}, ks), W.put_list(~String, ~W.put_str, Cf.withheld(t, ks), ""))
    case AskMerge{g, p, qs}:
      put_merged(Cf.finds(Cf.merge(g, p), qs))

# the error form of every input that is not exactly one request
def refused() -> String:
  W.err("config: malformed request")

def run.end(whole: Bool, a: Ask) -> String:
  match whole:
    case True{}:
      answer(a)
    case False{}:
      refused()

def run(r: W.Dec<Ask>) -> String:
  match r:
    case W.Got{a, s}:
      run.end(W.end(s), a)
    case W.Bad{}:
      refused()

def ffi(input: String) -> String:
  run(get_ask(W.get_nat(input)))
