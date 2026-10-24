# eukhe: the laws of area listing

import Base
import ../bend/staging.bend as Sg
import ../bend/listing.bend as Ls
import ./base.bend as LawsBase

# ---- listing ----

# LAWS: the real rule of how the sessions directory is listed
# (bend/listing.bend; crates/eukhe-core/src/durable/discovery.rs
# `list_sessions`), run by the compiled core through bend/ffi_staging.bend
# (its entry laws: laws/staging.bend). The Rust lists the directory, reads
# the cwd and the file times of every candidate the scan names, and builds
# the listing from the rows the rule answers. It refines the Listing model
# of bend/staging.bend: the laws list_one_location, list_import_lists_storage
# and list_import_keeps_others restated on the real listing. Each law is an
# open claim; PROOF.bend proves them (as Listing.<law>) with the lemmas of
# proof/listing/.
#
# R5: a session shows once: no id is listed both as a storage and as a
#     legacy file; a legacy file whose storage directory exists is no
#     session of its own; hidden directories are no sessions.
# R6: an import lists the imported session as a storage and changes the
#     listing of no other id.
# R7: the listing holds every session candidate whose cwd reads (not
#     empty) and that has a file, once, as what it is, with its newest
#     time; newest first, then by id, then by place.
# Every input is free: any names (UTF-8 or not), entry types, listings,
# cwds, times.

# Spec helpers: the listing
# -------------------------

def sp_dir(main: Bool, hid: Bool, s: String) -> Ls.Pick:
  match main:
    case True{}:
      match hid:
        case True{}:
          Ls.PSkip{}
        case False{}:
          Ls.PStore{s}
    case False{}:
      Ls.PSkip{}

def sp_legacy(gone: Bool, s: String) -> Ls.Pick:
  match gone:
    case True{}:
      Ls.PSkip{}
    case False{}:
      Ls.PLegacy{s}

def sp_stem(m: Maybe<&2, String>, all: List<&2, Sg.Seen>) -> Ls.Pick:
  match m:
    case None{}:
      Ls.PSkip{}
    case Some{+st}:
      sp_legacy(Bool.or(Bool.or(String.is_empty(st), Bool.or(LawsBase.text_same(st, "."), LawsBase.text_same(st, ".."))), LawsBase.text_has_name(st, all)), st)

# s is hidden: it starts with '.'
def sp_hidden(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Char.is_eq(c, '.')

def sp_pick.utf(k: Sg.Form, +s: String, all: List<&2, Sg.Seen>) -> Ls.Pick:
  match k:
    case Sg.KDir{main}:
      sp_dir(main, sp_hidden(s), s)
    case Sg.KFile{}:
      sp_stem(LawsBase.text_unsuffix(".jsonl", s), all)
    case Sg.KOther{}:
      Ls.PSkip{}

# what the entry e of the sessions directory listing all is (R5): a
# directory that holds main.jsonl and is not hidden is a storage under its
# name; a file `<stem>.jsonl` is a legacy file under its stem, unless the
# stem is empty, "." or "..", or an entry has that name (its storage
# directory exists); a name that is not UTF-8 is no session
def sp_pick(e: Sg.Seen, all: List<&2, Sg.Seen>) -> Ls.Pick:
  match e:
    case Sg.Seen{n, k}:
      match n:
        case Sg.Utf{s}:
          sp_pick.utf(k, s, all)
        case Sg.Raw{}:
          Ls.PSkip{}

def sp_scan.go(es: List<&2, Sg.Seen>, +all: List<&2, Sg.Seen>) -> List<&2, Ls.Pick>:
  match es:
    case Nil{}:
      Nil{}
    case e <> rest:
      sp_pick(e, all) <> sp_scan.go(rest, all)

def sp_scan(+es: List<&2, Sg.Seen>) -> List<&2, Ls.Pick>:
  sp_scan.go(es, es)

def sp_is_store(+n: String, p: Ls.Pick) -> Bool:
  match p:
    case Ls.PSkip{}:
      False{}
    case Ls.PStore{s}:
      LawsBase.text_same(s, n)
    case Ls.PLegacy{s}:
      False{}

def sp_is_legacy(+n: String, p: Ls.Pick) -> Bool:
  match p:
    case Ls.PSkip{}:
      False{}
    case Ls.PStore{s}:
      False{}
    case Ls.PLegacy{s}:
      LawsBase.text_same(s, n)

# n is listed as a storage
def sp_has_store(+n: String, ps: List<&2, Ls.Pick>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> rest:
      Bool.or(sp_is_store(n, p), sp_has_store(n, rest))

# n is listed as a legacy file
def sp_has_legacy(+n: String, ps: List<&2, Ls.Pick>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> rest:
      Bool.or(sp_is_legacy(n, p), sp_has_legacy(n, rest))

# n is listed, as either
def sp_lists(+n: String, +ps: List<&2, Ls.Pick>) -> Bool:
  Bool.or(sp_has_store(n, ps), sp_has_legacy(n, ps))

# the sessions directory after the legacy file with stem s is imported:
# the storage directory s, with main.jsonl (the model's `imported`)
def sp_imported(es: List<&2, Sg.Seen>, s: String) -> List<&2, Sg.Seen>:
  List.append(&2, Sg.Seen, es, [Sg.Seen{Sg.Utf{s}, Sg.KDir{True{}}}])

def sp_seens(os: List<&2, Ls.Obs>) -> List<&2, Sg.Seen>:
  match os:
    case Nil{}:
      Nil{}
    case o <> rest:
      match o:
        case Ls.Obs{e, c, ts}:
          e <> sp_seens(rest)

# a cwd reads, and is not empty
def sp_cwd(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{s}:
      Bool.not(String.is_empty(s))

def sp_skip(p: Ls.Pick) -> Bool:
  match p:
    case Ls.PSkip{}:
      True{}
    case Ls.PStore{s}:
      False{}
    case Ls.PLegacy{s}:
      False{}

def sp_some(ts: List<&2, Sg.Time>) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case t <> rest:
      True{}

# the entry o is listed (R7): a candidate whose cwd reads, with a file
def sp_listed(o: Ls.Obs, all: List<&2, Sg.Seen>) -> Bool:
  match o:
    case Ls.Obs{e, c, ts}:
      Bool.and(Bool.not(sp_skip(sp_pick(e, all))), Bool.and(sp_cwd(c), sp_some(ts)))

# the char codes of a text
def sp_codes(s: String) -> List<&2, Nat>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      match c:
        case Chr{x}:
          U32.to_nat(x) <> sp_codes(t)

# a strictly before b, item by item; a prefix first (on char codes: Rust's
# str order)
def sp_lex(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      False{}
    case Nil{} Con{y, v}:
      True{}
    case Con{x, u} Nil{}:
      False{}
    case Con{+x, u} Con{+y, v}:
      Bool.or(Nat.is_lt(x, y), Bool.and(Nat.is_eq(x, y), sp_lex(u, v)))

# a and b are the same items
def sp_same_nats(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, v}:
      False{}
    case Con{x, u} Nil{}:
      False{}
    case Con{x, u} Con{y, v}:
      Bool.and(Nat.is_eq(x, y), sp_same_nats(u, v))

# a time as its seconds, then its nanoseconds
def sp_tkey(t: Sg.Time) -> List<&2, Nat>:
  match t:
    case Sg.Time{s, n}:
      [s, n]

# a before b in time (seconds, then nanoseconds)
def sp_earlier(a: Sg.Time, b: Sg.Time) -> Bool:
  sp_lex(sp_tkey(a), sp_tkey(b))

def sp_later.pick(b: Bool, a: Sg.Time, c: Sg.Time) -> Sg.Time:
  match b:
    case True{}:
      c
    case False{}:
      a

# the newest of t and the times ts
def sp_newest(ts: List<&2, Sg.Time>, +t: Sg.Time) -> Sg.Time:
  match ts:
    case Nil{}:
      t
    case +u <> rest:
      sp_newest(rest, sp_later.pick(sp_earlier(t, u), t, u))

def sp_top(ts: List<&2, Sg.Time>) -> Sg.Time:
  match ts:
    case Nil{}:
      Sg.Time{0n, 0n}
    case t <> rest:
      sp_newest(rest, t)

# the row of the entry o at place i
def sp_row(o: Ls.Obs, all: List<&2, Sg.Seen>, i: Nat) -> Ls.Row:
  match o:
    case Ls.Obs{e, c, ts}:
      Ls.Row{i, sp_pick(e, all), sp_top(ts)}

def sp_bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# how many entries of os (the first at place k) are at place i and listed
def sp_count_listed(os: List<&2, Ls.Obs>, +all: List<&2, Sg.Seen>, +k: Nat, +i: Nat) -> Nat:
  match os:
    case Nil{}:
      0n
    case o <> rest:
      Nat.add(sp_bit(Bool.and(Nat.is_eq(k, i), sp_listed(o, all))), sp_count_listed(rest, all, 1n+k, i))

def sp_choose(b: Bool, x: Ls.Row, y: Ls.Row) -> Ls.Row:
  match b:
    case True{}:
      x
    case False{}:
      y

# the row of the entry at place i of os (the first at place k)
def sp_row_at(os: List<&2, Ls.Obs>, +all: List<&2, Sg.Seen>, +k: Nat, +i: Nat) -> Ls.Row:
  match os:
    case Nil{}:
      Ls.Row{i, Ls.PSkip{}, Sg.Time{0n, 0n}}
    case o <> rest:
      sp_choose(Nat.is_eq(k, i), sp_row(o, all, i), sp_row_at(rest, all, 1n+k, i))

def sp_ats(rs: List<&2, Ls.Row>) -> List<&2, Nat>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      match r:
        case Ls.Row{i, p, t}:
          i <> sp_ats(rest)

def sp_count(+i: Nat, xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> rest:
      Nat.add(sp_bit(Nat.is_eq(x, i)), sp_count(i, rest))

# the rows of the places ps, each as the spec makes it
def sp_fill(ps: List<&2, Nat>, +os: List<&2, Ls.Obs>, +all: List<&2, Sg.Seen>) -> List<&2, Ls.Row>:
  match ps:
    case Nil{}:
      Nil{}
    case i <> rest:
      sp_row_at(os, all, 0n, i) <> sp_fill(rest, os, all)

def sp_id(p: Ls.Pick) -> String:
  match p:
    case Ls.PSkip{}:
      ""
    case Ls.PStore{s}:
      s
    case Ls.PLegacy{s}:
      s

# a is listed before b (R7): newer first; at the same time, the smaller id
# first; at the same id, the smaller place first
def sp_before(a: Ls.Row, b: Ls.Row) -> Bool:
  match a b:
    case Ls.Row{+ia, +pa, +ta} Ls.Row{+ib, +pb, +tb}:
      +ka = sp_codes(sp_id(pa))
      +kb = sp_codes(sp_id(pb))
      Bool.or(sp_earlier(tb, ta), Bool.and(sp_same_nats(sp_tkey(ta), sp_tkey(tb)), Bool.or(sp_lex(ka, kb), Bool.and(sp_same_nats(ka, kb), Nat.is_lt(ia, ib)))))

# r is before every row of rs
def sp_all_before(+r: Ls.Row, rs: List<&2, Ls.Row>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case z <> rest:
      Bool.and(sp_before(r, z), sp_all_before(r, rest))

# every row is before every later row
def sp_sorted(rs: List<&2, Ls.Row>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case +r <> +rest:
      Bool.and(sp_all_before(r, rest), sp_sorted(rest))

def sp_blank.o(skip: Bool, e: Sg.Seen, c: Maybe<&2, String>, ts: List<&2, Sg.Time>) -> Ls.Obs:
  match skip:
    case True{}:
      Ls.Obs{e, None{}, Nil{}}
    case False{}:
      Ls.Obs{e, c, ts}

# os with no cwd and no times for every entry the scan skips (what the
# Rust sends: it reads nothing of them)
def sp_blank(os: List<&2, Ls.Obs>, +all: List<&2, Sg.Seen>) -> List<&2, Ls.Obs>:
  match os:
    case Nil{}:
      Nil{}
    case o <> rest:
      match o:
        case Ls.Obs{+e, c, ts}:
          sp_blank.o(sp_skip(sp_pick(e, all)), e, c, ts) <> sp_blank(rest, all)

# Laws: the listing (R5, R6, R7)
# ------------------------------

# LAW scan_exact (R5): what every entry of the sessions directory is to the listing is the
# spec's, in order
# EXCLUDES: a hidden or main-less directory listed, a legacy file listed
#   beside its storage directory (or any entry of its stem's name), a
#   wrong stem, a symlink or a Raw name listed, an entry lost or moved
law scan_exact:
  for +es: List<&2, Sg.Seen>
  {Ls.scan(es) == sp_scan(es) : List<&2, Ls.Pick>}

# LAW scan_one_location (R5): no id is listed both as a storage and as a legacy file
# (list_one_location, on the real listing)
# EXCLUDES: a session shown twice, once per location
law scan_one_location:
  for +es: List<&2, Sg.Seen>
  for +n: String
  {Bool.and(sp_has_store(n, Ls.scan(es)), sp_has_legacy(n, Ls.scan(es))) == False{} : Bool}

# LAW scan_import_lists_storage (R6): after the import of the legacy file with stem s (not
# hidden), s is listed as a storage (list_import_lists_storage)
# EXCLUDES: an imported session that vanishes from the listing
law scan_import_lists_storage:
  for +es: List<&2, Sg.Seen>
  for +s: String
  for shown: {sp_hidden(s) == False{} : Bool}
  {sp_has_store(s, Ls.scan(sp_imported(es, s))) == True{} : Bool}

# LAW scan_import_keeps_others (R6): an import changes the listing of no other id
# (list_import_keeps_others)
# EXCLUDES: an import that hides or shows another session
law scan_import_keeps_others:
  for +es: List<&2, Sg.Seen>
  for +s: String
  for +n: String
  for ne: {LawsBase.text_same(s, n) == False{} : Bool}
  {sp_lists(n, Ls.scan(sp_imported(es, s))) == sp_lists(n, Ls.scan(es)) : Bool}

# LAW scan_legacy_named (R5): a file `<stem>.jsonl` alone is a legacy file under its stem,
# for any stem but empty, "." and ".."
# EXCLUDES: a spec of stems narrower than the names of legacy files
law scan_legacy_named:
  for +st: String
  for full: {String.is_empty(st) == False{} : Bool}
  for nd: {Bool.or(LawsBase.text_same(st, "."), LawsBase.text_same(st, "..")) == False{} : Bool}
  {Ls.scan([Sg.Seen{Sg.Utf{String.append(st, ".jsonl")}, Sg.KFile{}}]) == [Ls.PLegacy{st}] : List<&2, Ls.Pick>}

# LAW scan_example (R5): the entries of the Rust listing test, and the edge names
# EXCLUDES: a spec that lists a near miss
law scan_example:
  {Ls.scan([Sg.Seen{Sg.Utf{"durable-1"}, Sg.KDir{True{}}}, Sg.Seen{Sg.Utf{"legacy-1.jsonl"}, Sg.KFile{}}, Sg.Seen{Sg.Utf{".x.import-1"}, Sg.KDir{True{}}}, Sg.Seen{Sg.Utf{"artifacts"}, Sg.KDir{False{}}}, Sg.Seen{Sg.Utf{"durable-1.jsonl"}, Sg.KFile{}}, Sg.Seen{Sg.Utf{".jsonl"}, Sg.KFile{}}, Sg.Seen{Sg.Utf{"..jsonl"}, Sg.KFile{}}, Sg.Seen{Sg.Utf{"a.jsonl.jsonl"}, Sg.KFile{}}, Sg.Seen{Sg.Utf{"a.jsonl"}, Sg.KFile{}}, Sg.Seen{Sg.Utf{"x.JSONL"}, Sg.KFile{}}, Sg.Seen{Sg.Utf{"link.jsonl"}, Sg.KOther{}}, Sg.Seen{Sg.Raw{}, Sg.KDir{True{}}}]) == [Ls.PStore{"durable-1"}, Ls.PLegacy{"legacy-1"}, Ls.PSkip{}, Ls.PSkip{}, Ls.PSkip{}, Ls.PSkip{}, Ls.PSkip{}, Ls.PSkip{}, Ls.PLegacy{"a"}, Ls.PSkip{}, Ls.PSkip{}, Ls.PSkip{}] : List<&2, Ls.Pick>}

# LAW rows_each_once (R7): every entry is listed once when it is listed (a candidate
# whose cwd reads and that has a file), and never otherwise
# EXCLUDES: a session lost, shown twice, or listed without a cwd or a file
law rows_each_once:
  for +os: List<&2, Ls.Obs>
  for +i: Nat
  {sp_count(i, sp_ats(Ls.rows(os))) == sp_count_listed(os, sp_seens(os), 0n, i) : Nat}

# LAW rows_are_entries (R7): every listed row is its entry as the spec makes it: its place,
# what it is (under its id), its newest time
# EXCLUDES: a row with another id, kind or time than its entry's, an
#   oldest time for the newest
law rows_are_entries:
  for +os: List<&2, Ls.Obs>
  {Ls.rows(os) == sp_fill(sp_ats(Ls.rows(os)), os, sp_seens(os)) : List<&2, Ls.Row>}

# LAW rows_newest_first (R7): every row is listed before every later one: newer first, then
# by id, then by place
# EXCLUDES: an oldest-first or unordered listing, ties broken otherwise
law rows_newest_first:
  for +os: List<&2, Ls.Obs>
  {sp_sorted(Ls.rows(os)) == True{} : Bool}

# LAW rows_order_strict (R7): no two rows are each before the other, so rows_each_once,
# rows_are_entries and rows_newest_first leave one listing
# EXCLUDES: an order under which two listings pass the laws
law rows_order_strict:
  for +a: Ls.Row
  for +b: Ls.Row
  {Bool.and(sp_before(a, b), sp_before(b, a)) == False{} : Bool}

# LAW rows_ignore_unread (R7): the listing reads nothing of an entry the scan skips: the
# Rust may send it with no cwd and no times
# EXCLUDES: a listing that depends on facts the Rust does not read
law rows_ignore_unread:
  for +os: List<&2, Ls.Obs>
  {Ls.rows(sp_blank(os, sp_seens(os))) == Ls.rows(os) : List<&2, Ls.Row>}

# LAW rows_example (R7): anchor: equal times list by id; a candidate without a cwd, with an
# empty cwd or without a file is not listed; a legacy file beside an entry
# of its stem's name is not listed
# EXCLUDES: a spec that lists any of them
law rows_example:
  {Ls.rows([Ls.Obs{Sg.Seen{Sg.Utf{"b"}, Sg.KDir{True{}}}, Some{"/p"}, [Sg.Time{10n, 0n}, Sg.Time{30n, 5n}, Sg.Time{20n, 0n}]}, Ls.Obs{Sg.Seen{Sg.Utf{"a"}, Sg.KDir{True{}}}, Some{"/p"}, [Sg.Time{30n, 5n}]}, Ls.Obs{Sg.Seen{Sg.Utf{"c.jsonl"}, Sg.KFile{}}, Some{"/q"}, [Sg.Time{40n, 0n}]}, Ls.Obs{Sg.Seen{Sg.Utf{"d"}, Sg.KDir{True{}}}, Some{""}, [Sg.Time{50n, 0n}]}, Ls.Obs{Sg.Seen{Sg.Utf{"e"}, Sg.KDir{True{}}}, None{}, [Sg.Time{50n, 0n}]}, Ls.Obs{Sg.Seen{Sg.Utf{"f"}, Sg.KDir{True{}}}, Some{"/x"}, []}, Ls.Obs{Sg.Seen{Sg.Utf{"c"}, Sg.KDir{False{}}}, None{}, []}, Ls.Obs{Sg.Seen{Sg.Utf{"g.jsonl"}, Sg.KFile{}}, Some{"/q"}, [Sg.Time{60n, 0n}]}]) == [Ls.Row{7n, Ls.PLegacy{"g"}, Sg.Time{60n, 0n}}, Ls.Row{1n, Ls.PStore{"a"}, Sg.Time{30n, 5n}}, Ls.Row{0n, Ls.PStore{"b"}, Sg.Time{30n, 5n}}] : List<&2, Ls.Row>}
