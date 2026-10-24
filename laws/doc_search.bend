# eukhe: the laws of area doc_search

import Base
import ../bend/doc_search.bend as Sr
import ../bend/ffi_doc_search.bend as FDs
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (F6) What grep searched
# -----------------------
# bend/doc_search.bend: every input is free: any walk (text files with
# any number of matches, over the size limit or not; binary files, files
# that do not open, excluded directories, symlinks, walk errors, in any
# order), any match cap of a file, any total match cap, any page.

# LAW grep_accounts_every_file: every walked entry is in exactly one class (no match, shown,
# paged out, not searched, or skipped with its reason): the classes add
# up to the walk
law grep_accounts_every_file:
  for +es: List<&2, Sr.Ent>
  for +p: Nat
  for +s: Nat
  for +k: Nat
  for +rem: Nat
  for +n: Nat
  {Sr.Count.total(Sr.account(Sr.run(es, p, s, k, rem, n))) == List.length(&2, Sr.Ent, es) : Nat}

# LAW grep_notes_every_gap: a result has the notice of a class of entries it did not search,
# skipped, or searched only in part exactly when that class is not empty
law grep_notes_every_gap:
  for +os: List<&2, Sr.Out>
  for +t: Sr.Note
  {Sr.noted(t, os) == Bool.not(Nat.is_eq(Sr.Note.count(Sr.account(os), t), 0n)) : Bool}

# LAW grep_notes_every_cut: a shown file whose matches were cut has its own notice
law grep_notes_every_cut:
  for +pre: List<&2, Sr.Out>
  for +i: Nat
  for +pa: Bool
  for +post: List<&2, Sr.Out>
  {Sr.mem(i, Sr.cuts(List.append(&2, Sr.Out, pre, Sr.Out{i, Sr.Shown{}, True{}, pa} <> post))) == True{} : Bool}

# (F7) Continuations
# ------------------
# bend/doc_search.bend: every input is free: any ordered list (the
# matching files of grep, the ranked paths of glob), any skip, any page
# size, and the continuation the page gives.

# LAW continuation_progresses: a continuation gives a page that is not empty
law continuation_progresses:
  for +ps: List<&2, Nat>
  for +s: Nat
  for +k: Nat
  for +c: Nat
  for h: {Sr.next(ps, s, k) == Some{c} : Maybe<&2, Nat>}
  {List.is_empty(&2, Nat, Sr.page(ps, c, k)) == False{} : Bool}

# LAW continuation_contiguous: a page and the page of its continuation are, together, the start
# of the list after the skip: nothing left out between them, nothing
# twice
law continuation_contiguous:
  for +ps: List<&2, Nat>
  for +s: Nat
  for +k: Nat
  for +c: Nat
  for h: {Sr.next(ps, s, k) == Some{c} : Maybe<&2, Nat>}
  exs rest: List<&2, Nat>
  {List.append(&2, Nat, Sr.page(ps, s, k), List.append(&2, Nat, Sr.page(ps, c, k), rest)) == List.drop(&2, Nat, ps, s) : List<&2, Nat>}

# LAW continuation_disjoint: in a list with no item twice, a page and the page of its
# continuation have no item in common
law continuation_disjoint:
  for +ps: List<&2, Nat>
  for +s: Nat
  for +k: Nat
  for +c: Nat
  for +x: Nat
  for h: {Sr.next(ps, s, k) == Some{c} : Maybe<&2, Nat>}
  for nd: {Sr.nodup(ps) == True{} : Bool}
  {Bool.and(Sr.mem(x, Sr.page(ps, s, k)), Sr.mem(x, Sr.page(ps, c, k))) == False{} : Bool}

# (F8) The rules, exactly
# -----------------------
# bend/doc_search.bend: each rule the entry runs, stated whole by a spec
# here (helpers ds_*, which never call the code): the class, cut and
# matches of each entry of a walk, the matches a file fetches, a page and
# its continuation, the match limit.

# the spec of a page: the items of ps after the first s, k of them
def ds_first(ps: List<&2, Nat>, k: Nat) -> List<&2, Nat>:
  match ps:
    case Nil{}:
      Nil{}
    case x <> t:
      match k:
        case 0n:
          Nil{}
        case 1n+j:
          x <> ds_first(t, j)

def ds_window(ps: List<&2, Nat>, s: Nat, k: Nat) -> List<&2, Nat>:
  match ps:
    case Nil{}:
      Nil{}
    case x <> t:
      match s:
        case 0n:
          ds_first(x <> t, k)
        case 1n+r:
          ds_window(t, r, k)

def ds_some_if(b: Bool, c: Nat) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{c}
    case False{}:
      None{}

# the spec of a continuation: s + k, when k is not 0 and an item of the n
# follows the page
def ds_more(+n: Nat, +s: Nat, +k: Nat) -> Maybe<&2, Nat>:
  ds_some_if(Bool.and(Nat.is_lt(0n, k), Nat.is_lt(Nat.add(s, k), n)), Nat.add(s, k))

def ds_when(b: Bool, m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      m
    case False{}:
      None{}

# the numbers i, i + 1, ... (t of them)
def ds_from(t: Nat, +i: Nat) -> List<&2, Nat>:
  match t:
    case 0n:
      Nil{}
    case 1n+u:
      i <> ds_from(u, Nat.add(1n, i))

# LAW page_is_window: a page is the k items after the first s, in order
# EXCLUDES: a page that skips other than s items, holds other than k, or
#   reorders them (the continuation laws hold for many wrong pages)
law page_is_window:
  for +ps: List<&2, Nat>
  for +s: Nat
  for +k: Nat
  {Sr.page(ps, s, k) == ds_window(ps, s, k) : List<&2, Nat>}

# LAW next_is_more: the continuation is s + k exactly when k is not 0 and an item follows the
# page, and none otherwise
# EXCLUDES: a continuation that never comes (the continuation laws are
#   then vacuous), one that comes at the end, one that is not s + k
law next_is_more:
  for +ps: List<&2, Nat>
  for +s: Nat
  for +k: Nat
  {Sr.next(ps, s, k) == ds_more(List.length(&2, Nat, ps), s, k) : Maybe<&2, Nat>}

# LAW past_is_beyond: the skip is past the end exactly when the list is not empty and the skip is
# its length or more
# EXCLUDES: a past-the-end notice for an empty result or for a skip that
#   still shows items, none for a skip past the end
law past_is_beyond:
  for +ps: List<&2, Nat>
  for +s: Nat
  {Sr.past(ps, s) == Bool.and(Nat.is_lt(0n, List.length(&2, Nat, ps)), Nat.is_le(List.length(&2, Nat, ps), s)) : Bool}

# LAW grep_scope_pages: grep's continuation and past-the-end notice are those of its page in a scope of
# several files, and none in a scope of one file
# EXCLUDES: paging one file, no paging for a directory
law grep_scope_pages:
  for +m: Bool
  for +ps: List<&2, Nat>
  for +s: Nat
  for +k: Nat
  {(Sr.grep.next(m, ps, s, k), Sr.grep.past(m, ps, s)) == (ds_when(m, Sr.next(ps, s, k)), Bool.and(m, Sr.past(ps, s))) : Maybe<&2, Nat> & Bool}

# LAW upto_counts: the matching files of a search are numbered 0 to t - 1, in walk order
# EXCLUDES: a page of other numbers than the files found
law upto_counts:
  for +t: Nat
  {Sr.upto(t) == ds_from(t, 0n) : List<&2, Nat>}

# the spec of one entry of a walk with rem matches left and n matching
# files before it: a file opens only while a match is left to keep; it
# keeps at most p and at most rem; it is cut when it holds more than it
# may keep; a matching file is shown when its number is on the page
def ds_cls_if(b: Bool, x: Sr.Class, y: Sr.Class) -> Sr.Class:
  match b:
    case True{}:
      x
    case False{}:
      y

def ds_opens(w: Sr.Reason) -> Bool:
  match w:
    case Sr.Binary{}:
      True{}
    case Sr.Unreadable{}:
      True{}
    case Sr.Excluded{}:
      False{}
    case Sr.Link{}:
      False{}
    case Sr.Broken{}:
      False{}

def ds_onpage(+n: Nat, +s: Nat, +k: Nat) -> Sr.Class:
  ds_cls_if(Bool.and(Nat.is_le(s, n), Nat.is_lt(n, Nat.add(s, k))), Sr.Shown{}, Sr.PagedOut{})

def ds_bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def ds_out(e: Sr.Ent, +p: Nat, +s: Nat, +k: Nat, +rem: Nat, +n: Nat) -> Sr.Out:
  match e:
    case Sr.Ent{i, f}:
      match f:
        case Sr.Opened{+h, big}:
          +live = Nat.is_lt(0n, rem)
          Sr.Out{i, ds_cls_if(live, ds_cls_if(Nat.is_eq(h, 0n), Sr.NoMatch{}, ds_onpage(n, s, k)), Sr.Unsearched{}), Bool.and(live, Nat.is_lt(Nat.min(p, rem), h)), Bool.and(live, big)}
        case Sr.Skip{+w}:
          Sr.Out{i, ds_cls_if(Bool.and(Nat.is_eq(rem, 0n), ds_opens(w)), Sr.Unsearched{}, Sr.Skipped{w}), False{}, False{}}

def ds_kept(e: Sr.Ent, +p: Nat, +rem: Nat) -> Nat:
  match e:
    case Sr.Ent{i, f}:
      match f:
        case Sr.Opened{h, big}:
          Nat.min(h, Nat.min(p, rem))
        case Sr.Skip{w}:
          0n

def ds_seen(e: Sr.Ent, +rem: Nat, +n: Nat) -> Nat:
  match e:
    case Sr.Ent{i, f}:
      match f:
        case Sr.Opened{h, big}:
          Nat.add(ds_bit(Bool.and(Nat.is_lt(0n, rem), Nat.is_lt(0n, h))), n)
        case Sr.Skip{w}:
          n

# LAW grep_walk_spec: a walk is its first entry, as the spec classes it, then the rest of the
# walk with the matches it kept taken off and one more matching file when it matched;
# an empty walk has no entry
# EXCLUDES: a wrong class (a match shown off its page, a file searched
#   after the cap, a skip counted as not searched), a cut missed or made up,
#   a per-file or total cap not kept, a page number that skips a file
law grep_walk_spec:
  for +e: Sr.Ent
  for +es: List<&2, Sr.Ent>
  for +p: Nat
  for +s: Nat
  for +k: Nat
  for +rem: Nat
  for +n: Nat
  {(Sr.run(Nil{}, p, s, k, rem, n), Sr.run(e <> es, p, s, k, rem, n)) == (Nil{}, ds_out(e, p, s, k, rem, n) <> Sr.run(es, p, s, k, Nat.sub(rem, ds_kept(e, p, rem)), ds_seen(e, rem, n))) : List<&2, Sr.Out> & List<&2, Sr.Out>}

# the matches each entry keeps, in walk order
def ds_keeps(es: List<&2, Sr.Ent>, +p: Nat, +rem: Nat) -> List<&2, Nat>:
  match es:
    case Nil{}:
      Nil{}
    case +e <> rest:
      ds_kept(e, p, rem) <> ds_keeps(rest, p, Nat.sub(rem, ds_kept(e, p, rem)))

# LAW grep_keeps_spec: the matches each entry of a walk keeps: at most p of a file, at most
# the matches left in all
# EXCLUDES: a file that keeps more than the caps let it, or fewer than it
#   holds under them
law grep_keeps_spec:
  for +es: List<&2, Sr.Ent>
  for +p: Nat
  for +rem: Nat
  {Sr.keeps(es, p, rem) == ds_keeps(es, p, rem) : List<&2, Nat>}

# the line a range needs reached: its end, or base lines from its start
def ds_need(r: Sr.Range, +base: Nat) -> Nat:
  match r:
    case Sr.Range{a, z}:
      match z:
        case Some{e}:
          e
        case None{}:
          Nat.add(Nat.sub(a, 1n), base)

def ds_needs(rs: List<&2, Sr.Range>, +base: Nat) -> Nat:
  match rs:
    case Nil{}:
      0n
    case r <> t:
      Nat.max(ds_need(r, base), ds_needs(t, base))

def ds_fetch(rs: List<&2, Sr.Range>, +p: Nat, +rem: Nat, +maxb: Nat) -> Nat:
  match rs:
    case Nil{}:
      Nat.add(1n, Nat.min(p, rem))
    case r <> t:
      Nat.max(Nat.add(1n, p), Nat.min(ds_needs(r <> t, Nat.add(1n, p)), Nat.add(1n, maxb)))

# LAW fetch_reaches: a file of no line range fetches one match more than it may keep (min(p,
# rem) + 1); a file of line ranges fetches enough to reach the last line
# any range needs (its end, or p + 1 lines from an open range's start),
# at most maxb + 1, and at least p + 1
# EXCLUDES: a fetch that cannot show a cut, one that stops before a
#   selected line, one past what a file of maxb bytes holds
law fetch_reaches:
  for +rs: List<&2, Sr.Range>
  for +p: Nat
  for +rem: Nat
  for +maxb: Nat
  {Sr.fetch(rs, p, rem, maxb) == ds_fetch(rs, p, rem, maxb) : Nat}

# the spec of the match limit: round r, then the rounds after it; in a
# round each file with more than r matches gives one, in file order,
# while the budget lasts; there are as many rounds as the most matches of
# a file
def ds_sum(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      Nat.add(x, ds_sum(t))

def ds_top(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case x <> t:
      Nat.max(x, ds_top(t))

def ds_round(cs: List<&2, Nat>, +r: Nat, +b: Nat) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      +g = ds_bit(Bool.and(Nat.is_lt(0n, b), Nat.is_lt(r, c)))
      g <> ds_round(t, r, Nat.sub(b, g))

def ds_plus(xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case x <> t:
      match ys:
        case Nil{}:
          Nil{}
        case y <> u:
          Nat.add(x, y) <> ds_plus(t, u)

def ds_rounds(f: Nat, +cs: List<&2, Nat>, +r: Nat, +b: Nat) -> List<&2, Nat>:
  match f:
    case 0n:
      ds_round(cs, r, 0n)
    case 1n+g:
      +got = ds_round(cs, r, b)
      ds_plus(got, ds_rounds(g, cs, Nat.add(1n, r), Nat.sub(b, ds_sum(got))))

# LAW limit_round_robin: under a limit of l the page's files keep their matches one per file
# per round, in file order, l in all
# EXCLUDES: one file taking the whole limit, a file skipped in a round,
#   more than l matches kept, fewer than min(l, all) kept
law limit_round_robin:
  for +cs: List<&2, Nat>
  for +l: Nat
  {Sr.rr(cs, l) == ds_rounds(ds_top(cs), cs, 0n, l) : List<&2, Nat>}

# LAW limit_cuts: the limit cuts matches exactly when the page holds more than l
# EXCLUDES: a limit notice for a page under the limit, none for one over
law limit_cuts:
  for +cs: List<&2, Nat>
  for +l: Nat
  {Sr.rr.cut(cs, l) == Nat.is_lt(l, ds_sum(cs)) : Bool}

# (F9) The compiled entry
# -----------------------
# bend/ffi_doc_search.bend, for every request and event that fits the
# wire: its replies are the rules' answers, spelled by the spec spellers
# here (ds_spell over the Wr primitives, whose round trips laws/wire.bend
# proves). Requests and replies are lists of Nats: a Bool is 0 or 1, a
# Maybe<Nat> 0 (none) or 1 + its value.

# the whole input or reply of a list of Nats
def ds_spell(+xs: List<&2, Nat>) -> String:
  Wr.put_list(~Nat, ~Wr.put_nat, xs, "")

# a list that fits the wire: its count and every item
def ds_fits(+xs: List<&2, Nat>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))

def ds_opt(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{v}:
      Nat.add(1n, v)

def ds_why(w: Sr.Reason) -> Nat:
  match w:
    case Sr.Binary{}:
      0n
    case Sr.Unreadable{}:
      1n
    case Sr.Excluded{}:
      2n
    case Sr.Link{}:
      3n
    case Sr.Broken{}:
      4n

def ds_class(c: Sr.Class) -> Nat:
  match c:
    case Sr.NoMatch{}:
      0n
    case Sr.Shown{}:
      1n
    case Sr.PagedOut{}:
      2n
    case Sr.Unsearched{}:
      3n
    case Sr.Skipped{w}:
      Nat.add(4n, ds_why(w))

def ds_bounds(rs: List<&2, Sr.Range>) -> List<&2, Nat>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> t:
      match r:
        case Sr.Range{a, z}:
          a <> ds_opt(z) <> ds_bounds(t)

# the events: the next file and its ranges; what a file held
def ds_ask(rs: List<&2, Sr.Range>) -> List<&2, Nat>:
  0n <> ds_bounds(rs)

def ds_met(f: Sr.Form) -> List<&2, Nat>:
  match f:
    case Sr.Opened{h, big}:
      [1n, h, ds_bit(big)]
    case Sr.Skip{w}:
      [2n, ds_why(w)]

# the reply to what a file held: its class, cut, searched in part, kept
def ds_said(o: Sr.Out, +kept: Nat) -> List<&2, Nat>:
  match o:
    case Sr.Out{i, c, cut, pa}:
      [ds_class(c), ds_bit(cut), ds_bit(pa), kept]

# LAW search_page_answers: a grep page request [0, t, s, k, multi] answers the continuation,
# the past-the-end notice and the page of the t matching files
# EXCLUDES: a page of other files, a continuation or notice the rules do
#   not give, t, s and k swapped or misread
law search_page_answers:
  for +t: Nat
  for +s: Nat
  for +k: Nat
  for +m: Bool
  for h: {ds_fits([0n, t, s, k, ds_bit(m)]) == True{} : Bool}
  {FDs.ffi(ds_spell([0n, t, s, k, ds_bit(m)])) == ds_spell(ds_opt(Sr.grep.next(m, Sr.upto(t), s, k)) <> ds_bit(Sr.grep.past(m, Sr.upto(t), s)) <> Sr.page(Sr.upto(t), s, k)) : String}

# LAW search_limit_answers: a match limit request [1, l, c ...] answers whether the limit cuts,
# then what each file keeps
# EXCLUDES: a limit run on other counts or another limit, the cut flag
#   dropped or flipped
law search_limit_answers:
  for +l: Nat
  for +cs: List<&2, Nat>
  for h: {ds_fits(1n <> l <> cs) == True{} : Bool}
  {FDs.ffi(ds_spell(1n <> l <> cs)) == ds_spell(ds_bit(Sr.rr.cut(cs, l)) <> Sr.rr(cs, l)) : String}

def ds_nat_if(b: Bool, x: Nat, y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

def ds_page_size(lim: Maybe<&2, Nat>) -> Nat:
  match lim:
    case None{}:
      20n
    case Some{l}:
      Nat.add(1n, l)

# the spec of grep's scope: several files when the path has more than one
# root or a directory root; then 20 matches a file and the skip asked,
# else 200 and no skip; a page of the match limit + 1 files, else 20
def ds_scope(roots: Nat, dirs: Nat, +skip: Nat, lim: Maybe<&2, Nat>) -> List<&2, Nat>:
  +m = Bool.or(Nat.is_lt(1n, roots), Nat.is_lt(0n, dirs))
  [ds_bit(m), ds_nat_if(m, 20n, 200n), ds_nat_if(m, skip, 0n), ds_page_size(lim)]

# LAW search_scope_answers: a scope request [2, roots, dirs, skip, lim] answers whether the
# scope holds several files, the matches a file keeps, the skip and the
# page size: several files with more than one root or a directory root,
# 20 matches a file and the skip asked; one file: 200 and no skip; a page
# of the match limit + 1 files, 20 without a limit
# EXCLUDES: one file paged or skipped, a directory read as one file, a
#   cap of the other scope, a page size off by one, fields swapped
law search_scope_answers:
  for +roots: Nat
  for +dirs: Nat
  for +skip: Nat
  for +lim: Maybe<&2, Nat>
  for h: {ds_fits([2n, roots, dirs, skip, ds_opt(lim)]) == True{} : Bool}
  {FDs.ffi(ds_spell([2n, roots, dirs, skip, ds_opt(lim)])) == ds_spell(ds_scope(roots, dirs, skip, lim)) : String}

# the spec reader: whether s is exactly the spelling of a list of Nats,
# nothing after it, of the shape a call (ds_call_ok), an open
# (ds_open_ok) or an event (ds_event_ok) needs
def ds_whole.end(e: Bool, xs: List<&2, Nat>) -> Maybe<&2, List<&2, Nat>>:
  match e:
    case True{}:
      Some{xs}
    case False{}:
      None{}

def ds_whole(r: Wr.Dec<List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
  match r:
    case Wr.Got{xs, rest}:
      ds_whole.end(String.is_empty(rest), xs)
    case Wr.Bad{}:
      None{}

def ds_pairs_ok(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case a <> t:
      match t:
        case Nil{}:
          False{}
        case b <> u:
          ds_pairs_ok(u)

def ds_len_is(xs: List<&2, Nat>, n: Nat) -> Bool:
  Nat.is_eq(List.length(&2, Nat, xs), n)

def ds_last_bit(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      match t:
        case Nil{}:
          Nat.is_le(x, 1n)
        case y <> u:
          ds_last_bit(t)

# the shape of a call: [0, t, s, k, multi 0 or 1], [1, l, c ...],
# [2, roots, dirs, skip, lim]
def ds_call_ok(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +tag <> +t:
      Bool.or(Bool.and(Nat.is_eq(tag, 0n), Bool.and(ds_len_is(t, 4n), ds_last_bit(t))), Bool.or(Bool.and(Nat.is_eq(tag, 1n), Nat.is_lt(0n, List.length(&2, Nat, t))), Bool.and(Nat.is_eq(tag, 2n), ds_len_is(t, 4n))))

def ds_last_why(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Nat.is_le(x, 4n)

# the shape of an event: [0, start, stop ...], [1, h, big 0 or 1],
# [2, why 0 to 4]
def ds_event_ok(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case +tag <> +t:
      Bool.or(Bool.and(Nat.is_eq(tag, 0n), ds_pairs_ok(t)), Bool.or(Bool.and(Nat.is_eq(tag, 1n), Bool.and(ds_len_is(t, 2n), ds_last_bit(t))), Bool.and(Nat.is_eq(tag, 2n), Bool.and(ds_len_is(t, 1n), ds_last_why(t)))))

def ds_open_ok(xs: List<&2, Nat>) -> Bool:
  ds_len_is(xs, 6n)

def ds_call_of(m: Maybe<&2, List<&2, Nat>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{xs}:
      ds_call_ok(xs)

def ds_open_of(m: Maybe<&2, List<&2, Nat>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{xs}:
      ds_open_ok(xs)

def ds_event_of(m: Maybe<&2, List<&2, Nat>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{xs}:
      ds_event_ok(xs)

# the list s spells, whole
def ds_read(s: String) -> Maybe<&2, List<&2, Nat>>:
  ds_whole(Wr.get_list(~Nat, ~Wr.get_nat, s))

# LAW search_ffi_refuses: any input that is not exactly a call's list answers the error form
# EXCLUDES: a default page, limit or glob for bad input, input left over
#   read, an unknown tag or a multi of 2 taken for a call
law search_ffi_refuses:
  for +s: String
  for no: {ds_call_of(ds_read(s)) == False{} : Bool}
  {FDs.ffi(s) == Wr.err("doc_search: malformed request") : String}

# LAW search_open_answers: an open [p, s, k, rem, t, maxb] starts the walk with those limits
# and no matching file met; the reply is empty
# EXCLUDES: limits swapped or dropped, a walk that starts with files met
law search_open_answers:
  for +p: Nat
  for +s: Nat
  for +k: Nat
  for +rem: Nat
  for +t: Nat
  for +maxb: Nat
  for h: {ds_fits([p, s, k, rem, t, maxb]) == True{} : Bool}
  {FDs.open(ds_spell([p, s, k, rem, t, maxb])) == (FDs.Walk{p, s, k, rem, 0n, t, maxb}, "") : FDs.St & String}

# LAW search_open_refuses: any other open opens the refused state, with the error form
# EXCLUDES: a walk on default limits for a bad open
law search_open_refuses:
  for +s: String
  for no: {ds_open_of(ds_read(s)) == False{} : Bool}
  {FDs.open(s) == (FDs.Shut{}, Wr.err("doc_search: malformed open")) : FDs.St & String}

# LAW search_shut_refuses: the refused state answers every event with the error form
# EXCLUDES: a walk run on made-up limits after a refused open
law search_shut_refuses:
  for +s: String
  {FDs.step(FDs.Shut{}, s) == (FDs.Shut{}, Wr.err("doc_search: the open was refused")) : FDs.St & String}

# LAW search_step_refuses: an event that is not exactly an event's list answers the error form
# and keeps the walk
# EXCLUDES: a guessed event, a walk changed by a bad event
law search_step_refuses:
  for +p: Nat
  for +s: Nat
  for +k: Nat
  for +rem: Nat
  for +n: Nat
  for +t: Nat
  for +maxb: Nat
  for +x: String
  for no: {ds_event_of(ds_read(x)) == False{} : Bool}
  {FDs.step(FDs.Walk{p, s, k, rem, n, t, maxb}, x) == (FDs.Walk{p, s, k, rem, n, t, maxb}, Wr.err("doc_search: malformed event")) : FDs.St & String}

# LAW search_ask_stops: with no match left to keep, the next file is not opened: the reply is
# [0, t], the t files not met are not searched, and the walk stays
# EXCLUDES: a file opened after the total cap, a wrong count of files not
#   searched
law search_ask_stops:
  for +p: Nat
  for +s: Nat
  for +k: Nat
  for +n: Nat
  for +t: Nat
  for +maxb: Nat
  for +rs: List<&2, Sr.Range>
  for h: {ds_fits(ds_ask(rs)) == True{} : Bool}
  {FDs.step(FDs.Walk{p, s, k, 0n, n, t, maxb}, ds_spell(ds_ask(rs))) == (FDs.Walk{p, s, k, 0n, n, t, maxb}, ds_spell([0n, t])) : FDs.St & String}

# LAW search_ask_fetches: with a match left, the next file is searched: the reply is [1,
# fetch], the matches its ranges need, and the walk stays
# EXCLUDES: a stop before the cap, a fetch of other ranges or caps
law search_ask_fetches:
  for +p: Nat
  for +s: Nat
  for +k: Nat
  for +r: Nat
  for +n: Nat
  for +t: Nat
  for +maxb: Nat
  for +rs: List<&2, Sr.Range>
  for h: {ds_fits(ds_ask(rs)) == True{} : Bool}
  {FDs.step(FDs.Walk{p, s, k, 1n+r, n, t, maxb}, ds_spell(ds_ask(rs))) == (FDs.Walk{p, s, k, 1n+r, n, t, maxb}, ds_spell([1n, Sr.fetch(rs, p, 1n+r, maxb)])) : FDs.St & String}

# LAW search_met_answers: what a file held answers its class, cut, searched in part and the
# matches it keeps, as the rules class the entry; the walk goes on with the
# matches left, the matching files met and one file fewer to meet
# EXCLUDES: a reply that is not the rules' decision, a walk that forgets
#   the matches kept or the matching files met
law search_met_answers:
  for +p: Nat
  for +s: Nat
  for +k: Nat
  for +rem: Nat
  for +n: Nat
  for +t: Nat
  for +maxb: Nat
  for +f: Sr.Form
  for h: {ds_fits(ds_met(f)) == True{} : Bool}
  {FDs.step(FDs.Walk{p, s, k, rem, n, t, maxb}, ds_spell(ds_met(f))) == (FDs.Walk{p, s, k, Sr.left(Sr.Ent{0n, f}, p, rem), Sr.seen(Sr.Ent{0n, f}, rem, n), Nat.sub(t, 1n), maxb}, ds_spell(ds_said(Sr.out(Sr.Ent{0n, f}, p, s, k, rem, n), Sr.kept(Sr.Ent{0n, f}, p, rem)))) : FDs.St & String}

# the replies of the stepper to the files of a walk, after the reply of r
def ds_drive(es: List<&2, Sr.Ent>, r: FDs.St & String) -> List<&2, String>:
  match es:
    case Nil{}:
      match r:
        case (st, said):
          [said]
    case e <> rest:
      match e:
        case Sr.Ent{i, f}:
          match r:
            case (st, said):
              said <> ds_drive(rest, FDs.step(st, ds_spell(ds_met(f))))

# what the rules say of each entry of a walk, spelled
def ds_trace(os: List<&2, Sr.Out>, ks: List<&2, Nat>) -> List<&2, String>:
  match os:
    case Nil{}:
      Nil{}
    case o <> t:
      match ks:
        case Nil{}:
          Nil{}
        case k <> u:
          ds_spell(ds_said(o, k)) <> ds_trace(t, u)

def ds_walk_fits(es: List<&2, Sr.Ent>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> t:
      match e:
        case Sr.Ent{i, f}:
          Bool.and(ds_fits(ds_met(f)), ds_walk_fits(t))

# LAW search_walk_runs: a walk the stepper is fed file by file answers what the rules' run
# gives each entry, and the matches each keeps
# EXCLUDES: a stepper whose state drifts from the run (matches left or
#   matching files met miscounted between files)
law search_walk_runs:
  for +es: List<&2, Sr.Ent>
  for +p: Nat
  for +s: Nat
  for +k: Nat
  for +rem: Nat
  for +n: Nat
  for +t: Nat
  for +maxb: Nat
  for h: {ds_walk_fits(es) == True{} : Bool}
  {ds_drive(es, (FDs.Walk{p, s, k, rem, n, t, maxb}, "")) == "" <> ds_trace(Sr.run(es, p, s, k, rem, n), Sr.keeps(es, p, rem)) : List<&2, String>}

# LAW search_calls_example: anchor: the calls Rust writes, as text: a page of 5 files (2 from 0,
# several files), the limit 3 over 3, 1 and 4 matches, the scope of a
# directory root with skip 7 and no limit, the scope of one file with a
# limit of 2
# EXCLUDES: a codec that reads other fields or writes another reply
law search_calls_example:
  {[FDs.ffi("5,0,5,0,2,1,"), FDs.ffi("5,1,3,3,1,4,"), FDs.ffi("5,2,1,1,7,0,"), FDs.ffi("5,2,1,0,7,3,")] == ["4,3,0,0,1,", "4,1,1,1,1,", "4,1,20,7,20,", "4,0,200,0,3,"] : List<&2, String>}

# LAW search_walk_example: anchor: an open (20 a file, page 0 to 20, 30 in all, 3 files, 100
# bytes), the first file asked for (fetch 21) and found with 25 matches
# (shown, cut, 20 kept), the second skipped as binary
# EXCLUDES: a stepper Rust's text would misread
law search_walk_example:
  {ds_drive([Sr.Ent{0n, Sr.Opened{25n, False{}}}, Sr.Ent{1n, Sr.Skip{Sr.Binary{}}}], FDs.open("6,20,0,20,30,3,100,")) == ["", "4,1,1,0,20,", "4,4,0,0,0,"] : List<&2, String>} & {FDs.step(FDs.Walk{20n, 0n, 20n, 30n, 0n, 3n, 100n}, "1,0,") == (FDs.Walk{20n, 0n, 20n, 30n, 0n, 3n, 100n}, "2,1,21,") : FDs.St & String} & {FDs.step(FDs.Walk{20n, 0n, 20n, 0n, 1n, 2n, 100n}, "1,0,") == (FDs.Walk{20n, 0n, 20n, 0n, 1n, 2n, 100n}, "2,0,2,") : FDs.St & String}

# LAW search_refuses_example: anchor: a multi of 2, input left over, an open of 5 limits and a
# skip reason of 7 are refused
# EXCLUDES: a codec that accepts what Rust never writes
law search_refuses_example:
  {[FDs.ffi("5,0,5,0,2,2,"), FDs.ffi("5,0,5,0,2,1,x")] == [Wr.err("doc_search: malformed request"), Wr.err("doc_search: malformed request")] : List<&2, String>} & {FDs.open("5,20,0,20,30,3,") == (FDs.Shut{}, Wr.err("doc_search: malformed open")) : FDs.St & String} & {FDs.step(FDs.Walk{20n, 0n, 20n, 30n, 0n, 3n, 100n}, "2,2,7,") == (FDs.Walk{20n, 0n, 20n, 30n, 0n, 3n, 100n}, Wr.err("doc_search: malformed event")) : FDs.St & String}

# (F10) The helpers the laws above lean on
# ----------------------------------------
# grep_accounts_every_file, grep_notes_every_gap, grep_notes_every_cut and
# continuation_disjoint read the result through the model's account,
# membership and no-duplicate tests; these laws pin those to specs here.

# how many entries of os are of class code k (ds_class), and how many
# were searched in part
def ds_n(os: List<&2, Sr.Out>, +k: Nat) -> Nat:
  match os:
    case Nil{}:
      0n
    case o <> t:
      match o:
        case Sr.Out{i, c, cut, pa}:
          Nat.add(ds_bit(Nat.is_eq(ds_class(c), k)), ds_n(t, k))

def ds_partials(os: List<&2, Sr.Out>) -> Nat:
  match os:
    case Nil{}:
      0n
    case o <> t:
      match o:
        case Sr.Out{i, c, cut, pa}:
          Nat.add(ds_bit(pa), ds_partials(t))

# LAW grep_account_exact: the account of a result counts, in each class, exactly the entries of
# that class (no match, shown, paged out, not searched, binary, unreadable,
# excluded, symlink, walk error), and the entries searched in part
# EXCLUDES: an entry counted in another class (a symlink counted as
#   excluded), so a notice of the wrong class shows and the right one is
#   missing
law grep_account_exact:
  for +os: List<&2, Sr.Out>
  {Sr.account(os) == Sr.Count{ds_n(os, 0n), ds_n(os, 1n), ds_n(os, 2n), ds_n(os, 3n), ds_n(os, 4n), ds_n(os, 5n), ds_n(os, 6n), ds_n(os, 7n), ds_n(os, 8n), ds_partials(os)} : Sr.Count}

def ds_mem(+x: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> t:
      Bool.or(Nat.is_eq(y, x), ds_mem(x, t))

def ds_nodup(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +y <> +t:
      Bool.and(Bool.not(ds_mem(y, t)), ds_nodup(t))

# LAW search_list_tests_exact: the model's membership and no-duplicate tests are the specs'
# EXCLUDES: continuation_disjoint or grep_notes_every_cut made vacuous by a
#   test that always answers one way
law search_list_tests_exact:
  for +x: Nat
  for +xs: List<&2, Nat>
  {Sr.mem(x, xs) == ds_mem(x, xs) : Bool} & {Sr.nodup(xs) == ds_nodup(xs) : Bool}

# how many entries of os the notice n reports: those skipped for its
# reason, those not searched, those searched in part
def ds_note_n(+os: List<&2, Sr.Out>, n: Sr.Note) -> Nat:
  match n:
    case Sr.NSkip{w}:
      ds_n(os, Nat.add(4n, ds_why(w)))
    case Sr.NPartial{}:
      ds_partials(os)
    case Sr.NUnsearched{}:
      ds_n(os, 3n)

# LAW search_note_count_exact: the count a notice reads off a result's
# account is the number of entries of the notice's class: those skipped
# for its reason, those not searched, those searched in part
# EXCLUDES: grep_notes_every_gap made circular by a notice that reads
#   another class's counter (a symlink notice that counts excluded
#   directories: no notice for a skipped symlink, a symlink notice for a
#   tree with only node_modules)
law search_note_count_exact:
  for +os: List<&2, Sr.Out>
  for +n: Sr.Note
  {Sr.Note.count(Sr.account(os), n) == ds_note_n(os, n) : Nat}

def ds_cut_if(b: Bool, i: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      i <> rest
    case False{}:
      rest

# the shown entries whose matches were cut, in walk order
def ds_cuts(os: List<&2, Sr.Out>) -> List<&2, Nat>:
  match os:
    case Nil{}:
      Nil{}
    case o <> t:
      match o:
        case Sr.Out{i, c, cut, pa}:
          ds_cut_if(Bool.and(Nat.is_eq(ds_class(c), 1n), cut), i, ds_cuts(t))

# LAW search_cuts_exact: the files with a cut notice are exactly the shown
# files whose matches were cut, in walk order
# EXCLUDES: a cut notice for a file that was not cut or not shown (the
#   converse grep_notes_every_cut does not state)
law search_cuts_exact:
  for +os: List<&2, Sr.Out>
  {Sr.cuts(os) == ds_cuts(os) : List<&2, Nat>}
