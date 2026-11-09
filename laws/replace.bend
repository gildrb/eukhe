# eukhe: the laws of area replace

import Base
import ../bend/ffi_replace.bend as FRp
import ../bend/replace.bend as Rp
import ../bend/semver.bend as Sv
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# The orphan entry of the compiled core (bend/ffi_orphan.bend)

# LAW replace_never_downgrades: client starts never take the daemon back to a lower build. For any
# client starts (any builds, interactive or background), no daemon ranks
# below a daemon that ran before it
law replace_never_downgrades:
  for +ss: List<&2, Rp.Start>
  {Rp.never_back(Rp.daemons(ss)) == True{} : Bool}

# LAW replacement_terminates: replacements stop. Client starts whose builds are all in bs (k
# builds) replace the daemon k - 1 times at most
law replacement_terminates:
  for +bs: List<&2, Rp.Build>
  for +ss: List<&2, Rp.Start>
  for cover: {Rp.covers(bs, ss) == True{} : Bool}
  {Nat.is_le(Rp.replaced(ss), Nat.sub(List.length(&2, Rp.Build, bs), 1n)) == True{} : Bool}

# The builds of client starts, by the laws' own equality (independent of
# the model's Rp.covers)

# the numbers of xs and ys are equal, item by item, and as many
def rp_nats_same(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} y <> yr:
      False{}
    case x <> xr Nil{}:
      False{}
    case +x <> xr +y <> yr:
      Bool.and(Nat.is_eq(x, y), rp_nats_same(xr, yr))

# a and b are the same build: equal build ids and equal ranks
def rp_build_same(a: Rp.Build, b: Rp.Build) -> Bool:
  match a b:
    case Rp.Build{ra, ia} Rp.Build{rb, ib}:
      Bool.and(String.eq(ia, ib), rp_nats_same(ra, rb))

# b is one of the builds bs
def rp_built(bs: List<&2, Rp.Build>, +b: Rp.Build) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case e <> t:
      Bool.or(rp_build_same(e, b), rp_built(t, b))

# the build of every start of ss is one of bs
def rp_all_built(+bs: List<&2, Rp.Build>, ss: List<&2, Rp.Start>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case s <> rest:
      match s:
        case Rp.Start{c, k}:
          Bool.and(rp_built(bs, c), rp_all_built(bs, rest))

# LAW replacement_terminates_any: replacements stop. Client starts whose builds are all in bs (k
# builds), by the laws' own build equality (same id, same rank), replace the
# daemon k - 1 times at most
# EXCLUDES: a vacuous replacement_terminates (a model whose Rp.covers or
#   Rp.ranks_eq answers False for builds that are in bs), endless
#   replacements between the builds of bs
law replacement_terminates_any:
  for +bs: List<&2, Rp.Build>
  for +ss: List<&2, Rp.Start>
  for cover: {rp_all_built(bs, ss) == True{} : Bool}
  {Nat.is_le(Rp.replaced(ss), Nat.sub(List.length(&2, Rp.Build, bs), 1n)) == True{} : Bool}

# LAW replacement_terminates_example: witness and teeth: an interactive start of an older build o,
# then of a newer build n: both builds are in [o, n], and the one
# replacement meets the bound k - 1 = 1
# EXCLUDES: a vacuous replacement_terminates_any (no starts satisfy its
#   premise), a bound met only because nothing is ever replaced
law replacement_terminates_example:
  {rp_all_built([Rp.Build{[1n, 0n, 1n, 0n], "o"}, Rp.Build{[1n, 0n, 1n, 1n], "n"}], [Rp.Start{Rp.Build{[1n, 0n, 1n, 0n], "o"}, Rp.Interactive{}}, Rp.Start{Rp.Build{[1n, 0n, 1n, 1n], "n"}, Rp.Interactive{}}]) == True{} : Bool} & {Rp.replaced([Rp.Start{Rp.Build{[1n, 0n, 1n, 0n], "o"}, Rp.Interactive{}}, Rp.Start{Rp.Build{[1n, 0n, 1n, 1n], "n"}, Rp.Interactive{}}]) == 1n : Nat} & {Nat.sub(List.length(&2, Rp.Build, [Rp.Build{[1n, 0n, 1n, 0n], "o"}, Rp.Build{[1n, 0n, 1n, 1n], "n"}]), 1n) == 1n : Nat}

# LAW background_never_replaces: a background client (the dashboard, the gateway, ACP, a reconnect)
# never replaces a running daemon
law background_never_replaces:
  for +c: Rp.Build
  for +d: Rp.Build
  {Rp.after(Rp.Start{c, Rp.Background{}}, Some{d}) == d : Rp.Build}

# The rank of a version, read by semver.bend's reader (the spec): the text
# before the first '-' read as a version X.Y.Z (Sv.Ver.parse: decimal
# numbers without leading zeros, three of them, nothing else) whose
# numbers have at most 14 digits; [X, Y, 0, Z] with a '-' (a prerelease),
# [X, Y, 1, Z] without; [] for any other text. A number of 15 digits or
# more is past the range of the compiled core's numbers (2^48 - 1): its
# version has no rank, as text that is no version. A text of more than 64
# chars has no rank either (no version is that long): the first 65 chars
# of any text decide its rank, so Rust sends only those.

def rank_spec.core.at(dash: Bool, c: Char, rest: String) -> String:
  match dash:
    case True{}:
      SNil{}
    case False{}:
      SCon{c, rest}

# the text before the first '-'
def rank_spec.core(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, r}:
      rank_spec.core.at(Char.is_eq(c, '-'), c, rank_spec.core(r))

def rank_spec.tier.at(dash: Bool, rest: Nat) -> Nat:
  match dash:
    case True{}:
      0n
    case False{}:
      rest

# 0 with a '-' in the text, else 1
def rank_spec.tier(s: String) -> Nat:
  match s:
    case SNil{}:
      1n
    case SCon{c, r}:
      rank_spec.tier.at(Char.is_eq(c, '-'), rank_spec.tier(r))

def rank_spec.keep(ok: Bool, a: Nat, b: Nat, t: Nat, c: Nat) -> List<&2, Nat>:
  match ok:
    case True{}:
      [a, b, t, c]
    case False{}:
      Nil{}

def rank_spec.of(m: Maybe<&2, Sv.Ver>, t: Nat) -> List<&2, Nat>:
  match m:
    case None{}:
      Nil{}
    case Some{v}:
      match v:
        case Sv.Ver{+a, +b, +c}:
          rank_spec.keep(Bool.and(LawsBase.rank_spec.short(a), Bool.and(LawsBase.rank_spec.short(b), LawsBase.rank_spec.short(c))), a, b, t, c)

def rank_spec.cap(short: Bool, +s: String) -> List<&2, Nat>:
  match short:
    case True{}:
      rank_spec.of(Sv.Ver.parse(rank_spec.core(s)), rank_spec.tier(s))
    case False{}:
      Nil{}

def rank_spec(+s: String) -> List<&2, Nat>:
  rank_spec.cap(Nat.is_le(String.length(s), 64n), s)

# The order of ranks: lexicographic, the empty rank lowest
def rank_below(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      False{}
    case Nil{} y <> yr:
      True{}
    case x <> xr Nil{}:
      False{}
    case +x <> xr +y <> yr:
      Bool.or(Nat.is_lt(x, y), Bool.and(Nat.is_eq(x, y), rank_below(xr, yr)))

def rel_spec.pick(same: Bool, older: Bool, newer: Bool) -> Rp.Rel:
  match same older newer:
    case True{} _ _:
      Rp.Same{}
    case False{} True{} _:
      Rp.Older{}
    case False{} False{} True{}:
      Rp.Newer{}
    case False{} False{} False{}:
      Rp.Other{}

# how daemon d relates to client c: the same build id is the same build;
# else the daemon's rank is below (older), above (newer) or neither
# (another build of an equal rank)
def rel_spec(c: Rp.Build, d: Rp.Build) -> Rp.Rel:
  match c d:
    case Rp.Build{+rc, ic} Rp.Build{+rd, id}:
      rel_spec.pick(String.eq(ic, id), rank_below(rd, rc), rank_below(rc, rd))

# an interactive start replaces an older daemon; every other start keeps
# the daemon and names the relation
def verdict_spec(r: Rp.Rel, k: Rp.Caller) -> Rp.Verdict:
  match r k:
    case Rp.Older{} Rp.Interactive{}:
      Rp.Replace{}
    case Rp.Older{} Rp.Background{}:
      Rp.Keep{Rp.Older{}}
    case Rp.Same{} _:
      Rp.Keep{Rp.Same{}}
    case Rp.Newer{} _:
      Rp.Keep{Rp.Newer{}}
    case Rp.Other{} _:
      Rp.Keep{Rp.Other{}}

# LAW replace_rank_reads_semver: the rank of every text is the rank semver.bend's reader gives it,
# with numbers of at most 14 digits
# EXCLUDES: a reader that accepts a leading zero, an empty field, two or
# four fields, a sign or any other symbol; a reader that rounds, clamps or
# wraps a number past the range instead of refusing it; a wrong tier
law replace_rank_reads_semver:
  for +s: String
  {Rp.rank(s) == rank_spec(s) : List<&2, Nat>}

# LAW replace_rank_example: the versions of the release history rank as documented
# EXCLUDES: a misread spec: textual instead of numeric order, a prerelease
# above its release, a parse of text that is no version
law replace_rank_example:
  {[Rp.rank("garbage"), Rp.rank("0.9.0-dev"), Rp.rank("0.9.9-main.46"), Rp.rank("0.10.40"), Rp.rank("1.2.3-"), Rp.rank("01.2.3"), Rp.rank("1.2"), Rp.rank("1.2.3.4"), Rp.rank(""), Rp.rank("1..3"), Rp.rank("+1.2.3")] == [[], [0n, 9n, 0n, 0n], [0n, 9n, 0n, 9n], [0n, 10n, 1n, 40n], [1n, 2n, 0n, 3n], [], [], [], [], [], []] : List<&2, List<&2, Nat>>}

# LAW replace_rank_past_range_example: a number of 15 digits has no rank, in any place
# EXCLUDES: a reader that folds a long field into a Nat (the compiled core
# aborts past 2^48 - 1)
law replace_rank_past_range_example:
  {[Rp.rank("100000000000000.0.0"), Rp.rank("0.100000000000000.0"), Rp.rank("0.0.100000000000000-dev")] == [[], [], []] : List<&2, List<&2, Nat>>}

# LAW replace_build_of_rank: a build made from a version text and a build id carries exactly
# that text's semver rank and that id
# EXCLUDES: a build whose rank is an order-preserving recoding of the
#   version's (a prefix, a shift): it orders like semver between two such
#   builds, yet a new client of it keeps an older daemon of the rank semver
#   gives (an adversary found this gap)
law replace_build_of_rank:
  for +v: String
  for i: String
  {Rp.Build.of(v, i) == Rp.Build{rank_spec(v), i} : Rp.Build}

# The order of ranks (A: ranks compare lexicographically, the empty rank
# lowest), as properties of Rp.lt stated apart from its code. Together
# replace_lt_prefix, _first_difference and _only_when fix the order: a rank
# is below another exactly when the other extends it, or when at the first
# place where the two differ its number is smaller. The empty rank is then
# below every nonempty rank, and no rank is below it.

# ys is xs followed by at least one more number
def rp_extends(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Type:
  &y: Nat -> &yr: List<&2, Nat> -> {ys == List.append(&2, Nat, xs, y <> yr) : List<&2, Nat>}

# after a prefix p that xs and ys share, xs has a number x and ys a number
# y with x < y
def rp_first_smaller(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Type:
  &p: List<&2, Nat> -> &x: Nat -> &xr: List<&2, Nat> -> &y: Nat -> &yr: List<&2, Nat> -> {xs == List.append(&2, Nat, p, x <> xr) : List<&2, Nat>} & {ys == List.append(&2, Nat, p, y <> yr) : List<&2, Nat>} & {Nat.is_lt(x, y) == True{} : Bool}

# LAW replace_lt_irreflexive: no rank is below itself
# EXCLUDES: an order that calls an equal rank lower (another build of the
#   daemon's own version replacing it)
law replace_lt_irreflexive:
  for +xs: List<&2, Nat>
  {Rp.lt(xs, xs) == False{} : Bool}

# LAW replace_lt_asymmetric: of two ranks, at most one is below the other
# EXCLUDES: two builds each older than the other (replacements back and
#   forth between them)
law replace_lt_asymmetric:
  for +xs: List<&2, Nat>
  for +ys: List<&2, Nat>
  for below: {Rp.lt(xs, ys) == True{} : Bool}
  {Rp.lt(ys, xs) == False{} : Bool}

# LAW replace_lt_transitive: a rank below a second rank that is below a third is below the third
# EXCLUDES: a cycle of builds, each older than the next (replacements that
#   never stop)
law replace_lt_transitive:
  for +xs: List<&2, Nat>
  for +ys: List<&2, Nat>
  for +zs: List<&2, Nat>
  for below: {Rp.lt(xs, ys) == True{} : Bool}
  for then: {Rp.lt(ys, zs) == True{} : Bool}
  {Rp.lt(xs, zs) == True{} : Bool}

# LAW replace_lt_total: two ranks neither of which is below the other are equal
# EXCLUDES: unequal ranks the order leaves unordered (an older daemon of
#   another version kept as "another build")
law replace_lt_total:
  for +xs: List<&2, Nat>
  for +ys: List<&2, Nat>
  for no: {Rp.lt(xs, ys) == False{} : Bool}
  for nor: {Rp.lt(ys, xs) == False{} : Bool}
  {xs == ys : List<&2, Nat>}

# LAW replace_lt_first_difference: two ranks that agree up to a place where the first has the
# smaller number are ordered: the first is below the second, whatever
# follows that place
# EXCLUDES: an order that lets a later number (minor, tier, patch) or the
#   length outweigh an earlier one, compares from the last number, compares
#   numbers the wrong way round or as text (10 below 9), or answers
#   differently once a common prefix is added
law replace_lt_first_difference:
  for +p: List<&2, Nat>
  for +x: Nat
  for +y: Nat
  for +xr: List<&2, Nat>
  for +yr: List<&2, Nat>
  for less: {Nat.is_lt(x, y) == True{} : Bool}
  {Rp.lt(List.append(&2, Nat, p, x <> xr), List.append(&2, Nat, p, y <> yr)) == True{} : Bool}

# LAW replace_lt_prefix: a rank is below every longer rank that begins with it
# EXCLUDES: an order that stops at the shorter rank and calls the two equal
law replace_lt_prefix:
  for +xs: List<&2, Nat>
  for +y: Nat
  for +ys: List<&2, Nat>
  {Rp.lt(xs, List.append(&2, Nat, xs, y <> ys)) == True{} : Bool}

# LAW replace_lt_only_when: a rank is below another only when the other extends it, or when at
# the first place where the two differ its number is smaller
# EXCLUDES: an order that ranks a version that does not parse (the empty
#   rank) above a release, calls a longer rank below its own prefix, or
#   puts a rank below another for any other reason (a shared major number
#   alone, a larger number at the first difference)
law replace_lt_only_when:
  for +xs: List<&2, Nat>
  for +ys: List<&2, Nat>
  for below: {Rp.lt(xs, ys) == True{} : Bool}
  rp_extends(xs, ys) | rp_first_smaller(xs, ys)

# LAW replace_relation_exact: the relation of the daemon to the client is exactly rel_spec
# EXCLUDES: a relation that ignores the build ids, compares ranks the
# wrong way round, or calls an equal rank older or newer
law replace_relation_exact:
  for +c: Rp.Build
  for +d: Rp.Build
  {Rp.relation(c, d) == rel_spec(c, d) : Rp.Rel}

# LAW replace_verdict_exact: the verdict of a start is exactly verdict_spec of the relation
# EXCLUDES: a start that never replaces (an older daemon kept for good), a
# background start that replaces, a replaced newer daemon
law replace_verdict_exact:
  for +c: Rp.Build
  for +d: Rp.Build
  for +k: Rp.Caller
  {Rp.verdict(c, d, k) == verdict_spec(rel_spec(c, d), k) : Rp.Verdict}

# LAW replace_ping_pong_example: the ping-pong pair settles on the newer build: an old dashboard
# (0.9.9-main.46) and a new client (0.10.40) by every caller, and a client
# of the daemon's own build
# EXCLUDES: the regression where the two replaced each other forever
law replace_ping_pong_example:
  {[Rp.verdict(Rp.Build.of("0.9.9-main.46", "o"), Rp.Build.of("0.10.40", "n"), Rp.Background{}), Rp.verdict(Rp.Build.of("0.9.9-main.46", "o"), Rp.Build.of("0.10.40", "n"), Rp.Interactive{}), Rp.verdict(Rp.Build.of("0.10.40", "n"), Rp.Build.of("0.9.9-main.46", "o"), Rp.Background{}), Rp.verdict(Rp.Build.of("0.10.40", "n"), Rp.Build.of("0.9.9-main.46", "o"), Rp.Interactive{}), Rp.verdict(Rp.Build.of("0.10.40", "n"), Rp.Build.of("0.10.40", "n"), Rp.Interactive{}), Rp.verdict(Rp.Build.of("0.10.0-dev", "a"), Rp.Build.of("0.10.0-dev", "b"), Rp.Interactive{})] == [Rp.Keep{Rp.Newer{}}, Rp.Keep{Rp.Newer{}}, Rp.Keep{Rp.Older{}}, Rp.Replace{}, Rp.Keep{Rp.Same{}}, Rp.Keep{Rp.Other{}}] : List<&2, Rp.Verdict>}

# The history of client starts, by the laws' own terms (independent of the
# model's after, daemons, replaced, never_back and not_below): the daemon
# after each start, the count of replacements, and the order of the
# daemons' ranks

# the daemon after a start whose spec verdict on the running b is v
def rp_after_pick(v: Rp.Verdict, c: Rp.Build, b: Rp.Build) -> Rp.Build:
  match v:
    case Rp.Replace{}:
      c
    case Rp.Keep{r}:
      b

# the daemon after a start of client c by caller k: none running, the
# client's build; else the client's build when verdict_spec of the
# relation of the running b to c is Replace, else b
def rp_after_spec(s: Rp.Start, d: Maybe<&2, Rp.Build>) -> Rp.Build:
  match s:
    case Rp.Start{+c, k}:
      match d:
        case None{}:
          c
        case Some{+b}:
          rp_after_pick(verdict_spec(rel_spec(c, b), k), c, b)

# the daemon after each start, from the running d on
def rp_daemons_spec.go(ss: List<&2, Rp.Start>, d: Maybe<&2, Rp.Build>) -> List<&2, Rp.Build>:
  match ss:
    case Nil{}:
      Nil{}
    case +s <> rest:
      +n = rp_after_spec(s, d)
      n <> rp_daemons_spec.go(rest, Some{n})

# the daemon after each start, from no daemon on
def rp_daemons_spec(ss: List<&2, Rp.Start>) -> List<&2, Rp.Build>:
  rp_daemons_spec.go(ss, None{})

# 1 for a Replace, 0 for a Keep
def rp_verdict_count(v: Rp.Verdict) -> Nat:
  match v:
    case Rp.Replace{}:
      1n
    case Rp.Keep{r}:
      0n

# 1 when the spec verdict of the start on a running daemon is Replace
def rp_replaces_spec(s: Rp.Start, d: Maybe<&2, Rp.Build>) -> Nat:
  match s:
    case Rp.Start{+c, k}:
      match d:
        case None{}:
          0n
        case Some{+b}:
          rp_verdict_count(verdict_spec(rel_spec(c, b), k))

# the starts of ss that replace a running daemon, from the running d on
def rp_replaced_spec.go(ss: List<&2, Rp.Start>, +d: Maybe<&2, Rp.Build>) -> Nat:
  match ss:
    case Nil{}:
      0n
    case +s <> rest:
      Nat.add(rp_replaces_spec(s, d), rp_replaced_spec.go(rest, Some{rp_after_spec(s, d)}))

# the starts of ss that replace a running daemon, from no daemon on
def rp_replaced_spec(ss: List<&2, Rp.Start>) -> Nat:
  rp_replaced_spec.go(ss, None{})

# the rank of a build
def rp_rank_of(b: Rp.Build) -> List<&2, Nat>:
  match b:
    case Rp.Build{r, i}:
      r

# the build id of a build
def rp_id_of(b: Rp.Build) -> String:
  match b:
    case Rp.Build{r, i}:
      i

# 1 for True, 0 for False
def rp_one_if(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# a daemon running (d) and n another build than it, by build id; with
# none running, False
def rp_other_than(d: Maybe<&2, Rp.Build>, +n: Rp.Build) -> Bool:
  match d:
    case None{}:
      False{}
    case Some{b}:
      Bool.not(String.eq(rp_id_of(n), rp_id_of(b)))

# rank r is below no rank of seen
def rp_rank_not_below(seen: List<&2, List<&2, Nat>>, +r: List<&2, Nat>) -> Bool:
  match seen:
    case Nil{}:
      True{}
    case e <> t:
      Bool.and(Bool.not(rank_below(r, e)), rp_rank_not_below(t, r))

# no build of xs ranks below a build before it (seen: the ranks before xs)
def rp_never_back_spec.go(xs: List<&2, Rp.Build>, +seen: List<&2, List<&2, Nat>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> t:
      +r = rp_rank_of(x)
      Bool.and(rp_rank_not_below(seen, r), rp_never_back_spec.go(t, r <> seen))

# no build of xs ranks (rank_below) below a build before it
def rp_never_back_spec(xs: List<&2, Rp.Build>) -> Bool:
  rp_never_back_spec.go(xs, Nil{})

# LAW replace_after_exact_spec: the daemon after a start is exactly rp_after_spec: none running, the
# client's build; else the client's build when verdict_spec(rel_spec(c, b), k)
# is Replace, else the running build b
# EXCLUDES: an after that asks the verdict with client and daemon swapped
#   (an interactive start that goes back to an older build), replaces on a
#   Keep, keeps on a Replace, or starts another build when none runs
law replace_after_exact_spec:
  for +s: Rp.Start
  for +d: Maybe<&2, Rp.Build>
  {Rp.after(s, d) == rp_after_spec(s, d) : Rp.Build}

# LAW replace_daemons_exact_spec: the running daemon after each start is exactly rp_daemons_spec (the
# fold of rp_after_spec from no daemon)
# EXCLUDES: a trace that drops, repeats or reorders a daemon, or threads
#   another daemon to the next start
law replace_daemons_exact_spec:
  for +ss: List<&2, Rp.Start>
  {Rp.daemons(ss) == rp_daemons_spec(ss) : List<&2, Rp.Build>}

# LAW replace_replaces_new_daemon: a start counts 1 replacement when a daemon b runs and the
# daemon after the start has another build id than b, else 0; with no
# daemon running it counts none
# EXCLUDES: a per-start count that counts a start that keeps the daemon (a
#   background start, a newer, equal or other daemon) or misses one that
#   replaces it, while the history count replaced stays right (an
#   adversary found this gap); a replacement counted for a start with no
#   daemon running (replace-3 found it pinned only by an example)
law replace_replaces_new_daemon:
  for +s: Rp.Start
  for +d: Maybe<&2, Rp.Build>
  {Rp.replaces(s, d) == rp_one_if(rp_other_than(d, Rp.after(s, d))) : Nat}

# LAW replace_replaces_background: a background start counts no replacement, whatever daemon
# runs (or none)
# EXCLUDES: every caller counted as interactive
law replace_replaces_background:
  for +c: Rp.Build
  for +d: Maybe<&2, Rp.Build>
  {Rp.replaces(Rp.Start{c, Rp.Background{}}, d) == 0n : Nat}

# LAW replace_replaces_example: anchor: the adversary's input: with o (0.9.9-main.46, rank
# [0, 9, 0, 9]) running, a background start of n (0.10.40, rank
# [0, 10, 1, 40]) replaces nothing and an interactive one replaces o; with
# no daemon running, no start replaces
# EXCLUDES: every caller treated as interactive, a replacement counted
#   when no daemon runs
law replace_replaces_example:
  {[Rp.replaces(Rp.Start{Rp.Build{[0n, 10n, 1n, 40n], "n"}, Rp.Background{}}, Some{Rp.Build{[0n, 9n, 0n, 9n], "o"}}), Rp.replaces(Rp.Start{Rp.Build{[0n, 10n, 1n, 40n], "n"}, Rp.Interactive{}}, Some{Rp.Build{[0n, 9n, 0n, 9n], "o"}}), Rp.replaces(Rp.Start{Rp.Build{[0n, 10n, 1n, 40n], "n"}, Rp.Interactive{}}, None{})] == [0n, 1n, 0n] : List<&2, Nat>}

# LAW replace_replaced_exact_spec: the count of replacements is exactly the starts whose spec verdict on
# the running daemon is Replace
# EXCLUDES: a count that misses or invents a replacement (a replacements
#   bound met by a count of 0), or counts a start with no daemon
law replace_replaced_exact_spec:
  for +ss: List<&2, Rp.Start>
  {Rp.replaced(ss) == rp_replaced_spec(ss) : Nat}

# LAW replace_never_back_exact_spec: the model's never_back is exactly rp_never_back_spec: no build ranks
# (rank_below) below a build before it
# EXCLUDES: a never_back that answers True (or False) for every list, or
#   compares only neighbours or the wrong way round (replace_never_downgrades
#   then says nothing)
law replace_never_back_exact_spec:
  for +xs: List<&2, Rp.Build>
  {Rp.never_back(xs) == rp_never_back_spec(xs) : Bool}

# LAW replace_never_downgrades_spec: client starts never take the daemon back to a lower build, by
# the laws' own order: in the model's daemons after any starts, no daemon
# ranks below a daemon that ran before it
# EXCLUDES: a daemon that goes back to an older build, hidden by a model's
#   own never_back
law replace_never_downgrades_spec:
  for +ss: List<&2, Rp.Start>
  {rp_never_back_spec(Rp.daemons(ss)) == True{} : Bool}

# LAW replace_history_example: anchor: n of version 0.10.40 (rank [0, 10, 1, 40]) and o of
# 0.9.9-main.46 (rank [0, 9, 0, 9]): interactive starts of n then o keep
# n ([n, n], no replacement); of o then n replace o ([o, n], one
# replacement); an interactive start of o then a background start of n
# keep o ([o, o], no replacement); the model's never_back refuses the
# history [n, o] and accepts [o, n]
# EXCLUDES: the adversary's model (the daemon back to o with no
#   replacement counted, a never_back that accepts every history), a
#   background start that replaces
law replace_history_example:
  {[Rp.daemons([Rp.Start{Rp.Build{[0n, 10n, 1n, 40n], "n"}, Rp.Interactive{}}, Rp.Start{Rp.Build{[0n, 9n, 0n, 9n], "o"}, Rp.Interactive{}}]), Rp.daemons([Rp.Start{Rp.Build{[0n, 9n, 0n, 9n], "o"}, Rp.Interactive{}}, Rp.Start{Rp.Build{[0n, 10n, 1n, 40n], "n"}, Rp.Interactive{}}]), Rp.daemons([Rp.Start{Rp.Build{[0n, 9n, 0n, 9n], "o"}, Rp.Interactive{}}, Rp.Start{Rp.Build{[0n, 10n, 1n, 40n], "n"}, Rp.Background{}}])] == [[Rp.Build{[0n, 10n, 1n, 40n], "n"}, Rp.Build{[0n, 10n, 1n, 40n], "n"}], [Rp.Build{[0n, 9n, 0n, 9n], "o"}, Rp.Build{[0n, 10n, 1n, 40n], "n"}], [Rp.Build{[0n, 9n, 0n, 9n], "o"}, Rp.Build{[0n, 9n, 0n, 9n], "o"}]] : List<&2, List<&2, Rp.Build>>} & {[Rp.replaced([Rp.Start{Rp.Build{[0n, 10n, 1n, 40n], "n"}, Rp.Interactive{}}, Rp.Start{Rp.Build{[0n, 9n, 0n, 9n], "o"}, Rp.Interactive{}}]), Rp.replaced([Rp.Start{Rp.Build{[0n, 9n, 0n, 9n], "o"}, Rp.Interactive{}}, Rp.Start{Rp.Build{[0n, 10n, 1n, 40n], "n"}, Rp.Interactive{}}]), Rp.replaced([Rp.Start{Rp.Build{[0n, 9n, 0n, 9n], "o"}, Rp.Interactive{}}, Rp.Start{Rp.Build{[0n, 10n, 1n, 40n], "n"}, Rp.Background{}}])] == [0n, 1n, 0n] : List<&2, Nat>} & {[Rp.never_back([Rp.Build{[0n, 10n, 1n, 40n], "n"}, Rp.Build{[0n, 9n, 0n, 9n], "o"}]), Rp.never_back([Rp.Build{[0n, 9n, 0n, 9n], "o"}, Rp.Build{[0n, 10n, 1n, 40n], "n"}])] == [False{}, True{}] : List<&2, Bool>}

# ---- replace: client starts, exactly ----

# The spec of client starts, built on verdict_spec(rel_spec(c, d), k) and
# rank_below alone (never the model's code): each start meets the daemon
# the start before it left (none before the first); with no daemon the
# client's build starts, which is no replacement; else the client's build
# replaces the daemon exactly when the verdict is Replace, and the daemon
# stays otherwise.

def rp_rank(b: Rp.Build) -> List<&2, Nat>:
  match b:
    case Rp.Build{r, i}:
      r

def rp_after.pick(v: Rp.Verdict, c: Rp.Build, b: Rp.Build) -> Rp.Build:
  match v:
    case Rp.Replace{}:
      c
    case Rp.Keep{r}:
      b

# the daemon after the start s on the running daemon d (or none)
def rp_after(s: Rp.Start, d: Maybe<&2, Rp.Build>) -> Rp.Build:
  match s:
    case Rp.Start{+c, k}:
      match d:
        case None{}:
          c
        case Some{+b}:
          rp_after.pick(verdict_spec(rel_spec(c, b), k), c, b)

def rp_bump(v: Rp.Verdict) -> Nat:
  match v:
    case Rp.Replace{}:
      1n
    case Rp.Keep{r}:
      0n

# 1 when the start s replaces the running daemon d, else 0
def rp_replaces(s: Rp.Start, d: Maybe<&2, Rp.Build>) -> Nat:
  match s:
    case Rp.Start{+c, k}:
      match d:
        case None{}:
          0n
        case Some{+b}:
          rp_bump(verdict_spec(rel_spec(c, b), k))

def rp_trace.go(ss: List<&2, Rp.Start>, d: Maybe<&2, Rp.Build>) -> List<&2, Rp.Build>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> rest:
      +n = rp_after(s, d)
      n <> rp_trace.go(rest, Some{n})

# the running daemon after each start, in order, from no daemon
def rp_trace(ss: List<&2, Rp.Start>) -> List<&2, Rp.Build>:
  rp_trace.go(ss, None{})

def rp_count.go(ss: List<&2, Rp.Start>, +d: Maybe<&2, Rp.Build>) -> Nat:
  match ss:
    case Nil{}:
      0n
    case +s <> rest:
      Nat.add(rp_replaces(s, d), rp_count.go(rest, Some{rp_after(s, d)}))

# the number of starts that replace the daemon, from no daemon
def rp_count(ss: List<&2, Rp.Start>) -> Nat:
  rp_count.go(ss, None{})

# b ranks below no build of seen
def rp_not_below(seen: List<&2, Rp.Build>, +b: Rp.Build) -> Bool:
  match seen:
    case Nil{}:
      True{}
    case e <> t:
      Bool.and(Bool.not(rank_below(rp_rank(b), rp_rank(e))), rp_not_below(t, b))

def rp_never_back.go(xs: List<&2, Rp.Build>, +seen: List<&2, Rp.Build>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +x <> t:
      Bool.and(rp_not_below(seen, x), rp_never_back.go(t, x <> seen))

# no build of xs ranks below a build before it
def rp_never_back(xs: List<&2, Rp.Build>) -> Bool:
  rp_never_back.go(xs, Nil{})

# two ranks are the same list of numbers
def rp_ranks_eq(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} y <> yr:
      False{}
    case x <> xr Nil{}:
      False{}
    case x <> xr y <> yr:
      Bool.and(Nat.is_eq(x, y), rp_ranks_eq(xr, yr))

# two builds are equal: the same build id and the same rank
def rp_same_build(a: Rp.Build, b: Rp.Build) -> Bool:
  match a b:
    case Rp.Build{ra, ia} Rp.Build{rb, ib}:
      Bool.and(String.eq(ia, ib), rp_ranks_eq(ra, rb))

# b is one of bs
def rp_has(bs: List<&2, Rp.Build>, +b: Rp.Build) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case e <> t:
      Bool.or(rp_same_build(e, b), rp_has(t, b))

# every start's build is one of bs
def rp_covers(+bs: List<&2, Rp.Build>, ss: List<&2, Rp.Start>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case s <> rest:
      match s:
        case Rp.Start{c, k}:
          Bool.and(rp_has(bs, c), rp_covers(bs, rest))

# LAW replace_after_exact (D1): the daemon after a start is exactly rp_after, for every start
# (interactive or background) and every daemon (or none): with no daemon, the client's build;
# else the client's build when verdict_spec of rel_spec is Replace, else the daemon it met
# EXCLUDES: an interactive start that keeps an older daemon, or replaces a
# newer daemon, another build of an equal rank or the same build; a start
# with no daemon that starts another build
law replace_after_exact:
  for +s: Rp.Start
  for +d: Maybe<&2, Rp.Build>
  {Rp.after(s, d) == rp_after(s, d) : Rp.Build}

# LAW replace_daemons_exact (D1): the running daemons after client starts are exactly rp_trace:
# one per start, in order, each rp_after of its start on the daemon before it (none before the
# first)
# EXCLUDES: daemons(ss) = Nil (never_back holds of it vacuously), a trace
# that drops, repeats or reorders a start, or restarts from no daemon
law replace_daemons_exact:
  for +ss: List<&2, Rp.Start>
  {Rp.daemons(ss) == rp_trace(ss) : List<&2, Rp.Build>}

# LAW replace_replaced_exact (D1): the count of replacements is exactly rp_count: one per start
# whose verdict on the daemon before it is Replace
# EXCLUDES: replaced.go always counting 0 (replacement_terminates holds of
# it), a count of starts, of interactive starts, or of daemon changes
# counted against no daemon
law replace_replaced_exact:
  for +ss: List<&2, Rp.Start>
  {Rp.replaced(ss) == rp_count(ss) : Nat}

# LAW replace_not_below_exact (D1): not_below(seen, b) is exactly: b's rank is below the rank of no
# build of seen (rank_below)
# EXCLUDES: not_below always True (replace_never_downgrades vacuous), a
# check of one build of seen only, or of the order the wrong way round
law replace_not_below_exact:
  for +seen: List<&2, Rp.Build>
  for +b: Rp.Build
  {Rp.not_below(seen, b) == rp_not_below(seen, b) : Bool}

# LAW replace_never_back_exact (D1): never_back(xs) is exactly: no build of xs ranks below a build
# before it (rank_below)
# EXCLUDES: never_back always True (replace_never_downgrades vacuous), a
# check of neighbours only, or of the order the wrong way round
law replace_never_back_exact:
  for +xs: List<&2, Rp.Build>
  {Rp.never_back(xs) == rp_never_back(xs) : Bool}

# LAW replace_covers_exact (D1): covers(bs, ss) is exactly: every start's build is one of bs (the
# same build id and the same rank)
# EXCLUDES: covers always False (replacement_terminates vacuous), a match
# by id alone or by rank alone, a check of the first start only
law replace_covers_exact:
  for +bs: List<&2, Rp.Build>
  for +ss: List<&2, Rp.Start>
  {Rp.covers(bs, ss) == rp_covers(bs, ss) : Bool}

# ---- replace: the entry ----

# LAWS (D1, the compiled core): the launcher's replacement verdict runs as
# the model of bend/replace.bend through the compiled core's entry
# bend/ffi_replace.bend (crates/eukhe-client daemon_build.rs). The laws of the
# model itself are in section supervisor. Every input is free: any
# versions, any build ids, any caller.

# LAW replace_rank_cut: the first 65 chars of a version decide its rank, so the entry may
# read only those
# EXCLUDES: a cut that changes a rank (a cut below 65 chars, or a rank that
# reads past its 65th char)
law replace_rank_cut:
  for +s: String
  {Rp.rank(String.take(s, 65n)) == Rp.rank(s) : List<&2, Nat>}

# LAW replace_ffi_relation: the entry's relation is the model's relation of the two builds: it
# reads the versions, and the build ids only through their equality
# EXCLUDES: an entry that swaps client and daemon, ignores the ids, or
# misreads a version
law replace_ffi_relation:
  for +c: String
  for +d: String
  for +ic: String
  for +id: String
  for +f: {Bool.and(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d))) == True{} : Bool}
  {FRp.ffi(FRp.put_req(FRp.ReqRelation{c, d, String.eq(ic, id)}, "")) == FRp.put_rel(Rp.relation(Rp.Build.of(c, ic), Rp.Build.of(d, id)), "") : String}

# LAW replace_ffi_verdict: the entry's verdict is the model's verdict of a start
# EXCLUDES: an entry that ignores or swaps the caller
law replace_ffi_verdict:
  for +c: String
  for +d: String
  for +ic: String
  for +id: String
  for +k: Rp.Caller
  for +f: {Bool.and(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d))) == True{} : Bool}
  {FRp.ffi(FRp.put_req(FRp.ReqVerdict{c, d, String.eq(ic, id), k}, "")) == FRp.put_verdict(Rp.verdict(Rp.Build.of(c, ic), Rp.Build.of(d, id), k), "") : String}

# LAW replace_ffi_example: the requests Rust writes, as text, with their replies: a new client
# by an interactive start on an older daemon (replace), the same build,
# and a relation to a newer daemon; a malformed request is refused
# EXCLUDES: a request or reply format other than WIRE.md's
law replace_ffi_example:
  {[FRp.ffi("1,7,0.10.4013,0.9.9-main.46F0,"), FRp.ffi("1,7,0.10.407,0.10.40T0,"), FRp.ffi("0,13,0.9.9-main.467,0.10.40F"), FRp.ffi("0,7,0.10.40")] == ["0,", "1,0,", "2,", Wr.err("replace: malformed request")] : List<&2, String>}

# Spec spellers of the entry: the grammar of the header of
# bend/ffi_replace.bend and WIRE.md (a constructor is its tag, the index
# of its declaration from 0, then its fields), spelled with the wire
# primitives only, never the entry's own encoders.

# a caller: tag 0 Interactive, 1 Background
def rp_spell_caller(k: Rp.Caller, rest: String) -> String:
  match k:
    case Rp.Interactive{}:
      Wr.put_nat(0n, rest)
    case Rp.Background{}:
      Wr.put_nat(1n, rest)

# a relation: tag 0 Same, 1 Older, 2 Newer, 3 Other
def rp_spell_rel(r: Rp.Rel, rest: String) -> String:
  match r:
    case Rp.Same{}:
      Wr.put_nat(0n, rest)
    case Rp.Older{}:
      Wr.put_nat(1n, rest)
    case Rp.Newer{}:
      Wr.put_nat(2n, rest)
    case Rp.Other{}:
      Wr.put_nat(3n, rest)

# a verdict: tag 0 Replace, or tag 1 Keep then the relation
def rp_spell_verdict(v: Rp.Verdict, rest: String) -> String:
  match v:
    case Rp.Replace{}:
      Wr.put_nat(0n, rest)
    case Rp.Keep{r}:
      Wr.put_nat(1n, rp_spell_rel(r, rest))

# a request: tag 0 Relation{client, daemon, same}, or tag 1
# Verdict{client, daemon, same, caller}
def rp_spell_req(q: FRp.Req, rest: String) -> String:
  match q:
    case FRp.ReqRelation{c, d, same}:
      Wr.put_nat(0n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, rest))))
    case FRp.ReqVerdict{c, d, same, k}:
      Wr.put_nat(1n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, rp_spell_caller(k, rest)))))

# both versions of a request fit the wire
def rp_req_fits(q: FRp.Req) -> Bool:
  match q:
    case FRp.ReqRelation{c, d, same}:
      Bool.and(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d)))
    case FRp.ReqVerdict{c, d, same, k}:
      Bool.and(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d)))

# the relation of a daemon of version d to a client of version c, the
# build ids equal exactly when same: rel_spec of the builds
# Build{rank_spec(c), ic} and Build{rank_spec(d), id} with same = (ic == id)
def rp_rel_of(+c: String, +d: String, same: Bool) -> Rp.Rel:
  +rc = rank_spec(c)
  +rd = rank_spec(d)
  rel_spec.pick(same, rank_below(rd, rc), rank_below(rc, rd))

# the spelled reply of the laws' decision on a request: the relation, or
# verdict_spec of the relation and the caller
def rp_spell_answer(q: FRp.Req) -> String:
  match q:
    case FRp.ReqRelation{c, d, same}:
      rp_spell_rel(rp_rel_of(c, d, same), "")
    case FRp.ReqVerdict{c, d, same, k}:
      rp_spell_verdict(verdict_spec(rp_rel_of(c, d, same), k), "")

# LAW replace_ffi_relation_spelled: a relation request spelled as WIRE.md says, whose versions fit,
# answers the spelled tag of rel_spec of the two versions' ranks and the
# id equality same
# EXCLUDES: wrong or swapped Rel tags on the wire (an Older or Other
#   answered with another tag), a reply in a format only the entry's own
#   encoder reads, a request tag other than 0
law replace_ffi_relation_spelled:
  for +c: String
  for +d: String
  for +same: Bool
  for +f: {Bool.and(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d))) == True{} : Bool}
  {FRp.ffi(rp_spell_req(FRp.ReqRelation{c, d, same}, "")) == rp_spell_answer(FRp.ReqRelation{c, d, same}) : String}

# LAW replace_ffi_verdict_spelled: a verdict request spelled as WIRE.md says, whose versions fit,
# by any caller, answers the spelled verdict_spec of that relation and
# caller
# EXCLUDES: wrong or swapped Verdict, Rel or Caller tags on the wire, a
#   reply in a format only the entry's own encoder reads
law replace_ffi_verdict_spelled:
  for +c: String
  for +d: String
  for +same: Bool
  for +k: Rp.Caller
  for +f: {Bool.and(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d))) == True{} : Bool}
  {FRp.ffi(rp_spell_req(FRp.ReqVerdict{c, d, same, k}, "")) == rp_spell_answer(FRp.ReqVerdict{c, d, same, k}) : String}

# LAW replace_ffi_unknown_request: a request tag of 2 or more (any rest, any length of the tag)
# answers the malformed error
# EXCLUDES: an unknown request read as a relation or a verdict, or
#   answered with a default
law replace_ffi_unknown_request:
  for +n: Nat
  for +rest: String
  {FRp.ffi(Wr.put_nat(2n+n, rest)) == Wr.err("replace: malformed request") : String}

# LAW replace_ffi_unknown_caller: a verdict request whose caller tag is 2 or more (versions that
# fit, any same, any rest) answers the malformed error
# EXCLUDES: an unknown caller read as Background or Interactive, or
#   answered with a default
law replace_ffi_unknown_caller:
  for +c: String
  for +d: String
  for +f: {Bool.and(LawsBase.wire_fits(String.length(c)), LawsBase.wire_fits(String.length(d))) == True{} : Bool}
  for +same: Bool
  for +n: Nat
  for +rest: String
  {FRp.ffi(Wr.put_nat(1n, Wr.put_str(c, Wr.put_str(d, Wr.put_bool(same, Wr.put_nat(2n+n, rest)))))) == Wr.err("replace: malformed request") : String}

# LAW replace_ffi_left_over: a spelled request that fits followed by any more input answers the
# left-over error
# EXCLUDES: trailing input ignored (the request answered), or read as part
#   of the request
law replace_ffi_left_over:
  for +q: FRp.Req
  for f: {rp_req_fits(q) == True{} : Bool}
  for +ch: Char
  for +t: String
  {FRp.ffi(rp_spell_req(q, SCon{ch, t})) == Wr.err("replace: input left over") : String}

# LAW replace_ffi_reads_only_requests: every answer that is not the error form comes from an input that
# is exactly one spelled request that fits, and answers its spelled reply
# EXCLUDES: an answer for input that is no request (an unknown tag read as
#   a known one, a default for malformed input, trailing input accepted)
law replace_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FRp.ffi(s)) == False{} : Bool}
  exs q: FRp.Req
  {(s, (rp_req_fits(q), FRp.ffi(s))) == (rp_spell_req(q, ""), (True{}, rp_spell_answer(q))) : String & (Bool & String)}

# LAW replace_ffi_malformed_unless_request: every answer but the malformed error comes from an input that
# begins with a spelled request that fits
# EXCLUDES: the left-over error (or any answer) for input that does not
#   begin with a request
law replace_ffi_malformed_unless_request:
  for +s: String
  for other: {String.eq(FRp.ffi(s), Wr.err("replace: malformed request")) == False{} : Bool}
  exs q: FRp.Req
  exs rest: String
  {(s, rp_req_fits(q)) == (rp_spell_req(q, rest), True{}) : String & Bool}

# LAW replace_ffi_tags_example: anchor: literal bytes per WIRE.md: a relation request per Rel tag
# (0 Same: same ids; 1 Older: the daemon's version lower; 2 Newer: higher;
# 3 Other: equal versions, other ids), a verdict Replace (an interactive
# start on an older daemon), a Keep with Rel tags 2 and 3, a background
# start on an older daemon (Keep Older), an unknown caller tag 2, an
# unknown request tag 2, and input left over
# EXCLUDES: Rel, Verdict, Caller or request tags in another order, a
#   refusal in another form
law replace_ffi_tags_example:
  {[FRp.ffi("0,5,1.0.05,1.0.0T"), FRp.ffi("0,5,1.0.15,1.0.0F"), FRp.ffi("0,5,1.0.05,1.0.1F"), FRp.ffi("0,5,1.0.05,1.0.0F"), FRp.ffi("1,5,1.0.15,1.0.0F0,"), FRp.ffi("1,5,1.0.05,1.0.1F0,"), FRp.ffi("1,5,1.0.05,1.0.0F0,"), FRp.ffi("1,5,1.0.15,1.0.0F1,"), FRp.ffi("1,5,1.0.05,1.0.0F2,"), FRp.ffi("2,5,1.0.05,1.0.0F"), FRp.ffi("0,5,1.0.05,1.0.0Tx")] == ["0,", "1,", "2,", "3,", "0,", "1,2,", "1,3,", "1,1,", "E replace: malformed request", "E replace: malformed request", "E replace: input left over"] : List<&2, String>}


# The whole entry, every input
# ----------------------------
# The request and the reply as the wire grammar of WIRE.md (and the
# header of bend/ffi_replace.bend), read and spelled with the wire
# primitives alone (never the entry's own codec), and the answer from the
# spec above (rank_spec, rank_below, rel_spec.pick, verdict_spec; never
# the model's code):
#   request  0, then the client's and the daemon's versions (strings) and
#            whether the build ids are equal (a Bool): the relation | 1,
#            the same, then the caller (0 interactive | 1 background):
#            the verdict
#   reply    the relation: 0 same | 1 older | 2 newer | 3 other; the
#            verdict: 0 replace | 1, then the relation it keeps
# A request that cannot be read answers "replace: malformed request"; a
# request with input after it answers "replace: input left over".

def rp_read.caller(c: String, d: String, same: Bool, r: Wr.Dec<Nat>) -> Wr.Dec<FRp.Req>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{FRp.ReqVerdict{c, d, same, Rp.Interactive{}}, s}
        case 1n:
          Wr.Got{FRp.ReqVerdict{c, d, same, Rp.Background{}}, s}
        case 2n+p:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def rp_read.same(verdict: Bool, c: String, d: String, r: Wr.Dec<Bool>) -> Wr.Dec<FRp.Req>:
  match verdict:
    case False{}:
      match r:
        case Wr.Got{same, s}:
          Wr.Got{FRp.ReqRelation{c, d, same}, s}
        case Wr.Bad{}:
          Wr.Bad{}
    case True{}:
      match r:
        case Wr.Got{same, s}:
          rp_read.caller(c, d, same, Wr.get_nat(s))
        case Wr.Bad{}:
          Wr.Bad{}

def rp_read.daemon(verdict: Bool, c: String, r: Wr.Dec<String>) -> Wr.Dec<FRp.Req>:
  match r:
    case Wr.Got{d, s}:
      rp_read.same(verdict, c, d, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def rp_read.client(verdict: Bool, r: Wr.Dec<String>) -> Wr.Dec<FRp.Req>:
  match r:
    case Wr.Got{c, s}:
      rp_read.daemon(verdict, c, Wr.get_str(s))
    case Wr.Bad{}:
      Wr.Bad{}

def rp_read.tag(r: Wr.Dec<Nat>) -> Wr.Dec<FRp.Req>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          rp_read.client(False{}, Wr.get_str(s))
        case 1n:
          rp_read.client(True{}, Wr.get_str(s))
        case 2n+p:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

# the request at the head of s, and the input after it
def rp_read(s: String) -> Wr.Dec<FRp.Req>:
  rp_read.tag(Wr.get_nat(s))

# how a daemon of version d relates to a client of version c, with equal
# build ids exactly when same: the same build; else by the ranks
def rp_rel(+c: String, +d: String, same: Bool) -> Rp.Rel:
  +rc = rank_spec(c)
  +rd = rank_spec(d)
  rel_spec.pick(same, rank_below(rd, rc), rank_below(rc, rd))

def rp_reply(q: FRp.Req) -> String:
  match q:
    case FRp.ReqRelation{c, d, same}:
      rp_spell_rel(rp_rel(c, d, same), "")
    case FRp.ReqVerdict{c, d, same, k}:
      rp_spell_verdict(verdict_spec(rp_rel(c, d, same), k), "")

def rp_entry.of(d: Wr.Dec<FRp.Req>) -> String:
  match d:
    case Wr.Got{q, r}:
      match r:
        case SNil{}:
          rp_reply(q)
        case SCon{c, t}:
          Wr.err("replace: input left over")
    case Wr.Bad{}:
      Wr.err("replace: malformed request")

# the entry's answer to s
def rp_entry(s: String) -> String:
  rp_entry.of(rp_read(s))

# LAW replace_ffi_exact: for every input, the entry answers exactly: on a request (as the wire
# primitives read it) with nothing after it, the relation of the daemon's
# version to the client's (the same build when the ids are equal, else by
# rank_spec's ranks: older, newer or another build of an equal rank), or
# the verdict of the caller's start on it (only an interactive start on an
# older daemon replaces it); on a request with input after it, the error
# form "replace: input left over"; on any other input, the error form
# "replace: malformed request"
# EXCLUDES: client and daemon swapped, a misread version, id flag or
#   caller, a tag read as another, an answer on garbage or on a request
#   with input after it, another error text, a codec of the entry wrong
#   both ways (the spec never calls it)
law replace_ffi_exact:
  for +s: String
  {FRp.ffi(s) == rp_entry(s) : String}

# LAW replace_ffi_exact_example: anchor: the spec on the strings of replace_ffi_example, a
# background start that keeps an older daemon, and input left over
# EXCLUDES: a field order other than Rust's, a vacuous replace_ffi_exact
law replace_ffi_exact_example:
  {[rp_entry("1,7,0.10.4013,0.9.9-main.46F0,"), rp_entry("1,7,0.10.407,0.10.40T0,"), rp_entry("0,13,0.9.9-main.467,0.10.40F"), rp_entry("1,7,0.10.4013,0.9.9-main.46F1,"), rp_entry("0,7,0.10.40"), rp_entry("0,1,11,1F,")] == ["0,", "1,0,", "2,", "1,1,", Wr.err("replace: malformed request"), Wr.err("replace: input left over")] : List<&2, String>}
