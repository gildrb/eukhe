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

# ---- replace: the entry ----

# LAWS (D1, the compiled core): the launcher's replacement verdict runs as
# the model of bend/replace.bend through the compiled core's entry
# bend/ffi_replace.bend (crates/eukhe-tui daemon_build.rs). The laws of the
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
