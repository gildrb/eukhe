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
