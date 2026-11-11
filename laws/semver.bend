# eukhe: the laws of area semver

import Base
import ../bend/ffi_semver.bend as FSv
import ../bend/replace.bend as Rp
import ../bend/wire.bend as Wr
import ../bend/semver.bend as Sv
import ./base.bend as LawsBase

# Requirements
# ------------
# R stated, A inferred. R1 is bend/semver.bend's header (its sections 1-6
# are R1.1-R1.6), R2 bend/ffi_semver.bend's header with the replies Rust
# decodes (crates/eukhe-bend/src/rules/semver.rs, Release and Series).
# Each line names the laws that state it; *_example laws are anchors.
#
# R1    eukhe's release versions: the release script
#       (crates/eukhe-build-info/src/bin/eukhe-next-version.rs) and the
#       build script's check of EUKHE_RELEASE_VERSION.
# R1.1  A number is written in decimal, most significant digit first, no
#       leading zero, its digits '0' to '9', and read back only so:
#       semver_show_value, semver_roundtrip, semver_parse_exact,
#       semver_digit_only.
# R1.2  A version is major.minor.patch: three numbers, two dots, nothing
#       else: semver_show_value, semver_roundtrip, semver_parse_exact
#       (anchors semver_parse_patch_example, semver_parse_two_fields_example).
# R1.3  The order: major first, then minor, then patch, each by its value
#       (SemVer 2.0.0 section 11, less a `v` prefix and prerelease cases):
#       semver_le_refl, semver_le_antisym, semver_le_trans, semver_le_total,
#       semver_le_exact, semver_lt_exact.
# R1.4  The tag of v is `eukhe-v` then v written, its release's title
#       `Eukhe v` then v written; no other text names a version:
#       semver_tag_roundtrip, semver_tag_strip_spelled,
#       semver_tag_strip_exact, semver_tag_ver_exact; the title as the
#       entry writes it: semver_ffi_release.
# R1.5  The series of a version X.Y.Z is X.Y, the versions from X.Y.0 up to
#       X.(Y+1).0: semver_in_series_order. The next release of the series
#       is X.Y.P, P 1 + the highest patch among the version tags of the
#       series, 0 without one; other tags change nothing:
#       semver_next_in_series, semver_next_newer (P is above every patch of
#       the series), semver_next_no_skip (P - 1 is one of them when P > 0;
#       with the two before: P is 1 + the highest, 0 without one),
#       semver_fresh_series, semver_other_series, semver_next_not_tagged,
#       semver_next_tag_new.
# R1.6  A release: the workspace version is X.Y.0 and the next release of
#       X.Y is newer than every version tag; else there is none:
#       semver_release_refuses_unparsed_workspace,
#       semver_release_refuses_patch_workspace, semver_release_is_next,
#       semver_release_newest, semver_release_blocked (these five together:
#       a release exactly then, and it is that next release),
#       semver_release_progress.
# R2    The entry of the compiled core (section entry).
# R2.1  The release question answers 3, the release's version, tag and
#       title; else why there is none: 0 the workspace version is no
#       version, 1 it is no series start, 2 the next release and the
#       version tags it is not newer than, in their order:
#       semver_ffi_release, semver_ffi_release_unparsed,
#       semver_ffi_release_patch, semver_ffi_release_behind (anchors
#       semver_ffi_release_example, semver_ffi_behind_example,
#       semver_ffi_why_example).
# R2.2  The series question answers 0 (the release version is no version),
#       1 (it is not of the workspace's series, or the workspace version is
#       no version) or 2 (it is): semver_ffi_series (anchor
#       semver_ffi_series_example).
# R2.3  A request whose read texts hold 7 digits in a row is refused before
#       the unary model reads it: semver_ffi_release_long,
#       semver_ffi_series_long (anchor semver_ffi_long_example).
# R2.4  Every other input answers the error form: semver_ffi_exact,
#       semver_ffi_exact_fits, semver_ffi_left_over,
#       semver_ffi_left_over_spelled, semver_ffi_malformed_unless_request
#       (anchors semver_ffi_errors_example, semver_ffi_error_example,
#       semver_ffi_malformed_example).
# A1    (area replace, stated here) A version number of 15 digits or more
#       never ranks: replace_rank_in_range.

# ---- release ----

# LAWS (R1): eukhe's release versions. Each law is an open claim about
# the model in bend/semver.bend; PROOF.bend proves them (as Semver.<law>)
# with the lemmas of proof/semver/.

# (R1) Release versions
# ---------------------
# The model in bend/semver.bend; it runs as
# compiled Bend through the entry of section entry (R2). Every input is
# free: any version, any tags (any
# text, in any order: other series, other prefixes, no version at all),
# any workspace version.

# LAW semver_roundtrip: reading a written version gives it back
law semver_roundtrip:
  for v: Sv.Ver
  {Sv.Ver.parse(Sv.Ver.show(v)) == Some{v} : Maybe<&2, Sv.Ver>}

# LAW semver_le_refl: the order is reflexive
law semver_le_refl:
  for v: Sv.Ver
  {Sv.Ver.le(v, v) == True{} : Bool}

# LAW semver_le_antisym: the order is antisymmetric
law semver_le_antisym:
  for u: Sv.Ver
  for v: Sv.Ver
  for uv: {Sv.Ver.le(u, v) == True{} : Bool}
  for vu: {Sv.Ver.le(v, u) == True{} : Bool}
  {u == v : Sv.Ver}

# LAW semver_le_trans: the order is transitive
law semver_le_trans:
  for u: Sv.Ver
  for v: Sv.Ver
  for w: Sv.Ver
  for uv: {Sv.Ver.le(u, v) == True{} : Bool}
  for vw: {Sv.Ver.le(v, w) == True{} : Bool}
  {Sv.Ver.le(u, w) == True{} : Bool}

# LAW semver_le_total: the order is total
law semver_le_total:
  for u: Sv.Ver
  for v: Sv.Ver
  {Bool.or(Sv.Ver.le(u, v), Sv.Ver.le(v, u)) == True{} : Bool}

# LAW semver_le_exact: u is v or older exactly when u's major is lower, or equal with a lower minor, or both equal with a patch at most v's
# EXCLUDES: another total order (minor before major, patch first, any
#   order the laws of order alone let pass): a release below a tag of a
#   newer series
law semver_le_exact:
  for +a1: Nat
  for +b1: Nat
  for +c1: Nat
  for +a2: Nat
  for +b2: Nat
  for +c2: Nat
  {Sv.Ver.le(Sv.Ver{a1, b1, c1}, Sv.Ver{a2, b2, c2}) == Bool.or(Nat.is_lt(a1, a2), Bool.and(Nat.is_eq(a1, a2), Bool.or(Nat.is_lt(b1, b2), Bool.and(Nat.is_eq(b1, b2), Nat.is_le(c1, c2))))) : Bool}

# LAW semver_next_newer: the next release is newer than every tag of its series
law semver_next_newer:
  for s: Sv.Ver
  for +xs: List<&2, String>
  for +t: String
  for +ys: List<&2, String>
  for v: Sv.Ver
  for parsed: {Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>}
  for ins: {Sv.Ver.in_series(s, v) == True{} : Bool}
  {Sv.Ver.lt(v, Sv.Rel.next(s, List.append(&2, String, xs, t <> ys))) == True{} : Bool}

# LAW semver_next_not_tagged: the next release is no version a tag names, of any series
law semver_next_not_tagged:
  for +s: Sv.Ver
  for +xs: List<&2, String>
  for +t: String
  for +ys: List<&2, String>
  for +v: Sv.Ver
  for parsed: {Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>}
  {v != Sv.Rel.next(s, List.append(&2, String, xs, t <> ys)) : Sv.Ver}

# LAW semver_next_tag_new: the tag of the next release is none of the tags
law semver_next_tag_new:
  for +s: Sv.Ver
  for +xs: List<&2, String>
  for +t: String
  for +ys: List<&2, String>
  {Sv.Tag.of(Sv.Rel.next(s, List.append(&2, String, xs, t <> ys))) != t : String}

# LAW semver_fresh_series: a series with no tag starts at patch 0
law semver_fresh_series:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +tags: List<&2, String>
  for none: {Sv.Rel.none(Sv.Ver{a, b, c}, tags) == True{} : Bool}
  {Sv.Rel.next(Sv.Ver{a, b, c}, tags) == Sv.Ver{a, b, 0n} : Sv.Ver}

# LAW semver_other_series: a tag that names no version of the series does not change the
# next release
law semver_other_series:
  for s: Sv.Ver
  for +xs: List<&2, String>
  for +t: String
  for +ys: List<&2, String>
  for other: {Sv.Rel.ofs(s, t) == False{} : Bool}
  {Sv.Rel.next(s, List.append(&2, String, xs, t <> ys)) == Sv.Rel.next(s, List.append(&2, String, xs, ys)) : Sv.Ver}

# LAW semver_tag_roundtrip: the tag of v names v
law semver_tag_roundtrip:
  for v: Sv.Ver
  {Sv.Tag.ver(Sv.Tag.of(v)) == Some{v} : Maybe<&2, Sv.Ver>}

# LAW semver_release_newest: a release is newer than every version tag, of any series
law semver_release_newest:
  for c: String
  for +xs: List<&2, String>
  for +t: String
  for +ys: List<&2, String>
  for r: Sv.Ver
  for rel: {Sv.Rel.release(c, List.append(&2, String, xs, t <> ys)) == Some{r} : Maybe<&2, Sv.Ver>}
  for +v: Sv.Ver
  for parsed: {Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>}
  {Sv.Ver.lt(v, r) == True{} : Bool}

# LAW semver_release_progress: with the workspace version X.Y.0 and no version tag of another
# series, the release is the next release of X.Y
law semver_release_progress:
  for c: String
  for +a: Nat
  for +b: Nat
  for +tags: List<&2, String>
  for parsed: {Sv.Ver.parse(c) == Some{Sv.Ver{a, b, 0n}} : Maybe<&2, Sv.Ver>}
  for only: {Sv.Rel.only(Sv.Ver{a, b, 0n}, tags) == True{} : Bool}
  {Sv.Rel.release(c, tags) == Some{Sv.Rel.next(Sv.Ver{a, b, 0n}, tags)} : Maybe<&2, Sv.Ver>}

# LAW semver_release_refuses_patch_workspace: a workspace version X.Y.(1+z) gives no release, with any tags
# EXCLUDES: a workspace version that is no series start (0.10.3 instead of
# 0.10.0) releases anyway; a release whose number ignores the workspace
# version's patch
# LEAVES FREE: the error the script prints
law semver_release_refuses_patch_workspace:
  for c: String
  for +a: Nat
  for +b: Nat
  for +z: Nat
  for +tags: List<&2, String>
  for parsed: {Sv.Ver.parse(c) == Some{Sv.Ver{a, b, 1n+z}} : Maybe<&2, Sv.Ver>}
  {Sv.Rel.release(c, tags) == None{} : Maybe<&2, Sv.Ver>}

# LAW semver_release_refuses_unparsed_workspace: a workspace version that is no version gives no release, with any
# tags
# EXCLUDES: a broken Cargo.toml version ("0.10", "0.10.0-dev", "") falls
# back to a default series and releases
# LEAVES FREE: the error the script prints
law semver_release_refuses_unparsed_workspace:
  for c: String
  for +tags: List<&2, String>
  for unparsed: {Sv.Ver.parse(c) == None{} : Maybe<&2, Sv.Ver>}
  {Sv.Rel.release(c, tags) == None{} : Maybe<&2, Sv.Ver>}

# LAW semver_parse_patch_example: the premise of semver_release_refuses_patch_workspace holds for a
# real text: "0.10.1" reads as 0.10.1
# EXCLUDES: a refusal law that holds only because no text ever parses to
# a patch above 0
law semver_parse_patch_example:
  {Sv.Ver.parse("0.10.1") == Some{Sv.Ver{0n, 10n, 1n}} : Maybe<&2, Sv.Ver>}

# LAW semver_parse_two_fields_example: the premise of semver_release_refuses_unparsed_workspace holds for
# a real text: "0.10" is no version
# EXCLUDES: a refusal law that holds only because every text parses
law semver_parse_two_fields_example:
  {Sv.Ver.parse("0.10") == None{} : Maybe<&2, Sv.Ver>}

# LAW semver_parse_exact: a text reads as a version only when it is that version written
# EXCLUDES: a reader that accepts a leading zero, a sign, a space or any
#   other symbol, an empty field, two or four fields, digits in another
#   order (semver_roundtrip alone lets each pass)
law semver_parse_exact:
  for +s: String
  for +v: Sv.Ver
  for h: {Sv.Ver.parse(s) == Some{v} : Maybe<&2, Sv.Ver>}
  {s == Sv.Ver.show(v) : String}

# LAW semver_in_series_order: v is of the series of X.Y.Z exactly when v
# is X.Y.0 or newer and older than X.(Y+1).0: the series is that interval
# of the order (semver_le_exact, semver_lt_exact)
# EXCLUDES: a series test that ignores the major or the minor, reads the
#   patch, or takes X.(Y+1).0 in
law semver_in_series_order:
  for +a: Nat
  for +b: Nat
  for c: Nat
  for +v: Sv.Ver
  {Sv.Ver.in_series(Sv.Ver{a, b, c}, v) == Bool.and(Sv.Ver.le(Sv.Ver{a, b, 0n}, v), Sv.Ver.lt(v, Sv.Ver{a, 1n+b, 0n})) : Bool}

# LAW semver_next_in_series: the next release of the series of s, with any
# tags, is a version of that series
# EXCLUDES: a next release of another series (0.11.0 or 1.0.0 for the
#   workspace version 0.10.0), which the laws of newness let pass
law semver_next_in_series:
  for +s: Sv.Ver
  for tags: List<&2, String>
  {Sv.Ver.in_series(s, Sv.Rel.next(s, tags)) == True{} : Bool}

# LAW semver_next_no_skip: a next release X.Y.(p+1) skips no patch: a tag
# of the list names X.Y.p
# EXCLUDES: a next release that skips a patch (0.10.5 after the tag
#   eukhe-v0.10.3), counts on from the workspace version's patch or from a
#   tag of another series, or starts a series without tags past 0
#   (semver_next_newer alone lets each pass)
law semver_next_no_skip:
  for +s: Sv.Ver
  for +tags: List<&2, String>
  for +x: Nat
  for +y: Nat
  for +p: Nat
  for nx: {Sv.Rel.next(s, tags) == Sv.Ver{x, y, 1n+p} : Sv.Ver}
  exs xs: List<&2, String>
  exs t: String
  exs ys: List<&2, String>
  {tags == List.append(&2, String, xs, t <> ys) : List<&2, String>} & {Sv.Tag.ver(t) == Some{Sv.Ver{x, y, p}} : Maybe<&2, Sv.Ver>}

# LAW semver_release_is_next: a release from the workspace version X.Y.0 is
# the next release of X.Y
# EXCLUDES: a release that is not the series' next one (a patch skipped or
#   repeated, another series, the workspace version itself), which
#   semver_release_newest lets pass when it is newer than every tag
law semver_release_is_next:
  for c: String
  for +a: Nat
  for +b: Nat
  for +tags: List<&2, String>
  for parsed: {Sv.Ver.parse(c) == Some{Sv.Ver{a, b, 0n}} : Maybe<&2, Sv.Ver>}
  for +r: Sv.Ver
  for rel: {Sv.Rel.release(c, tags) == Some{r} : Maybe<&2, Sv.Ver>}
  {r == Sv.Rel.next(Sv.Ver{a, b, 0n}, tags) : Sv.Ver}

# LAW semver_release_blocked: a workspace version X.Y.0 gives no release
# only when a tag names the next release of X.Y or a newer version
# EXCLUDES: no release where one is due (semver_release_newest and the
#   refusals bound the release from one side only): a release held back by
#   a tag older than it, or by text that names no version
law semver_release_blocked:
  for c: String
  for +a: Nat
  for +b: Nat
  for +tags: List<&2, String>
  for parsed: {Sv.Ver.parse(c) == Some{Sv.Ver{a, b, 0n}} : Maybe<&2, Sv.Ver>}
  for none: {Sv.Rel.release(c, tags) == None{} : Maybe<&2, Sv.Ver>}
  exs xs: List<&2, String>
  exs t: String
  exs ys: List<&2, String>
  exs v: Sv.Ver
  {tags == List.append(&2, String, xs, t <> ys) : List<&2, String>} & ({Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>} & {Sv.Ver.le(Sv.Rel.next(Sv.Ver{a, b, 0n}, tags), v) == True{} : Bool})

# Decimal numerals, by the definition of positional notation: a digit is
# a char of code 48 to 57 ('0' to '9' in ASCII, and in Unicode after it;
# Base's Char.is_digit), of value its code less 48; a numeral is digits
# read most significant first (Horner's rule), with no leading zero.

# the value of a digit char
def num_digit(c: Char) -> Nat:
  Nat.sub(U32.to_nat(Char.to_u32(c)), 48n)

# the value of the digits s written after digits of value acc
def num_val(s: String, acc: Nat) -> Nat:
  match s:
    case SNil{}:
      acc
    case SCon{c, t}:
      num_val(t, Nat.add(num_digit(c), Nat.mul(acc, 10n)))

# every char of s is a digit
def num_digits(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(Char.is_digit(c), num_digits(t))

# s is not empty, and starts with no '0' unless it is "0"
def num_lead(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.or(Bool.not(Char.is_eq(c, '0')), String.is_empty(t))

# s is the decimal numeral of n (n has one: digits, no leading zero, of
# value n)
def numeral(+s: String, n: Nat) -> Bool:
  Bool.and(num_digits(s), Bool.and(num_lead(s), Nat.is_eq(num_val(s, 0n), n)))

# LAW semver_show_value: a written version is the numerals of its major,
# minor and patch, joined by two dots
# EXCLUDES: digits written in reverse ("0.01.24" for 0.10.42) by a writer
#   its reader undoes (semver_roundtrip alone lets it pass), a leading
#   zero, a digit char off by one or out of '0' to '9', fields in another
#   order or with another separator
law semver_show_value:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  exs x: String
  exs y: String
  exs z: String
  {Sv.Ver.show(Sv.Ver{a, b, c}) == String.append(x, SCon{'.', String.append(y, SCon{'.', z})}) : String} & {Bool.and(numeral(x, a), Bool.and(numeral(y, b), numeral(z, c))) == True{} : Bool}

# The rank of a version, read by semver.bend's reader (the spec): the text
# before the first '-' read as a version X.Y.Z (Sv.Ver.parse: decimal
# numbers without leading zeros, three of them, nothing else) whose
# numbers have at most 14 digits; [X, Y, 0, Z] with a '-' (a prerelease),
# [X, Y, 1, Z] without; [] for any other text. A number of 15 digits or
# more is past the range of the compiled core's numbers (2^48 - 1): its
# version has no rank, as text that is no version. A text of more than 64
# chars has no rank either (no version is that long): the first 65 chars
# of any text decide its rank, so Rust sends only those.

# a rank is empty, or four numbers whose version numbers (the first, the
# second and the fourth) have at most 14 digits
def rank_spec.in_range(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case a <> r1:
      match r1:
        case Nil{}:
          False{}
        case b <> r2:
          match r2:
            case Nil{}:
              False{}
            case t <> r3:
              match r3:
                case Nil{}:
                  False{}
                case c <> r4:
                  match r4:
                    case Nil{}:
                      Bool.and(LawsBase.rank_spec.short(a), Bool.and(LawsBase.rank_spec.short(b), LawsBase.rank_spec.short(c)))
                    case e <> r5:
                      False{}

# LAW replace_rank_in_range: every rank is empty or four numbers, and each version number in it
# has at most 14 digits: a version number past the range never ranks
# EXCLUDES: a clamped or wrapped number (the order of a hostile version
# would change), a rank of another length
law replace_rank_in_range:
  for +s: String
  {rank_spec.in_range(Rp.rank(s)) == True{} : Bool}

# ---- entry ----

# LAWS (R2): the entry of the compiled Bend core that runs the release
# rule (bend/ffi_semver.bend, called by crates/eukhe-build-info: the
# release script `eukhe-next-version` and the build script's check of
# EUKHE_RELEASE_VERSION). Each law is an open claim about FSv.ffi, the
# function the core runs, stated with spec spellers built only from the
# wire primitives of bend/wire.bend (their round trips: laws/wire.bend).

# (R2) The entry
# --------------
# A request is a release question (the workspace version and the
# repository's tags) or a series question (the workspace version and a
# release version). The entry answers it with the model's decision
# (Sv.Rel.release, Sv.Rel.next, Sv.Ver.parse, Sv.Ver.in_series) and, for
# no release, why. The model reads numbers in unary: a request whose read
# texts hold 7 digits in a row (the workspace version, a release version,
# a tag `eukhe-v...`; other tags are never read) answers the error form.
# Every other input answers the error form. Every input is free: any
# texts, any tags, in any order.

# The reply specs below read model functions that laws pin, for every
# input: Sv.Rel.release (the semver_release_* laws), Sv.Rel.next (the
# semver_next_* laws), Sv.Ver.parse (semver_parse_exact,
# semver_roundtrip), Sv.Ver.show (semver_show_value), Sv.Tag.ver and
# Sv.Tag.strip (semver_tag_ver_exact, semver_tag_roundtrip,
# semver_tag_strip_exact, semver_tag_strip_spelled), Sv.Ver.le and
# Sv.Ver.lt (semver_le_exact, semver_lt_exact), Sv.Ver.in_series
# (semver_in_series_order), and the digit test of Sv.Sym.of
# (semver_digit_only, semver_roundtrip).

# Spec spellers
# -------------

def spell_tags(ts: List<&2, String>, rest: String) -> String:
  Wr.put_list(~String, ~Wr.put_str, ts, rest)

# the release question: tag 0, the workspace version, the tags
def spell_release(c: String, ts: List<&2, String>) -> String:
  Wr.put_nat(0n, Wr.put_str(c, spell_tags(ts, "")))

# the series question: tag 1, the workspace version, the release version
def spell_series(w: String, r: String) -> String:
  Wr.put_nat(1n, Wr.put_str(w, Wr.put_str(r, "")))

def spell_req(q: FSv.Req) -> String:
  match q:
    case FSv.QRelease{c, ts}:
      spell_release(c, ts)
    case FSv.QSeries{w, r}:
      spell_series(w, r)

# a release: tag 3, its version, its tag `eukhe-v<version>`, its title
# `Eukhe v<version>`
def spell_rel(v: Sv.Ver) -> String:
  +t = Sv.Ver.show(v)
  Wr.put_nat(3n, Wr.put_str(t, Wr.put_str(String.append("eukhe-v", t), Wr.put_str(String.append("Eukhe v", t), ""))))

# the tag t names n or a version newer than n (n is not newer than it)
def behind_spec.of(m: Maybe<&2, Sv.Ver>, +n: Sv.Ver) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      Sv.Ver.le(n, v)

def behind_spec(+n: Sv.Ver, t: String) -> Bool:
  behind_spec.of(Sv.Tag.ver(t), n)

# every tag of ts names n or a newer version
def behind_all(+n: Sv.Ver, ts: List<&2, String>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case t <> r:
      Bool.and(behind_spec(n, t), behind_all(n, r))

def behind_count.add(b: Bool, k: Nat) -> Nat:
  match b:
    case True{}:
      1n+k
    case False{}:
      k

# how many tags of ts name n or a newer version
def behind_count(+n: Sv.Ver, ts: List<&2, String>) -> Nat:
  match ts:
    case Nil{}:
      0n
    case t <> r:
      behind_count.add(behind_spec(n, t), behind_count(n, r))

def pick_spec.at(m: Bool, t: String, rest: List<&2, String>) -> List<&2, String>:
  match m:
    case True{}:
      t <> rest
    case False{}:
      rest

# the tags of ts a mask ms keeps: a subsequence of ts, in its order
def pick_spec(ts: List<&2, String>, ms: List<&2, Bool>) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> r:
      match ms:
        case Nil{}:
          Nil{}
        case m <> mr:
          pick_spec.at(m, t, pick_spec(r, mr))

def series_spec.in(b: Bool) -> String:
  match b:
    case True{}:
      Wr.put_nat(2n, "")
    case False{}:
      Wr.put_nat(1n, "")

def series_spec.of(r: Maybe<&2, Sv.Ver>, w: Maybe<&2, Sv.Ver>) -> String:
  match r:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{v}:
      match w:
        case None{}:
          Wr.put_nat(1n, "")
        case Some{s}:
          series_spec.in(Sv.Ver.in_series(s, v))

# the reply to the series question: 0 the release is no version, 1 it is
# not of the workspace's series (or the workspace version is no version),
# 2 it is
def series_spec(w: String, r: String) -> String:
  series_spec.of(Sv.Ver.parse(r), Sv.Ver.parse(w))

# a char the model reads as a digit
def digit_spec.of(y: Sv.Sym) -> Bool:
  match y:
    case Sv.Digit{d}:
      True{}
    case Sv.Dot{}:
      False{}
    case Sv.Other{}:
      False{}

# for each char of s, whether the model reads it as a digit
def seven_spec.marks(s: String) -> List<&2, Bool>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      digit_spec.of(Sv.Sym.of(c)) <> seven_spec.marks(t)

# one pass that counts down: `need` more digits in a row make a run of 7;
# a digit takes one off (the last one answers yes), any other char starts
# the count again at 7, and the end of the text answers no
def seven_spec.go(ds: List<&2, Bool>, need: Nat) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case d <> t:
      match d:
        case False{}:
          seven_spec.go(t, 7n)
        case True{}:
          match need:
            case 0n:
              True{}
            case 1n+m:
              match m:
                case 0n:
                  True{}
                case 1n+k:
                  seven_spec.go(t, 1n+k)

# s holds 7 digits in a row: a count of the digits in a row reaches 7
def seven_spec(s: String) -> Bool:
  seven_spec.go(seven_spec.marks(s), 7n)

def seven_tag.of(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{r}:
      seven_spec(r)

# a tag the model reads (`eukhe-v...`) whose version holds 7 digits in a row
def seven_tag(t: String) -> Bool:
  seven_tag.of(Sv.Tag.strip(t))

def seven_tags(ts: List<&2, String>) -> Bool:
  match ts:
    case Nil{}:
      False{}
    case t <> r:
      Bool.or(seven_tag(t), seven_tags(r))

# every string of ts fits the wire
def strs_all(ts: List<&2, String>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case +t <> r:
      Bool.and(LawsBase.wire_fits(String.length(t)), strs_all(r))

# the release question fits the wire: each text and the count of tags
def release_fits(c: String, +ts: List<&2, String>) -> Bool:
  Bool.and(LawsBase.wire_fits(String.length(c)), Bool.and(LawsBase.wire_fits(List.length(&2, String, ts)), strs_all(ts)))

def series_fits(w: String, r: String) -> Bool:
  Bool.and(LawsBase.wire_fits(String.length(w)), LawsBase.wire_fits(String.length(r)))

# the refusal of a request with 7 digits in a row
def long_err() -> String:
  Wr.err("semver: a version number of more than 6 digits")

# LAW semver_ffi_release: a release question whose workspace version and
# tags give the release r (Sv.Rel.release) answers 3, r's version, its tag
# `eukhe-v<version>` and its title `Eukhe v<version>`
# EXCLUDES: another version, tag or title (the title of R1.4 dropped or
#   reworded), the release of another request, a field of the request
#   lost, swapped or misread
law semver_ffi_release:
  for +c: String
  for +ts: List<&2, String>
  for fit: {release_fits(c, ts) == True{} : Bool}
  for few: {Bool.or(seven_spec(c), seven_tags(ts)) == False{} : Bool}
  for +r: Sv.Ver
  for rel: {Sv.Rel.release(c, ts) == Some{r} : Maybe<&2, Sv.Ver>}
  {FSv.ffi(spell_release(c, ts)) == spell_rel(r) : String}

# LAW semver_ffi_release_unparsed: a release question whose workspace
# version is no version answers 0
# EXCLUDES: a release, or another reason (1 or 2), for a broken workspace
#   version
law semver_ffi_release_unparsed:
  for +c: String
  for +ts: List<&2, String>
  for fit: {release_fits(c, ts) == True{} : Bool}
  for few: {Bool.or(seven_spec(c), seven_tags(ts)) == False{} : Bool}
  for unparsed: {Sv.Ver.parse(c) == None{} : Maybe<&2, Sv.Ver>}
  {FSv.ffi(spell_release(c, ts)) == Wr.put_nat(0n, "") : String}

# LAW semver_ffi_release_patch: a release question whose workspace version
# is X.Y.(1+z), no series start, answers 1
# EXCLUDES: a release, or another reason (0 or 2), for a workspace version
#   that is no series start
law semver_ffi_release_patch:
  for +c: String
  for +ts: List<&2, String>
  for fit: {release_fits(c, ts) == True{} : Bool}
  for few: {Bool.or(seven_spec(c), seven_tags(ts)) == False{} : Bool}
  for +a: Nat
  for +b: Nat
  for +z: Nat
  for parsed: {Sv.Ver.parse(c) == Some{Sv.Ver{a, b, 1n+z}} : Maybe<&2, Sv.Ver>}
  {FSv.ffi(spell_release(c, ts)) == Wr.put_nat(1n, "") : String}

# LAW semver_ffi_release_behind: a release question whose workspace version
# X.Y.0 gives no release answers 2, the next release of X.Y, and the
# version tags that release is not newer than, in their order: the tags a
# mask of the list keeps, each naming the next release or a newer version,
# as many as the tags of the list that do
# EXCLUDES: a tag lost, repeated or invented in the list, a tag listed that
#   names an older version or no version, tags in another order, another
#   next release, another reason (0 or 1)
law semver_ffi_release_behind:
  for +c: String
  for +ts: List<&2, String>
  for fit: {release_fits(c, ts) == True{} : Bool}
  for few: {Bool.or(seven_spec(c), seven_tags(ts)) == False{} : Bool}
  for +a: Nat
  for +b: Nat
  for parsed: {Sv.Ver.parse(c) == Some{Sv.Ver{a, b, 0n}} : Maybe<&2, Sv.Ver>}
  for none: {Sv.Rel.release(c, ts) == None{} : Maybe<&2, Sv.Ver>}
  exs ms: List<&2, Bool>
  {FSv.ffi(spell_release(c, ts)) == Wr.put_nat(2n, Wr.put_str(Sv.Ver.show(Sv.Rel.next(Sv.Ver{a, b, 0n}, ts)), spell_tags(pick_spec(ts, ms), ""))) : String} & {Bool.and(behind_all(Sv.Rel.next(Sv.Ver{a, b, 0n}, ts), pick_spec(ts, ms)), Nat.is_eq(List.length(&2, String, pick_spec(ts, ms)), behind_count(Sv.Rel.next(Sv.Ver{a, b, 0n}, ts), ts))) == True{} : Bool}

# LAW semver_ffi_release_long: a release question whose read texts hold 7 digits in a row is refused
# EXCLUDES: a slow or stopped evaluation (the unary model on a huge number),
#   a default release, a refusal of a tag the model never reads
law semver_ffi_release_long:
  for +c: String
  for +ts: List<&2, String>
  for fit: {release_fits(c, ts) == True{} : Bool}
  for many: {Bool.or(seven_spec(c), seven_tags(ts)) == True{} : Bool}
  {FSv.ffi(spell_release(c, ts)) == long_err() : String}

# LAW semver_ffi_series: the series question answers whether the release version is of the workspace's series
# EXCLUDES: a release of another series (or no version) accepted, a release
#   of the series refused, the workspace and release versions swapped
law semver_ffi_series:
  for +w: String
  for +r: String
  for fit: {series_fits(w, r) == True{} : Bool}
  for few: {Bool.or(seven_spec(w), seven_spec(r)) == False{} : Bool}
  {FSv.ffi(spell_series(w, r)) == series_spec(w, r) : String}

# LAW semver_ffi_series_long: a series question whose versions hold 7 digits in a row is refused
# EXCLUDES: a slow or stopped evaluation, a default answer
law semver_ffi_series_long:
  for +w: String
  for +r: String
  for fit: {series_fits(w, r) == True{} : Bool}
  for many: {Bool.or(seven_spec(w), seven_spec(r)) == True{} : Bool}
  {FSv.ffi(spell_series(w, r)) == long_err() : String}

# LAW semver_ffi_exact: every input the entry answers with a value (not the error form) is a spelled request
# EXCLUDES: a default answer to a malformed request (an unknown tag, a
#   short string, a wrong count, input left over)
law semver_ffi_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FSv.ffi(s)) == False{} : Bool}
  exs q: FSv.Req
  {s == spell_req(q) : String}

# a request fits the wire: each text and the count of tags
def req_fits(q: FSv.Req) -> Bool:
  match q:
    case FSv.QRelease{c, +ts}:
      release_fits(c, ts)
    case FSv.QSeries{w, r}:
      series_fits(w, r)

# LAW semver_ffi_exact_fits: every input the entry answers with a value is a spelled request that fits the wire
# EXCLUDES: a decoder that reads a length or a count of 15 digits or more
#   (misread, or past the runtime's Nat)
law semver_ffi_exact_fits:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FSv.ffi(s)) == False{} : Bool}
  exs q: FSv.Req
  {s == spell_req(q) : String} & {req_fits(q) == True{} : Bool}

# a request spelled by the grammar, then rest (spell_req is it before
# nothing)
def spell_req_then(q: FSv.Req, rest: String) -> String:
  match q:
    case FSv.QRelease{c, ts}:
      Wr.put_nat(0n, Wr.put_str(c, spell_tags(ts, rest)))
    case FSv.QSeries{w, r}:
      Wr.put_nat(1n, Wr.put_str(w, Wr.put_str(r, rest)))

# LAW semver_ffi_left_over_spelled: a spelled request that fits, followed by any more input,
# answers exactly the error form "semver: input left after the request"
# (before the 7-digit check: a long request with input left over gets this
# text too)
# EXCLUDES: trailing input ignored or read as part of the request, the
#   left-over error reworded or swapped with another error text
law semver_ffi_left_over_spelled:
  for +q: FSv.Req
  for fit: {req_fits(q) == True{} : Bool}
  for +c: Char
  for +t: String
  {FSv.ffi(spell_req_then(q, SCon{c, t})) == Wr.err("semver: input left after the request") : String}

# LAW semver_ffi_malformed_unless_request: every answer but the error form "semver: malformed
# request" comes from an input that begins with a spelled request that fits
# EXCLUDES: the left-over or 7-digit error (or any answer) for input that
#   does not begin with a request, the malformed error reworded
law semver_ffi_malformed_unless_request:
  for +s: String
  for other: {String.eq(FSv.ffi(s), Wr.err("semver: malformed request")) == False{} : Bool}
  exs q: FSv.Req
  exs rest: String
  {(s, req_fits(q)) == (spell_req_then(q, rest), True{}) : String & Bool}

# LAW semver_ffi_errors_example: anchor: the error texts Rust reads: an unknown tag is
# malformed, a request with input left over is refused as such
# EXCLUDES: the two texts swapped or reworded
law semver_ffi_errors_example:
  {[FSv.ffi("2,"), FSv.ffi("0,6,0.10.00,x")] == [Wr.err("semver: malformed request"), Wr.err("semver: input left after the request")] : List<&2, String>}

# LAW semver_ffi_release_example: anchor: the exact bytes Rust sends for 0.10.0 with the tags eukhe-v0.10.3 and v1.2.3, and the release 0.10.4
# EXCLUDES: another spelling of the request or of the release
law semver_ffi_release_example:
  {FSv.ffi("0,6,0.10.02,13,eukhe-v0.10.36,v1.2.3") == "3,6,0.10.413,eukhe-v0.10.413,Eukhe v0.10.4" : String}

# LAW semver_ffi_behind_example: anchor: a tag of a newer series stops the release and is named
# EXCLUDES: a release past a newer series, the newer tag left out
law semver_ffi_behind_example:
  {FSv.ffi("0,6,0.10.02,13,eukhe-v0.11.313,eukhe-v0.10.3") == "2,6,0.10.41,13,eukhe-v0.11.3" : String}

# LAW semver_ffi_why_example: anchor: a workspace version 0.10.2 is no series start, 0.10 no version
# EXCLUDES: the two reasons swapped
law semver_ffi_why_example:
  {FSv.ffi("0,6,0.10.20,") == "1," : String} & {FSv.ffi("0,4,0.100,") == "0," : String}

# LAW semver_ffi_series_example: anchor: 0.10.7 is of the series 0.10.0, 0.11.7 is not, 0.10.07 is no version
# EXCLUDES: a series check that ignores the minor number or reads a leading zero
law semver_ffi_series_example:
  {FSv.ffi("1,6,0.10.06,0.10.7") == "2," : String} & {FSv.ffi("1,6,0.10.06,0.11.7") == "1," : String} & {FSv.ffi("1,6,0.10.07,0.10.07") == "0," : String}

# LAW semver_ffi_long_example: anchor: a tag eukhe-v0.10.1234567 is refused, a tag build-12345678 is never read
# EXCLUDES: a vacuous semver_ffi_release_long; a refusal of tags the model does not read
law semver_ffi_long_example:
  {FSv.ffi("0,6,0.10.01,19,eukhe-v0.10.1234567") == long_err() : String} & {FSv.ffi("0,6,0.10.01,14,build-12345678") == "3,6,0.10.013,eukhe-v0.10.013,Eukhe v0.10.0" : String}

# LAW semver_ffi_malformed_example: anchor: an unknown tag and input left over are refused
# EXCLUDES: a default answer to a request Rust never sends
law semver_ffi_malformed_example:
  {LawsBase.wire_opens_err(FSv.ffi("2,")) == True{} : Bool} & {LawsBase.wire_opens_err(FSv.ffi("0,6,0.10.00,x")) == True{} : Bool}

# LAW semver_ffi_error_example: anchor: the exact refusals: an unknown tag and a
# 15-digit count are malformed, input after a request is left over, a tag with
# 7 digits in a row is too long
# EXCLUDES: one error text for another (a left-over input called malformed),
#   an error text that varies with the input
law semver_ffi_error_example:
  {[FSv.ffi("2,"), FSv.ffi("0,999999999999999,"), FSv.ffi("0,6,0.10.00,x"), FSv.ffi("0,6,0.10.01,19,eukhe-v0.10.1234567")] == [Wr.err("semver: malformed request"), Wr.err("semver: malformed request"), Wr.err("semver: input left after the request"), long_err()] : List<&2, String>}

# ---- the entry, whole (R2) ----
#
# With the laws above, every input of the entry has one answer: an input
# that is a spelled request that fits (then nothing) answers the reply
# laws (a release question: semver_ffi_release when the model releases,
# else semver_ffi_release_unparsed, semver_ffi_release_patch or
# semver_ffi_release_behind as its workspace version reads, or
# semver_ffi_release_long; a series question: semver_ffi_series or
# semver_ffi_series_long); one followed by more input answers the
# left-over error; any other input answers the malformed error. The
# model's helpers the reply specs read (the order, the tag reader, the
# digit test of the 7-digit refusal) are pinned below.

# LAW semver_ffi_left_over: a request Rust spells that fits, followed by more
# input, answers exactly the left-over error
# EXCLUDES: trailing input ignored (a release answered for a request and a
#   half), or read as part of the request, or refused with another text
law semver_ffi_left_over:
  for +q: FSv.Req
  for +rest: String
  for fit: {req_fits(q) == True{} : Bool}
  for more: {String.is_empty(rest) == False{} : Bool}
  {FSv.ffi(spell_req_then(q, rest)) == Wr.err("semver: input left after the request") : String}

# LAW semver_lt_exact: v is newer than u exactly when v's major is higher, or
# equal with a higher minor, or both equal with a higher patch
# EXCLUDES: a newness test other than the strict order (a release equal to a
#   tag, or behind one, called newer), which the reply specs read through
#   Sv.Ver.lt
law semver_lt_exact:
  for +a1: Nat
  for +b1: Nat
  for +c1: Nat
  for +a2: Nat
  for +b2: Nat
  for +c2: Nat
  {Sv.Ver.lt(Sv.Ver{a1, b1, c1}, Sv.Ver{a2, b2, c2}) == Bool.or(Nat.is_lt(a1, a2), Bool.and(Nat.is_eq(a1, a2), Bool.or(Nat.is_lt(b1, b2), Bool.and(Nat.is_eq(b1, b2), Nat.is_lt(c1, c2))))) : Bool}

# LAW semver_digit_only: the model reads a char as a digit only when it is
# that digit's char as the writer writes it (Sv.Dig.chr: '0' to '9' by
# semver_show_value; semver_roundtrip has the reader read each of them)
# EXCLUDES: another char (a letter, a sign, a space, '/' or ':') read as a
#   digit: a 7-digit refusal of `1.2.3a5678`, or a version read from a text
#   that is none
law semver_digit_only:
  for +c: Char
  for d: Sv.Dig
  for h: {Sv.Sym.of(c) == Sv.Digit{d} : Sv.Sym}
  {c == Sv.Dig.chr(d) : Char}

# LAW semver_tag_strip_spelled: the model strips `eukhe-v` from every text
# that starts with it, and keeps what follows
# EXCLUDES: a tag the model does not read (its version ignored, its 7-digit
#   run let through), the text after the prefix cut or changed
law semver_tag_strip_spelled:
  for +r: String
  {Sv.Tag.strip(String.append("eukhe-v", r)) == Some{r} : Maybe<&2, String>}

# LAW semver_tag_strip_exact: the model strips only `eukhe-v`: a text it
# strips is `eukhe-v` then the text it answers
# EXCLUDES: another prefix read as a tag (`v1.2.3`, `build-12345678` read,
#   refused for 7 digits or counted as a version)
law semver_tag_strip_exact:
  for +t: String
  for +r: String
  for h: {Sv.Tag.strip(t) == Some{r} : Maybe<&2, String>}
  {t == String.append("eukhe-v", r) : String}

# LAW semver_tag_ver_exact: a text names a version only when it is that
# version's tag, `eukhe-v` then the version written (with
# semver_tag_roundtrip and semver_show_value: the tag reader reads exactly
# the tags `eukhe-v` then a version in decimal)
# EXCLUDES: a tag reader that reads `v1.2.3`, `eukhe-v0.10.03` or
#   `eukhe-v0.10.3-main.4` as a version (a release held back or moved by a
#   text that is no tag)
law semver_tag_ver_exact:
  for +t: String
  for +v: Sv.Ver
  for h: {Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>}
  {t == String.append("eukhe-v", Sv.Ver.show(v)) : String}
