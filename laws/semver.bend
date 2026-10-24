# eukhe: the laws of area semver

import Base
import ../bend/ffi_semver.bend as FSv
import ../bend/replace.bend as Rp
import ../bend/wire.bend as Wr
import ../bend/semver.bend as Sv
import ./base.bend as LawsBase

# ---- release ----

# LAWS (R1): eukhe's release versions. Each law is an open claim about
# the model in bend/semver.bend; PROOF.bend proves them (as Semver.<law>)
# with the lemmas of proof/semver/.

# (R1) Release versions
# ---------------------
# docs/develop.md "Releases", the model in bend/semver.bend; it runs as
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

# LAW semver_title: the release of v is titled `Eukhe v` ++ show(v)
law semver_title:
  for v: Sv.Ver
  {Sv.Rel.title(v) == String.append("Eukhe v", Sv.Ver.show(v)) : String}

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

# LAW semver_in_series_exact: a version is of the series of another when both majors and both minors are equal
# EXCLUDES: a series check that ignores the major or the minor, or reads
#   the patch
law semver_in_series_exact:
  for a1: Nat
  for b1: Nat
  for c1: Nat
  for a2: Nat
  for b2: Nat
  for c2: Nat
  {Sv.Ver.in_series(Sv.Ver{a1, b1, c1}, Sv.Ver{a2, b2, c2}) == Bool.and(Nat.is_eq(a1, a2), Nat.is_eq(b1, b2)) : Bool}

# The next patch, by the spec: the highest patch among the version tags
# of the series a.b (Nat.max of Base), plus one; 0 when there is none.

def top_spec.keep(hit: Bool, +p: Nat, acc: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      match acc:
        case None{}:
          Some{p}
        case Some{q}:
          Some{Nat.max(p, q)}
    case False{}:
      acc

def top_spec.add(m: Maybe<&2, Sv.Ver>, +a: Nat, +b: Nat, acc: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      acc
    case Some{v}:
      match v:
        case Sv.Ver{x, y, p}:
          top_spec.keep(Bool.and(Nat.is_eq(a, x), Nat.is_eq(b, y)), p, acc)

def top_spec(+a: Nat, +b: Nat, tags: List<&2, String>) -> Maybe<&2, Nat>:
  match tags:
    case Nil{}:
      None{}
    case t <> r:
      top_spec.add(Sv.Tag.ver(t), a, b, top_spec(a, b, r))

def next_spec(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{p}:
      1n+p

# LAW semver_next_exact: the next release of the series a.b is a.b.(1 + the highest patch of its tags), a.b.0 without one
# EXCLUDES: a next release that skips a patch or repeats one, reads the
#   tags of another series, or keeps the workspace version's patch (the
#   laws of the order and of newness alone let a release skip ahead)
law semver_next_exact:
  for +a: Nat
  for +b: Nat
  for c: Nat
  for +tags: List<&2, String>
  {Sv.Rel.next(Sv.Ver{a, b, c}, tags) == Sv.Ver{a, b, next_spec(top_spec(a, b, tags))} : Sv.Ver}

# every tag that names a version names one older than n
def newest_spec.of(m: Maybe<&2, Sv.Ver>, +n: Sv.Ver) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{v}:
      Sv.Ver.lt(v, n)

def newest_spec(+n: Sv.Ver, tags: List<&2, String>) -> Bool:
  match tags:
    case Nil{}:
      True{}
    case t <> r:
      Bool.and(newest_spec.of(Sv.Tag.ver(t), n), newest_spec(n, r))

def release_rule.newest(ok: Bool, n: Sv.Ver) -> Maybe<&2, Sv.Ver>:
  match ok:
    case True{}:
      Some{n}
    case False{}:
      None{}

def release_rule.at(+a: Nat, +b: Nat, c: Nat, +tags: List<&2, String>) -> Maybe<&2, Sv.Ver>:
  match c:
    case 0n:
      +n = {Sv.Ver{a, b, next_spec(top_spec(a, b, tags))} : Sv.Ver}
      release_rule.newest(newest_spec(n, tags), n)
    case 1n+z:
      None{}

def release_rule(m: Maybe<&2, Sv.Ver>, +tags: List<&2, String>) -> Maybe<&2, Sv.Ver>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      match v:
        case Sv.Ver{a, b, c}:
          release_rule.at(a, b, c, tags)

# LAW semver_release_exact: a commit releases exactly when its workspace version is X.Y.0 and the next release is newer than every version tag
# EXCLUDES: no release where one is due (semver_release_newest and the
#   refusals only bound the release from one side), a release past a
#   newer tag
law semver_release_exact:
  for c: String
  for +tags: List<&2, String>
  {Sv.Rel.release(c, tags) == release_rule(Sv.Ver.parse(c), tags) : Maybe<&2, Sv.Ver>}

# The decimal writer of the spec, independent of the model: a number's
# text is the text of the number before it with its last digit raised,
# a 9 becoming 0 and carrying left. It works on the text written last
# digit first, so the carry walks from the head.

def dec_pick(b: Bool, yes: Char, no: Char) -> Char:
  match b:
    case True{}:
      yes
    case False{}:
      no

# the digit after c ('0' to '8'); any other char stays
def dec_succ(+c: Char) -> Char:
  dec_pick(Char.is_eq(c, '0'), '1', dec_pick(Char.is_eq(c, '1'), '2', dec_pick(Char.is_eq(c, '2'), '3', dec_pick(Char.is_eq(c, '3'), '4', dec_pick(Char.is_eq(c, '4'), '5', dec_pick(Char.is_eq(c, '5'), '6', dec_pick(Char.is_eq(c, '6'), '7', dec_pick(Char.is_eq(c, '7'), '8', dec_pick(Char.is_eq(c, '8'), '9', c)))))))))

# the digit c raised: a 9 becomes 0 and the raised rest follows it;
# any other digit becomes the next one and the rest stays
def dec_raise_at(nine: Bool, c: Char, r: String, raised: String) -> String:
  match nine:
    case True{}:
      SCon{'0', raised}
    case False{}:
      SCon{dec_succ(c), r}

# the text, last digit first, of the number after the one s writes
def dec_raise(s: String) -> String:
  match s:
    case SNil{}:
      SCon{'1', SNil{}}
    case SCon{+c, +r}:
      dec_raise_at(Char.is_eq(c, '9'), c, r, dec_raise(r))

# n in decimal, most significant digit first, no leading zero
def dec_spec(n: Nat) -> String:
  match n:
    case 0n:
      SCon{'0', SNil{}}
    case 1n+p:
      String.reverse(dec_raise(String.reverse(dec_spec(p))))

# LAW semver_show_decimal: a version is written as its three numbers in decimal, most
# significant digit first, joined by dots
# EXCLUDES: digits written in reverse ("0.01.24" for 0.10.42) by a writer
# that its reader undoes, which semver_roundtrip alone lets pass; a
# leading zero; fields in another order or with another separator
law semver_show_decimal:
  for a: Nat
  for b: Nat
  for c: Nat
  {Sv.Ver.show(Sv.Ver{a, b, c}) == String.append(dec_spec(a), SCon{'.', String.append(dec_spec(b), SCon{'.', dec_spec(c)})}) : String}

# LAW semver_dec_spec_example: the spec's writer is decimal: 109 is "109"
# EXCLUDES: a spec writer that is wrong past one digit or past a carry
law semver_dec_spec_example:
  {dec_spec(109n) == "109" : String}

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

# a version's text, written by the spec's decimal writer
def show_spec(v: Sv.Ver) -> String:
  match v:
    case Sv.Ver{a, b, c}:
      String.append(dec_spec(a), SCon{'.', String.append(dec_spec(b), SCon{'.', dec_spec(c)})})

# a release: tag 3, its version, its tag `eukhe-v<version>`, its title
# `Eukhe v<version>`
def spell_rel(+v: Sv.Ver) -> String:
  +t = show_spec(v)
  Wr.put_nat(3n, Wr.put_str(t, Wr.put_str(String.append("eukhe-v", t), Wr.put_str(String.append("Eukhe v", t), ""))))

# the version tags among ts that n is not newer than, in their order
def newer_spec.pick(le: Bool, t: String, rest: List<&2, String>) -> List<&2, String>:
  match le:
    case True{}:
      t <> rest
    case False{}:
      rest

def newer_spec.keep(m: Maybe<&2, Sv.Ver>, +n: Sv.Ver, t: String, rest: List<&2, String>) -> List<&2, String>:
  match m:
    case None{}:
      rest
    case Some{v}:
      newer_spec.pick(Sv.Ver.le(n, v), t, rest)

def newer_spec(+n: Sv.Ver, ts: List<&2, String>) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case +t <> r:
      newer_spec.keep(Sv.Tag.ver(t), n, t, newer_spec(n, r))

# why the workspace version X.Y.c gives no release: not X.Y.0 (tag 1), or
# the next release X.Y.P is not newer than every version tag (tag 2, its
# version, the tags it is not newer than)
def why_spec.patch(a: Nat, b: Nat, c: Nat, +ts: List<&2, String>) -> String:
  match c:
    case 0n:
      +n = Sv.Rel.next(Sv.Ver{a, b, 0n}, ts)
      Wr.put_nat(2n, Wr.put_str(show_spec(n), spell_tags(newer_spec(n, ts), "")))
    case 1n+z:
      Wr.put_nat(1n, "")

# why there is no release: the workspace version is no version (tag 0), ...
def why_spec(m: Maybe<&2, Sv.Ver>, +ts: List<&2, String>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{v}:
      match v:
        case Sv.Ver{a, b, c}:
          why_spec.patch(a, b, c, ts)

def release_spec.of(r: Maybe<&2, Sv.Ver>, c: String, +ts: List<&2, String>) -> String:
  match r:
    case Some{v}:
      spell_rel(v)
    case None{}:
      why_spec(Sv.Ver.parse(c), ts)

# the reply to the release question: the release, else why there is none
def release_spec(+c: String, +ts: List<&2, String>) -> String:
  release_spec.of(Sv.Rel.release(c, ts), c, ts)

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

# s starts with n digits
def run_spec(n: Nat, s: String) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+m:
      match s:
        case SNil{}:
          False{}
        case SCon{c, t}:
          Bool.and(digit_spec.of(Sv.Sym.of(c)), run_spec(m, t))

# s holds 7 digits in a row
def seven_spec(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +t}:
      Bool.or(run_spec(7n, SCon{c, t}), seven_spec(t))

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

# LAW semver_ffi_release: the release question answers the model's release, else why there is none
# EXCLUDES: a reply that is not the model's (another version, tag or title,
#   a swapped reason, a lost or invented tag in the list of newer tags, tags
#   in another order), a release when the model has none, a field of the
#   request lost, swapped or misread
law semver_ffi_release:
  for +c: String
  for +ts: List<&2, String>
  for fit: {release_fits(c, ts) == True{} : Bool}
  for few: {Bool.or(seven_spec(c), seven_tags(ts)) == False{} : Bool}
  {FSv.ffi(spell_release(c, ts)) == release_spec(c, ts) : String}

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
