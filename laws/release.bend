# LAWS (R1): eukhe's release versions. Each law is an open claim about
# the model in bend/semver.bend; PROOF.bend proves them (as Release.<law>)
# with the lemmas of bend/proof_semver.bend.

import Base
import ../bend/semver.bend as Sv

# (R1) Release versions
# ---------------------
# docs/develop.md "Releases", the model in bend/semver.bend; the script
# scripts/release/next_version.py implements it and its bridge test runs
# both on the same cases. Every input is free: any version, any tags (any
# text, in any order: other series, other prefixes, no version at all),
# any workspace version.

# LAW: reading a written version gives it back
law semver_roundtrip:
  for v: Sv.Ver
  {Sv.Ver.parse(Sv.Ver.show(v)) == Some{v} : Maybe<&2, Sv.Ver>}

# LAW: the order is reflexive
law semver_le_refl:
  for v: Sv.Ver
  {Sv.Ver.le(v, v) == True{} : Bool}

# LAW: the order is antisymmetric
law semver_le_antisym:
  for u: Sv.Ver
  for v: Sv.Ver
  for uv: {Sv.Ver.le(u, v) == True{} : Bool}
  for vu: {Sv.Ver.le(v, u) == True{} : Bool}
  {u == v : Sv.Ver}

# LAW: the order is transitive
law semver_le_trans:
  for u: Sv.Ver
  for v: Sv.Ver
  for w: Sv.Ver
  for uv: {Sv.Ver.le(u, v) == True{} : Bool}
  for vw: {Sv.Ver.le(v, w) == True{} : Bool}
  {Sv.Ver.le(u, w) == True{} : Bool}

# LAW: the order is total
law semver_le_total:
  for u: Sv.Ver
  for v: Sv.Ver
  {Bool.or(Sv.Ver.le(u, v), Sv.Ver.le(v, u)) == True{} : Bool}

# LAW: the next release is newer than every tag of its series
law semver_next_newer:
  for s: Sv.Ver
  for +xs: List<&2, String>
  for +t: String
  for +ys: List<&2, String>
  for v: Sv.Ver
  for parsed: {Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>}
  for ins: {Sv.Ver.in_series(s, v) == True{} : Bool}
  {Sv.Ver.lt(v, Sv.Rel.next(s, List.append(&2, String, xs, t <> ys))) == True{} : Bool}

# LAW: the next release is no version a tag names, of any series
law semver_next_not_tagged:
  for +s: Sv.Ver
  for +xs: List<&2, String>
  for +t: String
  for +ys: List<&2, String>
  for +v: Sv.Ver
  for parsed: {Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>}
  {v != Sv.Rel.next(s, List.append(&2, String, xs, t <> ys)) : Sv.Ver}

# LAW: the tag of the next release is none of the tags
law semver_next_tag_new:
  for +s: Sv.Ver
  for +xs: List<&2, String>
  for +t: String
  for +ys: List<&2, String>
  {Sv.Tag.of(Sv.Rel.next(s, List.append(&2, String, xs, t <> ys))) != t : String}

# LAW: a series with no tag starts at patch 0
law semver_fresh_series:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +tags: List<&2, String>
  for none: {Sv.Rel.none(Sv.Ver{a, b, c}, tags) == True{} : Bool}
  {Sv.Rel.next(Sv.Ver{a, b, c}, tags) == Sv.Ver{a, b, 0n} : Sv.Ver}

# LAW: a tag that names no version of the series does not change the
# next release
law semver_other_series:
  for s: Sv.Ver
  for +xs: List<&2, String>
  for +t: String
  for +ys: List<&2, String>
  for other: {Sv.Rel.ofs(s, t) == False{} : Bool}
  {Sv.Rel.next(s, List.append(&2, String, xs, t <> ys)) == Sv.Rel.next(s, List.append(&2, String, xs, ys)) : Sv.Ver}

# LAW: the release of v is titled `Eukhe v` ++ show(v)
law semver_title:
  for v: Sv.Ver
  {Sv.Rel.title(v) == String.append("Eukhe v", Sv.Ver.show(v)) : String}

# LAW: the tag of v names v
law semver_tag_roundtrip:
  for v: Sv.Ver
  {Sv.Tag.ver(Sv.Tag.of(v)) == Some{v} : Maybe<&2, Sv.Ver>}

# LAW: a release is newer than every version tag, of any series
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

# LAW: with the workspace version X.Y.0 and no version tag of another
# series, the release is the next release of X.Y
law semver_release_progress:
  for c: String
  for +a: Nat
  for +b: Nat
  for +tags: List<&2, String>
  for parsed: {Sv.Ver.parse(c) == Some{Sv.Ver{a, b, 0n}} : Maybe<&2, Sv.Ver>}
  for only: {Sv.Rel.only(Sv.Ver{a, b, 0n}, tags) == True{} : Bool}
  {Sv.Rel.release(c, tags) == Some{Sv.Rel.next(Sv.Ver{a, b, 0n}, tags)} : Maybe<&2, Sv.Ver>}

# LAW: a workspace version X.Y.(1+z) gives no release, with any tags
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

# LAW: a workspace version that is no version gives no release, with any
# tags
# EXCLUDES: a broken Cargo.toml version ("0.10", "0.10.0-dev", "") falls
# back to a default series and releases
# LEAVES FREE: the error the script prints
law semver_release_refuses_unparsed_workspace:
  for c: String
  for +tags: List<&2, String>
  for unparsed: {Sv.Ver.parse(c) == None{} : Maybe<&2, Sv.Ver>}
  {Sv.Rel.release(c, tags) == None{} : Maybe<&2, Sv.Ver>}

# LAW: the premise of semver_release_refuses_patch_workspace holds for a
# real text: "0.10.1" reads as 0.10.1
# EXCLUDES: a refusal law that holds only because no text ever parses to
# a patch above 0
law semver_parse_patch_example:
  {Sv.Ver.parse("0.10.1") == Some{Sv.Ver{0n, 10n, 1n}} : Maybe<&2, Sv.Ver>}

# LAW: the premise of semver_release_refuses_unparsed_workspace holds for
# a real text: "0.10" is no version
# EXCLUDES: a refusal law that holds only because every text parses
law semver_parse_two_fields_example:
  {Sv.Ver.parse("0.10") == None{} : Maybe<&2, Sv.Ver>}

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

# LAW: a version is written as its three numbers in decimal, most
# significant digit first, joined by dots
# EXCLUDES: digits written in reverse ("0.01.24" for 0.10.42) by a writer
# that its reader undoes, which semver_roundtrip alone lets pass; a
# leading zero; fields in another order or with another separator
law semver_show_decimal:
  for a: Nat
  for b: Nat
  for c: Nat
  {Sv.Ver.show(Sv.Ver{a, b, c}) == String.append(dec_spec(a), SCon{'.', String.append(dec_spec(b), SCon{'.', dec_spec(c)})}) : String}

# LAW: the spec's writer is decimal: 109 is "109"
# EXCLUDES: a spec writer that is wrong past one digit or past a carry
law semver_dec_spec_example:
  {dec_spec(109n) == "109" : String}
