# LAWS (R1): eukhe's release versions. Each law is an open claim about
# the model in bend/semver.bend; PROOF.bend proves them (as Release.<law>)
# with the lemmas of bend/proof_semver.bend.

import Base
import ../bend/semver.bend as Sv

# (R1) Release versions
# ---------------------
# README "Releases", the model in bend/semver.bend; the script
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
