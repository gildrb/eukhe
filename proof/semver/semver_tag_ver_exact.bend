# eukhe: the proof of LAW semver_tag_ver_exact
#
# PROOF of LAW semver_tag_ver_exact: Tag.ver reads the text after the
# stripped `eukhe-v` (semver_tag_strip_exact: the text is the prefix then
# it) as a version, and a text reads as a version only when it is that
# version written (semver_parse_exact), as the spec writes it (sv_show).

import Base
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver
import ./semver_parse_exact.bend as PSemverParseExact
import ./semver_tag_strip_exact.bend as PSemverTagStripExact
import ./base.bend as LASemver
import ./base/tag.bend as LASemverTag

# G for a version, nothing for none
def ptv.if_some(m: Maybe<&2, Sv.Ver>, G: Type) -> Type:
  match m:
    case Some{x}:
      G
    case None{}:
      Unit

def ptv.at(m: Maybe<&2, String>, +t: String, +v: Sv.Ver, em: {Sv.Tag.strip(t) == m : Maybe<&2, String>}, h: {Sv.Tag.ver.of(m) == Some{v} : Maybe<&2, Sv.Ver>}) -> {t == String.append("eukhe-v", Semver.show_spec(v)) : String}:
  match m:
    case None{}:
      %h : ptv.if_some(_, {t == String.append("eukhe-v", Semver.show_spec(v)) : String})
      Unit{}
    case Some{+r}:
      +e1 = Semver.semver_tag_strip_exact(t, r, em)
      +e2 = Semver.semver_parse_exact(r, v, h)
      +e3 = Equal.trans(String, r, Sv.Ver.show(v), Semver.show_spec(v), e2, LASemver.sv_show(v))
      Equal.trans(String, t, String.append("eukhe-v", r), String.append("eukhe-v", Semver.show_spec(v)), e1, Equal.cong(String, String, z => String.append("eukhe-v", z), r, Semver.show_spec(v), e3))

def Semver.semver_tag_ver_exact(t, v, h):
  ptv.at(Sv.Tag.strip(t), t, v, {==}, h)
