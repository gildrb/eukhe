# eukhe: the proof of LAW project_entry_never_merges

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../base/logic/logic.bend as LLogicLogic

# Named entries
# -------------

# the first project entry, b saying whether it is named n
def pcf.merge_at(b: Bool, +fs: List<&2, Cf.Entry>, +x: Maybe<&2, List<&2, Cf.Entry>>, +y: Maybe<&2, List<&2, Cf.Entry>>, +r: Bool, h: {Bool.or(b, r) == True{} : Bool}, ih: {r == True{} : Bool} -> {x == y : Maybe<&2, List<&2, Cf.Entry>>}) -> {Cf.find.pick(b, fs, x) == Cf.find.pick(b, fs, y) : Maybe<&2, List<&2, Cf.Entry>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(h)

# LAW project_entry_never_merges
def pcf.project_entry_never_merges(+g: List<&2, Cf.Named>, p: List<&2, Cf.Named>, +n: Nat, h: {Cf.has(p, n) == True{} : Bool}) -> {Cf.find(Cf.merge(g, p), n) == Cf.find(p, n) : Maybe<&2, List<&2, Cf.Entry>>}:
  match p:
    case Nil{}:
      LLogicLogic.ppr.absurdF({Cf.find(Cf.merge(g, Nil{}), n) == Cf.find(Nil{}, n) : Maybe<&2, List<&2, Cf.Entry>>}, h)
    case e <> +rest:
      match e:
        case Cf.Named{+m, +fs}:
          pcf.merge_at(Nat.is_eq(m, n), fs, Cf.find(Cf.merge(g, rest), n), Cf.find(rest, n), Cf.has(rest, n), h, hr => pcf.project_entry_never_merges(g, rest, n, hr))

def Config.project_entry_never_merges(g, p, n, h):
  pcf.project_entry_never_merges(g, p, n, h)
