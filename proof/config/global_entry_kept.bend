# eukhe: the proof of LAW global_entry_kept

import Base
import ../../bend/config.bend as Cf
import ../../LAWS.bend as Laws
import ../base.bend as L

# the first project entry when the project does not name n
def pcf.kept_at(b: Bool, +fs: List<&2, Cf.Entry>, +x: Maybe<&2, List<&2, Cf.Entry>>, +y: Maybe<&2, List<&2, Cf.Entry>>, +r: Bool, h: {Bool.or(b, r) == False{} : Bool}, ih: {r == False{} : Bool} -> {x == y : Maybe<&2, List<&2, Cf.Entry>>}) -> {Cf.find.pick(b, fs, x) == y : Maybe<&2, List<&2, Cf.Entry>>}:
  match b:
    case True{}:
      L.ppr.absurd({Cf.find.pick(True{}, fs, x) == y : Maybe<&2, List<&2, Cf.Entry>>}, h)
    case False{}:
      ih(h)

# LAW global_entry_kept
def pcf.global_entry_kept(+g: List<&2, Cf.Named>, p: List<&2, Cf.Named>, +n: Nat, h: {Cf.has(p, n) == False{} : Bool}) -> {Cf.find(Cf.merge(g, p), n) == Cf.find(g, n) : Maybe<&2, List<&2, Cf.Entry>>}:
  match p:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Cf.Named{+m, +fs}:
          pcf.kept_at(Nat.is_eq(m, n), fs, Cf.find(Cf.merge(g, rest), n), Cf.find(g, n), Cf.has(rest, n), h, hr => pcf.global_entry_kept(g, rest, n, hr))

def Laws.global_entry_kept(g, p, n, h):
  pcf.global_entry_kept(g, p, n, h)
