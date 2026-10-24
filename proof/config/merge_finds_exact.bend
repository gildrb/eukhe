# eukhe: the proof of LAW merge_finds_exact
# The merged map lists the project entries before the global ones: a name
# is found among the project entries first (an induction on them), then
# among the global ones.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config

def pmf.pick(b: Bool, fs: List<&2, Cf.Entry>, x: Maybe<&2, List<&2, Cf.Entry>>, y: Maybe<&2, List<&2, Cf.Entry>>, ih: {x == y : Maybe<&2, List<&2, Cf.Entry>>}) -> {Cf.find.pick(b, fs, x) == Config.cf_find.pick(b, fs, y) : Maybe<&2, List<&2, Cf.Entry>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# the model's find is the laws' restatement
def pmf.find(es: List<&2, Cf.Named>, +n: Nat) -> {Cf.find(es, n) == Config.cf_find(es, n) : Maybe<&2, List<&2, Cf.Entry>>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Cf.Named{+m, fs}:
          pmf.pick(Nat.is_eq(m, n), fs, Cf.find(rest, n), Config.cf_find(rest, n), pmf.find(rest, n))

def pmf.first(b: Bool, fs: List<&2, Cf.Entry>, x: Maybe<&2, List<&2, Cf.Entry>>, y: Maybe<&2, List<&2, Cf.Entry>>, z: Maybe<&2, List<&2, Cf.Entry>>, ih: {x == Config.cf_or(y, z) : Maybe<&2, List<&2, Cf.Entry>>}) -> {Cf.find.pick(b, fs, x) == Config.cf_or(Config.cf_find.pick(b, fs, y), z) : Maybe<&2, List<&2, Cf.Entry>>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# a name in the merged map: the project's entry, else the global one
def pmf.merged(+g: List<&2, Cf.Named>, p: List<&2, Cf.Named>, +n: Nat) -> {Cf.find(Cf.merge(g, p), n) == Config.cf_or(Config.cf_find(p, n), Config.cf_find(g, n)) : Maybe<&2, List<&2, Cf.Entry>>}:
  match p:
    case Nil{}:
      pmf.find(g, n)
    case e <> +rest:
      match e:
        case Cf.Named{+m, fs}:
          pmf.first(Nat.is_eq(m, n), fs, Cf.find(Cf.merge(g, rest), n), Config.cf_find(rest, n), Config.cf_find(g, n), pmf.merged(g, rest, n))

def Config.merge_finds_exact(g, p, qs):
  match qs:
    case Nil{}:
      {==}
    case +q <> +rest:
      %pmf.merged(g, p, q) : {Cf.find(Cf.merge(g, p), q) <> Cf.finds(Cf.merge(g, p), rest) == _ <> Config.cf_merged(g, p, rest) : List<&2, Maybe<&2, List<&2, Cf.Entry>>>}
      %Config.merge_finds_exact(g, p, rest) : {Cf.find(Cf.merge(g, p), q) <> Cf.finds(Cf.merge(g, p), rest) == Cf.find(Cf.merge(g, p), q) <> _ : List<&2, Maybe<&2, List<&2, Cf.Entry>>>}
      {==}
