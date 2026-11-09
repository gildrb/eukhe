# eukhe: the proof of LAW lookup_first_value
# An induction on the document: an entry of the key answers, another is
# skipped.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config

def plf.step(b: Bool, v: Nat, x: Maybe<&2, Nat>, ys: List<&2, Nat>, ih: {x == Config.cf_first(ys) : Maybe<&2, Nat>}) -> {Cf.pick(b, v, x) == Config.cf_first(Config.cf_vals.put(b, v, ys)) : Maybe<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

def Config.lookup_first_value(d, j):
  match d:
    case Nil{}:
      {==}
    case e <> +t:
      match e:
        case Cf.Entry{+k, +v}:
          plf.step(Nat.is_eq(k, j), v, Cf.lookup(t, j), Config.cf_vals(t, j), Config.lookup_first_value(t, j))
