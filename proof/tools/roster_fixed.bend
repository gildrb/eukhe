# eukhe: the proof of LAW roster_fixed

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools

# 1. The roster
# -------------

def pl.roster_step(s: Tl.Sess, e: Tl.Ev) -> {Tl.Sess.roster(Tl.step(s, e)) == Tl.Sess.roster(s) : List<&2, Nat>}:
  match s:
    case Tl.Sess{r, d, x}:
      match e:
        case Tl.Join{t}:
          {==}
        case Tl.Quit{t}:
          {==}
        case Tl.Turn{}:
          {==}

def pl.roster_fixed(es: List<&2, Tl.Ev>, +s: Tl.Sess) -> {Tl.Sess.roster(Tl.run(es, s)) == Tl.Sess.roster(s) : List<&2, Nat>}:
  match es:
    case Nil{}:
      {==}
    case +e <> rest:
      Equal.trans(List<&2, Nat>, Tl.Sess.roster(Tl.run(rest, Tl.step(s, e))), Tl.Sess.roster(Tl.step(s, e)), Tl.Sess.roster(s), pl.roster_fixed(rest, Tl.step(s, e)), pl.roster_step(s, e))

# (S7) The tool surface

def Tools.roster_fixed(es, s):
  pl.roster_fixed(es, s)
