# eukhe: the proof of LAW roster_sent_per_request
# By induction on the events: a join or a quit records nothing and keeps
# the roster; a request records the roster in front, which is the copies
# of it with one more (prp.shift: every copy is the roster).

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools

# the copies of r before r <> x are r before the copies before x
def prp.shift(n: Nat, +r: List<&2, Nat>, -x: List<&2, List<&2, Nat>>) -> {List.append(&2, List<&2, Nat>, Tools.tr_copies(n, r), r <> x) == r <> List.append(&2, List<&2, Nat>, Tools.tr_copies(n, r), x) : List<&2, List<&2, Nat>>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      Equal.cong(List<&2, List<&2, Nat>>, List<&2, List<&2, Nat>>, z => r <> z, List.append(&2, List<&2, Nat>, Tools.tr_copies(m, r), r <> x), r <> List.append(&2, List<&2, Nat>, Tools.tr_copies(m, r), x), prp.shift(m, r, x))

def prp.sent(es: List<&2, Tl.Ev>, +s: Tl.Sess) -> {Tl.Sess.sent(Tl.run(es, s)) == List.append(&2, List<&2, Nat>, Tools.tr_copies(Tools.tr_turns(es), Tl.Sess.roster(s)), Tl.Sess.sent(s)) : List<&2, List<&2, Nat>>}:
  match es:
    case Nil{}:
      {==}
    case e <> +rest:
      match e:
        case Tl.Join{t}:
          match s:
            case Tl.Sess{r, d, x}:
              prp.sent(rest, Tl.Sess{r, t <> d, x})
        case Tl.Quit{t}:
          match s:
            case Tl.Sess{r, d, x}:
              prp.sent(rest, Tl.Sess{r, Tl.drop(d, t), x})
        case Tl.Turn{}:
          match s:
            case Tl.Sess{+r, +d, +x}:
              Equal.trans(List<&2, List<&2, Nat>>, Tl.Sess.sent(Tl.run(rest, Tl.Sess{r, d, r <> x})), List.append(&2, List<&2, Nat>, Tools.tr_copies(Tools.tr_turns(rest), r), r <> x), r <> List.append(&2, List<&2, Nat>, Tools.tr_copies(Tools.tr_turns(rest), r), x), prp.sent(rest, Tl.Sess{r, d, r <> x}), prp.shift(Tools.tr_turns(rest), r, x))

def Tools.roster_sent_per_request(es, s):
  prp.sent(es, s)
