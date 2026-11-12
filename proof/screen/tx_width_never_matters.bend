# eukhe: the proof of LAW tx_width_never_matters
#
# PROOF: induction on the events, for every blocks, next id and both widths:
# Open, Grow, Fin and Flush step the blocks alike under either width; a
# resize changes only the left width, and is left out on the right.

import Base
import ../../bend/screen.bend as Sc
import ../../laws/screen/interface.bend as Screen

def width.run(es: List<&2, Sc.Ev>, +bs: List<&2, Sc.Blk>, +n: Nat, w: Nat, v: Nat) -> {Sc.Tx.blocks(Sc.run(es, Sc.Tx{bs, n, w})) == Sc.Tx.blocks(Sc.run(Screen.tx_no_resize(es), Sc.Tx{bs, n, v})) : List<&2, Sc.Blk>}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case Sc.Open{}:
          width.run(rest, List.append(&2, Sc.Blk, bs, [Sc.Blk{n, Sc.Active{}, 0n}]), 1n+n, w, v)
        case Sc.Grow{x, k}:
          width.run(rest, Sc.edit(bs, x, Some{k}), n, w, v)
        case Sc.Fin{x}:
          width.run(rest, Sc.edit(bs, x, None{}), n, w, v)
        case Sc.Flush{}:
          width.run(rest, Sc.flush(bs), n, w, v)
        case Sc.Resize{u}:
          width.run(rest, bs, n, u, v)

def Screen.tx_width_never_matters(es, bs, n, w, v):
  width.run(es, bs, n, w, v)
