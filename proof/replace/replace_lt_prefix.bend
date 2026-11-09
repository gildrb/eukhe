# eukhe: the proof of LAW replace_lt_prefix
#
# PROOF of LAW replace_lt_prefix: by induction on the prefix (rlp.go): an
# empty prefix is below the nonempty rest, and each shared first number
# passes the question to the rest (LAReplace.pr.lex_same).

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ./base.bend as LAReplace

def rlp.go(xs: List<&2, Nat>, -y: Nat, -ys: List<&2, Nat>) -> {Rp.lt(xs, List.append(&2, Nat, xs, y <> ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +xr:
      Equal.trans(Bool, Rp.lex(x, x, Rp.lt(xr, List.append(&2, Nat, xr, y <> ys))), Rp.lt(xr, List.append(&2, Nat, xr, y <> ys)), True{}, LAReplace.pr.lex_same(x, Rp.lt(xr, List.append(&2, Nat, xr, y <> ys))), rlp.go(xr, y, ys))

def Replace.replace_lt_prefix(xs, y, ys):
  rlp.go(xs, y, ys)
