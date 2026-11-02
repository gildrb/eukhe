# eukhe: lemmas the proofs of area optchat share: the shipped over-budget
# test (OFit.over, which takes each line's size off the budget) is the
# view's size above the budget (OFit.view_size, the sum the laws speak of)

import Base
import ../../../bend/optchat/fit.bend as OFit
import ../../../bend/optchat/info.bend as OInfo
import ../../../bend/optchat/node.bend as ONode

# z + r > b exactly when z > b, or else r > b - z
def ov.add_gt(z: Nat, +r: Nat, b: Nat) -> {Nat.is_gt(Nat.add(z, r), b) == Bool.or(Nat.is_gt(z, b), Nat.is_gt(r, Nat.sub(b, z))) : Bool}:
  match z b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ov.add_gt(p, r, q)

# nothing is above every b: 0 > b is False
def ov.zero_gt(b: Nat) -> {False{} == Nat.is_gt(0n, b) : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+q:
      {==}

# the shipped test is the size's
def ov.over(+ph: Nat, +info: OInfo.Info, v: List<&2, ONode.Node>, +b: Nat) -> {OFit.over(ph, info, v, b) == Nat.is_gt(OFit.view_size(ph, info, v), b) : Bool}:
  match v:
    case Nil{}:
      ov.zero_gt(b)
    case +h <> +t:
      +z = OFit.line_size(ph, info, h)
      %Equal.sym(Bool, OFit.over(ph, info, t, Nat.sub(b, z)), Nat.is_gt(OFit.view_size(ph, info, t), Nat.sub(b, z)), ov.over(ph, info, t, Nat.sub(b, z))) : {Bool.or(Nat.is_gt(z, b), _) == Nat.is_gt(Nat.add(z, OFit.view_size(ph, info, t)), b) : Bool}
      Equal.sym(Bool, Nat.is_gt(Nat.add(z, OFit.view_size(ph, info, t)), b), Bool.or(Nat.is_gt(z, b), Nat.is_gt(OFit.view_size(ph, info, t), Nat.sub(b, z))), ov.add_gt(z, OFit.view_size(ph, info, t), b))
