# eukhe: lemmas the proofs of area orphan share

import Base
import ../../bend/orphan.bend as Or
import ../../bend/wire.bend as Wr
import ../../bend/ffi_orphan.bend as FO
import ../../LAWS.bend as Laws

def ps.ffi_work(k: Or.Work, +r: String) -> {Wr.Got{k, r} == FO.get_work(FO.put_work(k, r)) : Wr.Dec<Or.Work>}:
  match k:
    case Or.Idle{}:
      {==}
    case Or.Ongoing{}:
      {==}
