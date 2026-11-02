# eukhe: the proof of LAW notice_total_exact

import Base
import ../../bend/notice.bend as No
import ../../laws/notice.bend as Notice

# the model's total is the spec's sum, notice by notice
def nte.go(ns: List<&2, No.N>) -> {No.total(ns) == Notice.nt_sum(Notice.nt_shown(ns)) : Nat}:
  match ns:
    case Nil{}:
      {==}
    case n <> +t:
      match n:
        case No.N{s, +c}:
          %nte.go(t) : {Nat.add(c, No.total(t)) == Nat.add(c, _) : Nat}
          {==}

def Notice.notice_total_exact(ns):
  nte.go(ns)
