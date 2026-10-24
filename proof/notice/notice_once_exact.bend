# eukhe: the proof of LAW notice_once_exact

import Base
import ../../bend/notice.bend as No
import ../../laws/notice.bend as Notice

def no1.amo(c: Nat) -> {No.at_most_one(c) == Nat.is_le(c, 1n) : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          {==}

# the model's once is the spec's, notice by notice
def no1.go(ns: List<&2, No.N>) -> {No.once(ns) == Notice.nt_once(Notice.nt_shown(ns)) : Bool}:
  match ns:
    case Nil{}:
      {==}
    case n <> +t:
      match n:
        case No.N{s, +c}:
          %no1.amo(c) : {Bool.and(No.at_most_one(c), No.once(t)) == Bool.and(_, Notice.nt_once(Notice.nt_shown(t))) : Bool}
          %no1.go(t) : {Bool.and(No.at_most_one(c), No.once(t)) == Bool.and(No.at_most_one(c), _) : Bool}
          {==}

def Notice.notice_once_exact(ns):
  no1.go(ns)
