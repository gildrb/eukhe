# eukhe: the proof of LAW bound_notice_exact: both sides compute on every retention, count and holding

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

def Bound.bound_notice_exact(t, d, s):
  match t:
    case False{}:
      match d:
        case 0n:
          {==}
        case 1n++p:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
    case True{}:
      match d:
        case 0n:
          {==}
        case 1n++p:
          match s:
            case True{}:
              {==}
            case False{}:
              {==}
