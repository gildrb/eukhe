# eukhe: the proof of LAW dash_frame_spec
#
# PROOF: the stored token is the spec's (dash_stored_spec); the check of
# a presented token against it has the same form on both sides (fr.check).

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash.bend as Dash
import ./dash_stored_spec.bend as PDashStoredSpec

def fr.check(m: Maybe<&2, List<&2, Nat>>, b: Bool) -> {Da.check(m, b) == Dash.sp_check(m, b) : Da.Pass}:
  match m:
    case None{}:
      {==}
    case Some{bs}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}

def fr.frame(+f: Da.Disk, +b: Bool) -> {Da.frame(f, b) == Dash.sp_frame(f, b) : Da.Pass}:
  %Equal.sym(Maybe<&2, List<&2, Nat>>, Da.stored(f), Dash.sp_stored(f), Dash.dash_stored_spec(f)) : {Da.check(_, b) == Dash.sp_check(Dash.sp_stored(f), b) : Da.Pass}
  fr.check(Dash.sp_stored(f), b)

def Dash.dash_frame_spec(f, b):
  fr.frame(f, b)
