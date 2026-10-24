# eukhe: the proof of LAW dash_keep_spec
#
# PROOF: a kept file's token is the spec's (dash_stored_spec); a mode with
# no bit for the group or others (mode mod 64 is 0) is reused, any other
# one narrowed (kp.mode: 0, or a successor); the other cases compute.

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash.bend as Dash
import ./dash_stored_spec.bend as PDashStoredSpec

def kp.mode(n: Nat) -> {Da.keep.private(Nat.is_eq(n, 0n)) == Dash.sp_keep.mode(Nat.is_gt(n, 0n)) : Da.Keep}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def kp.held(m: Maybe<&2, List<&2, Nat>>, +mode: Nat) -> {Da.keep.held(m, mode) == Dash.sp_keep.held(m, mode) : Da.Keep}:
  match m:
    case None{}:
      {==}
    case Some{bs}:
      kp.mode(Nat.mod(mode, 64n))

def kp.keep(o: Da.Rotation, f: Da.Disk, +m: Nat) -> {Da.keep(o, f, m) == Dash.sp_keep(o, f, m) : Da.Keep}:
  match o:
    case Da.KeepToken{}:
      match f:
        case Da.NoFile{}:
          {==}
        case Da.Unread{}:
          {==}
        case Da.Holds{+s}:
          %Equal.sym(Maybe<&2, List<&2, Nat>>, Da.stored(Da.Holds{s}), Dash.sp_stored(Da.Holds{s}), Dash.dash_stored_spec(Da.Holds{s})) : {Da.keep.held(_, m) == Dash.sp_keep.held(Dash.sp_stored(Da.Holds{s}), m) : Da.Keep}
          kp.held(Dash.sp_stored(Da.Holds{s}), m)
        case Da.Huge{}:
          {==}
    case Da.RotateToken{}:
      {==}

def Dash.dash_keep_spec(o, f, m):
  kp.keep(o, f, m)
