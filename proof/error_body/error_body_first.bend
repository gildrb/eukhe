# eukhe: the proof of LAW error_body_first
#
# PROOF: every three probes: both sides compute (the code picks the place
# the list's first place that holds something names, then trims and cuts
# that text as the body of it alone).

import Base
import ../../bend/error_body.bend as Eb
import ../../laws/error_body.bend as ErrorBody
import ../base/staging.bend as LStg
import ./base.bend as LA

def ErrorBody.error_body_first(b, e, r):
  match b e r:
    case Eb.PNone{} Eb.PNone{} Eb.PNone{}:
      {==}
    case Eb.PNone{} Eb.PNone{} Eb.PText{z}:
      {==}
    case Eb.PNone{} Eb.PNone{} Eb.PObj{w}:
      {==}
    case Eb.PNone{} Eb.PText{t} Eb.PNone{}:
      {==}
    case Eb.PNone{} Eb.PText{t} Eb.PText{z}:
      {==}
    case Eb.PNone{} Eb.PText{t} Eb.PObj{w}:
      {==}
    case Eb.PNone{} Eb.PObj{o} Eb.PNone{}:
      {==}
    case Eb.PNone{} Eb.PObj{o} Eb.PText{z}:
      {==}
    case Eb.PNone{} Eb.PObj{o} Eb.PObj{w}:
      {==}
    case Eb.PText{x} Eb.PNone{} Eb.PNone{}:
      {==}
    case Eb.PText{x} Eb.PNone{} Eb.PText{z}:
      {==}
    case Eb.PText{x} Eb.PNone{} Eb.PObj{w}:
      {==}
    case Eb.PText{x} Eb.PText{t} Eb.PNone{}:
      {==}
    case Eb.PText{x} Eb.PText{t} Eb.PText{z}:
      {==}
    case Eb.PText{x} Eb.PText{t} Eb.PObj{w}:
      {==}
    case Eb.PText{x} Eb.PObj{o} Eb.PNone{}:
      {==}
    case Eb.PText{x} Eb.PObj{o} Eb.PText{z}:
      {==}
    case Eb.PText{x} Eb.PObj{o} Eb.PObj{w}:
      {==}
    case Eb.PObj{y} Eb.PNone{} Eb.PNone{}:
      {==}
    case Eb.PObj{y} Eb.PNone{} Eb.PText{z}:
      {==}
    case Eb.PObj{y} Eb.PNone{} Eb.PObj{w}:
      {==}
    case Eb.PObj{y} Eb.PText{t} Eb.PNone{}:
      {==}
    case Eb.PObj{y} Eb.PText{t} Eb.PText{z}:
      {==}
    case Eb.PObj{y} Eb.PText{t} Eb.PObj{w}:
      {==}
    case Eb.PObj{y} Eb.PObj{o} Eb.PNone{}:
      {==}
    case Eb.PObj{y} Eb.PObj{o} Eb.PText{z}:
      {==}
    case Eb.PObj{y} Eb.PObj{o} Eb.PObj{w}:
      {==}
