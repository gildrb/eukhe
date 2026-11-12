# eukhe: the proof of LAW arg_repair_coerce_array
#
# PROOF: by cases on the value, a string's shape and the `items.type`
# (ca.lone: the one-item array exactly for `string`).

import Base
import ../../bend/arg_repair.bend as Ar
import ../../laws/arg_repair/coerce.bend as ArgRepairCoerce
import ./base.bend as AB
import ./base/coerce.bend as AC

def ca.lone_at(b: Bool) -> {Ar.spell.one.at(b) == ArgRepairCoerce.sp_when(b, Ar.TOne{}) : Maybe<&2, Ar.To>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ca.lone(it: Maybe<&2, String>) -> {Ar.spell.one(it) == ArgRepairCoerce.sp_lone(it) : Maybe<&2, Ar.To>}:
  match it:
    case None{}:
      {==}
    case Some{+t}:
      ca.lone_at(String.eq(t, "string"))

def ArgRepairCoerce.arg_repair_coerce_array(n, it, v):
  match v:
    case Ar.VNull{}:
      {==}
    case Ar.VBool{b}:
      {==}
    case Ar.VNum{x}:
      {==}
    case Ar.VStr{t, m, sh}:
      match sh:
        case Ar.SPlain{}:
          ca.lone(it)
        case Ar.SBrace{o}:
          ca.lone(it)
        case Ar.SBracket{a}:
          match a:
            case True{}:
              {==}
            case False{}:
              {==}
    case Ar.VArr{}:
      {==}
    case Ar.VObj{}:
      {==}
