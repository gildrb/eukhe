# eukhe: the proof of LAW sweep_stays_out_real

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA
import ../../laws/base.bend as LawsBase
import ./meet_exact.bend as PMeetExact

def so.dir(sw: Bool, m: Bool) -> {Staging.sp_descend(Staging.sp_met.dir(sw, m)) == Bool.and(Bool.not(sw), Bool.not(m)) : Bool}:
  match sw m:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def so.lock(a: Bool, b: Bool) -> {Staging.sp_descend(Staging.sp_met.lock(a, b)) == False{} : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def so.file(m: Maybe<&2, String>, +all: List<&2, Sg.Seen>) -> {Staging.sp_descend(Staging.sp_met.file(m, all)) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      so.lock(Staging.sp_swept(x), LawsBase.text_has_name(x, all))

def so.one(e: Sg.Seen, +all: List<&2, Sg.Seen>) -> {Staging.sp_descend(Staging.sp_met(e, all)) == Staging.sp_plain(e) : Bool}:
  match e:
    case Sg.Seen{n, k}:
      match n:
        case Sg.Utf{+s}:
          match k:
            case Sg.KDir{main}:
              so.dir(Staging.sp_swept(s), main)
            case Sg.KFile{}:
              so.file(LawsBase.text_unsuffix(".lock", s), all)
            case Sg.KOther{}:
              {==}
        case Sg.Raw{}:
          match k:
            case Sg.KDir{main}:
              so.dir(False{}, main)
            case Sg.KFile{}:
              {==}
            case Sg.KOther{}:
              {==}

def so.go(es: List<&2, Sg.Seen>, +all: List<&2, Sg.Seen>) -> {Staging.sp_descends(Staging.sp_meet.go(es, all)) == Staging.sp_plains(es) : List<&2, Bool>}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      %so.one(e, all) : {Staging.sp_descend(Staging.sp_met(e, all)) <> Staging.sp_descends(Staging.sp_meet.go(rest, all)) == _ <> Staging.sp_plains(rest) : List<&2, Bool>}
      %so.go(rest, all) : {Staging.sp_descend(Staging.sp_met(e, all)) <> Staging.sp_descends(Staging.sp_meet.go(rest, all)) == Staging.sp_descend(Staging.sp_met(e, all)) <> _ : List<&2, Bool>}
      {==}

def Staging.sweep_stays_out_real(es):
  %Equal.sym(List<&2, Sg.Met>, Sg.meet(es), Staging.sp_meet(es), Staging.meet_exact(es)) : {Staging.sp_descends(_) == Staging.sp_plains(es) : List<&2, Bool>}
  so.go(es, es)
