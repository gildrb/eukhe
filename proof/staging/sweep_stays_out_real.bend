# eukhe: the proof of LAW sweep_stays_out_real
# Entry by entry (so.one): the class meet gives (LA.rr.met: the class on
# the laws' text helpers) enters exactly a directory with no main.jsonl
# that it does not judge a leftover; a file, a symlink, a storage and a
# leftover are never entered.

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA
import ../../laws/base.bend as LawsBase

def so.dir(sw: Bool, m: Bool) -> {Staging.sp_descend(LA.rr.m.dir(sw, m)) == Bool.and(Bool.not(m), Bool.not(Staging.sp_leftover(LA.rr.m.dir(sw, m)))) : Bool}:
  match sw m:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def so.lock(a: Bool, b: Bool) -> {Staging.sp_descend(LA.rr.m.lock(a, b)) == False{} : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def so.file(m: Maybe<&2, String>, +all: List<&2, Sg.Seen>) -> {Staging.sp_descend(LA.rr.m.file(m, all)) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      so.lock(LA.sp_swept(x), LawsBase.text_has_name(x, all))

def so.one(e: Sg.Seen, +all: List<&2, Sg.Seen>) -> {Staging.sp_descend(LA.rr.m(e, all)) == Bool.and(Staging.sp_open_dir(e), Bool.not(Staging.sp_leftover(LA.rr.m(e, all)))) : Bool}:
  match e:
    case Sg.Seen{n, k}:
      match n:
        case Sg.Utf{+s}:
          match k:
            case Sg.KDir{main}:
              so.dir(LA.sp_swept(s), main)
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

def so.go(es: List<&2, Sg.Seen>, +all: List<&2, Sg.Seen>) -> {Staging.sp_descends(Sg.meet.go(es, all)) == Staging.sp_enters(es, Sg.meet.go(es, all)) : List<&2, Bool>}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      +x = Staging.sp_descends(Sg.meet.go(rest, all))
      +y = Staging.sp_enters(rest, Sg.meet.go(rest, all))
      %Equal.sym(Sg.Met, Sg.met(e, all), LA.rr.m(e, all), LA.rr.met(e, all)) : {Staging.sp_descend(_) <> x == Bool.and(Staging.sp_open_dir(e), Bool.not(Staging.sp_leftover(_))) <> y : List<&2, Bool>}
      %Equal.sym(Bool, Staging.sp_descend(LA.rr.m(e, all)), Bool.and(Staging.sp_open_dir(e), Bool.not(Staging.sp_leftover(LA.rr.m(e, all)))), so.one(e, all)) : {_ <> x == Bool.and(Staging.sp_open_dir(e), Bool.not(Staging.sp_leftover(LA.rr.m(e, all)))) <> y : List<&2, Bool>}
      %Equal.sym(List<&2, Bool>, x, y, so.go(rest, all)) : {Bool.and(Staging.sp_open_dir(e), Bool.not(Staging.sp_leftover(LA.rr.m(e, all)))) <> _ == Bool.and(Staging.sp_open_dir(e), Bool.not(Staging.sp_leftover(LA.rr.m(e, all)))) <> y : List<&2, Bool>}
      {==}

def Staging.sweep_stays_out_real(es):
  so.go(es, es)
