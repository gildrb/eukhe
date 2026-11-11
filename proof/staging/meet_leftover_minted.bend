# eukhe: the proof of LAW meet_leftover_minted

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA
import ../../laws/base.bend as LawsBase

# x is a directory with a name Rust mints
def ml.G(x: Maybe<&2, Sg.Seen>) -> Type:
  Sigma<&1, &1, String, t => Sigma<&1, &1, Staging.SpLab, l => Sigma<&1, &1, String, id => Sigma<&1, &1, Bool, m => {x == Some{Sg.Seen{Sg.Utf{Staging.sp_mint(t, l, id)}, Sg.KDir{m}}} : Maybe<&2, Sg.Seen>} & ({String.is_empty(t) == False{} : Bool} & {Staging.sp_hexn(32n, id) == True{} : Bool})>>>>

def ml.fin(-s: String, +main: Bool, ms: LA.mi.MS(s)) -> ml.G(Some{Sg.Seen{Sg.Utf{s}, Sg.KDir{main}}}):
  (+t, (+l, (+id, (es, (ht, hid))))) = ms
  (t, (l, (id, (main, (Equal.cong(String, Maybe<&2, Sg.Seen>, z => Some{Sg.Seen{Sg.Utf{z}, Sg.KDir{main}}}, s, Staging.sp_mint(t, l, id), es), (ht, hid))))))

def ml.dir(sw: Bool, +s: String, +main: Bool, esw: {Staging.sp_swept(s) == sw : Bool}, r: {LA.rr.m.dir(sw, main) == Sg.MLeftover{} : Sg.Met}) -> ml.G(Some{Sg.Seen{Sg.Utf{s}, Sg.KDir{main}}}):
  match sw:
    case True{}:
      ml.fin(s, main, LA.mi.swept(s, esw))
    case False{}:
      LA.mi.absurd_l(ml.G(Some{Sg.Seen{Sg.Utf{s}, Sg.KDir{main}}}), LA.rr.m.dir(False{}, main), r, LA.mi.dirf_l(ml.G(Some{Sg.Seen{Sg.Utf{s}, Sg.KDir{main}}}), main))

# an entry the real rule judges as a directory is a directory with a minted name
def ml.m(e: Sg.Seen, +all: List<&2, Sg.Seen>, r: {LA.rr.m(e, all) == Sg.MLeftover{} : Sg.Met}) -> ml.G(Some{e}):
  match e:
    case Sg.Seen{n, k}:
      match n:
        case Sg.Utf{+s}:
          match k:
            case Sg.KDir{+main}:
              ml.dir(Staging.sp_swept(s), s, main, {==}, r)
            case Sg.KFile{}:
              LA.mi.absurd_l(ml.G(Some{Sg.Seen{Sg.Utf{s}, Sg.KFile{}}}), LA.rr.m.file(LawsBase.text_unsuffix(".lock", s), all), r, LA.mi.file_l(ml.G(Some{Sg.Seen{Sg.Utf{s}, Sg.KFile{}}}), LawsBase.text_unsuffix(".lock", s), all))
            case Sg.KOther{}:
              LA.mi.absurd_l(ml.G(Some{Sg.Seen{Sg.Utf{s}, Sg.KOther{}}}), Sg.MKeep{}, r, Unit{})
        case Sg.Raw{}:
          match k:
            case Sg.KDir{+main}:
              LA.mi.absurd_l(ml.G(Some{Sg.Seen{Sg.Raw{}, Sg.KDir{main}}}), LA.rr.m.dir(False{}, main), r, LA.mi.dirf_l(ml.G(Some{Sg.Seen{Sg.Raw{}, Sg.KDir{main}}}), main))
            case Sg.KFile{}:
              LA.mi.absurd_l(ml.G(Some{Sg.Seen{Sg.Raw{}, Sg.KFile{}}}), Sg.MKeep{}, r, Unit{})
            case Sg.KOther{}:
              LA.mi.absurd_l(ml.G(Some{Sg.Seen{Sg.Raw{}, Sg.KOther{}}}), Sg.MKeep{}, r, Unit{})

# the entry at index k of es, judged as a directory in the listing all
def ml.at(es: List<&2, Sg.Seen>, k: Nat, +all: List<&2, Sg.Seen>, h: {List.get(&2, Sg.Met, Sg.meet.go(es, all), k) == Some{Sg.MLeftover{}} : Maybe<&2, Sg.Met>}) -> ml.G(List.get(&2, Sg.Seen, es, k)):
  match es:
    case Nil{}:
      LA.mi.none_some(Sg.Met, ml.G(None{}), Sg.MLeftover{}, h)
    case +e <> +rest:
      match k:
        case 0n:
          +hm = Equal.cong(Maybe<&2, Sg.Met>, Sg.Met, z => LA.mi.val(z), Some{Sg.met(e, all)}, Some{Sg.MLeftover{}}, h)
          ml.m(e, all, Equal.trans(Sg.Met, LA.rr.m(e, all), Sg.met(e, all), Sg.MLeftover{}, Equal.sym(Sg.Met, Sg.met(e, all), LA.rr.m(e, all), LA.rr.met(e, all)), hm))
        case 1n+j:
          ml.at(rest, j, all, h)

def Staging.meet_leftover_minted(es, k, judged):
  ml.at(es, k, es, judged)
