# eukhe: the proof of LAW meet_orphan_minted

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA
import ../../laws/base.bend as LawsBase

# x is the lock file of a name Rust mints, and no entry of all has that name
def om.G(x: Maybe<&2, Sg.Seen>, all: List<&2, Sg.Seen>) -> Type:
  Sigma<&1, &1, String, t => Sigma<&1, &1, Staging.SpLab, l => Sigma<&1, &1, String, id => {x == Some{Sg.Seen{Sg.Utf{String.append(Staging.sp_mint(t, l, id), ".lock")}, Sg.KFile{}}} : Maybe<&2, Sg.Seen>} & ({String.is_empty(t) == False{} : Bool} & ({Staging.sp_hexn(32n, id) == True{} : Bool} & {LawsBase.text_has_name(Staging.sp_mint(t, l, id), all) == False{} : Bool}))>>>

def om.fin(+x: String, -s: String, +all: List<&2, Sg.Seen>, ms: LA.mi.MS(x), eb: {LawsBase.text_has_name(x, all) == False{} : Bool}, us: {s == String.append(x, ".lock") : String}) -> om.G(Some{Sg.Seen{Sg.Utf{s}, Sg.KFile{}}}, all):
  (+t, (+l, (+id, (+ex, (ht, hid))))) = ms
  +eq = Equal.cong(String, Maybe<&2, Sg.Seen>, z => Some{Sg.Seen{Sg.Utf{z}, Sg.KFile{}}}, s, String.append(Staging.sp_mint(t, l, id), ".lock"),
    Equal.trans(String, s, String.append(x, ".lock"), String.append(Staging.sp_mint(t, l, id), ".lock"), us, Equal.cong(String, String, z => String.append(z, ".lock"), x, Staging.sp_mint(t, l, id), ex)))
  +hn = Equal.trans(Bool, LawsBase.text_has_name(Staging.sp_mint(t, l, id), all), LawsBase.text_has_name(x, all), False{},
    Equal.cong(String, Bool, z => LawsBase.text_has_name(z, all), Staging.sp_mint(t, l, id), x, Equal.sym(String, x, Staging.sp_mint(t, l, id), ex)), eb)
  (t, (l, (id, (eq, (ht, (hid, hn))))))

def om.lock(a: Bool, b: Bool, +x: String, -s: String, +all: List<&2, Sg.Seen>, ea: {LA.sp_swept(x) == a : Bool}, eb: {LawsBase.text_has_name(x, all) == b : Bool}, us: {s == String.append(x, ".lock") : String}, r: {LA.rr.m.lock(a, b) == Sg.MOrphan{} : Sg.Met}) -> om.G(Some{Sg.Seen{Sg.Utf{s}, Sg.KFile{}}}, all):
  match a b:
    case True{} True{}:
      LA.mi.absurd_o(om.G(Some{Sg.Seen{Sg.Utf{s}, Sg.KFile{}}}, all), Sg.MKeep{}, r, Unit{})
    case True{} False{}:
      om.fin(x, s, all, LA.mi.swept(x, ea), eb, us)
    case False{} True{}:
      LA.mi.absurd_o(om.G(Some{Sg.Seen{Sg.Utf{s}, Sg.KFile{}}}, all), Sg.MKeep{}, r, Unit{})
    case False{} False{}:
      LA.mi.absurd_o(om.G(Some{Sg.Seen{Sg.Utf{s}, Sg.KFile{}}}, all), Sg.MKeep{}, r, Unit{})

def om.file(m: Maybe<&2, String>, -s: String, +all: List<&2, Sg.Seen>, us: LA.mi.US(".lock", s, m), r: {LA.rr.m.file(m, all) == Sg.MOrphan{} : Sg.Met}) -> om.G(Some{Sg.Seen{Sg.Utf{s}, Sg.KFile{}}}, all):
  match m:
    case None{}:
      LA.mi.absurd_o(om.G(Some{Sg.Seen{Sg.Utf{s}, Sg.KFile{}}}, all), Sg.MKeep{}, r, Unit{})
    case Some{+x}:
      om.lock(LA.sp_swept(x), LawsBase.text_has_name(x, all), x, s, all, {==}, {==}, us, r)

# an entry the real rule judges as a lock file is the lock file of a
# minted name whose directory is not in the listing
def om.m(e: Sg.Seen, +all: List<&2, Sg.Seen>, r: {LA.rr.m(e, all) == Sg.MOrphan{} : Sg.Met}) -> om.G(Some{e}, all):
  match e:
    case Sg.Seen{n, k}:
      match n:
        case Sg.Utf{+s}:
          match k:
            case Sg.KDir{+main}:
              LA.mi.absurd_o(om.G(Some{Sg.Seen{Sg.Utf{s}, Sg.KDir{main}}}, all), LA.rr.m.dir(LA.sp_swept(s), main), r, LA.mi.dir_o(om.G(Some{Sg.Seen{Sg.Utf{s}, Sg.KDir{main}}}, all), LA.sp_swept(s), main))
            case Sg.KFile{}:
              om.file(LawsBase.text_unsuffix(".lock", s), s, all, LA.mi.uns(".lock", s), r)
            case Sg.KOther{}:
              LA.mi.absurd_o(om.G(Some{Sg.Seen{Sg.Utf{s}, Sg.KOther{}}}, all), Sg.MKeep{}, r, Unit{})
        case Sg.Raw{}:
          match k:
            case Sg.KDir{+main}:
              LA.mi.absurd_o(om.G(Some{Sg.Seen{Sg.Raw{}, Sg.KDir{main}}}, all), LA.rr.m.dir(False{}, main), r, LA.mi.dir_o(om.G(Some{Sg.Seen{Sg.Raw{}, Sg.KDir{main}}}, all), False{}, main))
            case Sg.KFile{}:
              LA.mi.absurd_o(om.G(Some{Sg.Seen{Sg.Raw{}, Sg.KFile{}}}, all), Sg.MKeep{}, r, Unit{})
            case Sg.KOther{}:
              LA.mi.absurd_o(om.G(Some{Sg.Seen{Sg.Raw{}, Sg.KOther{}}}, all), Sg.MKeep{}, r, Unit{})

# the entry at index k of es, judged as a lock file in the listing all
def om.at(es: List<&2, Sg.Seen>, k: Nat, +all: List<&2, Sg.Seen>, h: {List.get(&2, Sg.Met, Sg.meet.go(es, all), k) == Some{Sg.MOrphan{}} : Maybe<&2, Sg.Met>}) -> om.G(List.get(&2, Sg.Seen, es, k), all):
  match es:
    case Nil{}:
      LA.mi.none_some(Sg.Met, om.G(None{}, all), Sg.MOrphan{}, h)
    case +e <> +rest:
      match k:
        case 0n:
          +hm = Equal.cong(Maybe<&2, Sg.Met>, Sg.Met, z => LA.mi.val(z), Some{Sg.met(e, all)}, Some{Sg.MOrphan{}}, h)
          om.m(e, all, Equal.trans(Sg.Met, LA.rr.m(e, all), Sg.met(e, all), Sg.MOrphan{}, Equal.sym(Sg.Met, Sg.met(e, all), LA.rr.m(e, all), LA.rr.met(e, all)), hm))
        case 1n+j:
          om.at(rest, j, all, h)

def Staging.meet_orphan_minted(es, k, judged):
  om.at(es, k, es, judged)
