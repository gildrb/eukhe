# eukhe: lemmas of area listing: the verdicts of the scan, entry by entry
#
# The scan's verdict on an entry (the spec's sp_pick, which the code's
# Ls.pick is: ls.pick) lists it as a storage under n exactly when it is a
# storage directory named n (lsv.store1), as a legacy file under n exactly
# when it is `<n>.jsonl` and n is free (lsv.legacy1), and is always about
# the entry itself (lsv.own1); folded over the entries (lsv.stores,
# lsv.legacies, lsv.owns).

import Base
import ../../../bend/staging.bend as Sg
import ../../../bend/listing.bend as Ls
import ../../../laws/listing.bend as Listing
import ../../../laws/base.bend as LawsBase
import ../../base/staging.bend as LStg
import ./scan.bend as LA
import ./stem.bend as LT

def lsv.and_t(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def lsv.and_f(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# Storages
# --------

def lsv.dir(+n: String, main: Bool, hid: Bool, +s: String) -> {Listing.sp_is_store(n, Listing.sp_dir(main, hid, s)) == Bool.and(main, Bool.and(Bool.not(hid), LawsBase.text_same(s, n))) : Bool}:
  match main:
    case True{}:
      match hid:
        case True{}:
          {==}
        case False{}:
          {==}
    case False{}:
      {==}

def lsv.store1(+n: String, e: Sg.Seen, +all: List<&2, Sg.Seen>) -> {Listing.sp_is_store(n, Listing.sp_pick(e, all)) == Listing.sp_store_entry(n, e) : Bool}:
  match e:
    case Sg.Seen{nm, k}:
      match nm:
        case Sg.Utf{+s}:
          match k:
            case Sg.KDir{main}:
              lsv.dir(n, main, Listing.sp_hidden(s), s)
            case Sg.KFile{}:
              LA.ls.stem_not_store(n, LawsBase.text_unsuffix(".jsonl", s), all)
            case Sg.KOther{}:
              {==}
        case Sg.Raw{}:
          {==}

def lsv.stores(+n: String, xs: List<&2, Sg.Seen>, +all: List<&2, Sg.Seen>) -> {Listing.sp_has_store(n, LA.ls.sp_scan.go(xs, all)) == Listing.sp_store_named(n, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      %lsv.store1(n, x, all) : {Bool.or(Listing.sp_is_store(n, Listing.sp_pick(x, all)), Listing.sp_has_store(n, LA.ls.sp_scan.go(r, all))) == Bool.or(_, Listing.sp_store_named(n, r)) : Bool}
      %lsv.stores(n, r, all) : {Bool.or(Listing.sp_is_store(n, Listing.sp_pick(x, all)), Listing.sp_has_store(n, LA.ls.sp_scan.go(r, all))) == Bool.or(Listing.sp_is_store(n, Listing.sp_pick(x, all)), _) : Bool}
      {==}

# Legacy files
# ------------

def lsv.leg(+n: String, g: Bool, +st: String) -> {Listing.sp_is_legacy(n, Listing.sp_legacy(g, st)) == Bool.and(Bool.not(g), LawsBase.text_same(st, n)) : Bool}:
  match g:
    case True{}:
      {==}
    case False{}:
      {==}

def lsv.fin(c: Bool, +n: String, +st: String, +all: List<&2, Sg.Seen>, ec: {LawsBase.text_same(st, n) == c : Bool}) -> {Bool.and(Bool.not(Bool.or(Bool.or(String.is_empty(st), Bool.or(LawsBase.text_same(st, "."), LawsBase.text_same(st, ".."))), LawsBase.text_has_name(st, all))), c) == Bool.and(c, Bool.not(Bool.or(Bool.or(String.is_empty(n), Bool.or(LawsBase.text_same(n, "."), LawsBase.text_same(n, ".."))), LawsBase.text_has_name(n, all)))) : Bool}:
  match c:
    case True{}:
      %Equal.sym(String, st, n, LStg.stg.same_eq(st, n, ec)) : {Bool.and(Bool.not(Bool.or(Bool.or(String.is_empty(_), Bool.or(LawsBase.text_same(_, "."), LawsBase.text_same(_, ".."))), LawsBase.text_has_name(_, all))), True{}) == Bool.not(Bool.or(Bool.or(String.is_empty(n), Bool.or(LawsBase.text_same(n, "."), LawsBase.text_same(n, ".."))), LawsBase.text_has_name(n, all))) : Bool}
      lsv.and_t(Bool.not(Bool.or(Bool.or(String.is_empty(n), Bool.or(LawsBase.text_same(n, "."), LawsBase.text_same(n, ".."))), LawsBase.text_has_name(n, all))))
    case False{}:
      lsv.and_f(Bool.not(Bool.or(Bool.or(String.is_empty(st), Bool.or(LawsBase.text_same(st, "."), LawsBase.text_same(st, ".."))), LawsBase.text_has_name(st, all))))

def lsv.file(+n: String, +f: String, +all: List<&2, Sg.Seen>, m: Maybe<&2, String>, em: {LawsBase.text_unsuffix(".jsonl", f) == m : Maybe<&2, String>}) -> {Listing.sp_is_legacy(n, Listing.sp_stem(m, all)) == Bool.and(LawsBase.text_same(f, String.append(n, ".jsonl")), Listing.sp_legacy_free(n, all)) : Bool}:
  match m:
    case None{}:
      %Equal.sym(Bool, LawsBase.text_same(f, String.append(n, ".jsonl")), False{}, LT.lst.no_stem(f, n, em)) : {False{} == Bool.and(_, Listing.sp_legacy_free(n, all)) : Bool}
      {==}
    case Some{+st}:
      %Equal.sym(Bool, Listing.sp_is_legacy(n, Listing.sp_legacy(Bool.or(Bool.or(String.is_empty(st), Bool.or(LawsBase.text_same(st, "."), LawsBase.text_same(st, ".."))), LawsBase.text_has_name(st, all)), st)), Bool.and(Bool.not(Bool.or(Bool.or(String.is_empty(st), Bool.or(LawsBase.text_same(st, "."), LawsBase.text_same(st, ".."))), LawsBase.text_has_name(st, all))), LawsBase.text_same(st, n)), lsv.leg(n, Bool.or(Bool.or(String.is_empty(st), Bool.or(LawsBase.text_same(st, "."), LawsBase.text_same(st, ".."))), LawsBase.text_has_name(st, all)), st)) : {_ == Bool.and(LawsBase.text_same(f, String.append(n, ".jsonl")), Listing.sp_legacy_free(n, all)) : Bool}
      %Equal.sym(Bool, LawsBase.text_same(f, String.append(n, ".jsonl")), LawsBase.text_same(st, n), LT.lst.same_stem(f, st, n, em)) : {Bool.and(Bool.not(Bool.or(Bool.or(String.is_empty(st), Bool.or(LawsBase.text_same(st, "."), LawsBase.text_same(st, ".."))), LawsBase.text_has_name(st, all))), LawsBase.text_same(st, n)) == Bool.and(_, Listing.sp_legacy_free(n, all)) : Bool}
      lsv.fin(LawsBase.text_same(st, n), n, st, all, {==})

def lsv.legacy1(+n: String, e: Sg.Seen, +all: List<&2, Sg.Seen>) -> {Listing.sp_is_legacy(n, Listing.sp_pick(e, all)) == Bool.and(Listing.sp_file_entry(n, e), Listing.sp_legacy_free(n, all)) : Bool}:
  match e:
    case Sg.Seen{nm, k}:
      match nm:
        case Sg.Utf{+s}:
          match k:
            case Sg.KDir{main}:
              LA.ls.dir_not_legacy(n, main, Listing.sp_hidden(s), s)
            case Sg.KFile{}:
              lsv.file(n, s, all, LawsBase.text_unsuffix(".jsonl", s), {==})
            case Sg.KOther{}:
              {==}
        case Sg.Raw{}:
          {==}

def lsv.or_and(a: Bool, +b: Bool, +k: Bool) -> {Bool.or(Bool.and(a, k), Bool.and(b, k)) == Bool.and(Bool.or(a, b), k) : Bool}:
  match a:
    case True{}:
      match k:
        case True{}:
          {==}
        case False{}:
          lsv.and_f(b)
    case False{}:
      {==}

def lsv.legacies(+n: String, xs: List<&2, Sg.Seen>, +all: List<&2, Sg.Seen>) -> {Listing.sp_has_legacy(n, LA.ls.sp_scan.go(xs, all)) == Bool.and(Listing.sp_file_named(n, xs), Listing.sp_legacy_free(n, all)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      +K = Listing.sp_legacy_free(n, all)
      %Equal.sym(Bool, Listing.sp_is_legacy(n, Listing.sp_pick(x, all)), Bool.and(Listing.sp_file_entry(n, x), K), lsv.legacy1(n, x, all)) : {Bool.or(_, Listing.sp_has_legacy(n, LA.ls.sp_scan.go(r, all))) == Bool.and(Bool.or(Listing.sp_file_entry(n, x), Listing.sp_file_named(n, r)), K) : Bool}
      %Equal.sym(Bool, Listing.sp_has_legacy(n, LA.ls.sp_scan.go(r, all)), Bool.and(Listing.sp_file_named(n, r), K), lsv.legacies(n, r, all)) : {Bool.or(Bool.and(Listing.sp_file_entry(n, x), K), _) == Bool.and(Bool.or(Listing.sp_file_entry(n, x), Listing.sp_file_named(n, r)), K) : Bool}
      lsv.or_and(Listing.sp_file_entry(n, x), Listing.sp_file_named(n, r), K)

# Each verdict is about its entry
# -------------------------------

def lsv.own_dir(main: Bool, hid: Bool, +s: String, eh: {Listing.sp_hidden(s) == hid : Bool}) -> {Listing.sp_own1(Listing.sp_dir(main, hid, s), Sg.Seen{Sg.Utf{s}, Sg.KDir{main}}) == True{} : Bool}:
  match main:
    case True{}:
      match hid:
        case True{}:
          {==}
        case False{}:
          %Equal.sym(Bool, Listing.sp_hidden(s), False{}, eh) : {Bool.and(True{}, Bool.and(Bool.not(_), LawsBase.text_same(s, s))) == True{} : Bool}
          LStg.stg.same_refl(s)
    case False{}:
      {==}

def lsv.own_leg(g: Bool, +f: String, +st: String, em: {LawsBase.text_unsuffix(".jsonl", f) == Some{st} : Maybe<&2, String>}) -> {Listing.sp_own1(Listing.sp_legacy(g, st), Sg.Seen{Sg.Utf{f}, Sg.KFile{}}) == True{} : Bool}:
  match g:
    case True{}:
      {==}
    case False{}:
      Equal.trans(Bool, LawsBase.text_same(f, String.append(st, ".jsonl")), LawsBase.text_same(st, st), True{}, LT.lst.same_stem(f, st, st, em), LStg.stg.same_refl(st))

def lsv.own_file(+f: String, +all: List<&2, Sg.Seen>, m: Maybe<&2, String>, em: {LawsBase.text_unsuffix(".jsonl", f) == m : Maybe<&2, String>}) -> {Listing.sp_own1(Listing.sp_stem(m, all), Sg.Seen{Sg.Utf{f}, Sg.KFile{}}) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+st}:
      lsv.own_leg(Bool.or(Bool.or(String.is_empty(st), Bool.or(LawsBase.text_same(st, "."), LawsBase.text_same(st, ".."))), LawsBase.text_has_name(st, all)), f, st, em)

def lsv.own1(e: Sg.Seen, +all: List<&2, Sg.Seen>) -> {Listing.sp_own1(Listing.sp_pick(e, all), e) == True{} : Bool}:
  match e:
    case Sg.Seen{nm, k}:
      match nm:
        case Sg.Utf{+s}:
          match k:
            case Sg.KDir{main}:
              lsv.own_dir(main, Listing.sp_hidden(s), s, {==})
            case Sg.KFile{}:
              lsv.own_file(s, all, LawsBase.text_unsuffix(".jsonl", s), {==})
            case Sg.KOther{}:
              {==}
        case Sg.Raw{}:
          {==}

def lsv.owns(xs: List<&2, Sg.Seen>, +all: List<&2, Sg.Seen>) -> {Listing.sp_own(LA.ls.sp_scan.go(xs, all), xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      %Equal.sym(Bool, Listing.sp_own1(Listing.sp_pick(x, all), x), True{}, lsv.own1(x, all)) : {Bool.and(_, Listing.sp_own(LA.ls.sp_scan.go(r, all), r)) == True{} : Bool}
      lsv.owns(r, all)
