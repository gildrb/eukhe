# eukhe: lemmas the proofs of area listing share: the scan

import Base
import ../../../bend/staging.bend as Sg
import ../../../bend/listing.bend as Ls
import ../../../laws/listing.bend as Listing
import ../../../laws/base.bend as LawsBase
import ../../base/staging.bend as LStg

# ---- the scan: the code is its spec ----

def ls.hidden(s: String) -> {Ls.hidden(s) == Listing.sp_hidden(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      match c:
        case Chr{x}:
          {==}

def ls.dir(main: Bool, hid: Bool, s: String) -> {Ls.pick.dir(main, hid, s) == Listing.sp_dir(main, hid, s) : Ls.Pick}:
  match main hid:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def ls.legacy(g: Bool, s: String) -> {Ls.pick.legacy(g, s) == Listing.sp_legacy(g, s) : Ls.Pick}:
  match g:
    case True{}:
      {==}
    case False{}:
      {==}

def ls.stem(m: Maybe<&2, String>, +all: List<&2, Sg.Seen>) -> {Ls.pick.stem(m, all) == Listing.sp_stem(m, all) : Ls.Pick}:
  match m:
    case None{}:
      {==}
    case Some{+st}:
      +e = String.is_empty(st)
      +h = Sg.has_name(st, all)
      +a = Sg.same(st, ".")
      +b = Sg.same(st, "..")
      %LStg.stg.same(st, ".") : {Ls.pick.legacy(Bool.or(Bool.or(e, Bool.or(a, b)), h), st) == Listing.sp_legacy(Bool.or(Bool.or(e, Bool.or(_, LawsBase.text_same(st, ".."))), LawsBase.text_has_name(st, all)), st) : Ls.Pick}
      %LStg.stg.same(st, "..") : {Ls.pick.legacy(Bool.or(Bool.or(e, Bool.or(a, b)), h), st) == Listing.sp_legacy(Bool.or(Bool.or(e, Bool.or(a, _)), LawsBase.text_has_name(st, all)), st) : Ls.Pick}
      %LStg.stg.has_name(st, all) : {Ls.pick.legacy(Bool.or(Bool.or(e, Bool.or(a, b)), h), st) == Listing.sp_legacy(Bool.or(Bool.or(e, Bool.or(a, b)), _), st) : Ls.Pick}
      ls.legacy(Bool.or(Bool.or(e, Bool.or(a, b)), h), st)

def ls.utf(k: Sg.Form, +s: String, +all: List<&2, Sg.Seen>) -> {Ls.pick.utf(k, s, all) == Listing.sp_pick.utf(k, s, all) : Ls.Pick}:
  match k:
    case Sg.KDir{+main}:
      %ls.hidden(s) : {Ls.pick.dir(main, Ls.hidden(s), s) == Listing.sp_dir(main, _, s) : Ls.Pick}
      ls.dir(main, Ls.hidden(s), s)
    case Sg.KFile{}:
      %LStg.stg.unsuffix(".jsonl", s) : {Ls.pick.stem(Sg.unsuffix(".jsonl", s), all) == Listing.sp_stem(_, all) : Ls.Pick}
      ls.stem(Sg.unsuffix(".jsonl", s), all)
    case Sg.KOther{}:
      {==}

def ls.pick(e: Sg.Seen, +all: List<&2, Sg.Seen>) -> {Ls.pick(e, all) == Listing.sp_pick(e, all) : Ls.Pick}:
  match e:
    case Sg.Seen{n, k}:
      match n:
        case Sg.Utf{s}:
          ls.utf(k, s, all)
        case Sg.Raw{}:
          {==}

def ls.scan_go(es: List<&2, Sg.Seen>, +all: List<&2, Sg.Seen>) -> {Ls.scan.go(es, all) == Listing.sp_scan.go(es, all) : List<&2, Ls.Pick>}:
  match es:
    case Nil{}:
      {==}
    case +e <> +rest:
      %ls.pick(e, all) : {Ls.pick(e, all) <> Ls.scan.go(rest, all) == _ <> Listing.sp_scan.go(rest, all) : List<&2, Ls.Pick>}
      %ls.scan_go(rest, all) : {Ls.pick(e, all) <> Ls.scan.go(rest, all) == Ls.pick(e, all) <> _ : List<&2, Ls.Pick>}
      {==}

# ---- what the spec's picks say ----

def ls.or_true(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# a stem's pick is no storage
def ls.legacy_not_store(+n: String, g: Bool, s: String) -> {Listing.sp_is_store(n, Listing.sp_legacy(g, s)) == False{} : Bool}:
  match g:
    case True{}:
      {==}
    case False{}:
      {==}

def ls.stem_not_store(+n: String, m: Maybe<&2, String>, +all: List<&2, Sg.Seen>) -> {Listing.sp_is_store(n, Listing.sp_stem(m, all)) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+st}:
      ls.legacy_not_store(n, Bool.or(Bool.or(String.is_empty(st), Bool.or(LawsBase.text_same(st, "."), LawsBase.text_same(st, ".."))), LawsBase.text_has_name(st, all)), st)

# a directory's pick is no legacy file
def ls.dir_not_legacy(+n: String, main: Bool, hid: Bool, s: String) -> {Listing.sp_is_legacy(n, Listing.sp_dir(main, hid, s)) == False{} : Bool}:
  match main hid:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# a storage picked under id s is listed under the name s
def ls.dir_store(+n: String, main: Bool, hid: Bool, +s: String, h: {Listing.sp_is_store(n, Listing.sp_dir(main, hid, s)) == True{} : Bool}) -> {LawsBase.text_same(s, n) == True{} : Bool}:
  match main hid:
    case True{} True{}:
      LStg.stg.absurdF({LawsBase.text_same(s, n) == True{} : Bool}, h)
    case True{} False{}:
      h
    case False{} True{}:
      LStg.stg.absurdF({LawsBase.text_same(s, n) == True{} : Bool}, h)
    case False{} False{}:
      LStg.stg.absurdF({LawsBase.text_same(s, n) == True{} : Bool}, h)

def ls.name(e: Sg.Seen) -> Sg.Name:
  match e:
    case Sg.Seen{n, k}:
      n

# an entry picked as a storage under n has the name n
def ls.store_named(+n: String, e: Sg.Seen, +all: List<&2, Sg.Seen>, h: {Listing.sp_is_store(n, Listing.sp_pick(e, all)) == True{} : Bool}) -> {LawsBase.text_named(n, ls.name(e)) == True{} : Bool}:
  match e:
    case Sg.Seen{nm, k}:
      match nm:
        case Sg.Utf{+s}:
          match k:
            case Sg.KDir{main}:
              ls.dir_store(n, main, Listing.sp_hidden(s), s, h)
            case Sg.KFile{}:
              LStg.stg.absurdF({LawsBase.text_same(s, n) == True{} : Bool}, Equal.trans(Bool, False{}, Listing.sp_is_store(n, Listing.sp_stem(LawsBase.text_unsuffix(".jsonl", s), all)), True{}, Equal.sym(Bool, Listing.sp_is_store(n, Listing.sp_stem(LawsBase.text_unsuffix(".jsonl", s), all)), False{}, ls.stem_not_store(n, LawsBase.text_unsuffix(".jsonl", s), all)), h))
            case Sg.KOther{}:
              LStg.stg.absurdF({LawsBase.text_same(s, n) == True{} : Bool}, h)
        case Sg.Raw{}:
          LStg.stg.absurdF({False{} == True{} : Bool}, h)

def ls.hsn.at(+n: String, x: Sg.Seen, -r: List<&2, Sg.Seen>, +all: List<&2, Sg.Seen>, b: Bool, eb: {Listing.sp_is_store(n, Listing.sp_pick(x, all)) == b : Bool},
  h: {Bool.or(b, Listing.sp_has_store(n, Listing.sp_scan.go(r, all))) == True{} : Bool},
  ih: {Listing.sp_has_store(n, Listing.sp_scan.go(r, all)) == True{} : Bool} -> {LawsBase.text_has_name(n, r) == True{} : Bool}) -> {LawsBase.text_has_name(n, x <> r) == True{} : Bool}:
  match x:
    case Sg.Seen{+nm, +k}:
      match b:
        case True{}:
          %Equal.sym(Bool, LawsBase.text_named(n, nm), True{}, ls.store_named(n, Sg.Seen{nm, k}, all, eb)) : {Bool.or(_, LawsBase.text_has_name(n, r)) == True{} : Bool}
          {==}
        case False{}:
          %Equal.sym(Bool, LawsBase.text_has_name(n, r), True{}, ih(h)) : {Bool.or(LawsBase.text_named(n, nm), _) == True{} : Bool}
          ls.or_true(LawsBase.text_named(n, nm))

# a name listed as a storage is the name of an entry
def ls.has_store_named(+n: String, xs: List<&2, Sg.Seen>, +all: List<&2, Sg.Seen>, h: {Listing.sp_has_store(n, Listing.sp_scan.go(xs, all)) == True{} : Bool}) -> {LawsBase.text_has_name(n, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      LStg.stg.absurdF({LawsBase.text_has_name(n, Nil{}) == True{} : Bool}, h)
    case +x <> +r:
      ls.hsn.at(n, x, r, all, Listing.sp_is_store(n, Listing.sp_pick(x, all)), {==}, h, h2 => ls.has_store_named(n, r, all, h2))

def ls.leg(+n: String, base: Bool, hn: Bool, +st: String, +all: List<&2, Sg.Seen>, ehn: {LawsBase.text_has_name(st, all) == hn : Bool},
  h: {Listing.sp_is_legacy(n, Listing.sp_legacy(Bool.or(base, hn), st)) == True{} : Bool}) -> {LawsBase.text_has_name(n, all) == False{} : Bool}:
  match base:
    case True{}:
      LStg.stg.absurdF({LawsBase.text_has_name(n, all) == False{} : Bool}, h)
    case False{}:
      match hn:
        case True{}:
          LStg.stg.absurdF({LawsBase.text_has_name(n, all) == False{} : Bool}, h)
        case False{}:
          %LStg.stg.same_eq(st, n, h) : {LawsBase.text_has_name(_, all) == False{} : Bool}
          ehn

def ls.legacy_stem(+n: String, m: Maybe<&2, String>, +all: List<&2, Sg.Seen>, h: {Listing.sp_is_legacy(n, Listing.sp_stem(m, all)) == True{} : Bool}) -> {LawsBase.text_has_name(n, all) == False{} : Bool}:
  match m:
    case None{}:
      LStg.stg.absurdF({LawsBase.text_has_name(n, all) == False{} : Bool}, h)
    case Some{+st}:
      ls.leg(n, Bool.or(String.is_empty(st), Bool.or(LawsBase.text_same(st, "."), LawsBase.text_same(st, ".."))), LawsBase.text_has_name(st, all), st, all, {==}, h)

# an entry picked as a legacy file under n: no entry has the name n
def ls.legacy_free(+n: String, e: Sg.Seen, +all: List<&2, Sg.Seen>, h: {Listing.sp_is_legacy(n, Listing.sp_pick(e, all)) == True{} : Bool}) -> {LawsBase.text_has_name(n, all) == False{} : Bool}:
  match e:
    case Sg.Seen{nm, k}:
      match nm:
        case Sg.Utf{+s}:
          match k:
            case Sg.KDir{main}:
              LStg.stg.absurdF({LawsBase.text_has_name(n, all) == False{} : Bool}, Equal.trans(Bool, False{}, Listing.sp_is_legacy(n, Listing.sp_dir(main, Listing.sp_hidden(s), s)), True{}, Equal.sym(Bool, Listing.sp_is_legacy(n, Listing.sp_dir(main, Listing.sp_hidden(s), s)), False{}, ls.dir_not_legacy(n, main, Listing.sp_hidden(s), s)), h))
            case Sg.KFile{}:
              ls.legacy_stem(n, LawsBase.text_unsuffix(".jsonl", s), all, h)
            case Sg.KOther{}:
              LStg.stg.absurdF({LawsBase.text_has_name(n, all) == False{} : Bool}, h)
        case Sg.Raw{}:
          LStg.stg.absurdF({LawsBase.text_has_name(n, all) == False{} : Bool}, h)

def ls.hlf.at(+n: String, x: Sg.Seen, -r: List<&2, Sg.Seen>, +all: List<&2, Sg.Seen>, b: Bool, eb: {Listing.sp_is_legacy(n, Listing.sp_pick(x, all)) == b : Bool},
  h: {Bool.or(b, Listing.sp_has_legacy(n, Listing.sp_scan.go(r, all))) == True{} : Bool},
  ih: {Listing.sp_has_legacy(n, Listing.sp_scan.go(r, all)) == True{} : Bool} -> {LawsBase.text_has_name(n, all) == False{} : Bool}) -> {LawsBase.text_has_name(n, all) == False{} : Bool}:
  match b:
    case True{}:
      ls.legacy_free(n, x, all, eb)
    case False{}:
      ih(h)

# a name listed as a legacy file is the name of no entry
def ls.has_legacy_free(+n: String, xs: List<&2, Sg.Seen>, +all: List<&2, Sg.Seen>, h: {Listing.sp_has_legacy(n, Listing.sp_scan.go(xs, all)) == True{} : Bool}) -> {LawsBase.text_has_name(n, all) == False{} : Bool}:
  match xs:
    case Nil{}:
      LStg.stg.absurdF({LawsBase.text_has_name(n, all) == False{} : Bool}, h)
    case +x <> +r:
      ls.hlf.at(n, x, r, all, Listing.sp_is_legacy(n, Listing.sp_pick(x, all)), {==}, h, h2 => ls.has_legacy_free(n, r, all, h2))

# ---- an import ----

def ls.or_assoc(a: Bool, +b: Bool, +c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def ls.has_name_app(+s: String, xs: List<&2, Sg.Seen>, +ys: List<&2, Sg.Seen>) -> {LawsBase.text_has_name(s, List.append(&2, Sg.Seen, xs, ys)) == Bool.or(LawsBase.text_has_name(s, xs), LawsBase.text_has_name(s, ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> +r:
      match x:
        case Sg.Seen{+nm, k}:
          %Equal.sym(Bool, LawsBase.text_has_name(s, List.append(&2, Sg.Seen, r, ys)), Bool.or(LawsBase.text_has_name(s, r), LawsBase.text_has_name(s, ys)), ls.has_name_app(s, r, ys)) : {Bool.or(LawsBase.text_named(s, nm), _) == Bool.or(Bool.or(LawsBase.text_named(s, nm), LawsBase.text_has_name(s, r)), LawsBase.text_has_name(s, ys)) : Bool}
          ls.or_assoc(LawsBase.text_named(s, nm), LawsBase.text_has_name(s, r), LawsBase.text_has_name(s, ys))

def ls.store_app(+n: String, xs: List<&2, Sg.Seen>, +ys: List<&2, Sg.Seen>, +all: List<&2, Sg.Seen>) -> {Listing.sp_has_store(n, Listing.sp_scan.go(List.append(&2, Sg.Seen, xs, ys), all)) == Bool.or(Listing.sp_has_store(n, Listing.sp_scan.go(xs, all)), Listing.sp_has_store(n, Listing.sp_scan.go(ys, all))) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      +a = Listing.sp_is_store(n, Listing.sp_pick(x, all))
      %Equal.sym(Bool, Listing.sp_has_store(n, Listing.sp_scan.go(List.append(&2, Sg.Seen, r, ys), all)), Bool.or(Listing.sp_has_store(n, Listing.sp_scan.go(r, all)), Listing.sp_has_store(n, Listing.sp_scan.go(ys, all))), ls.store_app(n, r, ys, all)) : {Bool.or(a, _) == Bool.or(Bool.or(a, Listing.sp_has_store(n, Listing.sp_scan.go(r, all))), Listing.sp_has_store(n, Listing.sp_scan.go(ys, all))) : Bool}
      ls.or_assoc(a, Listing.sp_has_store(n, Listing.sp_scan.go(r, all)), Listing.sp_has_store(n, Listing.sp_scan.go(ys, all)))

def ls.legacy_app(+n: String, xs: List<&2, Sg.Seen>, +ys: List<&2, Sg.Seen>, +all: List<&2, Sg.Seen>) -> {Listing.sp_has_legacy(n, Listing.sp_scan.go(List.append(&2, Sg.Seen, xs, ys), all)) == Bool.or(Listing.sp_has_legacy(n, Listing.sp_scan.go(xs, all)), Listing.sp_has_legacy(n, Listing.sp_scan.go(ys, all))) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      +a = Listing.sp_is_legacy(n, Listing.sp_pick(x, all))
      %Equal.sym(Bool, Listing.sp_has_legacy(n, Listing.sp_scan.go(List.append(&2, Sg.Seen, r, ys), all)), Bool.or(Listing.sp_has_legacy(n, Listing.sp_scan.go(r, all)), Listing.sp_has_legacy(n, Listing.sp_scan.go(ys, all))), ls.legacy_app(n, r, ys, all)) : {Bool.or(a, _) == Bool.or(Bool.or(a, Listing.sp_has_legacy(n, Listing.sp_scan.go(r, all))), Listing.sp_has_legacy(n, Listing.sp_scan.go(ys, all))) : Bool}
      ls.or_assoc(a, Listing.sp_has_legacy(n, Listing.sp_scan.go(r, all)), Listing.sp_has_legacy(n, Listing.sp_scan.go(ys, all)))

def ls.not_store_s(+n: String, hid: Bool, +s: String, ne: {LawsBase.text_same(s, n) == False{} : Bool}) -> {Listing.sp_is_store(n, Listing.sp_dir(True{}, hid, s)) == False{} : Bool}:
  match hid:
    case True{}:
      {==}
    case False{}:
      ne

def ls.leg_false(+n: String, g: Bool, +st: String, ne: {LawsBase.text_same(st, n) == False{} : Bool}) -> {Listing.sp_is_legacy(n, Listing.sp_legacy(g, st)) == False{} : Bool}:
  match g:
    case True{}:
      {==}
    case False{}:
      ne

# an entry's storage pick does not depend on the listing
def ls.ks_one(+n: String, x: Sg.Seen, +es: List<&2, Sg.Seen>, +all: List<&2, Sg.Seen>) -> {Listing.sp_is_store(n, Listing.sp_pick(x, all)) == Listing.sp_is_store(n, Listing.sp_pick(x, es)) : Bool}:
  match x:
    case Sg.Seen{nm, k}:
      match nm:
        case Sg.Utf{+s}:
          match k:
            case Sg.KDir{main}:
              {==}
            case Sg.KFile{}:
              +m = LawsBase.text_unsuffix(".jsonl", s)
              Equal.trans(Bool, Listing.sp_is_store(n, Listing.sp_stem(m, all)), False{}, Listing.sp_is_store(n, Listing.sp_stem(m, es)),
                ls.stem_not_store(n, m, all), Equal.sym(Bool, Listing.sp_is_store(n, Listing.sp_stem(m, es)), False{}, ls.stem_not_store(n, m, es)))
            case Sg.KOther{}:
              {==}
        case Sg.Raw{}:
          {==}

def ls.ks_go(+n: String, xs: List<&2, Sg.Seen>, +es: List<&2, Sg.Seen>, +all: List<&2, Sg.Seen>) -> {Listing.sp_has_store(n, Listing.sp_scan.go(xs, all)) == Listing.sp_has_store(n, Listing.sp_scan.go(xs, es)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      %ls.ks_one(n, x, es, all) : {Bool.or(Listing.sp_is_store(n, Listing.sp_pick(x, all)), Listing.sp_has_store(n, Listing.sp_scan.go(r, all))) == Bool.or(_, Listing.sp_has_store(n, Listing.sp_scan.go(r, es))) : Bool}
      %ls.ks_go(n, r, es, all) : {Bool.or(Listing.sp_is_store(n, Listing.sp_pick(x, all)), Listing.sp_has_store(n, Listing.sp_scan.go(r, all))) == Bool.or(Listing.sp_is_store(n, Listing.sp_pick(x, all)), _) : Bool}
      {==}

def ls.kl_at(+n: String, +base: Bool, +hn: Bool, c: Bool, +st: String, +s: String, ec: {LawsBase.text_same(s, st) == c : Bool}, ne: {LawsBase.text_same(s, n) == False{} : Bool})
  -> {Listing.sp_is_legacy(n, Listing.sp_legacy(Bool.or(base, Bool.or(hn, Bool.or(c, False{}))), st)) == Listing.sp_is_legacy(n, Listing.sp_legacy(Bool.or(base, hn), st)) : Bool}:
  match c:
    case False{}:
      %Equal.sym(Bool, Bool.or(hn, False{}), hn, LStg.stg.or_false(hn)) : {Listing.sp_is_legacy(n, Listing.sp_legacy(Bool.or(base, _), st)) == Listing.sp_is_legacy(n, Listing.sp_legacy(Bool.or(base, hn), st)) : Bool}
      {==}
    case True{}:
      %Equal.sym(Bool, Bool.or(hn, True{}), True{}, ls.or_true(hn)) : {Listing.sp_is_legacy(n, Listing.sp_legacy(Bool.or(base, _), st)) == Listing.sp_is_legacy(n, Listing.sp_legacy(Bool.or(base, hn), st)) : Bool}
      %Equal.sym(Bool, Bool.or(base, True{}), True{}, ls.or_true(base)) : {Listing.sp_is_legacy(n, Listing.sp_legacy(_, st)) == Listing.sp_is_legacy(n, Listing.sp_legacy(Bool.or(base, hn), st)) : Bool}
      %LStg.stg.same_eq(s, st, ec) : {False{} == Listing.sp_is_legacy(n, Listing.sp_legacy(Bool.or(base, hn), _)) : Bool}
      Equal.sym(Bool, Listing.sp_is_legacy(n, Listing.sp_legacy(Bool.or(base, hn), s)), False{}, ls.leg_false(n, Bool.or(base, hn), s, ne))

def ls.kl_stem(+n: String, m: Maybe<&2, String>, +es: List<&2, Sg.Seen>, +s: String, +ne: {LawsBase.text_same(s, n) == False{} : Bool})
  -> {Listing.sp_is_legacy(n, Listing.sp_stem(m, List.append(&2, Sg.Seen, es, [Sg.Seen{Sg.Utf{s}, Sg.KDir{True{}}}]))) == Listing.sp_is_legacy(n, Listing.sp_stem(m, es)) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+st}:
      +d = {[Sg.Seen{Sg.Utf{s}, Sg.KDir{True{}}}] : List<&2, Sg.Seen>}
      +base = Bool.or(String.is_empty(st), Bool.or(LawsBase.text_same(st, "."), LawsBase.text_same(st, "..")))
      %Equal.sym(Bool, LawsBase.text_has_name(st, List.append(&2, Sg.Seen, es, d)), Bool.or(LawsBase.text_has_name(st, es), LawsBase.text_has_name(st, d)), ls.has_name_app(st, es, d)) : {Listing.sp_is_legacy(n, Listing.sp_legacy(Bool.or(base, _), st)) == Listing.sp_is_legacy(n, Listing.sp_legacy(Bool.or(base, LawsBase.text_has_name(st, es)), st)) : Bool}
      ls.kl_at(n, base, LawsBase.text_has_name(st, es), LawsBase.text_same(s, st), st, s, {==}, ne)

def ls.kl_one(+n: String, x: Sg.Seen, +es: List<&2, Sg.Seen>, +s: String, +ne: {LawsBase.text_same(s, n) == False{} : Bool})
  -> {Listing.sp_is_legacy(n, Listing.sp_pick(x, List.append(&2, Sg.Seen, es, [Sg.Seen{Sg.Utf{s}, Sg.KDir{True{}}}]))) == Listing.sp_is_legacy(n, Listing.sp_pick(x, es)) : Bool}:
  match x:
    case Sg.Seen{nm, k}:
      match nm:
        case Sg.Utf{+t}:
          match k:
            case Sg.KDir{main}:
              {==}
            case Sg.KFile{}:
              ls.kl_stem(n, LawsBase.text_unsuffix(".jsonl", t), es, s, ne)
            case Sg.KOther{}:
              {==}
        case Sg.Raw{}:
          {==}

def ls.kl_go(+n: String, xs: List<&2, Sg.Seen>, +es: List<&2, Sg.Seen>, +s: String, +ne: {LawsBase.text_same(s, n) == False{} : Bool})
  -> {Listing.sp_has_legacy(n, Listing.sp_scan.go(xs, List.append(&2, Sg.Seen, es, [Sg.Seen{Sg.Utf{s}, Sg.KDir{True{}}}]))) == Listing.sp_has_legacy(n, Listing.sp_scan.go(xs, es)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      +all = List.append(&2, Sg.Seen, es, [Sg.Seen{Sg.Utf{s}, Sg.KDir{True{}}}])
      %ls.kl_one(n, x, es, s, ne) : {Bool.or(Listing.sp_is_legacy(n, Listing.sp_pick(x, all)), Listing.sp_has_legacy(n, Listing.sp_scan.go(r, all))) == Bool.or(_, Listing.sp_has_legacy(n, Listing.sp_scan.go(r, es))) : Bool}
      %ls.kl_go(n, r, es, s, ne) : {Bool.or(Listing.sp_is_legacy(n, Listing.sp_pick(x, all)), Listing.sp_has_legacy(n, Listing.sp_scan.go(r, all))) == Bool.or(Listing.sp_is_legacy(n, Listing.sp_pick(x, all)), _) : Bool}
      {==}
