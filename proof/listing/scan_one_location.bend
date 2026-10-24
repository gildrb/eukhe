# eukhe: the proof of LAW scan_one_location

import Base
import ../../bend/staging.bend as Sg
import ../../bend/listing.bend as Ls
import ../../laws/listing.bend as Listing
import ../../laws/base.bend as LawsBase
import ../base/staging.bend as LStg
import ./base/scan.bend as LA
import ./scan_exact.bend as PScanExact

# a name listed as a storage has an entry; one listed as a legacy file has
# none: not both
def ol.go(+n: String, +es: List<&2, Sg.Seen>, a: Bool, ea: {Listing.sp_has_store(n, Listing.sp_scan.go(es, es)) == a : Bool},
  b: Bool, eb: {Listing.sp_has_legacy(n, Listing.sp_scan.go(es, es)) == b : Bool}) -> {Bool.and(a, b) == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      match b:
        case False{}:
          {==}
        case True{}:
          LStg.stg.absurd({Bool.and(True{}, True{}) == False{} : Bool}, Equal.trans(Bool, True{}, LawsBase.text_has_name(n, es), False{},
            Equal.sym(Bool, LawsBase.text_has_name(n, es), True{}, LA.ls.has_store_named(n, es, es, ea)), LA.ls.has_legacy_free(n, es, es, eb)))

def Listing.scan_one_location(es, n):
  %Equal.sym(List<&2, Ls.Pick>, Ls.scan(es), Listing.sp_scan(es), Listing.scan_exact(es)) : {Bool.and(Listing.sp_has_store(n, _), Listing.sp_has_legacy(n, _)) == False{} : Bool}
  ol.go(n, es, Listing.sp_has_store(n, Listing.sp_scan.go(es, es)), {==}, Listing.sp_has_legacy(n, Listing.sp_scan.go(es, es)), {==})
