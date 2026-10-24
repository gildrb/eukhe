# eukhe: the proof of LAW scan_import_lists_storage

import Base
import ../../bend/staging.bend as Sg
import ../../bend/listing.bend as Ls
import ../../laws/listing.bend as Listing
import ../../laws/base.bend as LawsBase
import ../base/staging.bend as LStg
import ./base/scan.bend as LA
import ./scan_exact.bend as PScanExact

def Listing.scan_import_lists_storage(es, s, shown):
  +d = {[Sg.Seen{Sg.Utf{s}, Sg.KDir{True{}}}] : List<&2, Sg.Seen>}
  +all = List.append(&2, Sg.Seen, es, d)
  +x = Listing.sp_has_store(s, Listing.sp_scan.go(es, all))
  %Equal.sym(List<&2, Ls.Pick>, Ls.scan(all), Listing.sp_scan(all), Listing.scan_exact(all)) : {Listing.sp_has_store(s, _) == True{} : Bool}
  %Equal.sym(Bool, Listing.sp_has_store(s, Listing.sp_scan.go(all, all)), Bool.or(x, Listing.sp_has_store(s, Listing.sp_scan.go(d, all))), LA.ls.store_app(s, es, d, all)) : {_ == True{} : Bool}
  %Equal.sym(Bool, Listing.sp_hidden(s), False{}, shown) : {Bool.or(x, Bool.or(Listing.sp_is_store(s, Listing.sp_dir(True{}, _, s)), False{})) == True{} : Bool}
  %Equal.sym(Bool, LawsBase.text_same(s, s), True{}, LStg.stg.same_refl(s)) : {Bool.or(x, Bool.or(_, False{})) == True{} : Bool}
  LA.ls.or_true(x)
