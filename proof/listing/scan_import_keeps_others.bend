# eukhe: the proof of LAW scan_import_keeps_others

import Base
import ../../bend/staging.bend as Sg
import ../../bend/listing.bend as Ls
import ../../laws/listing.bend as Listing
import ../../laws/base.bend as LawsBase
import ../base/staging.bend as LStg
import ./base/scan.bend as LA
import ./scan_exact.bend as PScanExact

def Listing.scan_import_keeps_others(es, s, n, ne0):
  +ne = ne0
  +d = {[Sg.Seen{Sg.Utf{s}, Sg.KDir{True{}}}] : List<&2, Sg.Seen>}
  +all = List.append(&2, Sg.Seen, es, d)
  +hs = Listing.sp_has_store(n, Listing.sp_scan.go(es, all))
  +hl = Listing.sp_has_legacy(n, Listing.sp_scan.go(es, all))
  +rs = Listing.sp_lists(n, Listing.sp_scan(es))
  %Equal.sym(List<&2, Ls.Pick>, Ls.scan(all), Listing.sp_scan(all), Listing.scan_exact(all)) : {Listing.sp_lists(n, _) == Listing.sp_lists(n, Ls.scan(es)) : Bool}
  %Equal.sym(List<&2, Ls.Pick>, Ls.scan(es), Listing.sp_scan(es), Listing.scan_exact(es)) : {Listing.sp_lists(n, Listing.sp_scan(all)) == Listing.sp_lists(n, _) : Bool}
  %Equal.sym(Bool, Listing.sp_has_store(n, Listing.sp_scan.go(all, all)), Bool.or(hs, Listing.sp_has_store(n, Listing.sp_scan.go(d, all))), LA.ls.store_app(n, es, d, all)) : {Bool.or(_, Listing.sp_has_legacy(n, Listing.sp_scan.go(all, all))) == rs : Bool}
  %Equal.sym(Bool, Listing.sp_has_legacy(n, Listing.sp_scan.go(all, all)), Bool.or(hl, Listing.sp_has_legacy(n, Listing.sp_scan.go(d, all))), LA.ls.legacy_app(n, es, d, all)) : {Bool.or(Bool.or(hs, Listing.sp_has_store(n, Listing.sp_scan.go(d, all))), _) == rs : Bool}
  %Equal.sym(Bool, Listing.sp_is_store(n, Listing.sp_dir(True{}, Listing.sp_hidden(s), s)), False{}, LA.ls.not_store_s(n, Listing.sp_hidden(s), s, ne)) : {Bool.or(Bool.or(hs, Bool.or(_, False{})), Bool.or(hl, Bool.or(Listing.sp_is_legacy(n, Listing.sp_dir(True{}, Listing.sp_hidden(s), s)), False{}))) == rs : Bool}
  %Equal.sym(Bool, Listing.sp_is_legacy(n, Listing.sp_dir(True{}, Listing.sp_hidden(s), s)), False{}, LA.ls.dir_not_legacy(n, True{}, Listing.sp_hidden(s), s)) : {Bool.or(Bool.or(hs, False{}), Bool.or(hl, Bool.or(_, False{}))) == rs : Bool}
  %Equal.sym(Bool, Bool.or(hs, False{}), hs, LStg.stg.or_false(hs)) : {Bool.or(_, Bool.or(hl, False{})) == rs : Bool}
  %Equal.sym(Bool, Bool.or(hl, False{}), hl, LStg.stg.or_false(hl)) : {Bool.or(hs, _) == rs : Bool}
  %Equal.sym(Bool, hs, Listing.sp_has_store(n, Listing.sp_scan.go(es, es)), LA.ls.ks_go(n, es, es, all)) : {Bool.or(_, hl) == rs : Bool}
  %Equal.sym(Bool, hl, Listing.sp_has_legacy(n, Listing.sp_scan.go(es, es)), LA.ls.kl_go(n, es, es, s, ne)) : {Bool.or(Listing.sp_has_store(n, Listing.sp_scan.go(es, es)), _) == rs : Bool}
  {==}
