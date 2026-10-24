# eukhe: the proof of LAW scan_legacy_named

import Base
import ../../bend/staging.bend as Sg
import ../../bend/listing.bend as Ls
import ../../laws/listing.bend as Listing
import ../../laws/base.bend as LawsBase
import ../base/staging.bend as LStg
import ./base/scan.bend as LA
import ./scan_exact.bend as PScanExact
import ../staging/base.bend as LAStaging

# a stem and its legacy file's name are not the same
def ln.ne(+x: String) -> {LawsBase.text_same(String.append(x, ".jsonl"), x) == False{} : Bool}:
  +el = Equal.trans(Bool, Nat.is_eq(String.length(String.append(x, ".jsonl")), String.length(x)), Nat.is_eq(Nat.add(String.length(x), 6n), String.length(x)), False{},
    Equal.cong(Nat, Bool, z => Nat.is_eq(z, String.length(x)), String.length(String.append(x, ".jsonl")), Nat.add(String.length(x), 6n), LStg.stg.len_app(x, ".jsonl")),
    LAStaging.rr.ne_add(String.length(x), 5n))
  LStg.stg.same_len(String.append(x, ".jsonl"), x, el)

def Listing.scan_legacy_named(st, full, nd):
  +k = String.append(st, ".jsonl")
  +f = {[Sg.Seen{Sg.Utf{k}, Sg.KFile{}}] : List<&2, Sg.Seen>}
  +dots = Bool.or(LawsBase.text_same(st, "."), LawsBase.text_same(st, ".."))
  %Equal.sym(List<&2, Ls.Pick>, Ls.scan(f), Listing.sp_scan(f), Listing.scan_exact(f)) : {_ == [Ls.PLegacy{st}] : List<&2, Ls.Pick>}
  %Equal.sym(Maybe<&2, String>, LawsBase.text_unsuffix(".jsonl", k), Some{st}, LStg.stg.unsuffix_app(st, ".jsonl")) : {[Listing.sp_stem(_, f)] == [Ls.PLegacy{st}] : List<&2, Ls.Pick>}
  %Equal.sym(Bool, String.is_empty(st), False{}, full) : {[Listing.sp_legacy(Bool.or(Bool.or(_, dots), LawsBase.text_has_name(st, f)), st)] == [Ls.PLegacy{st}] : List<&2, Ls.Pick>}
  %Equal.sym(Bool, dots, False{}, nd) : {[Listing.sp_legacy(Bool.or(Bool.or(False{}, _), LawsBase.text_has_name(st, f)), st)] == [Ls.PLegacy{st}] : List<&2, Ls.Pick>}
  %Equal.sym(Bool, LawsBase.text_same(k, st), False{}, ln.ne(st)) : {[Listing.sp_legacy(Bool.or(False{}, Bool.or(_, False{})), st)] == [Ls.PLegacy{st}] : List<&2, Ls.Pick>}
  {==}
