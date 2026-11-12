# eukhe: the proof of LAW scan_verdict_at_entry
#
# PROOF: the code's scan answers each entry in place (vn.nth: the verdict
# at the length of pre is the code's pick of e against the whole listing),
# the code's pick is the spec's verdict (ls.pick), and an entry's verdict
# lists n as a storage, resp. a legacy file, exactly as R5 says
# (lsv.store1, lsv.legacy1).

import Base
import ../../bend/staging.bend as Sg
import ../../bend/listing.bend as Ls
import ../../laws/listing.bend as Listing
import ./base/scan.bend as LA
import ./base/verdict.bend as LV

# the verdict at the place of e is the code's pick of e
def vn.nth(pre: List<&2, Sg.Seen>, +e: Sg.Seen, +post: List<&2, Sg.Seen>, +all: List<&2, Sg.Seen>) -> {Listing.sp_nth(Ls.scan.go(List.append(&2, Sg.Seen, pre, e <> post), all), List.length(&2, Sg.Seen, pre)) == Some{Ls.pick(e, all)} : Maybe<&2, Ls.Pick>}:
  match pre:
    case Nil{}:
      {==}
    case x <> t:
      vn.nth(t, e, post, all)

def Listing.scan_verdict_at_entry(pre, e, post, n):
  +es = List.append(&2, Sg.Seen, pre, e <> post)
  +at = Listing.sp_nth(Ls.scan.go(es, es), List.length(&2, Sg.Seen, pre))
  r = {(Listing.sp_store_entry(n, e), Bool.and(Listing.sp_file_entry(n, e), Listing.sp_legacy_free(n, es))) : Bool & Bool}
  %Equal.sym(Maybe<&2, Ls.Pick>, at, Some{Ls.pick(e, es)}, vn.nth(pre, e, post, es)) : {(Listing.sp_is_store.at(n, _), Listing.sp_is_legacy.at(n, at)) == r : Bool & Bool}
  %Equal.sym(Maybe<&2, Ls.Pick>, at, Some{Ls.pick(e, es)}, vn.nth(pre, e, post, es)) : {(Listing.sp_is_store(n, Ls.pick(e, es)), Listing.sp_is_legacy.at(n, _)) == r : Bool & Bool}
  %Equal.sym(Ls.Pick, Ls.pick(e, es), Listing.sp_pick(e, es), LA.ls.pick(e, es)) : {(Listing.sp_is_store(n, _), Listing.sp_is_legacy(n, Ls.pick(e, es))) == r : Bool & Bool}
  %Equal.sym(Ls.Pick, Ls.pick(e, es), Listing.sp_pick(e, es), LA.ls.pick(e, es)) : {(Listing.sp_is_store(n, Listing.sp_pick(e, es)), Listing.sp_is_legacy(n, _)) == r : Bool & Bool}
  %Equal.sym(Bool, Listing.sp_is_store(n, Listing.sp_pick(e, es)), Listing.sp_store_entry(n, e), LV.lsv.store1(n, e, es)) : {(_, Listing.sp_is_legacy(n, Listing.sp_pick(e, es))) == r : Bool & Bool}
  %Equal.sym(Bool, Listing.sp_is_legacy(n, Listing.sp_pick(e, es)), Bool.and(Listing.sp_file_entry(n, e), Listing.sp_legacy_free(n, es)), LV.lsv.legacy1(n, e, es)) : {(Listing.sp_store_entry(n, e), _) == r : Bool & Bool}
  {==}
