# eukhe: the proof of LAW tree_commit_ffi_reads

import Base
import ../../bend/tree_commit.bend as Tc
import ../../bend/ffi_tree_commit.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/tree_commit.bend as TreeCommit
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/wire.bend as LWire
import ./base.bend as LATreeCommit
import ./base/entry.bend as LATcEntry

# PROOF of LAW tree_commit_ffi_reads: the count reads back (wire_nat_round_trip, it fits), then each change in turn (tce.go_rt); rest is never read.

def tcf.cons(+x: Tc.Ch, +t: List<&2, Tc.Ch>, +r: String, +h: {TreeCommit.req_fits(x <> t) == True{} : Bool}) -> {FTc.get_req(TreeCommit.spell_req(x <> t, r)) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Tc.Ch>>}:
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Tc.Ch, x <> t), TreeCommit.spell_chs(x <> t, r))), Wr.Got{List.length(&2, Tc.Ch, x <> t), TreeCommit.spell_chs(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, Tc.Ch, x <> t), TreeCommit.spell_chs(x <> t, r), LATcEntry.tce.and_l(LawsBase.wire_fits(List.length(&2, Tc.Ch, x <> t)), TreeCommit.chs_fit(x <> t), h))) : {Wr.get_list.start(~Tc.Ch, ~FTc.get_ch, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, Tc.Ch>>}
  LATcEntry.tce.go_rt(t, x, r, LATcEntry.tce.and_r(LawsBase.wire_fits(List.length(&2, Tc.Ch, x <> t)), TreeCommit.chs_fit(x <> t), h))

def TreeCommit.tree_commit_ffi_reads(cs, rest, h):
  match cs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, {==})) : {Wr.get_list.start(~Tc.Ch, ~FTc.get_ch, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Tc.Ch>>}
      {==}
    case Con{+x, +t}:
      tcf.cons(x, t, rest, h)
