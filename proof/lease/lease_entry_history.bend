# eukhe: the proof of LAW lease_entry_history
# By induction on the events: each spelled event steps the entry as the
# model with the laws' reply (LA.le.answers), so the state stays the
# model's lease after the events before it.

import Base
import ../../bend/lease.bend as Ls
import ../../bend/ffi_lease.bend as FLs
import ../../laws/lease.bend as Lease
import ./base.bend as LA

def lh.go(evs: List<&2, Ls.Ev>, +s: Ls.L, +out: String, +hf: {Lease.lw_all_fit(evs) == True{} : Bool}) -> {Lease.lw_run(evs, (FLs.Live{s}, out)) == (out <> Lease.lw_replies(evs, s), FLs.Live{Ls.go(evs, s)}) : List<&2, String> & FLs.St}:
  match evs:
    case Nil{}:
      {==}
    case +e <> +t:
      +he = LA.le.and_l(Lease.lw_fits(e), Lease.lw_all_fit(t), hf)
      +ht = LA.le.and_r(Lease.lw_fits(e), Lease.lw_all_fit(t), hf)
      +s2 = Ls.step(s, e)
      +r = Lease.lw_reply(s, e)
      %Equal.sym(FLs.St & String, FLs.step(FLs.Live{s}, Lease.lw_spell_ev(e)), (FLs.Live{s2}, r), LA.le.answers(s, e, he)) : {Lease.lw_cons(out, Lease.lw_run(t, _)) == (out <> (r <> Lease.lw_replies(t, s2)), FLs.Live{Ls.go(t, s2)}) : List<&2, String> & FLs.St}
      %Equal.sym(List<&2, String> & FLs.St, Lease.lw_run(t, (FLs.Live{s2}, r)), (r <> Lease.lw_replies(t, s2), FLs.Live{Ls.go(t, s2)}), lh.go(t, s2, r, ht)) : {Lease.lw_cons(out, _) == (out <> (r <> Lease.lw_replies(t, s2)), FLs.Live{Ls.go(t, s2)}) : List<&2, String> & FLs.St}
      {==}

def Lease.lease_entry_history(evs, fits):
  lh.go(evs, Ls.L.empty(), "", fits)
