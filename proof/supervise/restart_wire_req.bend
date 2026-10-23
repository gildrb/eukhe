# eukhe: the proof of LAW restart_wire_req

import Base
import ../../bend/supervise.bend as Su
import ../../bend/wire.bend as Wr
import ../../bend/ffi_supervise.bend as FS
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

def ps.ffi_cfg(+k: Nat, hk: {Laws.wire_fits(k) == True{} : Bool}, +w: Nat, hw: {Laws.wire_fits(w) == True{} : Bool}, +b: Nat, hb: {Laws.wire_fits(b) == True{} : Bool}, +m: Nat, hm: {Laws.wire_fits(m) == True{} : Bool}, +r: String) -> {Wr.Got{Su.Cfg{k, w, b, m}, r} == FS.get_cfg(FS.put_cfg(Su.Cfg{k, w, b, m}, r)) : Wr.Dec<Su.Cfg>}:
  %L.ps.ffi_nat(k, Wr.put_nat(w, Wr.put_nat(b, Wr.put_nat(m, r))), hk) : {Wr.Got{Su.Cfg{k, w, b, m}, r} == FS.get_cfg.k(_) : Wr.Dec<Su.Cfg>}
  %L.ps.ffi_nat(w, Wr.put_nat(b, Wr.put_nat(m, r)), hw) : {Wr.Got{Su.Cfg{k, w, b, m}, r} == FS.get_cfg.w(k, _) : Wr.Dec<Su.Cfg>}
  %L.ps.ffi_nat(b, Wr.put_nat(m, r), hb) : {Wr.Got{Su.Cfg{k, w, b, m}, r} == FS.get_cfg.b(k, w, _) : Wr.Dec<Su.Cfg>}
  %L.ps.ffi_nat(m, r, hm) : {Wr.Got{Su.Cfg{k, w, b, m}, r} == FS.get_cfg.m(k, w, b, _) : Wr.Dec<Su.Cfg>}
  {==}

def Laws.restart_wire_req(k, hk, w, hw, b, hb, m, hm, ages, hs, g, hg, rest):
  +r = rest
  %ps.ffi_cfg(k, hk, w, hw, b, hb, m, hm, FS.put_ages(ages, Wr.put_nat(g, r))) : {FS.get_req.cfg(_) == Wr.Got{FS.Req{Su.Cfg{k, w, b, m}, ages, g}, r} : Wr.Dec<FS.Req>}
  %LA.ps.ffi_list(ages, Wr.put_nat(g, r), hs) : {FS.get_req.ages(Su.Cfg{k, w, b, m}, _) == Wr.Got{FS.Req{Su.Cfg{k, w, b, m}, ages, g}, r} : Wr.Dec<FS.Req>}
  %L.ps.ffi_nat(g, r, hg) : {FS.get_req.gap(Su.Cfg{k, w, b, m}, ages, _) == Wr.Got{FS.Req{Su.Cfg{k, w, b, m}, ages, g}, r} : Wr.Dec<FS.Req>}
  {==}
