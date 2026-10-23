# eukhe: the proof of LAW restart_decide_window

import Base
import ../../bend/supervise.bend as Su
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.restart_decide_window(c, s, g):
  match s:
    case Su.St{a, n}:
      %LA.ps.rs_window(Su.Cfg.w(c), g, a) : {Su.St{0n <> Su.keep(Su.Cfg.w(c), Su.older(g, a)), 1n+List.length(&2, Nat, Su.keep(Su.Cfg.w(c), Su.older(g, a)))} == Su.St{0n <> _, 1n+List.length(&2, Nat, _)} : Su.St}
      {==}
