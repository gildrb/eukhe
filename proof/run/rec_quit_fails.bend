# eukhe: the proof of LAW rec_quit_fails

import Base
import ../../bend/run.bend as Rn
import ../../LAWS.bend as Laws

def quit_fails(+cfg: Rn.Cfg, -pass: Rn.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> {Rn.call(cfg, Rn.Act.reply(Rn.Quit{}, pass), r, c, a, n, p) == Rn.St{Rn.Failed{Rn.Model{}}, r, c, a, n, p} : Rn.St}:
  {==}

def Laws.rec_quit_fails(cfg, pass, r, c, a, n, p):
  quit_fails(cfg, pass, r, c, a, n, p)
