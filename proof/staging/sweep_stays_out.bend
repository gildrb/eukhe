# eukhe: the proof of LAW sweep_stays_out

import Base
import ../../bend/staging.bend as Sg
import ../../laws/staging.bend as Staging
import ./base.bend as LA

def pg.sweep_stays_out(+pre: List<&2, Sg.Node>, +i: Nat, +k: Sg.Sort, +h: Bool, +s: Bool, +post: List<&2, Sg.Node>) -> {Sg.sweep(List.append(&2, Sg.Node, pre, Sg.Node{i, k, h, s, False{}} <> post)) == List.append(&2, Sg.Node, Sg.sweep(pre), Sg.sweep(post)) : List<&2, Sg.Node>}:
  LA.pg.kept(pre, Sg.Node{i, k, h, s, False{}}, post, {==})

def Staging.sweep_stays_out(pre, i, k, h, s, post):
  pg.sweep_stays_out(pre, i, k, h, s, post)
