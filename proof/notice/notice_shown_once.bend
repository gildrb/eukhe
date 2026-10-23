# eukhe: the proof of LAW notice_shown_once

import Base
import ../../bend/notice.bend as No
import ../../LAWS.bend as Laws
import ./base.bend as LA

# notice_shown_once
# -----------------

def pn.amo(s: Bool, c: Nat, h: {LA.pn.ok(No.N{s, c}) == True{} : Bool}) -> {No.at_most_one(c) == True{} : Bool}:
  match s c:
    case True{} 0n:
      {==}
    case True{} 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          LA.notice.pn.absurdF({No.at_most_one(2n+q) == True{} : Bool}, h)
    case False{} 0n:
      {==}
    case False{} 1n+p:
      LA.notice.pn.absurdF({No.at_most_one(1n+p) == True{} : Bool}, h)

def pn.once_of_ok(ns: List<&2, No.N>, +h: {LA.pn.all_ok(ns) == True{} : Bool}) -> {No.once(ns) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case n <> +t:
      match n:
        case No.N{+s, +c}:
          LA.notice.pn.and_t(No.at_most_one(c), No.once(t), pn.amo(s, c, LA.notice.pn.and_l(LA.pn.ok(No.N{s, c}), LA.pn.all_ok(t), h)), pn.once_of_ok(t, LA.notice.pn.and_r(LA.pn.ok(No.N{s, c}), LA.pn.all_ok(t), h)))

def pn.notice_shown_once(+evs: List<&2, No.Ev>) -> {No.once(No.run(evs)) == True{} : Bool}:
  pn.once_of_ok(No.run(evs), LA.pn.ok_go(evs, Nil{}, {==}))

def Laws.notice_shown_once(evs):
  pn.notice_shown_once(evs)
