# eukhe: the proof of LAW notice_shown_once

import Base
import ../../bend/notice.bend as No
import ../../laws/notice.bend as Notice
import ./base.bend as LA

# notice_shown_once
# -----------------

# a notice in one of its two states showed at most once
def pn.amo(s: Bool, c: Nat, h: {LA.pn.ok(No.N{s, c}) == True{} : Bool}) -> {Nat.is_le(c, 1n) == True{} : Bool}:
  match s c:
    case True{} 0n:
      {==}
    case True{} 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          LA.notice.pn.absurdF({Nat.is_le(2n+q, 1n) == True{} : Bool}, h)
    case False{} 0n:
      {==}
    case False{} 1n+p:
      LA.notice.pn.absurdF({Nat.is_le(1n+p, 1n) == True{} : Bool}, h)

def pn.once_of_ok(ns: List<&2, No.N>, +h: {LA.pn.all_ok(ns) == True{} : Bool}) -> {Notice.nt_once(Notice.nt_shown(ns)) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case n <> +t:
      match n:
        case No.N{+s, +c}:
          LA.notice.pn.and_t(Nat.is_le(c, 1n), Notice.nt_once(Notice.nt_shown(t)), pn.amo(s, c, LA.notice.pn.and_l(LA.pn.ok(No.N{s, c}), LA.pn.all_ok(t), h)), pn.once_of_ok(t, LA.notice.pn.and_r(LA.pn.ok(No.N{s, c}), LA.pn.all_ok(t), h)))

def pn.notice_shown_once(+evs: List<&2, No.Ev>) -> {Notice.nt_once(Notice.nt_shown(No.run(evs))) == True{} : Bool}:
  pn.once_of_ok(No.run(evs), LA.pn.ok_go(evs, Nil{}, {==}))

def Notice.notice_shown_once(evs):
  pn.notice_shown_once(evs)
