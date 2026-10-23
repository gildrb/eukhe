# optchat: Taelin's rollback push and its agreement with fit

import Base
import ./bits.bend as OBits
import ./node.bend as ONode
import ./info.bend as OInfo
import ./fit.bend as OFit

# Taelin's rollback push
# ----------------------
# rollback_state_list.js (2022), verbatim; the list is newest first, and a
# state is a message id, in binary.

type Entry is Data:
  Entry{keep: Nat, life: Nat, state: List<&2, Bool>}

def push(states: List<&2, Entry>, +s: List<&2, Bool>) -> List<&2, Entry>:
  match states:
    case Nil{}:
      [Entry{0n, 0n, s}]
    case e <> older:
      match e:
        case Entry{keep, life, state}:
          match keep:
            case 0n:
              Entry{1n, life, state} <> older
            case 1n+kp:
              match life:
                case 1n+lp:
                  Entry{0n, 0n, s} <> Entry{0n, lp, state} <> older
                case 0n:
                  Entry{0n, 0n, s} <> push(older, state)

def Bitss.same(as: List<&2, List<&2, Bool>>, bs: List<&2, List<&2, Bool>>) -> Bool:
  match as bs:
    case Nil{} Nil{}:
      True{}
    case Nil{} y <> ys:
      False{}
    case x <> xs Nil{}:
      False{}
    case x <> xs y <> ys:
      Bool.and(OBits.Bits.same(x, y), Bitss.same(xs, ys))

def starts(v: List<&2, ONode.Node>) -> List<&2, List<&2, Bool>>:
  match v:
    case Nil{}:
      Nil{}
    case h <> t:
      OFit.pair_start(h) <> starts(t)

def states(es: List<&2, Entry>) -> List<&2, List<&2, Bool>>:
  match es:
    case Nil{}:
      Nil{}
    case e <> t:
      match e:
        case Entry{k, l, s}:
          s <> states(t)

# the view is push's list, oldest first: each state starts a line
def same_lines(+v: List<&2, ONode.Node>, +es: List<&2, Entry>) -> Bool:
  Bitss.same(starts(v), List.reverse(&2, List<&2, Bool>, states(es)))

# Push t = 0..n-1, one message each; the view appends each message and
# fits push's list length (every line 1 byte, every node built). True when
# the two agree after every push.
def agree.go(n: Nat, +m: OFit.Age, +tb: List<&2, Bool>, +es: List<&2, Entry>, +v: List<&2, ONode.Node>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      +es2 = push(es, tb)
      +tb2 = OBits.Bits.inc(tb)
      +v2 = OFit.fit.view(m, tb2, List.length(&2, Entry, es2), 0n, OInfo.All{1n}, List.append(&2, ONode.Node, v, [ONode.Node.leaf(tb)]))
      Bool.and(same_lines(v2, es2), agree.go(p, m, tb2, es2, v2))

def agree(+m: OFit.Age, n: Nat) -> Bool:
  agree.go(n, m, Nil{}, Nil{}, Nil{})

# how many of the pushes t = 0..n-1 the view agrees with
def agree.count.go(n: Nat, +m: OFit.Age, +tb: List<&2, Bool>, +es: List<&2, Entry>, +v: List<&2, ONode.Node>) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      +es2 = push(es, tb)
      +tb2 = OBits.Bits.inc(tb)
      +v2 = OFit.fit.view(m, tb2, List.length(&2, Entry, es2), 0n, OInfo.All{1n}, List.append(&2, ONode.Node, v, [ONode.Node.leaf(tb)]))
      Nat.add(OBits.bit(same_lines(v2, es2), 0n), agree.count.go(p, m, tb2, es2, v2))

def agree.count(+m: OFit.Age, n: Nat) -> Nat:
  agree.count.go(n, m, Nil{}, Nil{}, Nil{})
