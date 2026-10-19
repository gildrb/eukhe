# log: the model of the commit log of a durable storage, `main.jsonl`
# (crates/eukhe-durable/src/storage/jsonl/storage.rs, `JsonlStorage`),
# under power loss at any point.
#
# A file is a list of bytes; 0n is the newline that ends a line. A data
# byte is 1n+b. A line holds the bytes 1n+b of its content b..; a commit
# is one line. Open reads the complete lines and cuts the torn tail (the
# bytes after the last newline).
#
# One epoch is one open of the storage (with fsync on), its commits, and
# a crash. The file system does each step in order and the crash comes
# after the first p of them:
#
#   open:    flush the parent directory (the storage directory's entry)
#   commit:  append its line, flush the file, flush the storage directory
#            (the first commit of the epoch only: the file's entry), and
#            then acknowledge it
#
# A crash keeps the flushed bytes and the first k bytes not flushed (any
# prefix: a torn tail when k ends inside a line). When `drop` is set, a
# crash also loses each directory entry not flushed: then the file is
# gone unless both entries are durable. After the crash, what is on disk
# is the start of the next epoch.
#
# The bridge (bend/bridge_log.bend, crates/eukhe-durable/src/storage/
# jsonl/bridge.rs) runs the real `JsonlStorage` over a file system that
# crashes the same way, at every crash point, and compares.

import Base

# Bytes and lines
# ---------------

# the bytes of a content: each b is written as 1n+b
def data(l: List<&2, Nat>) -> List<&2, Nat>:
  match l:
    case Nil{}:
      Nil{}
    case b <> rest:
      (1n+b) <> data(rest)

# one line: its data bytes and the newline
def line(l: List<&2, Nat>) -> List<&2, Nat>:
  List.append(&2, Nat, data(l), [0n])

# the bytes of lines
def render(ls: List<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      List.append(&2, Nat, line(l), render(rest))

# A parse: the complete lines, and the tail after the last newline
type P is Data:
  P{lines: List<&2, List<&2, Nat>>, tail: List<&2, Nat>}

def P.ls(p: P) -> List<&2, List<&2, Nat>>:
  match p:
    case P{ls, t}:
      ls

def P.tl(p: P) -> List<&2, Nat>:
  match p:
    case P{ls, t}:
      t

# the data byte 1n+c before a parse: it starts the first line, or the
# tail when no line is complete
def push(c: Nat, ls: List<&2, List<&2, Nat>>, t: List<&2, Nat>) -> P:
  match ls:
    case Nil{}:
      P{Nil{}, c <> t}
    case l <> rest:
      P{(c <> l) <> rest, t}

def byte(b: Nat, p: P) -> P:
  match b:
    case 0n:
      match p:
        case P{ls, t}:
          P{Nil{} <> ls, t}
    case 1n+c:
      match p:
        case P{ls, t}:
          push(c, ls, t)

def parse(f: List<&2, Nat>) -> P:
  match f:
    case Nil{}:
      P{Nil{}, Nil{}}
    case b <> rest:
      byte(b, parse(rest))

# what open reads: the complete lines; the torn tail is cut
def recover(f: List<&2, Nat>) -> List<&2, List<&2, Nat>>:
  P.ls(parse(f))

# The disk
# --------

type Disk is Data:
  Absent{}                      # no file (or no storage directory)
  Present{bytes: List<&2, Nat>}

# the log that an open of the disk reads
def Disk.log(d: Disk) -> List<&2, List<&2, Nat>>:
  match d:
    case Absent{}:
      Nil{}
    case Present{b}:
      recover(b)

# One epoch: the commits it tries, the steps done before the crash, the
# bytes not flushed that the crash keeps, and whether it drops the
# entries not flushed
type Epoch is Data:
  Epoch{cs: List<&2, List<&2, Nat>>, p: Nat, k: Nat, drop: Bool}

def Epoch.cs(e: Epoch) -> List<&2, List<&2, Nat>>:
  match e:
    case Epoch{cs, p, k, drop}:
      cs

# The storage while it runs: the storage directory's entry is durable
# (de), the file's entry is durable (fe), the flushed lines, the line
# appended and not flushed, the acknowledged commits
type St is Data:
  St{de: Bool, fe: Bool, log: List<&2, List<&2, Nat>>, pend: Maybe<&2, List<&2, Nat>>, acked: List<&2, List<&2, Nat>>}

def St.acked(s: St) -> List<&2, List<&2, Nat>>:
  match s:
    case St{de, fe, log, pend, acked}:
      acked

# open: a file that is there has durable entries (the crash before kept
# them); its torn tail is cut
def open(d: Disk) -> St:
  match d:
    case Absent{}:
      St{False{}, False{}, Nil{}, None{}, Nil{}}
    case Present{b}:
      St{True{}, True{}, recover(b), None{}, Nil{}}

def parent(s: St) -> St:
  match s:
    case St{de, fe, log, pend, acked}:
      St{True{}, fe, log, pend, acked}

def append(c: List<&2, Nat>, s: St) -> St:
  match s:
    case St{de, fe, log, pend, acked}:
      St{de, fe, log, Some{c}, acked}

def opt(m: Maybe<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match m:
    case None{}:
      Nil{}
    case Some{l}:
      [l]

def flush(s: St) -> St:
  match s:
    case St{de, fe, log, pend, acked}:
      St{de, fe, List.append(&2, List<&2, Nat>, log, opt(pend)), None{}, acked}

def dir(s: St) -> St:
  match s:
    case St{de, fe, log, pend, acked}:
      St{de, True{}, log, pend, acked}

def ack(c: List<&2, Nat>, s: St) -> St:
  match s:
    case St{de, fe, log, pend, acked}:
      St{de, fe, log, pend, List.append(&2, List<&2, Nat>, acked, [c])}

# the commits after the first, with p steps left: append, flush, ack
def more(cs: List<&2, List<&2, Nat>>, p: Nat, s: St) -> St:
  match cs:
    case Nil{}:
      s
    case +c <> rest:
      match p:
        case 0n:
          s
        case 1n+p1:
          match p1:
            case 0n:
              append(c, s)
            case 1n+p2:
              more(rest, p2, ack(c, flush(append(c, s))))

# the first commit, with q steps left: append, flush, flush the
# directory, ack
def first(cs: List<&2, List<&2, Nat>>, q: Nat, s: St) -> St:
  match cs:
    case Nil{}:
      s
    case +c <> rest:
      match q:
        case 0n:
          s
        case 1n+q1:
          match q1:
            case 0n:
              append(c, s)
            case 1n+q2:
              match q2:
                case 0n:
                  flush(append(c, s))
                case 1n+q3:
                  more(rest, q3, ack(c, dir(flush(append(c, s)))))

# an epoch's run up to the crash, after p steps
def run(d: Disk, cs: List<&2, List<&2, Nat>>, p: Nat) -> St:
  match p:
    case 0n:
      open(d)
    case 1n+q:
      first(cs, q, parent(open(d)))

# the bytes not flushed that a crash keeps
def cut(k: Nat, m: Maybe<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match m:
    case None{}:
      Nil{}
    case Some{l}:
      List.take(&2, Nat, line(l), k)

# whether the file outlives the crash
def keeps(drop: Bool, de: Bool, fe: Bool) -> Bool:
  match drop:
    case False{}:
      True{}
    case True{}:
      Bool.and(de, fe)

def stays(b: Bool, bytes: List<&2, Nat>) -> Disk:
  match b:
    case True{}:
      Present{bytes}
    case False{}:
      Absent{}

def crash(k: Nat, drop: Bool, s: St) -> Disk:
  match s:
    case St{de, fe, log, pend, acked}:
      stays(keeps(drop, de, fe), List.append(&2, Nat, render(log), cut(k, pend)))

# the disk after an epoch
def after(d: Disk, e: Epoch) -> Disk:
  match e:
    case Epoch{cs, p, k, drop}:
      crash(k, drop, run(d, cs, p))

# the commits an epoch acknowledged
def acked(d: Disk, e: Epoch) -> List<&2, List<&2, Nat>>:
  match e:
    case Epoch{cs, p, k, drop}:
      St.acked(run(d, cs, p))
