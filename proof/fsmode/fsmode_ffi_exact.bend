# eukhe: the proof of LAW fsmode_ffi_exact
# The entry reads every input as the laws' reader does (LAFs.fs.ask); a
# whole request gets the entry's answer, which is the laws' on every
# request (ffe.answer: the decisions by LAFs.fs.dir_reply, LAFs.fs.cwd_named
# and the peer's Bool; the rest compute); anything else gets the error
# form.

import Base
import ../../bend/ffi_fsmode.bend as FFs
import ../../bend/fsmode.bend as Fs
import ../../bend/wire.bend as Wr
import ../../laws/fsmode.bend as Fsmode
import ./base.bend as LAFs

def ffe.dir(k: Fs.Node, +u: Nat, +o: Nat, +m: Nat) -> {FFs.answer(Fs.AskDir{k, u, o, m}) == Fsmode.dir_reply(k, u, o, m) : String}:
  match k:
    case Fs.Missing{}:
      {==}
    case Fs.Dir{}:
      LAFs.fs.dir_reply(Nat.is_eq(u, o), Bool.or(Fsmode.wbit(m, 16n), Fsmode.wbit(m, 2n)))
    case Fs.Link{}:
      {==}
    case Fs.Other{}:
      {==}

def ffe.peer(b: Bool) -> {FFs.put_peer(Fs.peer.at(b)) == Wr.put_bool(b, "") : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ffe.cwd(c: Maybe<&2, String>, s: Fs.Stat) -> {FFs.answer(Fs.AskCwd{c, s}) == Fsmode.cwd_reply(c, s) : String}:
  match c:
    case None{}:
      match s:
        case Fs.Absent{}:
          {==}
        case Fs.AFile{}:
          {==}
        case Fs.ADir{}:
          {==}
    case Some{+p}:
      LAFs.fs.cwd_named(String.is_empty(p), s)

def ffe.answer(a: Fs.Ask) -> {FFs.answer(a) == Fsmode.spell_answer(a) : String}:
  match a:
    case Fs.AskDir{k, u, o, m}:
      ffe.dir(k, u, o, m)
    case Fs.AskPeer{+p, +o}:
      ffe.peer(Nat.is_eq(p, o))
    case Fs.AskMade{k}:
      match k:
        case Fs.DirMade{}:
          {==}
        case Fs.FileMade{}:
          {==}
    case Fs.AskCwd{c, s}:
      ffe.cwd(c, s)

def ffe.fin(b: Bool, a: Fs.Ask) -> {FFs.run.end(b, a) == Fsmode.ffi_spec.read(Fsmode.read_ask.end(b, a)) : String}:
  match b:
    case True{}:
      ffe.answer(a)
    case False{}:
      {==}

def ffe.whole(r: Wr.Dec<Fs.Ask>) -> {FFs.run(r) == Fsmode.ffi_spec.read(Fsmode.read_ask.whole(r)) : String}:
  match r:
    case Wr.Got{a, s}:
      ffe.fin(Wr.end(s), a)
    case Wr.Bad{}:
      {==}

def Fsmode.fsmode_ffi_exact(s):
  %LAFs.fs.ask(Wr.get_nat(s)) : {FFs.run(_) == Fsmode.ffi_spec(s) : String}
  ffe.whole(Fsmode.read_ask.go(Wr.get_nat(s)))
