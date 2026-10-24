# eukhe: the proof of LAW fsmode_ffi_answers
# The request's numbers and path read back (the wire's round trips,
# LWire.pw6.nat and Wire.wire_str_round_trip); the decisions are the laws'
# on every input (LAFs.fs.dir_reply, LAFs.fs.cwd_named); the rest are
# closed strings that compute.

import Base
import ../../bend/ffi_fsmode.bend as FFs
import ../../bend/fsmode.bend as Fs
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/fsmode.bend as Fsmode
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire
import ./base.bend as LAFs

def ffa.dir_node(k: Fs.Node, +u: Nat, +o: Nat, +m: Nat) -> {FFs.answer(Fs.AskDir{k, u, o, m}) == Fsmode.dir_reply(k, u, o, m) : String}:
  match k:
    case Fs.Missing{}:
      {==}
    case Fs.Dir{}:
      LAFs.fs.dir_reply(Nat.is_eq(u, o), Bool.or(Fsmode.wbit(m, 16n), Fsmode.wbit(m, 2n)))
    case Fs.Link{}:
      {==}
    case Fs.Other{}:
      {==}

def ffa.dir.go(k: Fs.Node, +u: Nat, +o: Nat, +m: Nat, hu: {LawsBase.wire_fits(u) == True{} : Bool}, ho: {LawsBase.wire_fits(o) == True{} : Bool}, hm: {LawsBase.wire_fits(m) == True{} : Bool}) -> {FFs.ffi(Fsmode.spell_ask(Fs.AskDir{k, u, o, m})) == Fsmode.spell_answer(Fs.AskDir{k, u, o, m}) : String}:
  match k:
    case Fs.Missing{}:
      %LWire.pw6.nat(u, Wr.put_nat(o, Wr.put_nat(m, "")), hu) : {FFs.run(FFs.get_dir.uid(Fs.Missing{}, _)) == Fsmode.dir_reply(Fs.Missing{}, u, o, m) : String}
      %LWire.pw6.nat(o, Wr.put_nat(m, ""), ho) : {FFs.run(FFs.get_dir.own(Fs.Missing{}, u, _)) == Fsmode.dir_reply(Fs.Missing{}, u, o, m) : String}
      %LWire.pw6.nat(m, "", hm) : {FFs.run(FFs.get_dir.mode(Fs.Missing{}, u, o, _)) == Fsmode.dir_reply(Fs.Missing{}, u, o, m) : String}
      ffa.dir_node(Fs.Missing{}, u, o, m)
    case Fs.Dir{}:
      %LWire.pw6.nat(u, Wr.put_nat(o, Wr.put_nat(m, "")), hu) : {FFs.run(FFs.get_dir.uid(Fs.Dir{}, _)) == Fsmode.dir_reply(Fs.Dir{}, u, o, m) : String}
      %LWire.pw6.nat(o, Wr.put_nat(m, ""), ho) : {FFs.run(FFs.get_dir.own(Fs.Dir{}, u, _)) == Fsmode.dir_reply(Fs.Dir{}, u, o, m) : String}
      %LWire.pw6.nat(m, "", hm) : {FFs.run(FFs.get_dir.mode(Fs.Dir{}, u, o, _)) == Fsmode.dir_reply(Fs.Dir{}, u, o, m) : String}
      ffa.dir_node(Fs.Dir{}, u, o, m)
    case Fs.Link{}:
      %LWire.pw6.nat(u, Wr.put_nat(o, Wr.put_nat(m, "")), hu) : {FFs.run(FFs.get_dir.uid(Fs.Link{}, _)) == Fsmode.dir_reply(Fs.Link{}, u, o, m) : String}
      %LWire.pw6.nat(o, Wr.put_nat(m, ""), ho) : {FFs.run(FFs.get_dir.own(Fs.Link{}, u, _)) == Fsmode.dir_reply(Fs.Link{}, u, o, m) : String}
      %LWire.pw6.nat(m, "", hm) : {FFs.run(FFs.get_dir.mode(Fs.Link{}, u, o, _)) == Fsmode.dir_reply(Fs.Link{}, u, o, m) : String}
      ffa.dir_node(Fs.Link{}, u, o, m)
    case Fs.Other{}:
      %LWire.pw6.nat(u, Wr.put_nat(o, Wr.put_nat(m, "")), hu) : {FFs.run(FFs.get_dir.uid(Fs.Other{}, _)) == Fsmode.dir_reply(Fs.Other{}, u, o, m) : String}
      %LWire.pw6.nat(o, Wr.put_nat(m, ""), ho) : {FFs.run(FFs.get_dir.own(Fs.Other{}, u, _)) == Fsmode.dir_reply(Fs.Other{}, u, o, m) : String}
      %LWire.pw6.nat(m, "", hm) : {FFs.run(FFs.get_dir.mode(Fs.Other{}, u, o, _)) == Fsmode.dir_reply(Fs.Other{}, u, o, m) : String}
      ffa.dir_node(Fs.Other{}, u, o, m)

def ffa.dir(k: Fs.Node, +u: Nat, +o: Nat, +m: Nat, +fits: {Fsmode.ask_fits(Fs.AskDir{k, u, o, m}) == True{} : Bool}) -> {FFs.ffi(Fsmode.spell_ask(Fs.AskDir{k, u, o, m})) == Fsmode.spell_answer(Fs.AskDir{k, u, o, m}) : String}:
  +hu = LLogicBool.wr_and_l(LawsBase.wire_fits(u), Bool.and(LawsBase.wire_fits(o), LawsBase.wire_fits(m)), fits)
  +hom = LLogicBool.wr_and_r(LawsBase.wire_fits(u), Bool.and(LawsBase.wire_fits(o), LawsBase.wire_fits(m)), fits)
  +ho = LLogicBool.wr_and_l(LawsBase.wire_fits(o), LawsBase.wire_fits(m), hom)
  +hm = LLogicBool.wr_and_r(LawsBase.wire_fits(o), LawsBase.wire_fits(m), hom)
  ffa.dir.go(k, u, o, m, hu, ho, hm)

def ffa.peer_eq(b: Bool) -> {FFs.put_peer(Fs.peer.at(b)) == Wr.put_bool(b, "") : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ffa.peer(+p: Nat, +o: Nat, +fits: {Fsmode.ask_fits(Fs.AskPeer{p, o}) == True{} : Bool}) -> {FFs.ffi(Fsmode.spell_ask(Fs.AskPeer{p, o})) == Fsmode.spell_answer(Fs.AskPeer{p, o}) : String}:
  %LWire.pw6.nat(p, Wr.put_nat(o, ""), LLogicBool.wr_and_l(LawsBase.wire_fits(p), LawsBase.wire_fits(o), fits)) : {FFs.run(FFs.get_peer(_)) == Fsmode.spell_answer(Fs.AskPeer{p, o}) : String}
  %LWire.pw6.nat(o, "", LLogicBool.wr_and_r(LawsBase.wire_fits(p), LawsBase.wire_fits(o), fits)) : {FFs.run(FFs.get_peer.own(p, _)) == Fsmode.spell_answer(Fs.AskPeer{p, o}) : String}
  ffa.peer_eq(Nat.is_eq(p, o))

def ffa.cwd.path(+p: String, s: Fs.Stat, fits: {LawsBase.wire_fits(String.length(p)) == True{} : Bool}) -> {FFs.ffi(Fsmode.spell_ask(Fs.AskCwd{Some{p}, s})) == Fsmode.spell_answer(Fs.AskCwd{Some{p}, s}) : String}:
  match s:
    case Fs.Absent{}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(p, "0,")), Wr.Got{p, "0,"}, Wire.wire_str_round_trip(p, "0,", fits)) : {FFs.run(FFs.get_cwd.path(_)) == Fsmode.spell_answer(Fs.AskCwd{Some{p}, Fs.Absent{}}) : String}
      LAFs.fs.cwd_named(String.is_empty(p), Fs.Absent{})
    case Fs.AFile{}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(p, "1,")), Wr.Got{p, "1,"}, Wire.wire_str_round_trip(p, "1,", fits)) : {FFs.run(FFs.get_cwd.path(_)) == Fsmode.spell_answer(Fs.AskCwd{Some{p}, Fs.AFile{}}) : String}
      LAFs.fs.cwd_named(String.is_empty(p), Fs.AFile{})
    case Fs.ADir{}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(p, "2,")), Wr.Got{p, "2,"}, Wire.wire_str_round_trip(p, "2,", fits)) : {FFs.run(FFs.get_cwd.path(_)) == Fsmode.spell_answer(Fs.AskCwd{Some{p}, Fs.ADir{}}) : String}
      LAFs.fs.cwd_named(String.is_empty(p), Fs.ADir{})

def ffa.cwd(c: Maybe<&2, String>, s: Fs.Stat, fits: {Fsmode.ask_fits(Fs.AskCwd{c, s}) == True{} : Bool}) -> {FFs.ffi(Fsmode.spell_ask(Fs.AskCwd{c, s})) == Fsmode.spell_answer(Fs.AskCwd{c, s}) : String}:
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
      ffa.cwd.path(p, s, fits)

def Fsmode.fsmode_ffi_answers(a, fits):
  match a:
    case Fs.AskDir{k, u, o, m}:
      ffa.dir(k, u, o, m, fits)
    case Fs.AskPeer{p, o}:
      ffa.peer(p, o, fits)
    case Fs.AskMade{k}:
      match k:
        case Fs.DirMade{}:
          {==}
        case Fs.FileMade{}:
          {==}
    case Fs.AskCwd{c, s}:
      ffa.cwd(c, s, fits)
