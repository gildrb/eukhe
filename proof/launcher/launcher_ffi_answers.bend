# eukhe: the proof of LAW launcher_ffi_answers
# A run start and a quiesce are closed strings: they compute. A commit and
# an adoption carry a number of the request: the wire's round trip reads
# it back (LWire.pw6.nat), the answers read back one by one
# (LLa.la.bools_rt), and the decision is the laws' (LLa.la.commits,
# LLa.la.adopt_n).

import Base
import ../../bend/ffi_launcher.bend as FLa
import ../../bend/launcher.bend as La
import ../../bend/wire.bend as Wr
import ../../laws/launcher.bend as Launcher
import ../base/wire.bend as LWire
import ./base.bend as LLa

def lfa.commit(xs: List<&2, Bool>, fits: {Launcher.ask_fits(La.AskCommit{xs}) == True{} : Bool}) -> {FLa.ffi(Launcher.spell_ask(La.AskCommit{xs})) == Launcher.spell_answer(La.AskCommit{xs}) : String}:
  match xs:
    case Nil{}:
      {==}
    case +a <> +t:
      %LWire.pw6.nat(1n+List.length(&2, Bool, t), Launcher.spell_bools(a <> t, ""), fits) : {FLa.run(FLa.get_commit(_)) == Launcher.spell_answer(La.AskCommit{a <> t}) : String}
      %LLa.la.bools_rt(t, a, "") : {FLa.run(FLa.get_commit.answers(_)) == Launcher.spell_answer(La.AskCommit{a <> t}) : String}
      %LLa.la.commits(a <> t) : {Wr.put_bool(_, "") == Wr.put_bool(Launcher.all_quiesced(a <> t), "") : String}
      {==}

def lfa.adopt(w: Maybe<&2, Nat>, fits: {Launcher.ask_fits(La.AskAdopt{w}) == True{} : Bool}) -> {FLa.ffi(Launcher.spell_ask(La.AskAdopt{w})) == Launcher.spell_answer(La.AskAdopt{w}) : String}:
  match w:
    case None{}:
      {==}
    case Some{+n}:
      %LWire.pw6.nat(n, "", fits) : {FLa.run(FLa.get_adopt.some(_)) == Launcher.spell_answer(La.AskAdopt{Some{n}}) : String}
      LLa.la.adopt_n(n)

def Launcher.launcher_ffi_answers(a, fits):
  match a:
    case La.AskPrompt{c}:
      match c:
        case True{}:
          {==}
        case False{}:
          {==}
    case La.AskQuiesce{b, c}:
      match b c:
        case True{} True{}:
          {==}
        case True{} False{}:
          {==}
        case False{} True{}:
          {==}
        case False{} False{}:
          {==}
    case La.AskCommit{xs}:
      lfa.commit(xs, fits)
    case La.AskAdopt{w}:
      lfa.adopt(w, fits)
