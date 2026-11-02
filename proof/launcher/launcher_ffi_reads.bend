# eukhe: the proof of LAW launcher_ffi_reads
#
# PROOF: the entry reads every input as the laws' reader does (LLa.la.ask);
# where that reader finds a whole request a, the entry answers its answer
# to a, which is the laws' spell_answer(a) on every request (lfr.answer:
# the run start and the quiesce by cases, the commit by LLa.la.commits,
# the adoption by LLa.la.adopt_n).

import Base
import ../../bend/ffi_launcher.bend as FLa
import ../../bend/launcher.bend as La
import ../../bend/wire.bend as Wr
import ../../laws/launcher.bend as Launcher
import ./base.bend as LLa

# the entry's answer to every request is the laws'
def lfr.answer(a: La.Ask) -> {FLa.answer(a) == Launcher.spell_answer(a) : String}:
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
    case La.AskCommit{+xs}:
      %LLa.la.commits(xs) : {Wr.put_bool(_, "") == Wr.put_bool(Launcher.all_quiesced(xs), "") : String}
      {==}
    case La.AskAdopt{w}:
      match w:
        case None{}:
          {==}
        case Some{n}:
          LLa.la.adopt_n(n)

def lfr.If(m: Maybe<&2, La.Ask>, x: La.Ask) -> Type:
  match m:
    case None{}:
      Unit
    case Some{y}:
      {FLa.answer(x) == Launcher.spell_answer(y) : String}

def lfr.some(+x: La.Ask, -a: La.Ask, e: {Some{x} == Some{a} : Maybe<&2, La.Ask>}) -> {FLa.answer(x) == Launcher.spell_answer(a) : String}:
  %e : lfr.If(_, x)
  lfr.answer(x)

def lfr.end(b: Bool, +x: La.Ask, -a: La.Ask, got: {Launcher.read_ask.end(b, x) == Some{a} : Maybe<&2, La.Ask>}) -> {FLa.run.end(b, x) == Launcher.spell_answer(a) : String}:
  match b:
    case True{}:
      lfr.some(x, a, got)
    case False{}:
      LLa.la.some_none(La.Ask, a, {FLa.fail() == Launcher.spell_answer(a) : String}, Equal.sym(Maybe<&2, La.Ask>, None{}, Some{a}, got))

def lfr.whole(r: Wr.Dec<La.Ask>, -a: La.Ask, got: {Launcher.read_ask.whole(r) == Some{a} : Maybe<&2, La.Ask>}) -> {FLa.run(r) == Launcher.spell_answer(a) : String}:
  match r:
    case Wr.Got{x, s}:
      lfr.end(Wr.end(s), x, a, got)
    case Wr.Bad{}:
      LLa.la.some_none(La.Ask, a, {FLa.fail() == Launcher.spell_answer(a) : String}, Equal.sym(Maybe<&2, La.Ask>, None{}, Some{a}, got))

def Launcher.launcher_ffi_reads(s, a, got):
  %LLa.la.ask(Wr.get_nat(s)) : {FLa.run(_) == Launcher.spell_answer(a) : String}
  lfr.whole(Launcher.read_ask.go(Wr.get_nat(s)), a, got)
