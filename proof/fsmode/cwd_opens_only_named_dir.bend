# eukhe: the proof of LAW cwd_opens_only_named_dir
# The entry answers the spelled cwd request with the laws' reply
# (fsmode_ffi_answers); that reply is "0," only for a non-empty path where
# a dir is: every other reply is another string ("1,", "2,", "3,").

import Base
import ../../bend/ffi_fsmode.bend as FFs
import ../../bend/fsmode.bend as Fs
import ../../laws/fsmode.bend as Fsmode
import ./base.bend as LA
import ./fsmode_ffi_answers.bend as PFsmodeFfiAnswers

def co.goal(c: Maybe<&2, String>, s: Fs.Stat) -> Type:
  &p: String -> {c == Some{p} : Maybe<&2, String>} & {String.is_empty(p) == False{} : Bool} & {s == Fs.ADir{} : Fs.Stat}

# another reply than "0,"
def co.ne(-G: Type, +x: String, e: {x == "0," : String}, ne: {String.eq(x, "0,") == False{} : Bool}) -> G:
  LA.fsmode.pf.absurdF(G, Equal.trans(Bool, False{}, String.eq(x, "0,"), True{}, Equal.sym(Bool, String.eq(x, "0,"), False{}, ne), Equal.cong(String, Bool, z => String.eq(z, "0,"), x, "0,", e)))

def co.named(+p: String, b: Bool, s: Fs.Stat, eb: {String.is_empty(p) == b : Bool}, e: {Fsmode.cwd_reply.named(b, s) == "0," : String}) -> co.goal(Some{p}, s):
  match b:
    case True{}:
      co.ne(co.goal(Some{p}, s), "1,", e, {==})
    case False{}:
      match s:
        case Fs.Absent{}:
          co.ne(co.goal(Some{p}, Fs.Absent{}), "2,", e, {==})
        case Fs.AFile{}:
          co.ne(co.goal(Some{p}, Fs.AFile{}), "3,", e, {==})
        case Fs.ADir{}:
          (p, ({==}, (eb, {==})))

def co.go(c: Maybe<&2, String>, s: Fs.Stat, e: {Fsmode.cwd_reply(c, s) == "0," : String}) -> co.goal(c, s):
  match c:
    case None{}:
      co.ne(co.goal(None{}, s), "1,", e, {==})
    case Some{+p}:
      co.named(p, String.is_empty(p), s, {==}, e)

def Fsmode.cwd_opens_only_named_dir(c, s, fits, opened):
  +a = {Fs.AskCwd{c, s} : Fs.Ask}
  co.go(c, s, Equal.trans(String, Fsmode.spell_answer(a), FFs.ffi(Fsmode.spell_ask(a)), "0,", Equal.sym(String, FFs.ffi(Fsmode.spell_ask(a)), Fsmode.spell_answer(a), Fsmode.fsmode_ffi_answers(a, fits)), opened))
