# eukhe: lemmas the proofs of two or more areas share: string

import Base
import ../../bend/wire.bend as Wr
import ./logic/string.bend as LLogicString
import ./logic/wire.bend as LLogicWire

# turning a around onto acc, then all of it around onto rest, puts a before rest
def wr_rev_rev(a: String, -acc: String, -rest: String) ->
  {String.reverse.go(String.reverse.go(a, acc), rest) == String.reverse.go(acc, LLogicString.wr_app(a, rest)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, t}:
      wr_rev_rev(t, SCon{c, acc}, rest)

# the reference reads back the chars of a
def wr_take_rt(+a: String, -rest: String) ->
  {LLogicWire.wo_take(String.length(a), LLogicString.wr_app(a, rest)) == Wr.Got{a, rest} : Wr.Dec<String>}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, +t}:
      %Equal.sym(Wr.Dec<String>, LLogicWire.wo_take(String.length(t), LLogicString.wr_app(t, rest)), Wr.Got{t, rest}, wr_take_rt(t, rest)) : {LLogicWire.wo_take_cons(c, _) == Wr.Got{SCon{c, t}, rest} : Wr.Dec<String>}
      {==}
