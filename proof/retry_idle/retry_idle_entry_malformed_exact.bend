# eukhe: the proof of LAW retry_idle_entry_malformed_exact
# The entry reads every input as the laws' reader does (LARetryIdle.ri.rq);
# where that reader finds no whole request, the entry answers its error
# form.

import Base
import ../../bend/ffi_retry_idle.bend as Fi
import ../../bend/wire.bend as Wr
import ../../laws/retry_idle.bend as RetryIdle
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LARetryIdle

def rme.Clash(m: Maybe<&2, RetryIdle.idle.Ask>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def rme.some_none(-a: RetryIdle.idle.Ask, -G: Type, e: {Some{a} == None{} : Maybe<&2, RetryIdle.idle.Ask>}) -> G:
  %e : rme.Clash(_, G)
  Unit{}

def rme.end(b: Bool, -a: RetryIdle.idle.Ask, no: {RetryIdle.read_ask.end(b, a) == None{} : Maybe<&2, RetryIdle.idle.Ask>}) -> {Fi.run.end(b, LARetryIdle.ri.req(a)) == SCon{'E', SCon{' ', "retry_idle: malformed request"}} : String}:
  match b:
    case True{}:
      rme.some_none(a, {Fi.answer(LARetryIdle.ri.req(a)) == SCon{'E', SCon{' ', "retry_idle: malformed request"}} : String}, no)
    case False{}:
      {==}

def rme.whole(r: Wr.Dec<RetryIdle.idle.Ask>, no: {RetryIdle.read_ask.whole(r) == None{} : Maybe<&2, RetryIdle.idle.Ask>}) -> {Fi.run(LARetryIdle.ri.conv(r)) == SCon{'E', SCon{' ', "retry_idle: malformed request"}} : String}:
  match r:
    case Wr.Got{a, s}:
      rme.end(Wr.end(s), a, no)
    case Wr.Bad{}:
      {==}

def RetryIdle.retry_idle_entry_malformed_exact(s, no):
  %LARetryIdle.ri.rq(Wr.get_nat(s)) : {Fi.run(_) == SCon{'E', SCon{' ', "retry_idle: malformed request"}} : String}
  rme.whole(RetryIdle.read_ask.go(Wr.get_nat(s)), no)
