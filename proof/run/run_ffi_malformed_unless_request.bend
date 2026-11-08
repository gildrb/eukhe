# eukhe: the proof of LAW run_ffi_malformed_unless_request
#
# PROOF: the decoder reads only spelled requests that fit, the rest after
# them untouched (LDk.dk.ask); when it reads none the entry answers the
# malformed error, which the premise excludes.

import Base
import ../../bend/ffi_run.bend as FRn
import ../../bend/wire.bend as Wr
import ../../laws/run/entry.bend as Run
import ../wire/base/spell.bend as LAWireSpell
import ./run_ffi_reads_only_requests/decode.bend as LDk

def mu.goal(+s: String) -> Type:
  &a: FRn.Ask -> &rest: String -> {(s, Run.run.ask_fits(a)) == (Run.run_spell_ask(a, rest), True{}) : String & Bool}

def mu.eq(+s: String, +a: FRn.Ask, +rest: String, e1: {s == Run.run_spell_ask(a, rest) : String}, e2: {Run.run.ask_fits(a) == True{} : Bool}) -> {(s, Run.run.ask_fits(a)) == (Run.run_spell_ask(a, rest), True{}) : String & Bool}:
  %Equal.sym(String, s, Run.run_spell_ask(a, rest), e1) : {(_, Run.run.ask_fits(a)) == (Run.run_spell_ask(a, rest), True{}) : String & Bool}
  %Equal.sym(Bool, Run.run.ask_fits(a), True{}, e2) : {(Run.run_spell_ask(a, rest), _) == (Run.run_spell_ask(a, rest), True{}) : String & Bool}
  {==}

def mu.main(+s: String, d: Wr.Dec<FRn.Ask>, inv: LDk.dk.Ask(s, d), other: {String.eq(FRn.ffi.go(d), Wr.err("run: malformed request")) == False{} : Bool}) -> mu.goal(s):
  match d:
    case Wr.Got{+a, +rest}:
      (e1, e2) = inv
      (a, (rest, mu.eq(s, a, rest, e1, e2)))
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(mu.goal(s), other)

def Run.run_ffi_malformed_unless_request(s, other):
  mu.main(s, FRn.get_ask(s), LDk.dk.ask(s), other)
