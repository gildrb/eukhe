# eukhe: the proof of LAW config_ffi_malformed_exact
# The entry reads every input as the laws' reader does (LFR.pfc.ask);
# where that reader finds no whole request, the entry answers its error
# form.

import Base
import ../../bend/config.bend as Cf
import ../../laws/config.bend as Config
import ../../bend/ffi_config.bend as FC
import ../../bend/wire.bend as Wr
import ../../spec/settings/config.bend as CS
import ./base/ffi_read.bend as LFR
import ./base/ffi_spell.bend as LFS
import ./base/ffi_reply.bend as LFP

def pme.end(b: Bool, -a: FC.Ask, no: {CS.cf_r_end(b, a) == None{} : Maybe<&2, FC.Ask>}) -> {FC.run.end(b, a) == SCon{'E', SCon{' ', "config: malformed request"}} : String}:
  match b:
    case True{}:
      LFR.pfc.some_none(FC.Ask, a, {FC.answer(a) == SCon{'E', SCon{' ', "config: malformed request"}} : String}, no)
    case False{}:
      {==}

def pme.whole(r: Wr.Dec<FC.Ask>, no: {CS.cf_r_whole(r) == None{} : Maybe<&2, FC.Ask>}) -> {FC.run(r) == SCon{'E', SCon{' ', "config: malformed request"}} : String}:
  match r:
    case Wr.Got{a, s}:
      pme.end(Wr.end(s), a, no)
    case Wr.Bad{}:
      {==}

def Config.config_ffi_malformed_exact(s, no):
  %Equal.sym(Wr.Dec<FC.Ask>, FC.get_ask(Wr.get_nat(s)), CS.cf_r_ask(Wr.get_nat(s)), LFR.pfc.ask(Wr.get_nat(s))) : {FC.run(_) == SCon{'E', SCon{' ', "config: malformed request"}} : String}
  pme.whole(CS.cf_r_ask(Wr.get_nat(s)), no)
