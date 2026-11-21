# eukhe: the proof of LAW runners_ffi_spec
# The entry answers the laws' reader and spelled decision (LARunnersEntry.rn.exact);
# that decision is the spec's (runners_registry_spec).

import Base
import ../../bend/ffi_runners.bend as FRu
import ../../bend/runners.bend as Ru
import ../../bend/wire.bend as Wr
import ../../laws/runners.bend as Runners
import ./base/entry.bend as LARunnersEntry
import ./runners_registry_spec.bend as PRunnersRegistrySpec

def ruf.reply(q: FRu.Req) -> {Runners.spell_answer(q) == Runners.ru_reply(q) : String}:
  match q:
    case FRu.QRegistry{}:
      %Runners.runners_registry_spec() : {Runners.spell_answer(FRu.QRegistry{}) == Wr.put_list(~Ru.ToolReg, ~Runners.spell_tool, _, "") : String}
      {==}
    case FRu.QMain{h}:
      match h:
        case True{}:
          {==}
        case False{}:
          {==}

def ruf.end(b: Bool, q: FRu.Req) -> {Runners.spec.end(b, q) == Runners.ru_spec.end(b, q) : String}:
  match b:
    case True{}:
      ruf.reply(q)
    case False{}:
      {==}

def ruf.run(r: Wr.Dec<FRu.Req>) -> {Runners.spec.run(r) == Runners.ru_spec.run(r) : String}:
  match r:
    case Wr.Got{q, s}:
      ruf.end(Wr.end(s), q)
    case Wr.Bad{}:
      {==}

def Runners.runners_ffi_spec(s):
  %ruf.run(Runners.read_req(s)) : {FRu.ffi(s) == _ : String}
  LARunnersEntry.rn.exact(s)
