# eukhe: the proof of LAW runners_ffi_spec
# The entry answers the laws' reader and spelled decision (LARunnersEntry.rn.exact);
# that decision is the spec's (runners_within_spec, runners_cell_spec,
# runners_registry_spec).

import Base
import ../../bend/ffi_runners.bend as FRu
import ../../bend/runners.bend as Ru
import ../../bend/wire.bend as Wr
import ../../laws/runners.bend as Runners
import ./base/entry.bend as LARunnersEntry
import ./runners_within_spec.bend as PRunnersWithinSpec
import ./runners_cell_spec.bend as PRunnersCellSpec
import ./runners_registry_spec.bend as PRunnersRegistrySpec

def ruf.reply(q: FRu.Req) -> {Runners.spell_answer(q) == Runners.ru_reply(q) : String}:
  match q:
    case FRu.QWithin{+c, +a}:
      %Runners.runners_within_spec(c, a) : {Runners.spell_answer(FRu.QWithin{c, a}) == Wr.put_bool(_, "") : String}
      {==}
    case FRu.QCell{+c, +a, +k}:
      %Runners.runners_cell_spec(c, a, k) : {Runners.spell_answer(FRu.QCell{c, a, k}) == Runners.spell_out(_) : String}
      {==}
    case FRu.QRegistry{+h}:
      %Runners.runners_registry_spec(h) : {Runners.spell_answer(FRu.QRegistry{h}) == Wr.put_list(~Ru.Tool, ~Runners.spell_tool, _, "") : String}
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
