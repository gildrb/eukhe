# eukhe: the proof of LAW shell_ffi_spec
# The entry answers the laws' reader and spelled decision (LASh.sh.exact);
# that decision is the spec's (shell_effects_spec, shell_within_spec, and
# the gate by cases).

import Base
import ../../bend/ffi_shell.bend as FSh
import ../../bend/tools.bend as Tl
import ../../bend/wire.bend as Wr
import ../../laws/shell.bend as Shell
import ./base.bend as LASh
import ./shell_effects_spec.bend as PShellEffectsSpec
import ./shell_within_spec.bend as PShellWithinSpec

def shfx.reply(q: FSh.Req) -> {Shell.spell_answer(q) == Shell.sh_reply(q) : String}:
  match q:
    case FSh.QStep{+a, +ps}:
      %Shell.shell_effects_spec(ps) : {Shell.spell_answer(FSh.QStep{a, ps}) == Shell.spell_ns(_, Wr.put_bool(Shell.sh_within(_, a), "")) : String}
      %Shell.shell_within_spec(Tl.join(Tl.parts.effs(ps)), a) : {Shell.spell_answer(FSh.QStep{a, ps}) == Shell.spell_ns(Tl.join(Tl.parts.effs(ps)), Wr.put_bool(_, "")) : String}
      {==}
    case FSh.QAllows{+a, +es}:
      %Shell.shell_within_spec(es, a) : {Shell.spell_answer(FSh.QAllows{a, es}) == Wr.put_bool(_, "") : String}
      {==}
    case FSh.QAnswer{i, y}:
      match y:
        case True{}:
          {==}
        case False{}:
          {==}

def shfx.end(b: Bool, q: FSh.Req) -> {Shell.spec.end(b, q) == Shell.sh_spec.end(b, q) : String}:
  match b:
    case True{}:
      shfx.reply(q)
    case False{}:
      {==}

def shfx.run(r: Wr.Dec<FSh.Req>) -> {Shell.spec.run(r) == Shell.sh_spec.run(r) : String}:
  match r:
    case Wr.Got{q, s}:
      shfx.end(Wr.end(s), q)
    case Wr.Bad{}:
      {==}

def Shell.shell_ffi_spec(s):
  %shfx.run(Shell.read_req(s)) : {FSh.ffi(s) == _ : String}
  LASh.sh.exact(s)
