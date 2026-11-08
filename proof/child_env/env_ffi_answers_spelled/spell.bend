# eukhe: lemmas of LAW env_ffi_answers_spelled: the entry's encoders write
# the laws' spelling
#
# The entry's put_var, its lists of variables and its request are the
# spelling of laws/child_env.bend (env_spell_var, env_spell_vars,
# env_spell_req), field by field; its lists of strings are
# LawsBase.wire_spell_strs (wire_strs_spells). So the round trip and the
# answer of the entry's own laws (env_ffi_round_trip, env_ffi_is_child)
# speak of the spelled request and reply.

import Base
import ../../../bend/child_env.bend as Env
import ../../../bend/ffi_child_env.bend as FEnv
import ../../../bend/wire.bend as Wr
import ../../../laws/child_env.bend as ChildEnv
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../wire/wire_strs_spells.bend as PWireStrsSpells
import ../base.bend as LA

# a variable
def pes.var(v: Env.Var, -rest: String) -> {FEnv.put_var(v, rest) == ChildEnv.env_spell_var(v, rest) : String}:
  match v:
    case Env.Var{n, x}:
      {==}

# the items of a list of variables
def pes.items(xs: List<&2, Env.Var>, -rest: String) -> {LA.pce.vs.items(xs, rest) == ChildEnv.env_spell_vars.items(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %pes.items(t, rest) : {FEnv.put_var(x, LA.pce.vs.items(t, rest)) == ChildEnv.env_spell_var(x, _) : String}
      pes.var(x, LA.pce.vs.items(t, rest))

# a list of variables: its count, then its items
def pes.vars(+xs: List<&2, Env.Var>, -rest: String) -> {Wr.put_list(~Env.Var, ~FEnv.put_var, xs, rest) == ChildEnv.env_spell_vars(xs, rest) : String}:
  %pes.items(xs, rest) : {Wr.put_list(~Env.Var, ~FEnv.put_var, xs, rest) == Wr.put_nat(List.length(&2, Env.Var, xs), _) : String}
  LA.pce.vs.put(xs, rest)

# a request
def pes.req(q: FEnv.Req, +rest: String) -> {FEnv.put_req(q, rest) == ChildEnv.env_spell_req(q, rest) : String}:
  match q:
    case FEnv.Req{+r, +k, +b, +o}:
      %pes.vars(o, rest) : {FEnv.put_req(FEnv.Req{r, k, b, o}, rest) == LawsBase.wire_spell_strs(r, LawsBase.wire_spell_strs(k, ChildEnv.env_spell_vars(b, _))) : String}
      %pes.vars(b, Wr.put_list(~Env.Var, ~FEnv.put_var, o, rest)) : {FEnv.put_req(FEnv.Req{r, k, b, o}, rest) == LawsBase.wire_spell_strs(r, LawsBase.wire_spell_strs(k, _)) : String}
      %Wire.wire_strs_spells(k, Wr.put_list(~Env.Var, ~FEnv.put_var, b, Wr.put_list(~Env.Var, ~FEnv.put_var, o, rest))) : {FEnv.put_req(FEnv.Req{r, k, b, o}, rest) == LawsBase.wire_spell_strs(r, _) : String}
      %Wire.wire_strs_spells(r, Wr.put_list(~String, ~Wr.put_str, k, Wr.put_list(~Env.Var, ~FEnv.put_var, b, Wr.put_list(~Env.Var, ~FEnv.put_var, o, rest)))) : {FEnv.put_req(FEnv.Req{r, k, b, o}, rest) == _ : String}
      {==}

# the entry's answer to a request is the spelled environment of the child
def pes.answer(q: FEnv.Req) -> {FEnv.ffi.run(q) == ChildEnv.env_spell_answer(q) : String}:
  match q:
    case FEnv.Req{r, k, b, o}:
      pes.vars(Env.child(r, k, b, o), "")
