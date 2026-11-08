# eukhe: the laws of area child_env

import Base
import ../bend/child_env.bend as Env
import ../bend/ffi_child_env.bend as FEnv
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- child_env ----

# LAWS (G3): no credential reaches a child. Each law is an open claim
# about the model in bend/child_env.bend; PROOF.bend proves them (as
# ChildEnv.<law>) with the lemmas of proof/child_env/.

# (G3) No credential reaches a child
# ----------------------------------
# The environment of a child the host starts for an agent: the overlay
# over the base, less the credential names (bend/child_env.bend). The
# `bash` tool's external steps get an empty keep list; a local kernel gets
# the names the user's own MCP config reads a credential from. Every input
# is free: any registry, any keep list, any base, any overlay (so no
# overlay can add a credential back).

# LAW env_drops_credentials: no variable of the environment of an external step of the `bash`
# tool has a credential name
law env_drops_credentials:
  for +reg: List<&2, String>
  for base: List<&2, Env.Var>
  for over: List<&2, Env.Var>
  for +v: Env.Var
  for i: Env.In(v, Env.child(reg, Nil{}, base, over))
  {Env.cred(reg, Env.Var.name(v)) == False{} : Bool}

# LAW env_kernel_keeps_only_listed: a variable of the environment of a kernel has a credential name
# only when the keep list holds that name and it is no provider name
law env_kernel_keeps_only_listed:
  for +reg: List<&2, String>
  for +keep: List<&2, String>
  for base: List<&2, Env.Var>
  for over: List<&2, Env.Var>
  for +v: Env.Var
  for i: Env.In(v, Env.child(reg, keep, base, over))
  for c: {Env.cred(reg, Env.Var.name(v)) == True{} : Bool}
  ({Env.listed(keep, Env.Var.name(v)) == True{} : Bool} & {Env.registered(reg, Env.Var.name(v)) == False{} : Bool})

# LAW env_keeps_the_rest: every variable of the overlay over the base whose name is not a
# credential reaches the child, with its value
law env_keeps_the_rest:
  for +reg: List<&2, String>
  for +keep: List<&2, String>
  for base: List<&2, Env.Var>
  for over: List<&2, Env.Var>
  for +v: Env.Var
  for i: Env.In(v, Env.merge(base, over))
  for c: {Env.cred(reg, Env.Var.name(v)) == False{} : Bool}
  Env.In(v, Env.child(reg, keep, base, over))

# LAW env_keeps_listed: every variable of the overlay over the base whose name the keep
# list holds, and that is no provider name, reaches the kernel, with its
# value
law env_keeps_listed:
  for +reg: List<&2, String>
  for +keep: List<&2, String>
  for base: List<&2, Env.Var>
  for over: List<&2, Env.Var>
  for +v: Env.Var
  for i: Env.In(v, Env.merge(base, over))
  for k: {Env.listed(keep, Env.Var.name(v)) == True{} : Bool}
  for r: {Env.registered(reg, Env.Var.name(v)) == False{} : Bool}
  Env.In(v, Env.child(reg, keep, base, over))

# The overlay over the base (every input free: duplicate names too)

# n is the name of a variable of xs
def env_named(+n: String, xs: List<&2, Env.Var>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case v <> rest:
      Bool.or(String.eq(Env.Var.name(v), n), env_named(n, rest))

# LAW env_child_from_merge: no variable reaches a child that the overlay over the base does
# not hold: the filter only drops, it never invents or changes a value
law env_child_from_merge:
  for +reg: List<&2, String>
  for +keep: List<&2, String>
  for +base: List<&2, Env.Var>
  for +over: List<&2, Env.Var>
  for +v: Env.Var
  for i: Env.In(v, Env.child(reg, keep, base, over))
  Env.In(v, Env.merge(base, over))

# LAW env_overlay_in_merge: every variable of the overlay is in the overlay over the base
law env_overlay_in_merge:
  for base: List<&2, Env.Var>
  for +over: List<&2, Env.Var>
  for +v: Env.Var
  for i: Env.In(v, over)
  Env.In(v, Env.merge(base, over))

# LAW env_base_in_merge: a variable of the base whose name the overlay does not name is in
# the overlay over the base
law env_base_in_merge:
  for +base: List<&2, Env.Var>
  for +over: List<&2, Env.Var>
  for +v: Env.Var
  for i: Env.In(v, base)
  for free: {env_named(Env.Var.name(v), over) == False{} : Bool}
  Env.In(v, Env.merge(base, over))

# LAW env_merge_named_from_overlay: a variable of the overlay over the base whose name the overlay
# names comes from the overlay: the overlay hides every variable of the
# base with that name
law env_merge_named_from_overlay:
  for +base: List<&2, Env.Var>
  for +over: List<&2, Env.Var>
  for +v: Env.Var
  for i: Env.In(v, Env.merge(base, over))
  for hit: {env_named(Env.Var.name(v), over) == True{} : Bool}
  Env.In(v, over)

# LAW env_merge_from_inputs: every variable of the overlay over the base comes from the
# overlay, or from the base under a name the overlay does not name
law env_merge_from_inputs:
  for +base: List<&2, Env.Var>
  for +over: List<&2, Env.Var>
  for +v: Env.Var
  for i: Env.In(v, Env.merge(base, over))
  Or(Env.In(v, over), (Env.In(v, base) & {env_named(Env.Var.name(v), over) == False{} : Bool}))

# The credential names (crates/eukhe-ai/src/env_api_keys.rs)

# LAW env_cred_example: anchor: a name whose ASCII upper case contains a secret pattern is
# a credential, at its start, middle or end, in any case: API_KEY, APIKEY,
# TOKEN, SECRET, PASSWORD, PASSWD, PASSPHRASE, CREDENTIAL, PRIVATE_KEY,
# ACCESS_KEY
law env_cred_example:
  {[Env.cred(Nil{}, "OPENAI_API_KEY"), Env.cred(Nil{}, "my_apikey"), Env.cred(Nil{}, "GITHUB_TOKEN"), Env.cred(Nil{}, "TOKENIZERS_PARALLELISM"), Env.cred(Nil{}, "AWS_WEB_IDENTITY_TOKEN_FILE"), Env.cred(Nil{}, "aws_secret_access_key"), Env.cred(Nil{}, "PGPASSWORD"), Env.cred(Nil{}, "db_passwd"), Env.cred(Nil{}, "GPG_PASSPHRASE"), Env.cred(Nil{}, "GOOGLE_APPLICATION_CREDENTIALS"), Env.cred(Nil{}, "TLS_PRIVATE_KEY"), Env.cred(Nil{}, "S3_ACCESS_KEY")] == [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}] : List<&2, Bool>}

# LAW env_not_cred_example: anchor: names a child needs are no credential: there is no KEY,
# AUTH or PASS pattern
law env_not_cred_example:
  {[Env.cred(Nil{}, "PATH"), Env.cred(Nil{}, "HOME"), Env.cred(Nil{}, "SSH_AUTH_SOCK"), Env.cred(Nil{}, "XAUTHORITY"), Env.cred(Nil{}, "KEYTIMEOUT"), Env.cred(Nil{}, "SSH_ASKPASS"), Env.cred(Nil{}, "LS_COLORS")] == [False{}, False{}, False{}, False{}, False{}, False{}, False{}] : List<&2, Bool>}

# LAW env_registry_example: anchor: a provider name is a credential and a provider name in any
# case, by the registry alone
law env_registry_example:
  {[Env.cred(["AWS_PROFILE"], "aws_profile"), Env.registered(["AWS_PROFILE"], "aws_profile"), Env.registered(Nil{}, "aws_profile"), Env.cred(Nil{}, "AWS_PROFILE")] == [True{}, True{}, False{}, False{}] : List<&2, Bool>}

# LAW env_step_example: anchor (the Rust tests of child_env): an external step gets no
# credential of the base or the overlay, and the overlay wins
law env_step_example:
  {Env.child(["OPENAI_API_KEY"], Nil{}, [Env.Var{"PATH", "/bin"}, Env.Var{"OPENAI_API_KEY", "sk"}, Env.Var{"db_password", "h"}, Env.Var{"HOME", "/home"}], [Env.Var{"GITHUB_TOKEN", "g"}, Env.Var{"PATH", "/usr/bin"}, Env.Var{"EUKHE_CODING_AGENT_DIR", "/agent"}]) == [Env.Var{"PATH", "/usr/bin"}, Env.Var{"EUKHE_CODING_AGENT_DIR", "/agent"}, Env.Var{"HOME", "/home"}] : List<&2, Env.Var>}

# LAW env_kernel_example: anchor: a kernel keeps only the kept credentials that are no
# provider name
law env_kernel_example:
  {Env.child(["OPENAI_API_KEY"], ["GITHUB_TOKEN", "OPENAI_API_KEY"], [Env.Var{"PATH", "/bin"}, Env.Var{"OPENAI_API_KEY", "sk"}, Env.Var{"GITHUB_TOKEN", "g"}, Env.Var{"SLACK_SECRET", "x"}], Nil{}) == [Env.Var{"PATH", "/bin"}, Env.Var{"GITHUB_TOKEN", "g"}] : List<&2, Env.Var>}

# ---- child_env_entry ----

# LAWS (G3, the compiled core): the entry bend/ffi_child_env.bend runs the
# child environment for the Rust code. Each law is an open claim about
# that entry; PROOF.bend proves them (as ChildEnv.<law>) with the lemmas of
# proof/child_env/.

# The entry of the compiled core (bend/ffi_child_env.bend)
# ---------------------------------------------------------
# The Rust code sends the registry, the keep list, the base and the
# overlay as text, and reads the environment of the child. It sends each
# value as a number (the model never reads a value and never invents a
# variable: env_child_from_merge), and maps the numbers back.

# the length of s fits the wire
def env_str_fits(+s: String) -> Bool:
  LawsBase.wire_fits(String.length(s))

# every item of xs fits the wire
def env_strs_fit(xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(env_str_fits(x), env_strs_fit(t))

# the lengths of a variable fit the wire
def env_var_fits(v: Env.Var) -> Bool:
  match v:
    case Env.Var{+n, +x}:
      Bool.and(env_str_fits(n), env_str_fits(x))

# every item of xs fits the wire
def env_vars_fit(xs: List<&2, Env.Var>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(env_var_fits(x), env_vars_fit(t))

# the numbers of a request fit the wire
def env_req_fits(q: FEnv.Req) -> Bool:
  match q:
    case FEnv.Req{+r, +k, +b, +o}:
      Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, String, r)), env_strs_fit(r)), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, String, k)), env_strs_fit(k)), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Env.Var, b)), env_vars_fit(b)), Bool.and(LawsBase.wire_fits(List.length(&2, Env.Var, o)), env_vars_fit(o)))))

# LAW env_ffi_round_trip: a request that fits reads back whole, and the input after it stays
# EXCLUDES: a name, a value, a registry or keep entry lost, swapped or
#   misread on the way to the model
law env_ffi_round_trip:
  for +q: FEnv.Req
  for +rest: String
  for h: {env_req_fits(q) == True{} : Bool}
  {FEnv.get_req(FEnv.put_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FEnv.Req>}

# LAW env_ffi_is_child: the entry answers the model's environment of the child
# EXCLUDES: an entry that filters anything but Env.child (a second rule, a
#   default environment)
law env_ffi_is_child:
  for +r: List<&2, String>
  for +k: List<&2, String>
  for +b: List<&2, Env.Var>
  for +o: List<&2, Env.Var>
  for h: {env_req_fits(FEnv.Req{r, k, b, o}) == True{} : Bool}
  {FEnv.ffi(FEnv.put_req(FEnv.Req{r, k, b, o}, "")) == Wr.put_list(~Env.Var, ~FEnv.put_var, Env.child(r, k, b, o), "") : String}

# LAW env_ffi_malformed: a malformed request answers the error form, never an environment
# EXCLUDES: a default (empty or unfiltered) environment for bad input
law env_ffi_malformed:
  for +s: String
  for h: {FEnv.get_req(s) == Wr.Bad{} : Wr.Dec<FEnv.Req>}
  {FEnv.ffi(s) == Wr.err("child_env: malformed request") : String}

# LAW env_ffi_left_over: a request with input left over answers the error form
# EXCLUDES: a reply to a request followed by anything
law env_ffi_left_over:
  for +s: String
  for +q: FEnv.Req
  for +r: String
  for h: {FEnv.get_req(s) == Wr.Got{q, r} : Wr.Dec<FEnv.Req>}
  for e: {String.is_empty(r) == False{} : Bool}
  {FEnv.ffi(s) == Wr.err("child_env: input left over") : String}

# LAW env_req_fits_example: witness: a request fits
law env_req_fits_example:
  {env_req_fits(FEnv.Req{["OPENAI_API_KEY"], ["GITHUB_TOKEN"], [Env.Var{"PATH", "0"}], [Env.Var{"HOME", "1"}]}) == True{} : Bool}

# The entry, spelled by the grammar Rust writes and reads
# (crates/eukhe-core/src/kernel/manager/startup.rs `child_env` and
# `read_env`), not by the entry's own encoders

# a variable: its name, then its value (a string each)
def env_spell_var(v: Env.Var, rest: String) -> String:
  match v:
    case Env.Var{n, x}:
      Wr.put_str(n, Wr.put_str(x, rest))

# the variables of xs, each spelled, then rest
def env_spell_vars.items(xs: List<&2, Env.Var>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      env_spell_var(x, env_spell_vars.items(t, rest))

# a list of variables: its count, then each variable
def env_spell_vars(+xs: List<&2, Env.Var>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Env.Var, xs), env_spell_vars.items(xs, rest))

# a request: the registry and the keep list (lists of strings), then the
# base and the overlay (lists of variables), then rest
def env_spell_req(q: FEnv.Req, rest: String) -> String:
  match q:
    case FEnv.Req{r, k, b, o}:
      LawsBase.wire_spell_strs(r, LawsBase.wire_spell_strs(k, env_spell_vars(b, env_spell_vars(o, rest))))

# the spelled reply of the model's decision on request q: the variables of
# the environment of the child
def env_spell_answer(q: FEnv.Req) -> String:
  match q:
    case FEnv.Req{r, k, b, o}:
      env_spell_vars(Env.child(r, k, b, o), "")

# LAW env_ffi_answers_spelled: a request spelled by the grammar, every count and length within
# the wire, is answered with the grammar's spelling of the environment of
# the child (Env.child of the registry, the keep list, the base and the
# overlay): its count, then each variable's name and value
# EXCLUDES: a field order, a variable's name and value, or a list count
#   that drifts from the grammar Rust reads and writes (swapped on both
#   sides of the entry alike); a field lost, swapped or defaulted
law env_ffi_answers_spelled:
  for +q: FEnv.Req
  for fits: {env_req_fits(q) == True{} : Bool}
  {FEnv.ffi(env_spell_req(q, "")) == env_spell_answer(q) : String}

# LAW env_ffi_left_over_spelled: a spelled request that fits, followed by any more input, answers
# the error form "child_env: input left over"
# EXCLUDES: trailing input ignored, read as part of the request, or
#   answered with the malformed error
law env_ffi_left_over_spelled:
  for +q: FEnv.Req
  for fits: {env_req_fits(q) == True{} : Bool}
  for +c: Char
  for +t: String
  {FEnv.ffi(env_spell_req(q, SCon{c, t})) == Wr.err("child_env: input left over") : String}

# LAW env_ffi_reads_only_requests: an answer that is not the error form answers a request: the
# input is exactly the spelling of a request whose counts and lengths fit
# the wire, and the answer is the spelled environment of the child
# EXCLUDES: a decoder that accepts a count larger or smaller than its
#   items, a short string, a missing or extra field, or input left over,
#   and answers it anyway (a default instead of the error form)
law env_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FEnv.ffi(s)) == False{} : Bool}
  exs q: FEnv.Req
  {(s, (env_req_fits(q), FEnv.ffi(s))) == (env_spell_req(q, ""), (True{}, env_spell_answer(q))) : String & (Bool & String)}

# LAW env_ffi_malformed_unless_request: every answer but the error form "child_env: malformed
# request" comes from an input that begins with a spelled request that fits
# EXCLUDES: the left-over error (or any answer) for input that does not
#   begin with a request, the malformed error spelled with another text
law env_ffi_malformed_unless_request:
  for +s: String
  for other: {String.eq(FEnv.ffi(s), Wr.err("child_env: malformed request")) == False{} : Bool}
  exs q: FEnv.Req
  exs rest: String
  {(s, env_req_fits(q)) == (env_spell_req(q, rest), True{}) : String & Bool}

# LAW env_ffi_tags_example: anchor: the bytes Rust sends and reads: a provider name X in the
# registry, no kept name, a base of X (value 0) and P (value 1), an
# overlay of P (value 2): only P with the overlay's value 2 reaches the
# child; nothing at all; a count larger than its items, a string shorter
# than its length, a missing list are malformed; a request with input left
# over is refused
# EXCLUDES: a grammar both sides of the Bend entry agree on but Rust does
#   not (a value before its name, a count after its items), a provider
#   name kept, the base's value over the overlay's
law env_ffi_tags_example:
  {[FEnv.ffi("1,1,X0,2,1,X1,01,P1,11,1,P1,2"), FEnv.ffi("0,0,0,0,"), FEnv.ffi("2,1,X"), FEnv.ffi("1,2,X"), FEnv.ffi("0,0,0,"), FEnv.ffi("0,0,0,0,x")] == ["1,1,P1,2", "0,", Wr.err("child_env: malformed request"), Wr.err("child_env: malformed request"), Wr.err("child_env: malformed request"), Wr.err("child_env: input left over")] : List<&2, String>}
