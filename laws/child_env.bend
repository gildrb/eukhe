# eukhe: the laws of area child_env

import Base
import ../bend/child_env.bend as Env
import ../bend/ffi_child_env.bend as FEnv
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- child_env ----

# LAWS (docs/tools.md S7 item 7, the environment of an external process
# and of a local kernel): no credential reaches a child. Each law is an
# open claim about the model in bend/child_env.bend; PROOF.bend proves them
# (as ChildEnv.<law>) with the lemmas of proof/child_env/.

# (S7 item 7) No credential reaches a child
# -----------------------------------------
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

# The environment of a child, whole
# ----------------------------------
# Written from the requirement (G3; crates/eukhe-ai/src/env_api_keys.rs,
# the header of bend/child_env.bend), never calling the model. The laws
# above read the model's own terms (Env.cred, Env.registered, Env.listed,
# Env.merge, Env.In) and pin properties of Env.child; these pin each term
# and Env.child to the spec, so a wrong term cannot make them vacuous and
# the order and repeats of the environment are pinned too.

# the ASCII upper case of s: a to z become A to Z (Base's Char.to_upper),
# every other char stays
def ce_up(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      SCon{Char.to_upper(c), ce_up(t)}

# u is one of the names ns, char for char
def ce_has(ns: List<&2, String>, +u: String) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case r <> t:
      Bool.or(String.eq(r, u), ce_has(t, u))

# the secret patterns of env_api_keys.rs
def ce_pats() -> List<&2, String>:
  ["API_KEY", "APIKEY", "TOKEN", "SECRET", "PASSWORD", "PASSWD", "PASSPHRASE", "CREDENTIAL", "PRIVATE_KEY", "ACCESS_KEY"]

# u contains one of the patterns ps
def ce_hits(ps: List<&2, String>, +u: String) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> t:
      Bool.or(String.contains(u, p), ce_hits(t, u))

# n is a provider name: its upper case is a name of the registry
def ce_provider(reg: List<&2, String>, n: String) -> Bool:
  ce_has(reg, ce_up(n))

# n is a credential name: its upper case is a provider name, or contains
# a secret pattern
def ce_cred(+reg: List<&2, String>, n: String) -> Bool:
  +u = ce_up(n)
  Bool.or(ce_has(reg, u), ce_hits(ce_pats(), u))

# n reaches the child: it is no credential, or it is no provider name and
# the keep list holds it
def ce_passes(+reg: List<&2, String>, keep: List<&2, String>, +n: String) -> Bool:
  Bool.or(Bool.not(ce_cred(reg, n)), Bool.and(Bool.not(ce_provider(reg, n)), ce_has(keep, n)))

# n is the name of a variable of xs
def ce_named(+n: String, xs: List<&2, Env.Var>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Env.Var{m, x} <> t:
      Bool.or(String.eq(m, n), ce_named(n, t))

def ce_hidden.pick(hit: Bool, v: Env.Var, r: List<&2, Env.Var>) -> List<&2, Env.Var>:
  match hit:
    case True{}:
      r
    case False{}:
      v <> r

# the variables of base, in order, whose name the overlay does not name
def ce_hidden(base: List<&2, Env.Var>, +over: List<&2, Env.Var>) -> List<&2, Env.Var>:
  match base:
    case Nil{}:
      Nil{}
    case Env.Var{+m, +x} <> t:
      ce_hidden.pick(ce_named(m, over), Env.Var{m, x}, ce_hidden(t, over))

# the overlay over the base: the overlay, then the base's variables it
# does not hide
def ce_merge(base: List<&2, Env.Var>, +over: List<&2, Env.Var>) -> List<&2, Env.Var>:
  List.append(&2, Env.Var, over, ce_hidden(base, over))

def ce_keep.pick(ok: Bool, v: Env.Var, r: List<&2, Env.Var>) -> List<&2, Env.Var>:
  match ok:
    case True{}:
      v <> r
    case False{}:
      r

# the variables of xs, in order, whose name passes
def ce_keep(+reg: List<&2, String>, +keep: List<&2, String>, xs: List<&2, Env.Var>) -> List<&2, Env.Var>:
  match xs:
    case Nil{}:
      Nil{}
    case Env.Var{+m, +x} <> t:
      ce_keep.pick(ce_passes(reg, keep, m), Env.Var{m, x}, ce_keep(reg, keep, t))

# the environment of a child: the overlay over the base, less every
# variable whose name does not pass
def ce_child(+reg: List<&2, String>, +keep: List<&2, String>, base: List<&2, Env.Var>, over: List<&2, Env.Var>) -> List<&2, Env.Var>:
  ce_keep(reg, keep, ce_merge(base, over))

# x is a variable of xs
def ce_in(+x: Env.Var, xs: List<&2, Env.Var>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case +w <> t:
      Or({x == w : Env.Var}, ce_in(x, t))

# LAW env_child_exact: the environment of a child is exactly the overlay (in order), then the base's variables (in order) whose name the overlay does not name, less every variable whose name is a credential (its ASCII upper case is a provider name or contains a secret pattern) unless the keep list holds the name and it is no provider name
# EXCLUDES: a variable dropped that passes, kept that does not, reordered,
#   repeated, or with another value; a credential test by another rule
law env_child_exact:
  for +reg: List<&2, String>
  for +keep: List<&2, String>
  for +base: List<&2, Env.Var>
  for +over: List<&2, Env.Var>
  {Env.child(reg, keep, base, over) == ce_child(reg, keep, base, over) : List<&2, Env.Var>}

# LAW env_terms_exact: the model's terms the laws above read mean what the spec says: cred, registered, listed, merge and In
# EXCLUDES: a credential, provider or membership test that makes the G3
#   laws above hold vacuously (always False, case-sensitive, a merge that
#   drops the overlay)
law env_terms_exact:
  for +reg: List<&2, String>
  for +ns: List<&2, String>
  for +n: String
  for +base: List<&2, Env.Var>
  for +over: List<&2, Env.Var>
  for +v: Env.Var
  {Env.cred(reg, n) == ce_cred(reg, n) : Bool} & {Env.registered(reg, n) == ce_provider(reg, n) : Bool} & {Env.listed(ns, n) == ce_has(ns, n) : Bool} & {Env.merge(base, over) == ce_merge(base, over) : List<&2, Env.Var>} & {Env.In(v, over) == ce_in(v, over) : Type}

# ---- child_env_entry ----

# LAWS (docs/tools.md S7 item 7, the compiled core): the entry bend/ffi_child_env.bend runs the
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


# The entry, whole
# ----------------
# The request and the reply as Rust writes and reads them (the header of
# bend/ffi_child_env.bend), spelled and read with the wire primitives and
# these helpers alone, never the entry's encoders or decoders, and
# answered with ce_child. With env_ffi_exact every input's answer follows:
# a reply that is no error is ce_child of the request the input spells;
# every error is one of the two error texts.

def ce_spell_var(v: Env.Var, rest: String) -> String:
  match v:
    case Env.Var{n, x}:
      Wr.put_str(n, Wr.put_str(x, rest))

# the request Rust writes for q, then rest
def ce_spell_req(q: FEnv.Req, rest: String) -> String:
  match q:
    case FEnv.Req{r, k, b, o}:
      Wr.put_list(~String, ~Wr.put_str, r, Wr.put_list(~String, ~Wr.put_str, k, Wr.put_list(~Env.Var, ~ce_spell_var, b, Wr.put_list(~Env.Var, ~ce_spell_var, o, rest))))

# the reply to q: the variables of the spec's environment of the child
def ce_reply(q: FEnv.Req) -> String:
  match q:
    case FEnv.Req{r, k, b, o}:
      Wr.put_list(~Env.Var, ~ce_spell_var, ce_child(r, k, b, o), "")

def ce_read_var.value(n: String, d: Wr.Dec<String>) -> Wr.Dec<Env.Var>:
  match d:
    case Wr.Got{x, s}:
      Wr.Got{Env.Var{n, x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_var.name(d: Wr.Dec<String>) -> Wr.Dec<Env.Var>:
  match d:
    case Wr.Got{n, s}:
      ce_read_var.value(n, Wr.get_str(s))
    case Wr.Bad{}:
      Wr.Bad{}

# a variable: its name, then its value
def ce_read_var(s: String) -> Wr.Dec<Env.Var>:
  ce_read_var.name(Wr.get_str(s))

def ce_read_req.over(r: List<&2, String>, k: List<&2, String>, b: List<&2, Env.Var>, d: Wr.Dec<List<&2, Env.Var>>) -> Wr.Dec<FEnv.Req>:
  match d:
    case Wr.Got{o, s}:
      Wr.Got{FEnv.Req{r, k, b, o}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_req.base(r: List<&2, String>, k: List<&2, String>, d: Wr.Dec<List<&2, Env.Var>>) -> Wr.Dec<FEnv.Req>:
  match d:
    case Wr.Got{b, s}:
      ce_read_req.over(r, k, b, Wr.get_list(~Env.Var, ~ce_read_var, s))
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_req.keep(r: List<&2, String>, d: Wr.Dec<List<&2, String>>) -> Wr.Dec<FEnv.Req>:
  match d:
    case Wr.Got{k, s}:
      ce_read_req.base(r, k, Wr.get_list(~Env.Var, ~ce_read_var, s))
    case Wr.Bad{}:
      Wr.Bad{}

def ce_read_req.reg(d: Wr.Dec<List<&2, String>>) -> Wr.Dec<FEnv.Req>:
  match d:
    case Wr.Got{r, s}:
      ce_read_req.keep(r, Wr.get_list(~String, ~Wr.get_str, s))
    case Wr.Bad{}:
      Wr.Bad{}

# the request at the start of s: the registry, the keep list, the base,
# the overlay
def ce_read_req(s: String) -> Wr.Dec<FEnv.Req>:
  ce_read_req.reg(Wr.get_list(~String, ~Wr.get_str, s))

def ce_entry.end(done: Bool, q: FEnv.Req) -> String:
  match done:
    case True{}:
      ce_reply(q)
    case False{}:
      Wr.err("child_env: input left over")

def ce_entry.go(d: Wr.Dec<FEnv.Req>) -> String:
  match d:
    case Wr.Got{q, s}:
      ce_entry.end(Wr.end(s), q)
    case Wr.Bad{}:
      Wr.err("child_env: malformed request")

# the entry's answer to s: the reply to the request s is, when nothing is
# left after it; else one of the two error texts
def ce_entry(s: String) -> String:
  ce_entry.go(ce_read_req(s))

# LAW env_ffi_exact: on every input the entry answers the spec: the spec's environment of the child, spelled, for the request the input spells (read by the spec's reader with the wire primitives) when nothing is left after it; `E child_env: input left over` when input is left; `E child_env: malformed request` for any other input
# EXCLUDES: an answer for an input that spells no request, a request read
#   otherwise than the grammar spells it, an environment other than the
#   spec's, a reply spelled otherwise, an error text that varies
law env_ffi_exact:
  for +s: String
  {FEnv.ffi(s) == ce_entry(s) : String}

# LAW env_ffi_spelled: every request Rust writes whose numbers fit the wire, spelled by the spec, gets the spec's environment of the child
# EXCLUDES: a request Rust writes refused or answered for another request
law env_ffi_spelled:
  for +q: FEnv.Req
  for h: {env_req_fits(q) == True{} : Bool}
  {FEnv.ffi(ce_spell_req(q, "")) == ce_reply(q) : String}

# LAW env_ffi_spec_example: anchor: the spec answers the grammar's bytes: the overlay's X first, then the base's PATH; the base's provider name A dropped; a 15-digit count and input left over refused
# EXCLUDES: a vacuous env_ffi_exact (a spec that refuses everything)
law env_ffi_spec_example:
  {[ce_entry("1,1,A0,2,4,PATH1,01,A1,11,1,X1,2"), ce_entry("123456789012345,"), ce_entry("0,0,0,0,x")] == ["2,1,X1,24,PATH1,0", Wr.err("child_env: malformed request"), Wr.err("child_env: input left over")] : List<&2, String>}
