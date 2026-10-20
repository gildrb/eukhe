# child_env: the environment of a child the host starts for an agent.
# The Rust code is crates/eukhe-core/src/kernel/manager/startup.rs
# (`child_env`, with `is_credential_env_var` and
# `is_provider_credential_env_var` of crates/eukhe-ai/src/env_api_keys.rs).
#
# An environment is a list of variables (a name and a value). The child
# environment is the overlay over the base (a name of the overlay hides
# every variable of the base with that name), less every variable whose
# name does not pass:
#
#   - a name that is not a credential passes;
#   - a credential name passes only when the keep list holds it and it is
#     not a provider name (a name of the registry).
#
# A name is a credential when its ASCII upper case is a name of the
# registry, or contains one of the secret patterns. The `bash` tool's
# external steps get an empty keep list; a local kernel gets the names
# the user's own MCP config reads a credential from.

import Base

# One variable: its name and its value.
type Var is Data:
  Var{name: String, value: String}

def Var.name(v: Var) -> String:
  match v:
    case Var{n, x}:
      n

# x is in xs
def In(+x: Var, xs: List<&2, Var>) -> Type:
  match xs:
    case Nil{}:
      Empty
    case +w <> t:
      Or({x == w : Var}, In(x, t))

# Names
# -----

# the ASCII upper case of s (only a to z change)
def up(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      SCon{Char.to_upper(c), up(t)}

# A name whose upper case contains one of these is a credential.
def patterns() -> List<&2, String>:
  ["API_KEY", "APIKEY", "TOKEN", "SECRET", "PASSWORD", "PASSWD", "PASSPHRASE", "CREDENTIAL", "PRIVATE_KEY", "ACCESS_KEY"]

# u is one of the names of ns
def listed(ns: List<&2, String>, +u: String) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case r <> rest:
      Bool.or(String.eq(r, u), listed(rest, u))

# u contains one of ps
def matched(ps: List<&2, String>, +u: String) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> rest:
      Bool.or(String.contains(u, p), matched(rest, u))

# n is a provider name: its upper case is a name of the registry
def registered(reg: List<&2, String>, n: String) -> Bool:
  listed(reg, up(n))

# n is a credential name
def cred(+reg: List<&2, String>, n: String) -> Bool:
  +u = up(n)
  Bool.or(listed(reg, u), matched(patterns(), u))

# n reaches the child: not a credential, or kept and not a provider name
def passes(+reg: List<&2, String>, keep: List<&2, String>, +n: String) -> Bool:
  Bool.or(Bool.not(cred(reg, n)), Bool.and(listed(keep, n), Bool.not(registered(reg, n))))

# Environments
# ------------

# n is the name of a variable of xs
def named(+n: String, xs: List<&2, Var>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case v <> rest:
      Bool.or(String.eq(Var.name(v), n), named(n, rest))

def under.put(hit: Bool, v: Var, r: List<&2, Var>) -> List<&2, Var>:
  match hit:
    case True{}:
      r
    case False{}:
      v <> r

# the variables of base whose name the overlay does not name
def under(base: List<&2, Var>, +over: List<&2, Var>) -> List<&2, Var>:
  match base:
    case Nil{}:
      Nil{}
    case +v <> rest:
      under.put(named(Var.name(v), over), v, under(rest, over))

# the overlay over the base
def merge(base: List<&2, Var>, +over: List<&2, Var>) -> List<&2, Var>:
  List.append(&2, Var, over, under(base, over))

def keep.put(ok: Bool, v: Var, r: List<&2, Var>) -> List<&2, Var>:
  match ok:
    case True{}:
      v <> r
    case False{}:
      r

# the variables of xs whose name passes
def keep(+reg: List<&2, String>, +ks: List<&2, String>, xs: List<&2, Var>) -> List<&2, Var>:
  match xs:
    case Nil{}:
      Nil{}
    case +v <> rest:
      keep.put(passes(reg, ks, Var.name(v)), v, keep(reg, ks, rest))

# the environment of a child: the overlay over the base, less every
# variable whose name does not pass
def child(+reg: List<&2, String>, +ks: List<&2, String>, base: List<&2, Var>, over: List<&2, Var>) -> List<&2, Var>:
  keep(reg, ks, merge(base, over))
