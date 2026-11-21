# eukhe: the laws of area path_policy: the effects of an access

import Base
import ../../bend/path_policy.bend as Pp

# ---- path_policy gate ----

# LAWS (G1): the effects of an access to a judged path. Each law is an
# open claim about the model in bend/path_policy.bend; PROOF.bend proves
# them (as PathPolicyGate.<law>) with the lemmas of proof/path_policy/.

# (G1) The effects table
# ----------------------
# gate_effs_exact pins the effects of every access with the spec helpers
# here, which never call the model: a model whose read of a secret lacks
# the secret effect fails it (an adversary found this gap). Effects: 0
# read, 1 write, 4 outside, 5 protected, 6 secret.

# the class is Secret
def pp_cls_secret(c: Pp.Cls) -> Bool:
  match c:
    case Pp.Inside{}:
      False{}
    case Pp.Outside{}:
      False{}
    case Pp.Protected{}:
      False{}
    case Pp.Secret{}:
      True{}

# a read's effects: read, and secret when it reads a secret (docs/tools.md
# G1.5, codes S7 item 8: read 0, secret 6)
def pp_read_effs(sec: Bool) -> List<&2, Nat>:
  match sec:
    case True{}:
      # G1.5 "read or list ... of a Secret path, read and secret" and
      # "search ... of a path that is or holds a secret: read and secret"
      [0n, 6n]
    case False{}:
      # G1.5 "read or list: read" and "search of any other path: read"
      [0n]

# a write's effects by the class (docs/tools.md G1.5; codes S7 item 8:
# write 1, outside 4, protected 5, secret 6)
def pp_write_effs(c: Pp.Cls) -> List<&2, Nat>:
  match c:
    case Pp.Inside{}:
      # G1.5 "write Inside: write"
      [1n]
    case Pp.Outside{}:
      # G1.5 "write Outside: write and outside"
      [1n, 4n]
    case Pp.Protected{}:
      # G1.5 "write Protected: write and protected"
      [1n, 5n]
    case Pp.Secret{}:
      # G1.5 "write Secret: write and secret"
      [1n, 6n]

# the effects of access a to a path of class c, row by row of the G1.5 table
def pp_effs(c: Pp.Cls, a: Pp.Acc) -> List<&2, Nat>:
  match a:
    case Pp.Rd{}:
      # G1.5 "read or list": a read of a Secret path reads the secret
      pp_read_effs(pp_cls_secret(c))
    case Pp.Ls{}:
      # G1.5 "read or list": the same row as a read
      pp_read_effs(pp_cls_secret(c))
    case Pp.Sr{h}:
      # G1.5 "search ... of a path that is (Secret) or holds (h) a
      # secret", else "search of any other path"
      pp_read_effs(Bool.or(h, pp_cls_secret(c)))
    case Pp.Wr{}:
      # G1.5 "write <class>"
      pp_write_effs(c)

# LAW gate_effs_exact: the effects of every access to a path of every class are exactly pp_effs
# EXCLUDES: a read of a secret without the secret effect, a write
#   outside the workspace or to a protected path without its effect, an
#   effect renumbered
law gate_effs_exact:
  for c: Pp.Cls
  for a: Pp.Acc
  {Pp.effs(c, a) == pp_effs(c, a) : List<&2, Nat>}
