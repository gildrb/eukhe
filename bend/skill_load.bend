# skill_load: what the skill and prompt template loaders do with each
# candidate file. The Rust code is crates/eukhe-core/src/skills/
# (`load_skills_from_dir` and `load_skill_from_file` in discovery.rs,
# `load_prompt_templates` in prompt_templates.rs).
#
# A candidate is a file the loader found (a SKILL.md, a root `.md` skill,
# a template `.md`), with its path and how reading it ends:
#
#   - good: the file loads; its path joins the loaded list;
#   - unreadable: the file or its metadata is not read (a read error,
#     text that is not UTF-8, a dangling link): a diagnostic with its
#     path, kind 0;
#   - malformed: its frontmatter is not valid YAML: a diagnostic with its
#     path, kind 1;
#   - incomplete: a skill without a description: a diagnostic with its
#     path, kind 2.
#
# No candidate is dropped without a word.

import Base

type Outcome is Data:
  Good{}
  Unreadable{}
  Malformed{}
  Incomplete{}

# One candidate file: its path and how reading it ends.
type Cand is Data:
  Cand{path: Nat, o: Outcome}

# One diagnostic: the path it names and its kind.
type Diag is Data:
  Diag{path: Nat, kind: Nat}

def Cand.path(c: Cand) -> Nat:
  match c:
    case Cand{p, o}:
      p

def Diag.path(d: Diag) -> Nat:
  match d:
    case Diag{p, k}:
      p

# c is in cs
def In(+c: Cand, cs: List<&2, Cand>) -> Type:
  match cs:
    case Nil{}:
      Empty
    case +x <> rest:
      Or({c == x : Cand}, In(c, rest))

# The loader
# ----------

# the paths of the candidates that load
def loaded(cs: List<&2, Cand>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> rest:
      match c:
        case Cand{p, o}:
          match o:
            case Good{}:
              p <> loaded(rest)
            case Unreadable{}:
              loaded(rest)
            case Malformed{}:
              loaded(rest)
            case Incomplete{}:
              loaded(rest)

# the diagnostics of the candidates that do not load
def diags(cs: List<&2, Cand>) -> List<&2, Diag>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> rest:
      match c:
        case Cand{p, o}:
          match o:
            case Good{}:
              diags(rest)
            case Unreadable{}:
              Diag{p, 0n} <> diags(rest)
            case Malformed{}:
              Diag{p, 1n} <> diags(rest)
            case Incomplete{}:
              Diag{p, 2n} <> diags(rest)

# The lists
# ---------

# the paths the diagnostics ds name
def named(ds: List<&2, Diag>) -> List<&2, Nat>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> rest:
      Diag.path(d) <> named(rest)

# the paths of the candidates cs
def paths(cs: List<&2, Cand>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> rest:
      Cand.path(c) <> paths(rest)

# n is in ns
def listed(ns: List<&2, Nat>, +n: Nat) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case x <> rest:
      Bool.or(Nat.is_eq(x, n), listed(rest, n))

# no two candidates of cs share a path
def distinct(cs: List<&2, Cand>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case +c <> +rest:
      Bool.and(Bool.not(listed(paths(rest), Cand.path(c))), distinct(rest))
