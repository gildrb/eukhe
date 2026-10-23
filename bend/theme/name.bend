# theme: the candidates a theme name resolves over, and name resolution with the default fallback

import Base

# Name resolution
# ---------------
# The candidates in lookup order: the registered files, the builtins, the
# custom directory's files. A candidate is a theme file (or a builtin) by
# the name it advertises; an invalid file never resolves. id tells the
# candidates apart (the builtins are 0 eukhe, 1 dark, 2 light).

type Cand is Data:
  Cand{name: String, valid: Bool, id: U32}

type Res is Data:
  Res{id: U32, warned: Bool}

def builtins() -> List<&2, Cand>:
  [Cand{"eukhe", True{}, 0}, Cand{"dark", True{}, 1}, Cand{"light", True{}, 2}]

def sources(reg: List<&2, Cand>, custom: List<&2, Cand>) -> List<&2, Cand>:
  List.append(&2, Cand, reg, List.append(&2, Cand, builtins(), custom))

# the default theme
def dflt() -> U32:
  0

# a candidate resolves name n
def names(c: Cand, +n: String) -> Bool:
  match c:
    case Cand{name, valid, id}:
      Bool.and(valid, String.eq(name, n))

def find.pick(hit: Bool, id: U32, other: Res) -> Res:
  match hit:
    case True{}:
      Res{id, False{}}
    case False{}:
      other

def find(src: List<&2, Cand>, +n: String) -> Res:
  match src:
    case Nil{}:
      Res{dflt(), True{}}
    case Con{Cand{name, valid, +id}, rest}:
      find.pick(names(Cand{name, valid, id}, n), id, find(rest, n))

def resolve.name.pick(empty: Bool, src: List<&2, Cand>, +n: String) -> Res:
  match empty:
    case True{}:
      Res{dflt(), False{}}
    case False{}:
      find(src, n)

# resolve name n: the empty name is the default theme; else the first
# candidate that resolves it; else the default theme, with a warning
def resolve.name(src: List<&2, Cand>, +n: String) -> Res:
  resolve.name.pick(String.is_empty(n), src, n)

# some candidate of src resolves n
def hit(src: List<&2, Cand>, +n: String) -> Bool:
  match src:
    case Nil{}:
      False{}
    case Con{c, rest}:
      Bool.or(names(c, n), hit(rest, n))
