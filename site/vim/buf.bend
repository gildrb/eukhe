# eukhe.com's Neovim: buffers and folders
# =======================================
#
# The files the editor holds, their lines, and Oil's folder listings.

import Base
import ./types.bend as T
import ./text.bend as X

# Lines
# -----

def Lines.len.go(ls: List<&2, String>, acc: Nat) -> Nat:
  match ls:
    case Nil{}:
      acc
    case Con{h, t}:
      Lines.len.go(t, 1n+acc)

# the lines in ls
def Lines.len(ls: List<&2, String>) -> Nat:
  Lines.len.go(ls, 0n)

# line i of ls; "" past the end
def Lines.at(ls: List<&2, String>, i: Nat) -> String:
  match ls i:
    case Nil{} _:
      SNil{}
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+p:
      Lines.at(t, p)

# ls from line i on
def Lines.drop(ls: List<&2, String>, i: Nat) -> List<&2, String>:
  match ls i:
    case Nil{} _:
      Nil{}
    case Con{h, t} 0n:
      Con{h, t}
    case Con{h, t} 1n+p:
      Lines.drop(t, p)

def Lines.take.go(ls: List<&2, String>, n: Nat, acc: List<&2, String>) -> List<&2, String>:
  match ls n:
    case Nil{} _:
      List.reverse(&2, String, acc)
    case Con{h, t} 0n:
      List.reverse(&2, String, acc)
    case Con{h, t} 1n+p:
      Lines.take.go(t, p, h <> acc)

# the first n lines of ls
def Lines.take(ls: List<&2, String>, n: Nat) -> List<&2, String>:
  Lines.take.go(ls, n, Nil{})

# at least one line: an empty file holds one empty line, as in Vim
def Lines.some(ls: List<&2, String>) -> List<&2, String>:
  match ls:
    case Nil{}:
      [""]
    case Con{h, t}:
      Con{h, t}

# Files
# -----

def Buf.path(b: T.Buf) -> String:
  match b:
    case T.Buf{path, lines}:
      path

def Buf.lines(b: T.Buf) -> List<&2, String>:
  match b:
    case T.Buf{path, lines}:
      lines

def Files.len.go(fs: List<&2, T.Buf>, acc: Nat) -> Nat:
  match fs:
    case Nil{}:
      acc
    case Con{h, t}:
      Files.len.go(t, 1n+acc)

# the files held
def Files.len(fs: List<&2, T.Buf>) -> Nat:
  Files.len.go(fs, 0n)

# file i; an empty file named "" past the end
def Files.at(fs: List<&2, T.Buf>, i: Nat) -> T.Buf:
  match fs i:
    case Nil{} _:
      T.Buf{"", [""]}
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+p:
      Files.at(t, p)

def Files.find.go(fs: List<&2, T.Buf>, +path: String, +i: Nat) -> Maybe<&2, Nat>:
  match fs:
    case Nil{}:
      None{}
    case Con{T.Buf{p, ls}, t}:
      X.Bool.when(Maybe<&2, Nat>, String.eq(p, path), u => Files.find.go(t, path, 1n+i), u => Some{i})

# the number of the file at path
def Files.find(fs: List<&2, T.Buf>, path: String) -> Maybe<&2, Nat>:
  Files.find.go(fs, path, 0n)

# each file with at least one line
def Files.some(fs: List<&2, T.Buf>, acc: List<&2, T.Buf>) -> List<&2, T.Buf>:
  match fs:
    case Nil{}:
      List.reverse(&2, T.Buf, acc)
    case Con{T.Buf{p, ls}, t}:
      Files.some(t, T.Buf{p, Lines.some(ls)} <> acc)

# Folders (Oil)
# -------------

def Path.slash.go(s: String, n: Nat, +i: Nat) -> Maybe<&2, Nat>:
  match s:
    case SNil{}:
      None{}
    case SCon{h, t}:
      X.Bool.when(Maybe<&2, Nat>, Char.is_eq(h, '/'), u => Path.slash.go(t, n, 1n+i), u => Some{i})

def Path.name.at(+rest: String, at: Maybe<&2, Nat>) -> String:
  match at:
    case None{}:
      rest
    case Some{i}:
      X.Text.take(rest, 1n+i)

def Path.name(+rest: String) -> String:
  Path.name.at(rest, Path.slash.go(rest, 0n, 0n))

# the entry path shows in folder dir: its next name, with a "/" when it is
# a folder; "" when path is not inside dir
def Path.child(+dir: String, +path: String) -> String:
  X.Bool.when(String, X.Text.prefix(dir, path), u => "", u => Path.name(X.Text.drop(path, X.Text.len(dir))))

# whether an entry is a folder: it ends in "/"
def Path.is_dir(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{h, SNil{}}:
      Char.is_eq(h, '/')
    case SCon{h, t}:
      Path.is_dir(t)

def Path.dir.go(s: String, +acc: String, +cut: String) -> String:
  match s:
    case SNil{}:
      String.reverse(cut)
    case SCon{+h, +t}:
      X.Bool.when(String, Char.is_eq(h, '/'), u => Path.dir.go(t, SCon{h, acc}, cut), u => Path.dir.go(t, SCon{h, acc}, SCon{h, acc}))

# the folder holding path: up to its last "/", or "" (the root)
def Path.dir(s: String) -> String:
  Path.dir.go(s, SNil{}, SNil{})

def Path.up.go(s: String, +acc: String, +cut: String) -> String:
  match s:
    case SNil{}:
      String.reverse(cut)
    case SCon{+h, SNil{}}:
      String.reverse(cut)
    case SCon{+h, +t}:
      X.Bool.when(String, Char.is_eq(h, '/'), u => Path.up.go(t, SCon{h, acc}, cut), u => Path.up.go(t, SCon{h, acc}, SCon{h, acc}))

# the folder above folder dir ("docs/" -> ""; "" stays "")
def Path.up(s: String) -> String:
  Path.up.go(s, SNil{}, SNil{})

def Oil.add(+e: String, out: List<&2, String>) -> List<&2, String>:
  match out:
    case Nil{}:
      X.Bool.when(List<&2, String>, String.is_empty(e), u => [e], u => Nil{})
    case Con{+h, +t}:
      X.Bool.when(List<&2, String>, Bool.or(String.is_empty(e), String.eq(h, e)), u => e <> h <> t, u => h <> t)

def Oil.collect(fs: List<&2, T.Buf>, +dir: String, +dirs: Bool, +out: List<&2, String>) -> List<&2, String>:
  match fs:
    case Nil{}:
      out
    case Con{T.Buf{p, ls}, t}:
      +e = Path.child(dir, p)
      +keep = Bool.not(Bool.xor(Path.is_dir(e), dirs))
      Oil.collect(t, dir, dirs, Bool.pick(List<&2, String>, keep, Oil.add(e, out), out))

def Oil.le.go(+a: String, +b: String) -> Bool:
  +fa = X.Text.fold(a)
  +fb = X.Text.fold(b)
  Bool.or(String.is_lt(fa, fb), Bool.and(String.eq(fa, fb), String.is_le(a, b)))

# Oil's order (view_options.case_insensitive): names compared in lower
# case, then as they are
def Oil.le(a: String, b: String) -> Bool:
  Oil.le.go(a, b)

def Oil.uniq(xs: List<&2, String>, out: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      List.reverse(&2, String, out)
    case Con{+x, t}:
      Oil.uniq(t, Oil.add(x, out))

# the entries of folder dir, as Oil lists them: "../" (in the root too, as
# Oil shows it at "/"), folders, then files, each in name order
def Oil.list(+fs: List<&2, T.Buf>, +dir: String) -> List<&2, String>:
  +ds = List.sort(~String, ~Oil.le, Oil.collect(fs, dir, True{}, Nil{}))
  +fl = List.sort(~String, ~Oil.le, Oil.collect(fs, dir, False{}, Nil{}))
  +es = List.append(&2, String, Oil.uniq(ds, Nil{}), Oil.uniq(fl, Nil{}))
  "../" <> es

# Targets
# -------

# the lines target t shows
def Tgt.lines(+fs: List<&2, T.Buf>, t: T.Tgt) -> List<&2, String>:
  match t:
    case T.File{i}:
      Buf.lines(Files.at(fs, i))
    case T.Dir{path}:
      Oil.list(fs, path)

# the name the statusline shows for target t: the file's path, or Oil's
# "oil:///" and the folder
def Tgt.name(+fs: List<&2, T.Buf>, t: T.Tgt) -> String:
  match t:
    case T.File{i}:
      Buf.path(Files.at(fs, i))
    case T.Dir{path}:
      "oil:///" ++ path

# whether a path of fs starts with d (d is a folder holding a file)
def Files.under(+d: String, fs: List<&2, T.Buf>) -> Bool:
  match fs:
    case Nil{}:
      False{}
    case Con{T.Buf{p, ls}, t}:
      Bool.or(X.Text.prefix(d, p), Files.under(d, t))

# whether the window may show target t over files fs: one of them (file 0
# when there are none), the root, or a folder of their paths
def Tgt.real(+fs: List<&2, T.Buf>, t: T.Tgt) -> Bool:
  match t:
    case T.File{i}:
      Nat.is_lt(i, Nat.max(Files.len(fs), 1n))
    case T.Dir{+d}:
      Bool.or(String.is_empty(d), Bool.and(Path.is_dir(d), Files.under(d, fs)))
