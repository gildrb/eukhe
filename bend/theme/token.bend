# theme: what each token needs of a file: its role, its entry, the required-token check, its concrete color

import Base
import ../color.bend as Co
import ./file.bend as TFile

# Tokens
# ------

type Role is Data:
  Req{}
  MdBody{}
  RefHeader{}
  RefSummary{}
  Background{}
  Foreground{}

def kind.pick(t14: Bool, t15: Bool, t18: Bool, t57: Bool, t58: Bool) -> Role:
  match t14:
    case True{}:
      RefHeader{}
    case False{}:
      match t15:
        case True{}:
          RefSummary{}
        case False{}:
          match t18:
            case True{}:
              MdBody{}
            case False{}:
              match t57:
                case True{}:
                  Background{}
                case False{}:
                  match t58:
                    case True{}:
                      Foreground{}
                    case False{}:
                      Req{}

def kind(+t: U32) -> Role:
  kind.pick(U32.is_eq(t, 14), U32.is_eq(t, 15), U32.is_eq(t, 18), U32.is_eq(t, 57), U32.is_eq(t, 58))

# a surface token (48..57): the terminal default there is the background
def surface(+t: U32) -> Bool:
  Bool.and(U32.is_ge(t, 48), U32.is_le(t, 57))

def toks() -> List<&2, U32>:
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58]

def get.pick(hit: Bool, v: TFile.Val, other: Maybe<&2, TFile.Val>) -> Maybe<&2, TFile.Val>:
  match hit:
    case True{}:
      Some{v}
    case False{}:
      other

# the value a file gives token t (the first entry for it)
def get(cols: List<&2, TFile.Ent>, +t: U32) -> Maybe<&2, TFile.Val>:
  match cols:
    case Nil{}:
      None{}
    case Con{TFile.Ent{k, v}, rest}:
      get.pick(U32.is_eq(k, t), v, get(rest, t))

def has(+cols: List<&2, TFile.Ent>, +t: U32) -> Bool:
  Maybe.is_some(&2, TFile.Val, get(cols, t))

# what token t of role k needs of a file: a required token its own entry,
# mdBody its own entry or text's (9); the others nothing
def ok.k(k: Role, +cols: List<&2, TFile.Ent>, +t: U32) -> Bool:
  match k:
    case Req{}:
      has(cols, t)
    case MdBody{}:
      Bool.or(has(cols, t), has(cols, 9))
    case RefHeader{}:
      True{}
    case RefSummary{}:
      True{}
    case Background{}:
      True{}
    case Foreground{}:
      True{}

def ok(+cols: List<&2, TFile.Ent>, +t: U32) -> Bool:
  ok.k(kind(t), cols, t)

def valid.go(+cols: List<&2, TFile.Ent>, ts: List<&2, U32>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case Con{t, rest}:
      Bool.and(ok(cols, t), valid.go(cols, rest))

# a file is valid when it writes every required token
def valid(f: TFile.Th) -> Bool:
  match f:
    case TFile.Th{name, cols, page, card, info}:
      valid.go(cols, toks())

# the color a value paints where the terminal cannot be asked; None for
# the terminal default
def concrete(v: TFile.Val) -> Maybe<&2, Co.Rgb>:
  match v:
    case TFile.Dflt{}:
      None{}
    case TFile.Idx{i}:
      Some{Co.ansi256(i)}
    case TFile.Hex{c}:
      Some{c}
