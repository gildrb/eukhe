# eukhe: the proof of LAW theme_valid_missing. When the file writes text
# (token 9), each token's test is "not a required token left unwritten"
# (tvm.role, one case per role: mdBody's fallback to text holds), and the
# fold over the tokens is the emptiness of the missing list (tvm.go). When
# it does not, token 9 fails both: valid is False (tvm.vf) and the missing
# list holds 9 (tvm.mf), splitting the tokens at 9.

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/token.bend as TToken
import ../../bend/theme/reader.bend as TReader
import ../../bend/theme/palette.bend as TPalette
import ../../laws/theme_model.bend as ThemeModel

def tvm.notnot(b: Bool) -> {b == Bool.not(Bool.not(b)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def tvm.or_true(b: Bool) -> {Bool.or(b, True{}) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def tvm.and_false(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def tvm.and_assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def tvm.role(k: TToken.Role, +cols: List<&2, TFile.Ent>, +t: U32, h9: {TToken.has(cols, 9) == True{} : Bool}) -> {TToken.ok.k(k, cols, t) == Bool.not(Bool.and(TReader.required.k(k), Bool.not(TToken.has(cols, t)))) : Bool}:
  match k:
    case TToken.Req{}:
      tvm.notnot(TToken.has(cols, t))
    case TToken.MdBody{}:
      %Equal.sym(Bool, TToken.has(cols, 9), True{}, h9) : {Bool.or(TToken.has(cols, t), _) == True{} : Bool}
      tvm.or_true(TToken.has(cols, t))
    case TToken.RefHeader{}:
      {==}
    case TToken.RefSummary{}:
      {==}
    case TToken.Background{}:
      {==}
    case TToken.Foreground{}:
      {==}

def tvm.keep(b: Bool, -t: U32, -r: List<&2, U32>) -> {List.is_empty(&2, U32, TReader.missing.keep(b, t, r)) == Bool.and(Bool.not(b), List.is_empty(&2, U32, r)) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def tvm.go(+cols: List<&2, TFile.Ent>, ts: List<&2, U32>, +h9: {TToken.has(cols, 9) == True{} : Bool}) -> {TToken.valid.go(cols, ts) == List.is_empty(&2, U32, TReader.missing.go(cols, ts)) : Bool}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, rest}:
      +b = Bool.and(TReader.required(t), Bool.not(TToken.has(cols, t)))
      %Equal.sym(Bool, List.is_empty(&2, U32, TReader.missing.keep(b, t, TReader.missing.go(cols, rest))), Bool.and(Bool.not(b), List.is_empty(&2, U32, TReader.missing.go(cols, rest))), tvm.keep(b, t, TReader.missing.go(cols, rest))) : {Bool.and(TToken.ok(cols, t), TToken.valid.go(cols, rest)) == _ : Bool}
      %tvm.go(cols, rest, h9) : {Bool.and(TToken.ok(cols, t), TToken.valid.go(cols, rest)) == Bool.and(Bool.not(b), _) : Bool}
      %tvm.role(TToken.kind(t), cols, t, h9) : {Bool.and(TToken.ok(cols, t), TToken.valid.go(cols, rest)) == Bool.and(_, TToken.valid.go(cols, rest)) : Bool}
      {==}

# the tokens before 9 and after it
def tvm.lo() -> List<&2, U32>:
  [0, 1, 2, 3, 4, 5, 6, 7, 8]

def tvm.hi() -> List<&2, U32>:
  [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58]

def tvm.vg_app(+cols: List<&2, TFile.Ent>, xs: List<&2, U32>, +ys: List<&2, U32>) -> {TToken.valid.go(cols, List.append(&2, U32, xs, ys)) == Bool.and(TToken.valid.go(cols, xs), TToken.valid.go(cols, ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+t, rest}:
      %Equal.sym(Bool, TToken.valid.go(cols, List.append(&2, U32, rest, ys)), Bool.and(TToken.valid.go(cols, rest), TToken.valid.go(cols, ys)), tvm.vg_app(cols, rest, ys)) : {Bool.and(TToken.ok(cols, t), _) == Bool.and(Bool.and(TToken.ok(cols, t), TToken.valid.go(cols, rest)), TToken.valid.go(cols, ys)) : Bool}
      tvm.and_assoc(TToken.ok(cols, t), TToken.valid.go(cols, rest), TToken.valid.go(cols, ys))

def tvm.keep_app(b: Bool, -t: U32, -r: List<&2, U32>, -m: List<&2, U32>) -> {TReader.missing.keep(b, t, List.append(&2, U32, r, m)) == List.append(&2, U32, TReader.missing.keep(b, t, r), m) : List<&2, U32>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def tvm.mg_app(+cols: List<&2, TFile.Ent>, xs: List<&2, U32>, +ys: List<&2, U32>) -> {TReader.missing.go(cols, List.append(&2, U32, xs, ys)) == List.append(&2, U32, TReader.missing.go(cols, xs), TReader.missing.go(cols, ys)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+t, rest}:
      %Equal.sym(List<&2, U32>, TReader.missing.go(cols, List.append(&2, U32, rest, ys)), List.append(&2, U32, TReader.missing.go(cols, rest), TReader.missing.go(cols, ys)), tvm.mg_app(cols, rest, ys)) : {TReader.missing.keep(Bool.and(TReader.required(t), Bool.not(TToken.has(cols, t))), t, _) == List.append(&2, U32, TReader.missing.keep(Bool.and(TReader.required(t), Bool.not(TToken.has(cols, t))), t, TReader.missing.go(cols, rest)), TReader.missing.go(cols, ys)) : List<&2, U32>}
      tvm.keep_app(Bool.and(TReader.required(t), Bool.not(TToken.has(cols, t))), t, TReader.missing.go(cols, rest), TReader.missing.go(cols, ys))

def tvm.empty_cons(m: List<&2, U32>, -t: U32, -r: List<&2, U32>) -> {List.is_empty(&2, U32, List.append(&2, U32, m, t <> r)) == False{} : Bool}:
  match m:
    case Nil{}:
      {==}
    case Con{x, rest}:
      {==}

# without text, the fold fails at token 9
def tvm.vf(+cols: List<&2, TFile.Ent>, e: {TToken.has(cols, 9) == False{} : Bool}) -> {TToken.valid.go(cols, TToken.toks()) == False{} : Bool}:
  +lo = tvm.lo()
  +hi = tvm.hi()
  %Equal.sym(Bool, TToken.valid.go(cols, List.append(&2, U32, lo, 9 <> hi)), Bool.and(TToken.valid.go(cols, lo), TToken.valid.go(cols, 9 <> hi)), tvm.vg_app(cols, lo, 9 <> hi)) : {_ == False{} : Bool}
  %Equal.sym(Bool, TToken.has(cols, 9), False{}, e) : {Bool.and(TToken.valid.go(cols, lo), Bool.and(_, TToken.valid.go(cols, hi))) == False{} : Bool}
  tvm.and_false(TToken.valid.go(cols, lo))

# without text, token 9 is missing
def tvm.mf(+cols: List<&2, TFile.Ent>, e: {TToken.has(cols, 9) == False{} : Bool}) -> {List.is_empty(&2, U32, TReader.missing.go(cols, TToken.toks())) == False{} : Bool}:
  +lo = tvm.lo()
  +hi = tvm.hi()
  %Equal.sym(List<&2, U32>, TReader.missing.go(cols, List.append(&2, U32, lo, 9 <> hi)), List.append(&2, U32, TReader.missing.go(cols, lo), TReader.missing.go(cols, 9 <> hi)), tvm.mg_app(cols, lo, 9 <> hi)) : {List.is_empty(&2, U32, _) == False{} : Bool}
  %Equal.sym(Bool, TToken.has(cols, 9), False{}, e) : {List.is_empty(&2, U32, List.append(&2, U32, TReader.missing.go(cols, lo), TReader.missing.keep(Bool.and(TReader.required(9), Bool.not(_)), 9, TReader.missing.go(cols, hi)))) == False{} : Bool}
  tvm.empty_cons(TReader.missing.go(cols, lo), 9, TReader.missing.go(cols, hi))

def tvm.top(+cols: List<&2, TFile.Ent>, b: Bool, +e: {TToken.has(cols, 9) == b : Bool}) -> {TToken.valid.go(cols, TToken.toks()) == List.is_empty(&2, U32, TReader.missing.go(cols, TToken.toks())) : Bool}:
  match b:
    case True{}:
      tvm.go(cols, TToken.toks(), e)
    case False{}:
      Equal.trans(Bool, TToken.valid.go(cols, TToken.toks()), False{}, List.is_empty(&2, U32, TReader.missing.go(cols, TToken.toks())), tvm.vf(cols, e), Equal.sym(Bool, List.is_empty(&2, U32, TReader.missing.go(cols, TToken.toks())), False{}, tvm.mf(cols, e)))

def ThemeModel.theme_valid_missing(nm, cols, pg, cd, io):
  tvm.top(cols, TToken.has(cols, 9), {==})
