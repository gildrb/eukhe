# eukhe: lemmas on the UTF-8 form of a code (bend/glob/items.bend utf8):
# per length branch, its length and the rest kept after it

import Base
import ../../../bend/glob/items.bend as GItems
import ../../../laws/glob.bend as Glob

def u8.d(+x: U32, +rest: List<&2, U32>, c: Bool) -> {(List.length(&2, U32, GItems.utf8.d(x, Nil{}, c)), GItems.utf8.d(x, rest, c)) == (Glob.sp_utf8_len(False{}, False{}, c), List.append(&2, U32, GItems.utf8.d(x, Nil{}, c), rest)) : Nat & List<&2, U32>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def u8.c(+x: U32, +rest: List<&2, U32>, b: Bool) -> {(List.length(&2, U32, GItems.utf8.c(x, Nil{}, b)), GItems.utf8.c(x, rest, b)) == (Glob.sp_utf8_len(False{}, b, U32.is_lt(x, 65536)), List.append(&2, U32, GItems.utf8.c(x, Nil{}, b), rest)) : Nat & List<&2, U32>}:
  match b:
    case True{}:
      {==}
    case False{}:
      u8.d(x, rest, U32.is_lt(x, 65536))

def u8.b(+x: U32, +rest: List<&2, U32>, a: Bool) -> {(List.length(&2, U32, GItems.utf8.b(x, Nil{}, a)), GItems.utf8.b(x, rest, a)) == (Glob.sp_utf8_len(a, U32.is_lt(x, 2048), U32.is_lt(x, 65536)), List.append(&2, U32, GItems.utf8.b(x, Nil{}, a), rest)) : Nat & List<&2, U32>}:
  match a:
    case True{}:
      {==}
    case False{}:
      u8.c(x, rest, U32.is_lt(x, 2048))

def u8r.d(+x: U32, +rest: List<&2, U32>, c: Bool) -> {GItems.utf8.d(x, rest, c) == List.append(&2, U32, GItems.utf8.d(x, Nil{}, c), rest) : List<&2, U32>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

def u8r.c(+x: U32, +rest: List<&2, U32>, b: Bool) -> {GItems.utf8.c(x, rest, b) == List.append(&2, U32, GItems.utf8.c(x, Nil{}, b), rest) : List<&2, U32>}:
  match b:
    case True{}:
      {==}
    case False{}:
      u8r.d(x, rest, U32.is_lt(x, 65536))

def u8r.b(+x: U32, +rest: List<&2, U32>, a: Bool) -> {GItems.utf8.b(x, rest, a) == List.append(&2, U32, GItems.utf8.b(x, Nil{}, a), rest) : List<&2, U32>}:
  match a:
    case True{}:
      {==}
    case False{}:
      u8r.c(x, rest, U32.is_lt(x, 2048))
# the UTF-8 form of x, then the rest
def u8r.rest(+x: U32, +rest: List<&2, U32>) -> {GItems.utf8(x, rest) == List.append(&2, U32, GItems.utf8(x, Nil{}), rest) : List<&2, U32>}:
  u8r.b(x, rest, U32.is_lt(x, 128))

