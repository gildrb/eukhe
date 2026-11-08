# eukhe: lemmas shared by the proofs of area privacy, section token: one
# value scrubbed (its token restores to it, and it moves no other index),
# then the values of one text (the map after them keeps every index, and
# scrubbing them again changes nothing)

import Base
import ../../../bend/privacy/token.bend as Tk
import ./token.bend as LTk

# The class of a value
# --------------------

# a token of a class that maps back is read in the map
def psc.rt_of(-m: Tk.Book, +k: Tk.Class, -i: Nat, +er: {Tk.reversible(k) == True{} : Bool}) -> {Tk.restore_tok(m, k, i) == Tk.value(Tk.Book.es(m), k, i) : Maybe<&2, String>}:
  %Equal.sym(Bool, Tk.reversible(k), True{}, er) : {Tk.restore_tok.of(_, m, k, i) == Tk.value(Tk.Book.es(m), k, i) : Maybe<&2, String>}
  {==}

# a token of a one-way class has no value
def psc.rt_none(-m: Tk.Book, +k: Tk.Class, -i: Nat, +er: {Tk.reversible(k) == False{} : Bool}) -> {Tk.restore_tok(m, k, i) == None{} : Maybe<&2, String>}:
  %Equal.sym(Bool, Tk.reversible(k), False{}, er) : {Tk.restore_tok.of(_, m, k, i) == None{} : Maybe<&2, String>}
  {==}

# One value
# ---------

def psc.keep1.k(r: Bool, +k: Tk.Class, +es: List<&2, Tk.Ent>, +c: Tk.Class, +v: String, +i: Nat, +x: String,
  +er: {Tk.reversible(k) == r : Bool},
  +h: {Tk.restore_tok(Tk.Book{es}, k, i) == Some{x} : Maybe<&2, String>}) ->
  {Tk.restore_tok(Tk.Book{Tk.Ent{c, v} <> es}, k, i) == Some{x} : Maybe<&2, String>}:
  match r:
    case True{}:
      +hv = Equal.trans(Maybe<&2, String>, Tk.value(es, k, i), Tk.restore_tok(Tk.Book{es}, k, i), Some{x}, Equal.sym(Maybe<&2, String>, Tk.restore_tok(Tk.Book{es}, k, i), Tk.value(es, k, i), psc.rt_of(Tk.Book{es}, k, i, er)), h)
      Equal.trans(Maybe<&2, String>, Tk.restore_tok(Tk.Book{Tk.Ent{c, v} <> es}, k, i), Tk.value(Tk.Ent{c, v} <> es, k, i), Some{x}, psc.rt_of(Tk.Book{Tk.Ent{c, v} <> es}, k, i, er), LTk.ptk.value_new(es, c, v, k, i, x, hv))
    case False{}:
      LTk.ptk.none_some(String, x, {Tk.restore_tok(Tk.Book{Tk.Ent{c, v} <> es}, k, i) == Some{x} : Maybe<&2, String>}, Equal.trans(Maybe<&2, String>, None{}, Tk.restore_tok(Tk.Book{es}, k, i), Some{x}, Equal.sym(Maybe<&2, String>, Tk.restore_tok(Tk.Book{es}, k, i), None{}, psc.rt_none(Tk.Book{es}, k, i, er)), h))

def psc.keep1.f(f: Maybe<&2, Nat>, +es: List<&2, Tk.Ent>, +c: Tk.Class, +v: String, +k: Tk.Class, +i: Nat, +x: String,
  +h: {Tk.restore_tok(Tk.Book{es}, k, i) == Some{x} : Maybe<&2, String>}) ->
  {Tk.restore_tok(Tk.Step.m(Tk.scrub_val.new(es, c, v, f)), k, i) == Some{x} : Maybe<&2, String>}:
  match f:
    case Some{j}:
      h
    case None{}:
      psc.keep1.k(Tk.reversible(k), k, es, c, v, i, x, {==}, h)

def psc.keep1.r(r: Bool, +m: Tk.Book, +c: Tk.Class, +v: String, +k: Tk.Class, +i: Nat, +x: String,
  +h: {Tk.restore_tok(m, k, i) == Some{x} : Maybe<&2, String>}) ->
  {Tk.restore_tok(Tk.Step.m(Tk.scrub_val.of(r, m, c, v)), k, i) == Some{x} : Maybe<&2, String>}:
  match r:
    case False{}:
      h
    case True{}:
      match m:
        case Tk.Book{+es}:
          psc.keep1.f(Tk.find(es, c, v), es, c, v, k, i, x, h)

# a value scrubbed keeps the value of every token the map holds
def psc.keep1(+m: Tk.Book, +c: Tk.Class, +v: String, +k: Tk.Class, +i: Nat, +x: String, +h: {Tk.restore_tok(m, k, i) == Some{x} : Maybe<&2, String>}) -> {Tk.restore_tok(Tk.Step.m(Tk.scrub_val(m, c, v)), k, i) == Some{x} : Maybe<&2, String>}:
  psc.keep1.r(Tk.reversible(c), m, c, v, k, i, x, h)

def psc.find1.f(f: Maybe<&2, Nat>, +es: List<&2, Tk.Ent>, +c: Tk.Class, +v: String, +k: Tk.Class, +x: String, +i: Nat,
  +ef: {Tk.find(es, c, v) == f : Maybe<&2, Nat>},
  +h: {Tk.find(es, k, x) == Some{i} : Maybe<&2, Nat>}) ->
  {Tk.find(Tk.Book.es(Tk.Step.m(Tk.scrub_val.new(es, c, v, f))), k, x) == Some{i} : Maybe<&2, Nat>}:
  match f:
    case Some{j}:
      h
    case None{}:
      LTk.ptk.find_new(es, c, v, k, x, i, h, ef)

def psc.find1.r(r: Bool, +m: Tk.Book, +c: Tk.Class, +v: String, +k: Tk.Class, +x: String, +i: Nat,
  +h: {Tk.find(Tk.Book.es(m), k, x) == Some{i} : Maybe<&2, Nat>}) ->
  {Tk.find(Tk.Book.es(Tk.Step.m(Tk.scrub_val.of(r, m, c, v))), k, x) == Some{i} : Maybe<&2, Nat>}:
  match r:
    case False{}:
      h
    case True{}:
      match m:
        case Tk.Book{+es}:
          psc.find1.f(Tk.find(es, c, v), es, c, v, k, x, i, {==}, h)

# a value scrubbed keeps the index every other value has
def psc.find1(+m: Tk.Book, +c: Tk.Class, +v: String, +k: Tk.Class, +x: String, +i: Nat, +h: {Tk.find(Tk.Book.es(m), k, x) == Some{i} : Maybe<&2, Nat>}) -> {Tk.find(Tk.Book.es(Tk.Step.m(Tk.scrub_val(m, c, v))), k, x) == Some{i} : Maybe<&2, Nat>}:
  psc.find1.r(Tk.reversible(c), m, c, v, k, x, i, h)

# what scrubbing v of class c from m gives: an index whose token restores
# to v and at which the map after it finds v (a class that maps back), or
# one way with the map unchanged
def psc.TokOk(c: Tk.Class, v: String, m: Tk.Book, s: Tk.Step) -> Type:
  match s:
    case Tk.Step{m1, t}:
      match t:
        case Tk.Mapped{i}:
          {Tk.reversible(c) == True{} : Bool} & ({Tk.restore_tok(m1, c, i) == Some{v} : Maybe<&2, String>} & {Tk.find(Tk.Book.es(m1), c, v) == Some{i} : Maybe<&2, Nat>})
        case Tk.OneWay{}:
          {Tk.reversible(c) == False{} : Bool} & {m1 == m : Tk.Book}

def psc.tok_ok.f(f: Maybe<&2, Nat>, +es: List<&2, Tk.Ent>, +c: Tk.Class, +v: String,
  +er: {Tk.reversible(c) == True{} : Bool},
  +ef: {Tk.find(es, c, v) == f : Maybe<&2, Nat>}) ->
  psc.TokOk(c, v, Tk.Book{es}, Tk.scrub_val.new(es, c, v, f)):
  match f:
    case Some{+j}:
      (er, (Equal.trans(Maybe<&2, String>, Tk.restore_tok(Tk.Book{es}, c, j), Tk.value(es, c, j), Some{v}, psc.rt_of(Tk.Book{es}, c, j, er), LTk.ptk.find_value(es, c, v, j, ef)), ef))
    case None{}:
      (er, (Equal.trans(Maybe<&2, String>, Tk.restore_tok(Tk.Book{Tk.Ent{c, v} <> es}, c, 1n+Tk.count(es, c)), Tk.value(Tk.Ent{c, v} <> es, c, 1n+Tk.count(es, c)), Some{v}, psc.rt_of(Tk.Book{Tk.Ent{c, v} <> es}, c, 1n+Tk.count(es, c), er), LTk.ptk.value_head(es, c, v)), LTk.ptk.find_head(es, c, v)))

def psc.tok_ok.r(r: Bool, +m: Tk.Book, +c: Tk.Class, +v: String, +er: {Tk.reversible(c) == r : Bool}) -> psc.TokOk(c, v, m, Tk.scrub_val.of(r, m, c, v)):
  match r:
    case False{}:
      (er, {==})
    case True{}:
      match m:
        case Tk.Book{+es}:
          psc.tok_ok.f(Tk.find(es, c, v), es, c, v, er, {==})

def psc.tok_ok(+m: Tk.Book, +c: Tk.Class, +v: String) -> psc.TokOk(c, v, m, Tk.scrub_val(m, c, v)):
  psc.tok_ok.r(Tk.reversible(c), m, c, v, {==})

def psc.held.r(r: Bool, +m: Tk.Book, +c: Tk.Class, +v: String, +i: Nat, +er: {Tk.reversible(c) == r : Bool}, +et: {Tk.reversible(c) == True{} : Bool}, +h: {Tk.find(Tk.Book.es(m), c, v) == Some{i} : Maybe<&2, Nat>}) -> {Tk.scrub_val.of(r, m, c, v) == Tk.Step{m, Tk.Mapped{i}} : Tk.Step}:
  match r:
    case True{}:
      match m:
        case Tk.Book{+es}:
          %Equal.sym(Maybe<&2, Nat>, Tk.find(es, c, v), Some{i}, h) : {Tk.scrub_val.new(es, c, v, _) == Tk.Step{Tk.Book{es}, Tk.Mapped{i}} : Tk.Step}
          {==}
    case False{}:
      LTk.ptk.absurd_tf({Tk.scrub_val.of(False{}, m, c, v) == Tk.Step{m, Tk.Mapped{i}} : Tk.Step}, Equal.trans(Bool, True{}, Tk.reversible(c), False{}, Equal.sym(Bool, Tk.reversible(c), True{}, et), er))

# a value the map holds, of a class that maps back, scrubs to its index
# and leaves the map
def psc.held(+m: Tk.Book, +c: Tk.Class, +v: String, +i: Nat, +er: {Tk.reversible(c) == True{} : Bool}, +h: {Tk.find(Tk.Book.es(m), c, v) == Some{i} : Maybe<&2, Nat>}) -> {Tk.scrub_val(m, c, v) == Tk.Step{m, Tk.Mapped{i}} : Tk.Step}:
  psc.held.r(Tk.reversible(c), m, c, v, i, {==}, er, h)

# a value of a one-way class scrubs one way and leaves the map
def psc.oneway(+m: Tk.Book, +c: Tk.Class, +v: String, +er: {Tk.reversible(c) == False{} : Bool}) -> {Tk.scrub_val(m, c, v) == Tk.Step{m, Tk.OneWay{}} : Tk.Step}:
  %Equal.sym(Bool, Tk.reversible(c), False{}, er) : {Tk.scrub_val.of(_, m, c, v) == Tk.Step{m, Tk.OneWay{}} : Tk.Step}
  {==}
