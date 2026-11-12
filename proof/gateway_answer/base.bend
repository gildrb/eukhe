# eukhe: lemmas shared by the proofs of area gateway_answer: the code's
# whitespace test is Rust's table (the laws' ga_white), Base's join is the
# code's, and the code's words of a spelled text are its words (by
# induction on the text and on each word)

import Base
import ../../bend/gateway_answer.bend as Ga
import ../../laws/base.bend as LawsBase
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/doc_commit.bend as DocCommit

# Logic
# -----

def gab.If(b: Bool, G: Type) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      G

# no case where False is True
def gab.absurd(-G: Type, +h: {False{} == True{} : Bool}) -> G:
  %h : gab.If(_, G)
  Unit{}

def gab.and_l(a: Bool, -b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def gab.and_r(a: Bool, -b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      gab.absurd({b == True{} : Bool}, h)

def gab.not_true(a: Bool, +h: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      gab.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

# Whitespace
# ----------

def gab.in(+x: U32, xs: List<&2, U32>) -> {Ga.in(x, xs) == GatewayAnswer.ga_ws_in(x, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case y <> rest:
      %gab.in(x, rest) : {Bool.or(U32.is_eq(x, y), Ga.in(x, rest)) == Bool.or(U32.is_eq(x, y), _) : Bool}
      {==}

def gab.space(c: Char) -> {Ga.space(c) == GatewayAnswer.ga_white(c) : Bool}:
  gab.in(Char.to_u32(c), Ga.spaces())

def gab.blank(s: String) -> {Ga.blank(s) == GatewayAnswer.ga_empty(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      %gab.space(c) : {Bool.and(Ga.space(c), Ga.blank(t)) == Bool.and(_, GatewayAnswer.ga_empty(t)) : Bool}
      %gab.blank(t) : {Bool.and(Ga.space(c), Ga.blank(t)) == Bool.and(Ga.space(c), _) : Bool}
      {==}

# a char of Rust's whitespace is the code's
def gab.space_on(+c: Char, +h: {GatewayAnswer.ga_white(c) == True{} : Bool}) -> {Ga.space(c) == True{} : Bool}:
  Equal.trans(Bool, Ga.space(c), GatewayAnswer.ga_white(c), True{}, gab.space(c), h)

# a char of no whitespace is none for the code
def gab.space_off(+c: Char, +h: {Bool.not(GatewayAnswer.ga_white(c)) == True{} : Bool}) -> {Ga.space(c) == False{} : Bool}:
  Equal.trans(Bool, Ga.space(c), GatewayAnswer.ga_white(c), False{}, gab.space(c), gab.not_true(GatewayAnswer.ga_white(c), h))

# Join
# ----

def gab.app_nil(s: String) -> {String.append(s, SNil{}) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %gab.app_nil(t) : {SCon{c, String.append(t, SNil{})} == SCon{c, _} : String}
      {==}

def gab.join_go(xs: List<&2, String>, +h: String, +sep: String) -> {String.join.go(xs, h, sep) == String.append(h, Ga.join.rest(sep, xs)) : String}:
  match xs:
    case Nil{}:
      Equal.sym(String, String.append(h, SNil{}), h, gab.app_nil(h))
    case +h2 <> +t:
      %gab.join_go(t, h2, sep) : {String.append(h, String.append(sep, String.join.go(t, h2, sep))) == String.append(h, String.append(sep, _)) : String}
      {==}

# Base's join is the code's
def gab.join(+sep: String, ws: List<&2, String>) -> {Ga.join(sep, ws) == String.join(ws, sep) : String}:
  match ws:
    case Nil{}:
      {==}
    case +w <> +t:
      Equal.sym(String, String.join.go(t, w, sep), String.append(w, Ga.join.rest(sep, t)), gab.join_go(t, w, sep))

# Words
# -----

# a whitespace run before r adds no word
def gab.skip(g: String, +r: String, +hb: {GatewayAnswer.ga_empty(g) == True{} : Bool}) -> {Ga.words(String.append(g, r)) == Ga.words(r) : List<&2, String>}:
  match g:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +hs = gab.space_on(c, gab.and_l(GatewayAnswer.ga_white(c), GatewayAnswer.ga_empty(t), hb))
      %Equal.sym(Bool, Ga.space(c), True{}, hs) : {Ga.words.at(_, Ga.worded(String.append(t, r)), c, Ga.words(String.append(t, r))) == Ga.words(r) : List<&2, String>}
      gab.skip(t, r, gab.and_r(GatewayAnswer.ga_white(c), GatewayAnswer.ga_empty(t), hb))

# a whitespace run holds no word
def gab.no_words(g: String, +hb: {GatewayAnswer.ga_empty(g) == True{} : Bool}) -> {Ga.words(g) == Nil{} : List<&2, String>}:
  match g:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +hs = gab.space_on(c, gab.and_l(GatewayAnswer.ga_white(c), GatewayAnswer.ga_empty(t), hb))
      %Equal.sym(Bool, Ga.space(c), True{}, hs) : {Ga.words.at(_, Ga.worded(t), c, Ga.words(t)) == Nil{} : List<&2, String>}
      gab.no_words(t, gab.and_r(GatewayAnswer.ga_white(c), GatewayAnswer.ga_empty(t), hb))

# a whitespace run is no word start
def gab.run_quiet(g: String, +hb: {GatewayAnswer.ga_empty(g) == True{} : Bool}) -> {Ga.worded(g) == False{} : Bool}:
  match g:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +hs = gab.space_on(c, gab.and_l(GatewayAnswer.ga_white(c), GatewayAnswer.ga_empty(t), hb))
      %Equal.sym(Bool, Ga.space(c), True{}, hs) : {Bool.not(_) == False{} : Bool}
      {==}

def gab.after.gap(g: String, +r: String, +h: {GatewayAnswer.ga_gap(False{}, g) == True{} : Bool}) -> {Ga.worded(String.append(g, r)) == False{} : Bool}:
  match g:
    case SNil{}:
      gab.absurd({Ga.worded(r) == False{} : Bool}, h)
    case SCon{+c, +t}:
      +he = gab.and_l(GatewayAnswer.ga_empty(SCon{c, t}), GatewayAnswer.ga_filled(SCon{c, t}), h)
      +hs = gab.space_on(c, gab.and_l(GatewayAnswer.ga_white(c), GatewayAnswer.ga_empty(t), he))
      %Equal.sym(Bool, Ga.space(c), True{}, hs) : {Bool.not(_) == False{} : Bool}
      {==}

# the rest of a well formed text after a word starts with no word char
def gab.after(m: GatewayAnswer.GaText, +h: {GatewayAnswer.ga_well(m, False{}) == True{} : Bool}) -> {Ga.worded(GatewayAnswer.ga_spell(m)) == False{} : Bool}:
  match m:
    case GatewayAnswer.GaEnd{+g}:
      gab.run_quiet(g, h)
    case GatewayAnswer.GaWord{+g, +w, +n}:
      gab.after.gap(g, String.append(w, GatewayAnswer.ga_spell(n)), gab.and_l(GatewayAnswer.ga_gap(False{}, g), Bool.and(GatewayAnswer.ga_word(w), GatewayAnswer.ga_well(n, False{})), h))

# a word, then a text that starts with no word char: that word, then the
# words of the text
def gab.word(t: String, +c: Char, +r: String, +hd: {GatewayAnswer.ga_dense(SCon{c, t}) == True{} : Bool}, +hr: {Ga.worded(r) == False{} : Bool}) -> {Ga.words(SCon{c, String.append(t, r)}) == SCon{c, t} <> Ga.words(r) : List<&2, String>}:
  match t:
    case SNil{}:
      +hs = gab.space_off(c, gab.and_l(Bool.not(GatewayAnswer.ga_white(c)), True{}, hd))
      %Equal.sym(Bool, Ga.space(c), False{}, hs) : {Ga.words.at(_, Ga.worded(r), c, Ga.words(r)) == SCon{c, SNil{}} <> Ga.words(r) : List<&2, String>}
      %Equal.sym(Bool, Ga.worded(r), False{}, hr) : {Ga.words.at(False{}, _, c, Ga.words(r)) == SCon{c, SNil{}} <> Ga.words(r) : List<&2, String>}
      {==}
    case SCon{+d, +u}:
      +hs = gab.space_off(c, gab.and_l(Bool.not(GatewayAnswer.ga_white(c)), GatewayAnswer.ga_dense(SCon{d, u}), hd))
      +hu = gab.and_r(Bool.not(GatewayAnswer.ga_white(c)), GatewayAnswer.ga_dense(SCon{d, u}), hd)
      +hsd = gab.space_off(d, gab.and_l(Bool.not(GatewayAnswer.ga_white(d)), GatewayAnswer.ga_dense(u), hu))
      %Equal.sym(Bool, Ga.space(c), False{}, hs) : {Ga.words.at(_, Bool.not(Ga.space(d)), c, Ga.words(SCon{d, String.append(u, r)})) == SCon{c, SCon{d, u}} <> Ga.words(r) : List<&2, String>}
      %Equal.sym(Bool, Ga.space(d), False{}, hsd) : {Ga.words.at(False{}, Bool.not(_), c, Ga.words(SCon{d, String.append(u, r)})) == SCon{c, SCon{d, u}} <> Ga.words(r) : List<&2, String>}
      %Equal.sym(List<&2, String>, Ga.words(SCon{d, String.append(u, r)}), SCon{d, u} <> Ga.words(r), gab.word(u, d, r, hu, hr)) : {Ga.words.glue(c, _) == SCon{c, SCon{d, u}} <> Ga.words(r) : List<&2, String>}
      {==}

# the gap before a word is whitespace only
def gab.gap(first: Bool, g: String, +h: {GatewayAnswer.ga_gap(first, g) == True{} : Bool}) -> {GatewayAnswer.ga_empty(g) == True{} : Bool}:
  match first:
    case True{}:
      h
    case False{}:
      gab.and_l(GatewayAnswer.ga_empty(g), GatewayAnswer.ga_filled(g), h)

def gab.spelled.word(w: String, +r: String, -ws: List<&2, String>, +hw: {GatewayAnswer.ga_word(w) == True{} : Bool}, +hr: {Ga.worded(r) == False{} : Bool}, ih: {Ga.words(r) == ws : List<&2, String>}) -> {Ga.words(String.append(w, r)) == w <> ws : List<&2, String>}:
  match w:
    case SNil{}:
      gab.absurd({Ga.words(r) == SNil{} <> ws : List<&2, String>}, hw)
    case SCon{+c, +t}:
      %ih : {Ga.words(SCon{c, String.append(t, r)}) == SCon{c, t} <> _ : List<&2, String>}
      gab.word(t, c, r, hw, hr)

# the code's words of a well formed text are its words
def gab.spelled(t: GatewayAnswer.GaText, +first: Bool, +h: {GatewayAnswer.ga_well(t, first) == True{} : Bool}) -> {Ga.words(GatewayAnswer.ga_spell(t)) == GatewayAnswer.ga_words_of(t) : List<&2, String>}:
  match t:
    case GatewayAnswer.GaEnd{+g}:
      gab.no_words(g, h)
    case GatewayAnswer.GaWord{+g, +w, +m}:
      +hg = gab.gap(first, g, gab.and_l(GatewayAnswer.ga_gap(first, g), Bool.and(GatewayAnswer.ga_word(w), GatewayAnswer.ga_well(m, False{})), h))
      +hr = gab.and_r(GatewayAnswer.ga_gap(first, g), Bool.and(GatewayAnswer.ga_word(w), GatewayAnswer.ga_well(m, False{})), h)
      +hw = gab.and_l(GatewayAnswer.ga_word(w), GatewayAnswer.ga_well(m, False{}), hr)
      +hm = gab.and_r(GatewayAnswer.ga_word(w), GatewayAnswer.ga_well(m, False{}), hr)
      +ih = gab.spelled(m, False{}, hm)
      Equal.trans(List<&2, String>, Ga.words(String.append(g, String.append(w, GatewayAnswer.ga_spell(m)))), Ga.words(String.append(w, GatewayAnswer.ga_spell(m))), w <> GatewayAnswer.ga_words_of(m), gab.skip(g, String.append(w, GatewayAnswer.ga_spell(m)), hg), gab.spelled.word(w, GatewayAnswer.ga_spell(m), GatewayAnswer.ga_words_of(m), hw, gab.after(m, hm), ih))

# a whitespace run before r leaves r's blank test
def gab.blank_skip(g: String, +r: String, +hb: {GatewayAnswer.ga_empty(g) == True{} : Bool}) -> {Ga.blank(String.append(g, r)) == Ga.blank(r) : Bool}:
  match g:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +hs = gab.space_on(c, gab.and_l(GatewayAnswer.ga_white(c), GatewayAnswer.ga_empty(t), hb))
      %Equal.sym(Bool, Ga.space(c), True{}, hs) : {Bool.and(_, Ga.blank(String.append(t, r))) == Ga.blank(r) : Bool}
      gab.blank_skip(t, r, gab.and_r(GatewayAnswer.ga_white(c), GatewayAnswer.ga_empty(t), hb))

# a word opens with a char of no whitespace
def gab.word_full(w: String, -r: String, +hw: {GatewayAnswer.ga_word(w) == True{} : Bool}) -> {Ga.blank(String.append(w, r)) == False{} : Bool}:
  match w:
    case SNil{}:
      gab.absurd({Ga.blank(r) == False{} : Bool}, hw)
    case SCon{+c, +t}:
      +hs = gab.space_off(c, gab.and_l(Bool.not(GatewayAnswer.ga_white(c)), GatewayAnswer.ga_dense(t), hw))
      %Equal.sym(Bool, Ga.space(c), False{}, hs) : {Bool.and(_, Ga.blank(String.append(t, r))) == False{} : Bool}
      {==}

# a well formed text with a word is no whitespace run
def gab.spell_full(t: GatewayAnswer.GaText, +first: Bool, +h: {GatewayAnswer.ga_well(t, first) == True{} : Bool}, some: {GatewayAnswer.ga_has_word(t) == True{} : Bool}) -> {Ga.blank(GatewayAnswer.ga_spell(t)) == False{} : Bool}:
  match t:
    case GatewayAnswer.GaEnd{g}:
      gab.absurd({Ga.blank(g) == False{} : Bool}, some)
    case GatewayAnswer.GaWord{+g, +w, +m}:
      +hg = gab.gap(first, g, gab.and_l(GatewayAnswer.ga_gap(first, g), Bool.and(GatewayAnswer.ga_word(w), GatewayAnswer.ga_well(m, False{})), h))
      +hr = gab.and_r(GatewayAnswer.ga_gap(first, g), Bool.and(GatewayAnswer.ga_word(w), GatewayAnswer.ga_well(m, False{})), h)
      +hw = gab.and_l(GatewayAnswer.ga_word(w), GatewayAnswer.ga_well(m, False{}), hr)
      Equal.trans(Bool, Ga.blank(String.append(g, String.append(w, GatewayAnswer.ga_spell(m)))), Ga.blank(String.append(w, GatewayAnswer.ga_spell(m))), False{}, gab.blank_skip(g, String.append(w, GatewayAnswer.ga_spell(m)), hg), gab.word_full(w, GatewayAnswer.ga_spell(m), hw))

# Fits
# ----

# every length fits, as the doc_commit spec says it (its list lemmas are
# reused)
def gab.fits(xs: List<&2, String>) -> {GatewayAnswer.ga_fit_strs(xs) == DocCommit.sp_fit_strs(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %gab.fits(t) : {Bool.and(LawsBase.wire_fits(String.length(x)), GatewayAnswer.ga_fit_strs(t)) == Bool.and(LawsBase.wire_fits(String.length(x)), _) : Bool}
      {==}
