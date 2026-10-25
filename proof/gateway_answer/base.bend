# eukhe: lemmas shared by the proofs of area gateway_answer: each helper of
# bend/gateway_answer.bend answers what its spec helper of
# laws/gateway_answer.bend answers, on every input (by induction on the
# text or the list for the scans, case by case for the choices)

import Base
import ../../bend/gateway_answer.bend as Ga
import ../../laws/base.bend as LawsBase
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/doc_commit.bend as DocCommit

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

def gab.worded(s: String) -> {Ga.worded(s) == GatewayAnswer.ga_opens(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      %gab.space(c) : {Bool.not(Ga.space(c)) == Bool.not(_) : Bool}
      {==}

def gab.glue(c: Char, ws: List<&2, String>) -> {Ga.words.glue(c, ws) == GatewayAnswer.ga_onto(c, ws) : List<&2, String>}:
  match ws:
    case Nil{}:
      {==}
    case w <> rest:
      {==}

def gab.at(sp: Bool, j: Bool, c: Char, ws: List<&2, String>) -> {Ga.words.at(sp, j, c, ws) == GatewayAnswer.ga_split.at(sp, j, c, ws) : List<&2, String>}:
  match sp j:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      gab.glue(c, ws)
    case False{} False{}:
      {==}

def gab.words(s: String) -> {Ga.words(s) == GatewayAnswer.ga_split(s) : List<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %gab.space(c) : {Ga.words.at(Ga.space(c), Ga.worded(t), c, Ga.words(t)) == GatewayAnswer.ga_split.at(_, GatewayAnswer.ga_opens(t), c, GatewayAnswer.ga_split(t)) : List<&2, String>}
      %gab.worded(t) : {Ga.words.at(Ga.space(c), Ga.worded(t), c, Ga.words(t)) == GatewayAnswer.ga_split.at(Ga.space(c), _, c, GatewayAnswer.ga_split(t)) : List<&2, String>}
      %gab.words(t) : {Ga.words.at(Ga.space(c), Ga.worded(t), c, Ga.words(t)) == GatewayAnswer.ga_split.at(Ga.space(c), Ga.worded(t), c, _) : List<&2, String>}
      gab.at(Ga.space(c), Ga.worded(t), c, Ga.words(t))

def gab.join_rest(+sep: String, ws: List<&2, String>) -> {Ga.join.rest(sep, ws) == GatewayAnswer.ga_glue.more(sep, ws) : String}:
  match ws:
    case Nil{}:
      {==}
    case w <> rest:
      %gab.join_rest(sep, rest) : {String.append(sep, String.append(w, Ga.join.rest(sep, rest))) == String.append(sep, String.append(w, _)) : String}
      {==}

def gab.join(+sep: String, ws: List<&2, String>) -> {Ga.join(sep, ws) == GatewayAnswer.ga_glue(sep, ws) : String}:
  match ws:
    case Nil{}:
      {==}
    case w <> rest:
      %gab.join_rest(sep, rest) : {String.append(w, Ga.join.rest(sep, rest)) == String.append(w, _) : String}
      {==}

def gab.line(+s: String) -> {Ga.line(s) == GatewayAnswer.ga_glue(" ", GatewayAnswer.ga_split(s)) : String}:
  %gab.words(s) : {Ga.join(" ", Ga.words(s)) == GatewayAnswer.ga_glue(" ", _) : String}
  gab.join(" ", Ga.words(s))

def gab.reason_of(+s: String, b: Bool) -> {Ga.reason.of(s, b) == GatewayAnswer.ga_line.pick(s, b) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      gab.line(s)

def gab.reason(m: Maybe<&2, String>) -> {Ga.reason(m) == GatewayAnswer.ga_line(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{+s}:
      %gab.blank(s) : {Ga.reason.of(s, Ga.blank(s)) == GatewayAnswer.ga_line.pick(s, _) : String}
      gab.reason_of(s, Ga.blank(s))

def gab.text_of(+t: String, b: Bool) -> {Ga.text.of(t, b) == GatewayAnswer.ga_text.pick(t, b) : Ga.Answer}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def gab.text_at(+j: String) -> {Ga.text.of(j, Ga.blank(j)) == GatewayAnswer.ga_text.pick(j, GatewayAnswer.ga_empty(j)) : Ga.Answer}:
  %gab.blank(j) : {Ga.text.of(j, Ga.blank(j)) == GatewayAnswer.ga_text.pick(j, _) : Ga.Answer}
  gab.text_of(j, Ga.blank(j))

def gab.text(+ts: List<&2, String>) -> {Ga.text(ts) == GatewayAnswer.ga_text(ts) : Ga.Answer}:
  +j = Ga.join("\n\n", ts)
  +g = GatewayAnswer.ga_glue("\n\n", ts)
  Equal.trans(Ga.Answer, Ga.text.of(j, Ga.blank(j)), GatewayAnswer.ga_text.pick(j, GatewayAnswer.ga_empty(j)), GatewayAnswer.ga_text.pick(g, GatewayAnswer.ga_empty(g)), gab.text_at(j), Equal.cong(String, Ga.Answer, z => GatewayAnswer.ga_text.pick(z, GatewayAnswer.ga_empty(z)), j, g, gab.join("\n\n", ts)))

# every length fits, as the doc_commit spec says it (its list lemmas are
# reused)
def gab.fits(xs: List<&2, String>) -> {GatewayAnswer.ga_fit_strs(xs) == DocCommit.sp_fit_strs(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %gab.fits(t) : {Bool.and(LawsBase.wire_fits(String.length(x)), GatewayAnswer.ga_fit_strs(t)) == Bool.and(LawsBase.wire_fits(String.length(x)), _) : Bool}
      {==}
