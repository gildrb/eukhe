# eukhe: lemmas shared by the proofs of the `/autonomous` laws (area
# slash_args)

import Base
import ../../../bend/slash_args.bend as Sa
import ../../../bend/gateway_answer.bend as Ga
import ../../../laws/slash_args/model.bend as SlashArgs
import ../../base/staging.bend as LStg
import ../base.bend as LA

# an on word: `/autonomous` reads the options of the words after it
def saa.on(+l: String, +k: {SlashArgs.sa_on(l) == True{} : Bool}, +ws: List<&2, String>) -> {Sa.auto.kw(String.eq(l, "status"), SlashArgs.sa_on(l), SlashArgs.sa_off(l), ws) == Sa.auto.on(Sa.options(ws)) : Sa.Auto}:
  %Equal.sym(Bool, String.eq(l, "status"), False{}, LA.sab.ne_on(l, "status", k, {==})) : {Sa.auto.kw(_, SlashArgs.sa_on(l), SlashArgs.sa_off(l), ws) == Sa.auto.on(Sa.options(ws)) : Sa.Auto}
  %Equal.sym(Bool, SlashArgs.sa_on(l), True{}, k) : {Sa.auto.kw(False{}, _, SlashArgs.sa_off(l), ws) == Sa.auto.on(Sa.options(ws)) : Sa.Auto}
  {==}

# a `--` word's step: the flag and name are R7's (LA.sab.raw, LA.sab.name)
def saa.flag(+x: String, t: List<&2, String>, r1: Sa.Read, r2: Sa.Read) -> {Sa.step(True{}, x, t, r1, r2) == Sa.step.known(Sa.index(SlashArgs.sa_name(SlashArgs.sa_raw(x)), Sa.flags(), 0n), x, SlashArgs.sa_raw(x), SlashArgs.sa_name(SlashArgs.sa_raw(x)), t, r1, r2) : Sa.Read}:
  +raw = SlashArgs.sa_raw(x)
  %Equal.sym(String, Sa.before_eq(x), raw, LA.sab.raw(x)) : {Sa.step.known(Sa.index(Sa.name.of(String.starts_with(_, "--autonomous-"), _), Sa.flags(), 0n), x, _, Sa.name.of(String.starts_with(_, "--autonomous-"), _), t, r1, r2) == Sa.step.known(Sa.index(SlashArgs.sa_name(raw), Sa.flags(), 0n), x, raw, SlashArgs.sa_name(raw), t, r1, r2) : Sa.Read}
  %Equal.sym(String, Sa.name.of(String.starts_with(raw, "--autonomous-"), raw), SlashArgs.sa_name(raw), LA.sab.name(raw)) : {Sa.step.known(Sa.index(_, Sa.flags(), 0n), x, raw, _, t, r1, r2) == Sa.step.known(Sa.index(SlashArgs.sa_name(raw), Sa.flags(), 0n), x, raw, SlashArgs.sa_name(raw), t, r1, r2) : Sa.Read}
  {==}

# the options of the words after an on word w, x, t: x's step first
def saa.opts(+s: String, +w: String, +x: String, +t: List<&2, String>, ws: {Sa.words(s) == w <> x <> t : List<&2, String>}, +k: {SlashArgs.sa_on(String.to_lower(w)) == True{} : Bool}, b: Bool, eb: {String.starts_with(x, "--") == b : Bool}) -> {Sa.auto(s) == Sa.auto.on(Sa.step(b, x, t, Sa.options(t), LA.sab.snd(Sa.reads(t)))) : Sa.Auto}:
  +l = String.to_lower(w)
  +fw = Equal.trans(Sa.Read, Sa.options(x <> t), Sa.step(String.starts_with(x, "--"), x, t, Sa.options(t), LA.sab.snd(Sa.reads(t))), Sa.step(b, x, t, Sa.options(t), LA.sab.snd(Sa.reads(t))), LA.sab.first_word(x, t, Sa.reads(t)), Equal.cong(Bool, Sa.Read, z => Sa.step(z, x, t, Sa.options(t), LA.sab.snd(Sa.reads(t))), String.starts_with(x, "--"), b, eb))
  Equal.trans(Sa.Auto, Sa.auto(s), Sa.auto.words(w <> x <> t), Sa.auto.on(Sa.step(b, x, t, Sa.options(t), LA.sab.snd(Sa.reads(t)))), LA.sab.auto_ws(s, w <> x <> t, ws), Equal.trans(Sa.Auto, Sa.auto.words(w <> x <> t), Sa.auto.on(Sa.options(x <> t)), Sa.auto.on(Sa.step(b, x, t, Sa.options(t), LA.sab.snd(Sa.reads(t)))), saa.on(l, k, x <> t), Equal.cong(Sa.Read, Sa.Auto, z => Sa.auto.on(z), Sa.options(x <> t), Sa.step(b, x, t, Sa.options(t), LA.sab.snd(Sa.reads(t))), fw)))

def saa.after.at(e: Bool, t: String, r: String) -> {Sa.after_eq.at(e, t, r) == SlashArgs.sa_after.at(e, t, r) : String}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

# the code's text after `=` is R7's
def saa.after(s: String) -> {Sa.after_eq(s) == SlashArgs.sa_after(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Sa.after_eq(t), SlashArgs.sa_after(t), saa.after(t)) : {Sa.after_eq.at(Char.is_eq(c, '='), t, _) == SlashArgs.sa_after(SCon{c, t}) : String}
      saa.after.at(Char.is_eq(c, '='), t, SlashArgs.sa_after(t))

def saa.ug.at(b: Bool, c: Char, r: String) -> {Sa.ungroup.at(b, c, r) == SlashArgs.sa_ungroup.at(b, c, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the code's drop of `,` and `_` is R8's
def saa.ungroup(s: String) -> {Sa.ungroup(s) == SlashArgs.sa_ungroup(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Sa.ungroup(t), SlashArgs.sa_ungroup(t), saa.ungroup(t)) : {Sa.ungroup.at(Bool.or(Char.is_eq(c, ','), Char.is_eq(c, '_')), c, _) == SlashArgs.sa_ungroup(SCon{c, t}) : String}
      saa.ug.at(Bool.or(Char.is_eq(c, ','), Char.is_eq(c, '_')), c, SlashArgs.sa_ungroup(t))
