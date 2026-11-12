# eukhe: the proof of LAW slash_args_auto_missing
#
# PROOF: after an on word the first option word's step comes first
# (LAA.saa.opts); its flag and name are R7's (LAA.saa.flag), a budget flag
# (smi.idx8); its value is R7's (smi.val: LAA.saa.after), none or empty,
# so the step answers the missing-value error.

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/gateway_answer.bend as Ga
import ../../laws/slash_args/model.bend as SlashArgs
import ../base/staging.bend as LStg
import ./base.bend as LA
import ./base/auto.bend as LAA

def smi.isnat(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{k}:
      True{}

def smi.idx8(b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool, b8: Bool, e: {Bool.or(b1, Bool.or(b2, Bool.or(b3, Bool.or(b4, Bool.or(b5, Bool.or(b6, Bool.or(b7, b8))))))) == True{} : Bool}) -> {smi.isnat(Sa.index.at(b1, 0n, Sa.index.at(b2, 1n, Sa.index.at(b3, 2n, Sa.index.at(b4, 3n, Sa.index.at(b5, 4n, Sa.index.at(b6, 5n, Sa.index.at(b7, 6n, Sa.index.at(b8, 7n, None{}))))))))) == True{} : Bool}:
  match b1:
    case True{}:
      {==}
    case False{}:
      match b2:
        case True{}:
          {==}
        case False{}:
          match b3:
            case True{}:
              {==}
            case False{}:
              match b4:
                case True{}:
                  {==}
                case False{}:
                  match b5:
                    case True{}:
                      {==}
                    case False{}:
                      match b6:
                        case True{}:
                          {==}
                        case False{}:
                          match b7:
                            case True{}:
                              {==}
                            case False{}:
                              match b8:
                                case True{}:
                                  {==}
                                case False{}:
                                  LStg.stg.absurdF({smi.isnat(Sa.index.at(False{}, 7n, None{})) == True{} : Bool}, e)

def smi.vm(v: Sa.Val) -> Maybe<&2, String>:
  match v:
    case Sa.VAt{x, took}:
      Some{x}
    case Sa.VNone{}:
      None{}

def smi.vnext(f: Bool, +w: String) -> {smi.vm(Sa.val.next.at(f, w)) == SlashArgs.sa_value.next(f, w) : Maybe<&2, String>}:
  match f:
    case True{}:
      {==}
    case False{}:
      {==}

def smi.val(e: Bool, +x: String, t: List<&2, String>) -> {smi.vm(Sa.val.of(e, x, t)) == SlashArgs.sa_value.at(e, x, t) : Maybe<&2, String>}:
  match e:
    case True{}:
      Equal.cong(String, Maybe<&2, String>, z => Some{z}, Sa.after_eq(x), SlashArgs.sa_after(x), LAA.saa.after(x))
    case False{}:
      match t:
        case Nil{}:
          {==}
        case +v <> u:
          smi.vnext(String.starts_with(v, "--"), v)

def smi.not_f(b: Bool, e: {Bool.not(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      LStg.stg.absurd({False{} == True{} : Bool}, e)

def smi.took(b: Bool, took: Bool, +raw: String, k: Nat, +name: String, x: String, r1: Sa.Read, r2: Sa.Read, eb: {b == True{} : Bool}) -> {Sa.step.took(b, took, raw, k, name, x, r1, r2) == Sa.RErr{Sa.auto_err("Missing value for ", raw)} : Sa.Read}:
  %Equal.sym(Bool, b, True{}, eb) : {Sa.step.took(_, took, raw, k, name, x, r1, r2) == Sa.RErr{Sa.auto_err("Missing value for ", raw)} : Sa.Read}
  {==}

def smi.step_val(v: Sa.Val, +raw: String, k: Nat, +name: String, r1: Sa.Read, r2: Sa.Read, g: {SlashArgs.sa_given(smi.vm(v)) == False{} : Bool}) -> {Sa.step.val(v, raw, k, name, r1, r2) == Sa.RErr{Sa.auto_err("Missing value for ", raw)} : Sa.Read}:
  match v:
    case Sa.VNone{}:
      {==}
    case Sa.VAt{+x, took}:
      smi.took(String.is_empty(x), took, raw, k, name, x, r1, r2, smi.not_f(String.is_empty(x), g))

def smi.known(m: Maybe<&2, Nat>, em: {smi.isnat(m) == True{} : Bool}, +x: String, +raw: String, +name: String, +t: List<&2, String>, r1: Sa.Read, r2: Sa.Read, g: {SlashArgs.sa_given(SlashArgs.sa_value(x, t)) == False{} : Bool}) -> {Sa.step.known(m, x, raw, name, t, r1, r2) == Sa.RErr{Sa.auto_err("Missing value for ", raw)} : Sa.Read}:
  match m:
    case None{}:
      LStg.stg.absurdF({Sa.step.known(None{}, x, raw, name, t, r1, r2) == Sa.RErr{Sa.auto_err("Missing value for ", raw)} : Sa.Read}, em)
    case Some{k}:
      +vv = Sa.val.of(String.contains(x, "="), x, t)
      smi.step_val(vv, raw, k, name, r1, r2, Equal.trans(Bool, SlashArgs.sa_given(smi.vm(vv)), SlashArgs.sa_given(SlashArgs.sa_value(x, t)), False{}, Equal.cong(Maybe<&2, String>, Bool, z => SlashArgs.sa_given(z), smi.vm(vv), SlashArgs.sa_value(x, t), smi.val(String.contains(x, "="), x, t)), g))

def SlashArgs.slash_args_auto_missing(s, w, x, t, ws, k, d, u, g):
  +r1 = Sa.options(t)
  +r2 = LA.sab.snd(Sa.reads(t))
  +raw = SlashArgs.sa_raw(x)
  +n = SlashArgs.sa_name(raw)
  +e = {Sa.RErr{Sa.auto_err("Missing value for ", raw)} : Sa.Read}
  +st = Equal.trans(Sa.Read, Sa.step(True{}, x, t, r1, r2), Sa.step.known(Sa.index(n, Sa.flags(), 0n), x, raw, n, t, r1, r2), e, LAA.saa.flag(x, t, r1, r2), smi.known(Sa.index(n, Sa.flags(), 0n), smi.idx8(String.eq(n, "max-continuations"), String.eq(n, "max-turns"), String.eq(n, "max-tokens"), String.eq(n, "timeout-ms"), String.eq(n, "gate"), String.eq(n, "gate-retries"), String.eq(n, "gate-timeout-ms"), String.eq(n, "subagent-keep-alive-ms"), u), x, raw, n, t, r1, r2, g))
  Equal.trans(Sa.Auto, Sa.auto(s), Sa.auto.on(Sa.step(True{}, x, t, r1, r2)), Sa.AErr{SlashArgs.sa_err("Missing value for ", raw)}, LAA.saa.opts(s, w, x, t, ws, k, True{}, d), Equal.cong(Sa.Read, Sa.Auto, z => Sa.auto.on(z), Sa.step(True{}, x, t, r1, r2), e, st))
