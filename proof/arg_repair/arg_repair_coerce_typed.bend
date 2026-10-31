# eukhe: the proof of LAW arg_repair_coerce_typed
#
# PROOF: every reading of the model is of its kind's type (ct.val: the
# kind's readings one by one, ct.int through the integer stages); the kind
# a declared `type` names is that name (ct.kind); so the reading names the
# declared type (ct.typed).

import Base
import ../../bend/arg_repair.bend as Ar
import ../../laws/arg_repair.bend as ArgRepair
import ./base.bend as AB

# a reading of the kind k is of its type
def ct.ok_to(k: Ar.Ty, t: Ar.To) -> Bool:
  match k:
    case Ar.KString{}:
      match t:
        case Ar.TBool{b}:
          False{}
        case Ar.TNum{y}:
          False{}
        case Ar.TStr{y}:
          True{}
        case Ar.TOne{}:
          False{}
        case Ar.TObj{}:
          False{}
        case Ar.TArr{}:
          False{}
    case Ar.KBoolean{}:
      match t:
        case Ar.TBool{b}:
          True{}
        case Ar.TNum{y}:
          False{}
        case Ar.TStr{y}:
          False{}
        case Ar.TOne{}:
          False{}
        case Ar.TObj{}:
          False{}
        case Ar.TArr{}:
          False{}
    case Ar.KInteger{}:
      match t:
        case Ar.TBool{b}:
          False{}
        case Ar.TNum{y}:
          True{}
        case Ar.TStr{y}:
          False{}
        case Ar.TOne{}:
          False{}
        case Ar.TObj{}:
          False{}
        case Ar.TArr{}:
          False{}
    case Ar.KNumber{}:
      match t:
        case Ar.TBool{b}:
          False{}
        case Ar.TNum{y}:
          True{}
        case Ar.TStr{y}:
          False{}
        case Ar.TOne{}:
          False{}
        case Ar.TObj{}:
          False{}
        case Ar.TArr{}:
          False{}
    case Ar.KObject{}:
      match t:
        case Ar.TBool{b}:
          False{}
        case Ar.TNum{y}:
          False{}
        case Ar.TStr{y}:
          False{}
        case Ar.TOne{}:
          False{}
        case Ar.TObj{}:
          True{}
        case Ar.TArr{}:
          False{}
    case Ar.KArray{}:
      match t:
        case Ar.TBool{b}:
          False{}
        case Ar.TNum{y}:
          False{}
        case Ar.TStr{y}:
          False{}
        case Ar.TOne{}:
          True{}
        case Ar.TObj{}:
          False{}
        case Ar.TArr{}:
          True{}
    case Ar.KOther{}:
      match t:
        case Ar.TBool{b}:
          False{}
        case Ar.TNum{y}:
          False{}
        case Ar.TStr{y}:
          False{}
        case Ar.TOne{}:
          False{}
        case Ar.TObj{}:
          False{}
        case Ar.TArr{}:
          False{}

def ct.ok(k: Ar.Ty, r: Maybe<&2, Ar.To>) -> Bool:
  match r:
    case None{}:
      True{}
    case Some{t}:
      ct.ok_to(k, t)

# the kind k is the one the name t names
def ct.kind_ok(+t: String, k: Ar.Ty) -> Bool:
  match k:
    case Ar.KString{}:
      String.eq(t, "string")
    case Ar.KBoolean{}:
      String.eq(t, "boolean")
    case Ar.KInteger{}:
      String.eq(t, "integer")
    case Ar.KNumber{}:
      String.eq(t, "number")
    case Ar.KObject{}:
      String.eq(t, "object")
    case Ar.KArray{}:
      String.eq(t, "array")
    case Ar.KOther{}:
      True{}

def ct.or_l(a: Bool, -b: Bool, h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, h) : {Bool.or(_, b) == True{} : Bool}
  {==}

def ct.or_r(a: Bool, -b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def ct.typed(k: Ar.Ty, +t: String, -n: String, -it: Maybe<&2, String>, r: Maybe<&2, Ar.To>, hk: {ct.kind_ok(t, k) == True{} : Bool}, hr: {ct.ok(k, r) == True{} : Bool}) -> {ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, r) == True{} : Bool}:
  match k:
    case Ar.KString{}:
      match r:
        case None{}:
          {==}
        case Some{x}:
          match x:
            case Ar.TBool{b}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TBool{b}}) == True{} : Bool}, hr)
            case Ar.TNum{y}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TNum{y}}) == True{} : Bool}, hr)
            case Ar.TStr{y}:
              hk
            case Ar.TOne{}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TOne{}}) == True{} : Bool}, hr)
            case Ar.TObj{}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TObj{}}) == True{} : Bool}, hr)
            case Ar.TArr{}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TArr{}}) == True{} : Bool}, hr)
    case Ar.KBoolean{}:
      match r:
        case None{}:
          {==}
        case Some{x}:
          match x:
            case Ar.TBool{b}:
              hk
            case Ar.TNum{y}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TNum{y}}) == True{} : Bool}, hr)
            case Ar.TStr{y}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TStr{y}}) == True{} : Bool}, hr)
            case Ar.TOne{}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TOne{}}) == True{} : Bool}, hr)
            case Ar.TObj{}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TObj{}}) == True{} : Bool}, hr)
            case Ar.TArr{}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TArr{}}) == True{} : Bool}, hr)
    case Ar.KInteger{}:
      match r:
        case None{}:
          {==}
        case Some{x}:
          match x:
            case Ar.TBool{b}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TBool{b}}) == True{} : Bool}, hr)
            case Ar.TNum{y}:
              ct.or_l(String.eq(t, "integer"), String.eq(t, "number"), hk)
            case Ar.TStr{y}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TStr{y}}) == True{} : Bool}, hr)
            case Ar.TOne{}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TOne{}}) == True{} : Bool}, hr)
            case Ar.TObj{}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TObj{}}) == True{} : Bool}, hr)
            case Ar.TArr{}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TArr{}}) == True{} : Bool}, hr)
    case Ar.KNumber{}:
      match r:
        case None{}:
          {==}
        case Some{x}:
          match x:
            case Ar.TBool{b}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TBool{b}}) == True{} : Bool}, hr)
            case Ar.TNum{y}:
              ct.or_r(String.eq(t, "integer"), String.eq(t, "number"), hk)
            case Ar.TStr{y}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TStr{y}}) == True{} : Bool}, hr)
            case Ar.TOne{}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TOne{}}) == True{} : Bool}, hr)
            case Ar.TObj{}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TObj{}}) == True{} : Bool}, hr)
            case Ar.TArr{}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TArr{}}) == True{} : Bool}, hr)
    case Ar.KObject{}:
      match r:
        case None{}:
          {==}
        case Some{x}:
          match x:
            case Ar.TBool{b}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TBool{b}}) == True{} : Bool}, hr)
            case Ar.TNum{y}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TNum{y}}) == True{} : Bool}, hr)
            case Ar.TStr{y}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TStr{y}}) == True{} : Bool}, hr)
            case Ar.TOne{}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TOne{}}) == True{} : Bool}, hr)
            case Ar.TObj{}:
              hk
            case Ar.TArr{}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TArr{}}) == True{} : Bool}, hr)
    case Ar.KArray{}:
      match r:
        case None{}:
          {==}
        case Some{x}:
          match x:
            case Ar.TBool{b}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TBool{b}}) == True{} : Bool}, hr)
            case Ar.TNum{y}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TNum{y}}) == True{} : Bool}, hr)
            case Ar.TStr{y}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TStr{y}}) == True{} : Bool}, hr)
            case Ar.TOne{}:
              hk
            case Ar.TObj{}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TObj{}}) == True{} : Bool}, hr)
            case Ar.TArr{}:
              hk
    case Ar.KOther{}:
      match r:
        case None{}:
          {==}
        case Some{x}:
          match x:
            case Ar.TBool{b}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TBool{b}}) == True{} : Bool}, hr)
            case Ar.TNum{y}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TNum{y}}) == True{} : Bool}, hr)
            case Ar.TStr{y}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TStr{y}}) == True{} : Bool}, hr)
            case Ar.TOne{}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TOne{}}) == True{} : Bool}, hr)
            case Ar.TObj{}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TObj{}}) == True{} : Bool}, hr)
            case Ar.TArr{}:
              AB.ab.absurd({ArgRepair.ar_typed(Some{Ar.Prop{n, Some{t}, it}}, Some{Ar.TArr{}}) == True{} : Bool}, hr)

def ct.kind_of(+t: String, s: Bool, b: Bool, i: Bool, n: Bool, o: Bool, a: Bool, es: {String.eq(t, "string") == s : Bool}, eb: {String.eq(t, "boolean") == b : Bool}, ei: {String.eq(t, "integer") == i : Bool}, en: {String.eq(t, "number") == n : Bool}, eo: {String.eq(t, "object") == o : Bool}, ea: {String.eq(t, "array") == a : Bool}) -> {ct.kind_ok(t, Ar.kind.of(t, s, b, i, n, o, a)) == True{} : Bool}:
  match s:
    case True{}:
      es
    case False{}:
      match b:
        case True{}:
          eb
        case False{}:
          match i:
            case True{}:
              ei
            case False{}:
              match n:
                case True{}:
                  en
                case False{}:
                  match o:
                    case True{}:
                      eo
                    case False{}:
                      match a:
                        case True{}:
                          ea
                        case False{}:
                          {==}

# the kind a declared type names is that name
def ct.kind(+t: String) -> {ct.kind_ok(t, Ar.kind(t)) == True{} : Bool}:
  ct.kind_of(t, String.eq(t, "string"), String.eq(t, "boolean"), String.eq(t, "integer"), String.eq(t, "number"), String.eq(t, "object"), String.eq(t, "array"), {==}, {==}, {==}, {==}, {==}, {==})

# Readings
# --------

def ct.word_of(t: Bool, f: Bool) -> {ct.ok(Ar.KBoolean{}, Ar.word.of(t, f)) == True{} : Bool}:
  match t:
    case True{}:
      {==}
    case False{}:
      match f:
        case True{}:
          {==}
        case False{}:
          {==}

def ct.bool(m: Maybe<&2, String>) -> {ct.ok(Ar.KBoolean{}, Ar.spell.bool(m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{s}:
      +w = Ar.lower(Ar.trim(s))
      ct.word_of(Bool.or(String.eq(w, "true"), Bool.or(String.eq(w, "yes"), Bool.or(String.eq(w, "on"), String.eq(w, "1")))), Bool.or(String.eq(w, "false"), Bool.or(String.eq(w, "no"), Bool.or(String.eq(w, "off"), String.eq(w, "0")))))

def ct.fit(ok: Bool, -x: String) -> {ct.ok(Ar.KInteger{}, Ar.int.fit(ok, x)) == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def ct.neg_at(z: Bool, +c: String) -> {ct.ok(Ar.KInteger{}, Ar.int.neg.at(z, c)) == True{} : Bool}:
  match z:
    case True{}:
      {==}
    case False{}:
      ct.fit(Ar.at_most(c, "9223372036854775808"), SCon{'-', c})

def ct.sign(neg: Bool, +c: String) -> {ct.ok(Ar.KInteger{}, Ar.int.sign(neg, c)) == True{} : Bool}:
  match neg:
    case True{}:
      ct.neg_at(String.eq(c, "0"), c)
    case False{}:
      ct.fit(Ar.at_most(c, "9223372036854775807"), c)

def ct.digits_at(ok: Bool, neg: Bool, +d: String) -> {ct.ok(Ar.KInteger{}, Ar.int.digits.at(ok, neg, d)) == True{} : Bool}:
  match ok:
    case True{}:
      ct.sign(neg, Ar.canon(d))
    case False{}:
      {==}

def ct.digits(neg: Bool, +d: String) -> {ct.ok(Ar.KInteger{}, Ar.int.digits(neg, d)) == True{} : Bool}:
  ct.digits_at(Bool.and(Bool.not(String.is_empty(d)), Ar.digits(d)), neg, d)

def ct.signed(minus: Bool, plus: Bool, c: Char, t: String) -> {ct.ok(Ar.KInteger{}, Ar.int.signed(minus, plus, c, t)) == True{} : Bool}:
  match minus:
    case True{}:
      ct.digits(True{}, t)
    case False{}:
      match plus:
        case True{}:
          ct.digits(False{}, t)
        case False{}:
          ct.digits(False{}, SCon{c, t})

def ct.int(s: String) -> {ct.ok(Ar.KInteger{}, Ar.int(s)) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      ct.signed(Char.is_eq(c, '-'), Char.is_eq(c, '+'), c, t)

def ct.int_m(m: Maybe<&2, String>) -> {ct.ok(Ar.KInteger{}, Ar.spell.int(m)) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{s}:
      ct.int(Ar.trim(s))

def ct.one_at(b: Bool) -> {ct.ok(Ar.KArray{}, Ar.spell.one.at(b)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ct.one(it: Maybe<&2, String>) -> {ct.ok(Ar.KArray{}, Ar.spell.one(it)) == True{} : Bool}:
  match it:
    case None{}:
      {==}
    case Some{t}:
      ct.one_at(String.eq(t, "string"))

def ct.spell(k: Ar.Ty, it: Maybe<&2, String>, t: Maybe<&2, String>, n: Maybe<&2, String>, sh: Ar.Shape) -> {ct.ok(k, Ar.spell(k, it, t, n, sh)) == True{} : Bool}:
  match k:
    case Ar.KString{}:
      {==}
    case Ar.KBoolean{}:
      ct.bool(t)
    case Ar.KInteger{}:
      ct.int_m(t)
    case Ar.KNumber{}:
      match n:
        case None{}:
          {==}
        case Some{x}:
          {==}
    case Ar.KObject{}:
      match sh:
        case Ar.SPlain{}:
          {==}
        case Ar.SBrace{o}:
          match o:
            case True{}:
              {==}
            case False{}:
              {==}
        case Ar.SBracket{a}:
          {==}
    case Ar.KArray{}:
      match sh:
        case Ar.SPlain{}:
          ct.one(it)
        case Ar.SBrace{o}:
          ct.one(it)
        case Ar.SBracket{a}:
          match a:
            case True{}:
              {==}
            case False{}:
              {==}
    case Ar.KOther{}:
      {==}

def ct.text(k: Ar.Ty, -x: String) -> {ct.ok(k, Ar.as_text(k, x)) == True{} : Bool}:
  match k:
    case Ar.KString{}:
      {==}
    case Ar.KBoolean{}:
      {==}
    case Ar.KInteger{}:
      {==}
    case Ar.KNumber{}:
      {==}
    case Ar.KObject{}:
      {==}
    case Ar.KArray{}:
      {==}
    case Ar.KOther{}:
      {==}

# every reading of the kind k is of its type
def ct.val(+k: Ar.Ty, it: Maybe<&2, String>, v: Ar.Val) -> {ct.ok(k, Ar.coerce.val(k, it, v)) == True{} : Bool}:
  match v:
    case Ar.VNull{}:
      {==}
    case Ar.VBool{b}:
      ct.text(k, Ar.bool_text(b))
    case Ar.VNum{x}:
      ct.text(k, x)
    case Ar.VStr{t, n, sh}:
      ct.spell(k, it, t, n, sh)
    case Ar.VArr{}:
      {==}
    case Ar.VObj{}:
      {==}

def ArgRepair.arg_repair_coerce_typed(p, v):
  match p:
    case None{}:
      {==}
    case Some{q}:
      match q:
        case Ar.Prop{+n, k, +it}:
          match k:
            case None{}:
              {==}
            case Some{+t}:
              ct.typed(Ar.kind(t), t, n, it, Ar.coerce.val(Ar.kind(t), it, v), ct.kind(t), ct.val(Ar.kind(t), it, v))
