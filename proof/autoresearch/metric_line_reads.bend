# eukhe: the proof of LAW metric_line_reads

import Base
import ../../bend/autoresearch/dec.bend as D
import ../../bend/autoresearch/line.bend as L
import ../../spec/autoresearch/decimal.bend as SD
import ../../spec/autoresearch/metric_line.bend as SL
import ../../laws/autoresearch/model.bend as Autoresearch
import ./base/line.bend as AL
import ./metric_line_reads/parse.bend as ALR
import ./metric_line_reads/value.bend as ALV

# the value fits: a canonical decimal worth the value as written
def alm.yes(-name: String, +neg: Bool, +int: List<&2, Nat>, +fs: List<&2, Nat>, eb: {Nat.is_le(D.len(ALV.alv.ds(int, fs)), 15n) == True{} : Bool}, hi: {SD.digits_ok(int) == True{} : Bool}, hf: {SD.digits_ok(fs) == True{} : Bool}) -> {Nat.is_le(SL.dlen(ALV.alv.sig(int, fs)), 15n) == True{} : Bool} & ({name == name : String} & ({SD.canon.ds(Bool.and(neg, L.any_d(ALV.alv.ds(int, fs))), ALV.alv.ds(int, fs), D.len(ALV.alv.f(fs))) == True{} : Bool} & {SD.same(D.Dec{Bool.and(neg, L.any_d(ALV.alv.ds(int, fs))), ALV.alv.ds(int, fs), D.len(ALV.alv.f(fs))}, D.Dec{neg, ALV.alv.app(int, fs), SL.dlen(fs)}) == True{} : Bool})):
  ((%ALV.alv.sig_eq(int, fs) : {Nat.is_le(_, 15n) == True{} : Bool}; eb), ({==}, (ALV.alv.canon_ok(neg, int, fs, hi, hf), ALV.alv.same(neg, ALV.alv.ds(int, fs), D.len(ALV.alv.f(fs)), SL.dlen(fs), ALV.alv.app(int, fs), ALV.alv.k(fs), ALV.alv.v1(int, fs), ALV.alv.e(int, fs)))))

# the value does not fit: nor do the spec's significant digits
def alm.no(+int: List<&2, Nat>, +fs: List<&2, Nat>, eb: {Nat.is_le(D.len(ALV.alv.ds(int, fs)), 15n) == False{} : Bool}) -> {Nat.is_le(SL.dlen(ALV.alv.sig(int, fs)), 15n) == False{} : Bool}:
  %ALV.alv.sig_eq(int, fs) : {Nat.is_le(_, 15n) == False{} : Bool}
  eb

# the 15-digit test, split
def alm.fit(b: Bool, -sp: String, -name: String, +neg: Bool, +int: List<&2, Nat>, fr: Maybe<&2, List<&2, Nat>>, -trail: String, eb: {Nat.is_le(D.len(ALV.alv.ds(int, L.frac_ds(fr))), 15n) == b : Bool}, hi: {SD.digits_ok(int) == True{} : Bool}, hf: {SD.digits_ok(L.frac_ds(fr)) == True{} : Bool}) -> SL.Means(L.canon.fit(b, name, neg, ALV.alv.ds(int, L.frac_ds(fr)), D.len(ALV.alv.f(L.frac_ds(fr)))), L.Parts{sp, name, neg, int, fr, trail}):
  match b:
    case False{}:
      match fr:
        case None{}:
          alm.no(int, Nil{}, eb)
        case Some{+x}:
          alm.no(int, x, eb)
    case True{}:
      match fr:
        case None{}:
          alm.yes(name, neg, int, Nil{}, eb, hi, hf)
        case Some{+x}:
          alm.yes(name, neg, int, x, eb, hi, hf)

def alm.fd_ok(frac: Maybe<&2, List<&2, Nat>>, hf: {SL.frac_ok(frac) == True{} : Bool}) -> {SD.digits_ok(L.frac_ds(frac)) == True{} : Bool}:
  match frac:
    case None{}:
      {==}
    case Some{+fs}:
      AL.al.and_r(SL.nonempty_ds(fs), SD.digits_ok(fs), hf)

def alm.frac(-sp: String, -name: String, +neg: Bool, +int: List<&2, Nat>, +frac: Maybe<&2, List<&2, Nat>>, -trail: String, hi: {SD.digits_ok(int) == True{} : Bool}, hf: {SL.frac_ok(frac) == True{} : Bool}) -> SL.Means(L.canon(L.Parts{sp, name, neg, int, frac, trail}), L.Parts{sp, name, neg, int, frac, trail}):
  alm.fit(Nat.is_le(D.len(ALV.alv.ds(int, L.frac_ds(frac))), 15n), sp, name, neg, int, frac, trail, {==}, hi, alm.fd_ok(frac, hf))

def alm.means(p: L.Parts, +ok: {SL.ok(p) == True{} : Bool}) -> SL.Means(L.canon(p), p):
  match p:
    case L.Parts{+sp, +name, +neg, +int, +frac, +trail}:
      +r2 = AL.al.and_r(Bool.and(SL.nonempty(name), SL.all_name(name)), Bool.and(Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)), Bool.and(SL.frac_ok(frac), SL.all_trail(trail))), AL.al.and_r(Bool.and(SL.nonempty(sp), SL.all_blank(sp)), Bool.and(Bool.and(SL.nonempty(name), SL.all_name(name)), Bool.and(Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)), Bool.and(SL.frac_ok(frac), SL.all_trail(trail)))), ok))
      alm.frac(sp, name, neg, int, frac, trail, AL.al.and_r(SL.nonempty_ds(int), SD.digits_ok(int), AL.al.and_l(Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)), Bool.and(SL.frac_ok(frac), SL.all_trail(trail)), r2)), AL.al.and_l(SL.frac_ok(frac), SL.all_trail(trail), AL.al.and_r(Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)), Bool.and(SL.frac_ok(frac), SL.all_trail(trail)), r2)))

def alm.reads(+p: L.Parts, +ok: {SL.ok(p) == True{} : Bool}) -> SL.Means(L.metric(SL.line(p)), p):
  %Equal.sym(Maybe<&2, L.Parts>, L.parse(SL.line(p)), Some{p}, ALR.alr.parse_line(p, ok)) : SL.Means(L.metric.of(_), p)
  alm.means(p, ok)

def Autoresearch.metric_line_reads(p, ok):
  alm.reads(p, ok)
