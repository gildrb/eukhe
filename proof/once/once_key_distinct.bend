# eukhe: the proof of LAW once_key_distinct
#
# PROOF: the entry answers each spelled request with its key
# (LE.oe.key_answers), so the two keys are equal; a key is the scope
# spelled before the id spelled, and two spelled strings that are equal
# spell the same string before the same rest (LE.oe.str_inj, twice).

import Base
import ../../bend/once.bend as O
import ../../bend/ffi_once.bend as FO
import ../../bend/wire.bend as Wr
import ../../laws/once.bend as Once
import ../../laws/base.bend as LawsBase
import ./base/entry.bend as LE

def ok.fst(-b: String, -d: String, p: {b == d : String} & {"" == "" : String}) -> {b == d : String}:
  (x, y) = p
  x

# the ids of two equal keys with the same scope spelling
def ok.ids(+b: String, +d: String, fb: {LawsBase.wire_fits(String.length(b)) == True{} : Bool}, fd: {LawsBase.wire_fits(String.length(d)) == True{} : Bool}, r: {Wr.put_str(b, "") == Wr.put_str(d, "") : String}) -> {b == d : String}:
  ok.fst(b, d, LE.oe.str_inj(b, d, "", "", fb, fd, r))

def ok.split(+a: String, +b: String, +c: String, +d: String, fb: {LawsBase.wire_fits(String.length(b)) == True{} : Bool}, fd: {LawsBase.wire_fits(String.length(d)) == True{} : Bool}, p: {a == c : String} & {Wr.put_str(b, "") == Wr.put_str(d, "") : String}) -> ({a == c : String} & {b == d : String}):
  (x, y) = p
  (x, ok.ids(b, d, fb, fd, y))

def ok.keys(+a: String, +b: String, +c: String, +d: String, +fa: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}, +fb: {LawsBase.wire_fits(String.length(b)) == True{} : Bool}, +fc: {LawsBase.wire_fits(String.length(c)) == True{} : Bool}, +fd: {LawsBase.wire_fits(String.length(d)) == True{} : Bool}, same: {FO.ffi(Once.on_spell_key(a, b)) == FO.ffi(Once.on_spell_key(c, d)) : String}) -> {O.key(a, b) == O.key(c, d) : String}:
  Equal.trans(String, O.key(a, b), FO.ffi(Once.on_spell_key(a, b)), O.key(c, d), Equal.sym(String, FO.ffi(Once.on_spell_key(a, b)), O.key(a, b), LE.oe.key_answers(a, b, fa, fb)), Equal.trans(String, FO.ffi(Once.on_spell_key(a, b)), FO.ffi(Once.on_spell_key(c, d)), O.key(c, d), same, LE.oe.key_answers(c, d, fc, fd)))

def ok.all(+a: String, +b: String, +c: String, +d: String, +fa: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}, +fb: {LawsBase.wire_fits(String.length(b)) == True{} : Bool}, +fc: {LawsBase.wire_fits(String.length(c)) == True{} : Bool}, +fd: {LawsBase.wire_fits(String.length(d)) == True{} : Bool}, same: {FO.ffi(Once.on_spell_key(a, b)) == FO.ffi(Once.on_spell_key(c, d)) : String}) -> ({a == c : String} & {b == d : String}):
  ok.split(a, b, c, d, fb, fd, LE.oe.str_inj(a, c, Wr.put_str(b, ""), Wr.put_str(d, ""), fa, fc, ok.keys(a, b, c, d, fa, fb, fc, fd, same)))

def Once.once_key_distinct(a, b, c, d, fa, fb, fc, fd, same):
  ok.all(a, b, c, d, fa, fb, fc, fd, same)
