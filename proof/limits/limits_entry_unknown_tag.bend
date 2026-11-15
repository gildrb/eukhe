# eukhe: the proof of LAW limits_entry_unknown_tag
#
# PROOF: each spelled tag that fits reads back (BE.be.nat; a kind's tag as
# that kind: limits_entry_answers' lpe.kind), and the decoder's case on a
# tag past the known ones answers no request, which the entry answers with
# the error form.

import Base
import ../../bend/limits.bend as L
import ../../bend/ffi_limits.bend as FL
import ../../bend/wire.bend as Wr
import ../../laws/limits.bend as Limits
import ../../laws/base.bend as LawsBase
import ../budget/base/entry.bend as BE
import ./limits_entry_answers.bend as PEntryAnswers

# a request tag past 7
def lut.req(+m: Nat, +rest: String, fm: {LawsBase.wire_fits(8n+m) == True{} : Bool}) -> {FL.ffi(Wr.put_nat(8n+m, rest)) == Wr.err("limits: malformed request") : String}:
  %BE.be.nat(8n+m, rest, fm) : {FL.ffi.got(FL.get_req.n(_)) == Wr.err("limits: malformed request") : String}
  {==}

# a kind tag past 5 in a profile
def lut.kind(+a: Nat, +rest: String, fa: {LawsBase.wire_fits(6n+a) == True{} : Bool}) -> {FL.ffi(Wr.put_nat(1n, Wr.put_nat(6n+a, rest))) == Wr.err("limits: malformed request") : String}:
  %BE.be.nat(1n, Wr.put_nat(6n+a, rest), {==}) : {FL.ffi.got(FL.get_req.n(_)) == Wr.err("limits: malformed request") : String}
  %BE.be.nat(6n+a, rest, fa) : {FL.ffi.got(FL.get_profile.k(FL.get_kind.n(_))) == Wr.err("limits: malformed request") : String}
  {==}

# an auth tag past 2 in a profile of kind k
def lut.auth(+k: L.Run, +b: Nat, +rest: String, fb: {LawsBase.wire_fits(3n+b) == True{} : Bool}) -> {FL.ffi(Wr.put_nat(1n, Wr.put_nat(Limits.sp_kind_tag(k), Wr.put_nat(3n+b, rest)))) == Wr.err("limits: malformed request") : String}:
  %BE.be.nat(1n, Wr.put_nat(Limits.sp_kind_tag(k), Wr.put_nat(3n+b, rest)), {==}) : {FL.ffi.got(FL.get_req.n(_)) == Wr.err("limits: malformed request") : String}
  %PEntryAnswers.lpe.kind(k, Wr.put_nat(3n+b, rest)) : {FL.ffi.got(FL.get_profile.k(_)) == Wr.err("limits: malformed request") : String}
  %BE.be.nat(3n+b, rest, fb) : {FL.ffi.got(FL.get_profile.a(k, FL.get_auth.n(_))) == Wr.err("limits: malformed request") : String}
  {==}

# a preset tag past 1
def lut.scale(+c: Nat, +rest: String, fc: {LawsBase.wire_fits(2n+c) == True{} : Bool}) -> {FL.ffi(Wr.put_nat(2n, Wr.put_nat(2n+c, rest))) == Wr.err("limits: malformed request") : String}:
  %BE.be.nat(2n, Wr.put_nat(2n+c, rest), {==}) : {FL.ffi.got(FL.get_req.n(_)) == Wr.err("limits: malformed request") : String}
  %BE.be.nat(2n+c, rest, fc) : {FL.ffi.got(FL.get_preset.c(FL.get_scale.n(_))) == Wr.err("limits: malformed request") : String}
  {==}

# a limit tag past 2 in a floor's limits
def lut.val(+d: Nat, +rest: String, fd: {LawsBase.wire_fits(3n+d) == True{} : Bool}) -> {FL.ffi(Wr.put_nat(5n, Wr.put_nat(3n+d, rest))) == Wr.err("limits: malformed request") : String}:
  %BE.be.nat(5n, Wr.put_nat(3n+d, rest), {==}) : {FL.ffi.got(FL.get_req.n(_)) == Wr.err("limits: malformed request") : String}
  %BE.be.nat(3n+d, rest, fd) : {FL.ffi.got(FL.get_floor.l(FL.get_lims.c(FL.get_val.n(_)))) == Wr.err("limits: malformed request") : String}
  {==}

def Limits.limits_entry_unknown_tag(k, m, a, b, c, d, rest, fm, fa, fb, fc, fd):
  (lut.req(m, rest, fm), (lut.kind(a, rest, fa), (lut.auth(k, b, rest, fb), (lut.scale(c, rest, fc), lut.val(d, rest, fd)))))
