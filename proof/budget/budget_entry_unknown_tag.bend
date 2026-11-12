# eukhe: the proof of LAW budget_entry_unknown_tag
#
# PROOF: each spelled tag that fits reads back (be.nat; a use's tag as that
# use: be.use_nat, be.use_of), and the decoder's case on a tag past the
# known ones answers no request, which the entry answers with the error
# form.

import Base
import ../../laws/budget.bend as Budget
import ../../laws/base.bend as LawsBase
import ../../bend/budget.bend as B
import ../../bend/ffi_budget.bend as FBg
import ../../bend/wire.bend as Wr
import ./base/entry.bend as BE

# a request tag past 4
def ut.req(+m: Nat, +rest: String, fm: {LawsBase.wire_fits(5n+m) == True{} : Bool}) -> {FBg.ffi(Wr.put_nat(5n+m, rest)) == Wr.err("budget: malformed request") : String}:
  %BE.be.nat(5n+m, rest, fm) : {FBg.ffi.got(FBg.get_req.tag(_)) == Wr.err("budget: malformed request") : String}
  {==}

# a use tag past 2
def ut.use(+n: Nat, +rest: String, fn: {LawsBase.wire_fits(3n+n) == True{} : Bool}) -> {FBg.ffi(Wr.put_nat(0n, Wr.put_nat(3n+n, rest))) == Wr.err("budget: malformed request") : String}:
  %BE.be.nat(0n, Wr.put_nat(3n+n, rest), {==}) : {FBg.ffi.got(FBg.get_req.tag(_)) == Wr.err("budget: malformed request") : String}
  %BE.be.nat(3n+n, rest, fn) : {FBg.ffi.got(FBg.get_reserve(_)) == Wr.err("budget: malformed request") : String}
  {==}

# a phase tag past 2 in a reserve, after the use u
def ut.phase(+u: B.Use, +n: Nat, +rest: String, fn: {LawsBase.wire_fits(3n+n) == True{} : Bool}) -> {FBg.ffi(Wr.put_nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(3n+n, rest)))) == Wr.err("budget: malformed request") : String}:
  %BE.be.nat(0n, Wr.put_nat(Budget.sp_use_tag(u), Wr.put_nat(3n+n, rest)), {==}) : {FBg.ffi.got(FBg.get_req.tag(_)) == Wr.err("budget: malformed request") : String}
  %BE.be.use_nat(u, Wr.put_nat(3n+n, rest)) : {FBg.ffi.got(FBg.get_reserve(_)) == Wr.err("budget: malformed request") : String}
  %BE.be.use_of(u, Wr.put_nat(3n+n, rest)) : {FBg.ffi.got(_) == Wr.err("budget: malformed request") : String}
  %BE.be.nat(3n+n, rest, fn) : {FBg.ffi.got(FBg.get_reserve.phase(u, FBg.get_phase.tag(_))) == Wr.err("budget: malformed request") : String}
  {==}

# a phase tag past 2 in a carve
def ut.carve(+n: Nat, +rest: String, fn: {LawsBase.wire_fits(3n+n) == True{} : Bool}) -> {FBg.ffi(Wr.put_nat(2n, Wr.put_nat(3n+n, rest))) == Wr.err("budget: malformed request") : String}:
  %BE.be.nat(2n, Wr.put_nat(3n+n, rest), {==}) : {FBg.ffi.got(FBg.get_req.tag(_)) == Wr.err("budget: malformed request") : String}
  %BE.be.nat(3n+n, rest, fn) : {FBg.ffi.got(FBg.get_carve(FBg.get_phase.tag(_))) == Wr.err("budget: malformed request") : String}
  {==}

def Budget.budget_entry_unknown_tag(u, m, n, rest, fm, fn):
  (ut.req(m, rest, fm), (ut.use(n, rest, fn), (ut.phase(u, n, rest, fn), ut.carve(n, rest, fn))))
