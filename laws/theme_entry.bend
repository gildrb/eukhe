# eukhe: the laws of area theme_entry: the theme entry
# (bend/ffi_theme.bend) as a whole, for every input string. The entry's
# other laws are in laws/theme.bend (section "The compiled entry", R6):
# theme_ffi_answers answers every request Rust writes with the rules'
# decision; this file pins every other input.
#
# R6 (laws/theme.bend): every request Rust writes is answered with the
#     rules' decision; any other input gets the error form.
# A1: every input the entry answers without the error form is a request
#     Rust writes (spec/theme/wire.bend `req`, spelled from the wire
#     primitives), every text, count and variable index within the wire
#     (`fits`), nothing after it; so theme_ffi_answers pins its answer:
#     theme_ffi_spelled.
# A2: every error the entry answers is exactly `E theme: malformed
#     request`: theme_ffi_refuses.

import Base
import ../bend/ffi_theme.bend as FTh
import ../bend/wire.bend as Wr
import ../spec/theme/wire.bend as Tw
import ./base.bend as LawsBase

# LAW theme_ffi_spelled (A1, R6): every input the entry does not answer
# with the error form is exactly one request Rust writes (Tw.req, from the
# wire primitives), every text, count and variable index within the wire
# EXCLUDES: a decision guessed for input that is no request (an unknown
#   tag, a list shorter than its count, a short text, a number past the
#   wire, a leading zero, input left over), a request spelled in a way
#   Rust never writes but the entry reads
law theme_ffi_spelled:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FTh.ffi(s)) == False{} : Bool}
  exs r: FTh.Req
  {s == Tw.req(r, "") : String} & {Tw.fits(r) == True{} : Bool}

# LAW theme_ffi_refuses (A2, R6): every error the entry answers is exactly
# `E theme: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form,
#   a decision that opens with 'E'
law theme_ffi_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FTh.ffi(s)) == True{} : Bool}
  {FTh.ffi(s) == Wr.err("theme: malformed request") : String}
