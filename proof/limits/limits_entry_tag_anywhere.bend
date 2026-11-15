# eukhe: the proof of LAW limits_entry_tag_anywhere
#
# PROOF: the fields spelled before the unknown tag read back
# (limits_entry_answers' lpe lemmas); the unknown tag reads as no value
# (BE.be.nat, then the decoder's case past the known ones); no value at
# any stage carries through every later stage to no request, which the
# entry answers with the error form. A preset's limit: the list's count
# reads back, the presets before it read back, its limits read as no
# value, so the list does (ltw.items, by induction on the presets).

import Base
import ../../bend/budget.bend as B
import ../../bend/limits.bend as L
import ../../bend/ffi_limits.bend as FL
import ../../bend/wire.bend as Wr
import ../../laws/limits.bend as Limits
import ../../laws/base.bend as LawsBase
import ../../laws/budget.bend as Budget
import ../../laws/wire.bend as Wire
import ../budget/base/entry.bend as BE
import ./limits_entry_answers.bend as PEntryAnswers
import ./limits_entry_unknown_tag.bend as PUnknownTag

# Maybe
# -----

def ltw.MIf(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# None is no Some
def ltw.none_some(-A: Data, -b: A, -G: Type, e: {None{} == Some{b} : Maybe<&2, A>}) -> G:
  %e : ltw.MIf(A, _, G)
  Unit{}

def ltw.get(-A: Data, m: Maybe<&2, A>, z: A) -> A:
  match m:
    case None{}:
      z
    case Some{x}:
      x

# Some is one to one
def ltw.some_inj(-A: Data, +a: A, -b: A, e: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  Equal.cong(Maybe<&2, A>, A, m => ltw.get(A, m, a), Some{a}, Some{b}, e)

# An unknown tag reads as no value
# --------------------------------

def ltw.kind(+m: Nat, +rest: String, f: {LawsBase.wire_fits(6n+m) == True{} : Bool}) -> {Wr.Bad{} == FL.get_kind(Wr.put_nat(6n+m, rest)) : Wr.Dec<L.Run>}:
  %BE.be.nat(6n+m, rest, f) : {Wr.Bad{} == FL.get_kind.n(_) : Wr.Dec<L.Run>}
  {==}

def ltw.auth(+m: Nat, +rest: String, f: {LawsBase.wire_fits(3n+m) == True{} : Bool}) -> {Wr.Bad{} == FL.get_auth(Wr.put_nat(3n+m, rest)) : Wr.Dec<L.Auth>}:
  %BE.be.nat(3n+m, rest, f) : {Wr.Bad{} == FL.get_auth.n(_) : Wr.Dec<L.Auth>}
  {==}

def ltw.val(+m: Nat, +rest: String, f: {LawsBase.wire_fits(3n+m) == True{} : Bool}) -> {Wr.Bad{} == FL.get_val(Wr.put_nat(3n+m, rest)) : Wr.Dec<L.Val>}:
  %BE.be.nat(3n+m, rest, f) : {Wr.Bad{} == FL.get_val.n(_) : Wr.Dec<L.Val>}
  {==}

# limits cut at a dimension whose tag reads as no value read as none
def ltw.lims(l: L.Lims, d: B.Dim, +bad: String, h: {Limits.sp_fit_lims(l) == True{} : Bool}, hb: {Wr.Bad{} == FL.get_val(bad) : Wr.Dec<L.Val>}) -> {Wr.Bad{} == FL.get_lims(Limits.sp_w_lims_cut(l, d, bad)) : Wr.Dec<L.Lims>}:
  match l:
    case L.Lims{+c, +k, +m, +n, +r}:
      match d:
        case B.Cost{}:
          %hb : {Wr.Bad{} == FL.get_lims.c(_) : Wr.Dec<L.Lims>}
          {==}
        case B.Tok{}:
          +b2 = Bool.and(Limits.sp_fit_val(k), Bool.and(Limits.sp_fit_val(m), Bool.and(Limits.sp_fit_val(n), Limits.sp_fit_val(r))))
          +fc = BE.be.and_l(Limits.sp_fit_val(c), b2, h)
          %PEntryAnswers.lpe.val(c, bad, fc) : {Wr.Bad{} == FL.get_lims.c(_) : Wr.Dec<L.Lims>}
          %hb : {Wr.Bad{} == FL.get_lims.k(c, _) : Wr.Dec<L.Lims>}
          {==}
        case B.Time{}:
          +h0 = h
          +b3 = Bool.and(Limits.sp_fit_val(m), Bool.and(Limits.sp_fit_val(n), Limits.sp_fit_val(r)))
          +b2 = Bool.and(Limits.sp_fit_val(k), b3)
          +fc = BE.be.and_l(Limits.sp_fit_val(c), b2, h0)
          +h1 = BE.be.and_r(Limits.sp_fit_val(c), b2, h0)
          +fk = BE.be.and_l(Limits.sp_fit_val(k), b3, h1)
          %PEntryAnswers.lpe.val(c, Limits.sp_w_val(k, bad), fc) : {Wr.Bad{} == FL.get_lims.c(_) : Wr.Dec<L.Lims>}
          %PEntryAnswers.lpe.val(k, bad, fk) : {Wr.Bad{} == FL.get_lims.k(c, _) : Wr.Dec<L.Lims>}
          %hb : {Wr.Bad{} == FL.get_lims.m(c, k, _) : Wr.Dec<L.Lims>}
          {==}
        case B.Calls{}:
          +h0 = h
          +b4 = Bool.and(Limits.sp_fit_val(n), Limits.sp_fit_val(r))
          +b3 = Bool.and(Limits.sp_fit_val(m), b4)
          +b2 = Bool.and(Limits.sp_fit_val(k), b3)
          +fc = BE.be.and_l(Limits.sp_fit_val(c), b2, h0)
          +h1 = BE.be.and_r(Limits.sp_fit_val(c), b2, h0)
          +fk = BE.be.and_l(Limits.sp_fit_val(k), b3, h1)
          +h2 = BE.be.and_r(Limits.sp_fit_val(k), b3, h1)
          +fm = BE.be.and_l(Limits.sp_fit_val(m), b4, h2)
          %PEntryAnswers.lpe.val(c, Limits.sp_w_val(k, Limits.sp_w_val(m, bad)), fc) : {Wr.Bad{} == FL.get_lims.c(_) : Wr.Dec<L.Lims>}
          %PEntryAnswers.lpe.val(k, Limits.sp_w_val(m, bad), fk) : {Wr.Bad{} == FL.get_lims.k(c, _) : Wr.Dec<L.Lims>}
          %PEntryAnswers.lpe.val(m, bad, fm) : {Wr.Bad{} == FL.get_lims.m(c, k, _) : Wr.Dec<L.Lims>}
          %hb : {Wr.Bad{} == FL.get_lims.n(c, k, m, _) : Wr.Dec<L.Lims>}
          {==}
        case B.Reqs{}:
          +h0 = h
          +b4 = Bool.and(Limits.sp_fit_val(n), Limits.sp_fit_val(r))
          +b3 = Bool.and(Limits.sp_fit_val(m), b4)
          +b2 = Bool.and(Limits.sp_fit_val(k), b3)
          +fc = BE.be.and_l(Limits.sp_fit_val(c), b2, h0)
          +h1 = BE.be.and_r(Limits.sp_fit_val(c), b2, h0)
          +fk = BE.be.and_l(Limits.sp_fit_val(k), b3, h1)
          +h2 = BE.be.and_r(Limits.sp_fit_val(k), b3, h1)
          +fm = BE.be.and_l(Limits.sp_fit_val(m), b4, h2)
          +h3 = BE.be.and_r(Limits.sp_fit_val(m), b4, h2)
          +fn = BE.be.and_l(Limits.sp_fit_val(n), Limits.sp_fit_val(r), h3)
          %PEntryAnswers.lpe.val(c, Limits.sp_w_val(k, Limits.sp_w_val(m, Limits.sp_w_val(n, bad))), fc) : {Wr.Bad{} == FL.get_lims.c(_) : Wr.Dec<L.Lims>}
          %PEntryAnswers.lpe.val(k, Limits.sp_w_val(m, Limits.sp_w_val(n, bad)), fk) : {Wr.Bad{} == FL.get_lims.k(c, _) : Wr.Dec<L.Lims>}
          %PEntryAnswers.lpe.val(m, Limits.sp_w_val(n, bad), fm) : {Wr.Bad{} == FL.get_lims.m(c, k, _) : Wr.Dec<L.Lims>}
          %PEntryAnswers.lpe.val(n, bad, fn) : {Wr.Bad{} == FL.get_lims.n(c, k, m, _) : Wr.Dec<L.Lims>}
          %hb : {Wr.Bad{} == FL.get_lims.r(c, k, m, n, _) : Wr.Dec<L.Lims>}
          {==}

# The presets
# -----------

# the item loop on what a cut of the presets spells, if any
def ltw.items_dec(r: Maybe<&2, String>, n: Nat) -> Maybe<&2, Wr.Dec<List<&2, L.Lims>>>:
  match r:
    case None{}:
      None{}
    case Some{s}:
      Some{LawsBase.wire_items(~L.Lims, ~FL.get_lims, n, s)}

# no list, if the cut spells anything
def ltw.items_bad(r: Maybe<&2, String>) -> Maybe<&2, Wr.Dec<List<&2, L.Lims>>>:
  match r:
    case None{}:
      None{}
    case Some{s}:
      Some{Wr.Bad{}}

# a preset before the cut reads back, so the loop reads no list as the
# loop after it does
def ltw.items_step(r: Maybe<&2, String>, +h: L.Lims, +n: Nat, fh: {Limits.sp_fit_lims(h) == True{} : Bool}, ih: {ltw.items_dec(r, n) == ltw.items_bad(r) : Maybe<&2, Wr.Dec<List<&2, L.Lims>>>}) -> {ltw.items_dec(Limits.sp_w_items_cut.then(h, r), 1n+n) == ltw.items_bad(Limits.sp_w_items_cut.then(h, r)) : Maybe<&2, Wr.Dec<List<&2, L.Lims>>>}:
  match r:
    case None{}:
      {==}
    case Some{+s}:
      +e = ltw.some_inj(Wr.Dec<List<&2, L.Lims>>, LawsBase.wire_items(~L.Lims, ~FL.get_lims, n, s), Wr.Bad{}, ih)
      %PEntryAnswers.lpe.lims(h, s, fh) : {Some{LawsBase.wire_items.then(L.Lims, _, r => LawsBase.wire_items(~L.Lims, ~FL.get_lims, n, r))} == Some{Wr.Bad{}} : Maybe<&2, Wr.Dec<List<&2, L.Lims>>>}
      %Equal.sym(Wr.Dec<List<&2, L.Lims>>, LawsBase.wire_items(~L.Lims, ~FL.get_lims, n, s), Wr.Bad{}, e) : {Some{LawsBase.wire_items.cons(L.Lims, h, _)} == Some{Wr.Bad{}} : Maybe<&2, Wr.Dec<List<&2, L.Lims>>>}
      {==}

# presets cut at the j-th one's limit whose tag reads as no value read
# as no list
def ltw.items(ps: List<&2, L.Lims>, j: Nat, +d: B.Dim, +bad: String, fp: {Limits.sp_fit_limss(ps) == True{} : Bool}, hb: {Wr.Bad{} == FL.get_val(bad) : Wr.Dec<L.Val>}) -> {ltw.items_dec(Limits.sp_w_items_cut(ps, j, d, bad), List.length(&2, L.Lims, ps)) == ltw.items_bad(Limits.sp_w_items_cut(ps, j, d, bad)) : Maybe<&2, Wr.Dec<List<&2, L.Lims>>>}:
  match ps:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      match j:
        case 0n:
          +fh = BE.be.and_l(Limits.sp_fit_lims(h), Limits.sp_fit_limss(t), fp)
          %ltw.lims(h, d, bad, fh, hb) : {Some{LawsBase.wire_items.then(L.Lims, _, r => LawsBase.wire_items(~L.Lims, ~FL.get_lims, List.length(&2, L.Lims, t), r))} == Some{Wr.Bad{}} : Maybe<&2, Wr.Dec<List<&2, L.Lims>>>}
          {==}
        case 1n++i:
          +h0 = fp
          +fh = BE.be.and_l(Limits.sp_fit_lims(h), Limits.sp_fit_limss(t), h0)
          +ft = BE.be.and_r(Limits.sp_fit_lims(h), Limits.sp_fit_limss(t), h0)
          ltw.items_step(Limits.sp_w_items_cut(t, i, d, bad), h, List.length(&2, L.Lims, t), fh, ltw.items(t, i, d, bad, ft, hb))

# The requests
# ------------

# a fill's head reads back; the fill goes on at its limits set
def ltw.fill_head(+t: L.Toggle, +k: L.Run, +a: L.Auth, +x: String) -> {FL.ffi.got(FL.get_fill.set(t, k, a, FL.get_lims(x))) == FL.ffi(Limits.sp_w_fill_head(t, k, a, x)) : String}:
  +g = FL.ffi.got(FL.get_fill.set(t, k, a, FL.get_lims(x)))
  %BE.be.nat(0n, Wr.put_bool(Limits.sp_on(t), Wr.put_nat(Limits.sp_kind_tag(k), Wr.put_nat(Limits.sp_auth_tag(a), x))), {==}) : {g == FL.ffi.got(FL.get_req.n(_)) : String}
  %PEntryAnswers.lpe.toggle(t, Wr.put_nat(Limits.sp_kind_tag(k), Wr.put_nat(Limits.sp_auth_tag(a), x))) : {g == FL.ffi.got(FL.get_fill.t(_)) : String}
  %PEntryAnswers.lpe.kind(k, Wr.put_nat(Limits.sp_auth_tag(a), x)) : {g == FL.ffi.got(FL.get_fill.k(t, _)) : String}
  %PEntryAnswers.lpe.auth(a, x) : {g == FL.ffi.got(FL.get_fill.a(t, k, _)) : String}
  {==}

# a fill cut in its j-th preset: the count and the presets before it read
# back, the cut preset reads as no list
def ltw.fill_ps(r: Maybe<&2, String>, +t: L.Toggle, +k: L.Run, +a: L.Auth, +set: L.Lims, +n: Nat, +s: String, fs: {Limits.sp_fit_lims(set) == True{} : Bool}, fc: {LawsBase.wire_fits(n) == True{} : Bool}, ih: {ltw.items_dec(r, n) == ltw.items_bad(r) : Maybe<&2, Wr.Dec<List<&2, L.Lims>>>}, at: {Limits.sp_w_fill_cut.ps(t, k, a, set, n, r) == Some{s} : Maybe<&2, String>}) -> {FL.ffi(s) == Wr.err("limits: malformed request") : String}:
  match r:
    case None{}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)
    case Some{+u}:
      +e = ltw.some_inj(Wr.Dec<List<&2, L.Lims>>, LawsBase.wire_items(~L.Lims, ~FL.get_lims, n, u), Wr.Bad{}, ih)
      %ltw.some_inj(String, Limits.sp_w_fill_head(t, k, a, Limits.sp_w_lims(set, Wr.put_nat(n, u))), s, at) : {FL.ffi(_) == Wr.err("limits: malformed request") : String}
      %ltw.fill_head(t, k, a, Limits.sp_w_lims(set, Wr.put_nat(n, u))) : {_ == Wr.err("limits: malformed request") : String}
      %PEntryAnswers.lpe.lims(set, Wr.put_nat(n, u), fs) : {FL.ffi.got(FL.get_fill.set(t, k, a, _)) == Wr.err("limits: malformed request") : String}
      %Equal.sym(Wr.Dec<List<&2, L.Lims>>, Wr.get_list(~L.Lims, ~FL.get_lims, Wr.put_nat(n, u)), LawsBase.wire_read_list(~L.Lims, ~FL.get_lims, Wr.put_nat(n, u)), Wire.wire_list_reads_items(~L.Lims, ~FL.get_lims, Wr.put_nat(n, u))) : {FL.ffi.got(FL.get_fill.ps(t, k, a, set, _)) == Wr.err("limits: malformed request") : String}
      %BE.be.nat(n, u, fc) : {FL.ffi.got(FL.get_fill.ps(t, k, a, set, LawsBase.wire_read_list.count(~L.Lims, ~FL.get_lims, _))) == Wr.err("limits: malformed request") : String}
      %Equal.sym(Wr.Dec<List<&2, L.Lims>>, LawsBase.wire_items(~L.Lims, ~FL.get_lims, n, u), Wr.Bad{}, e) : {FL.ffi.got(FL.get_fill.ps(t, k, a, set, _)) == Wr.err("limits: malformed request") : String}
      {==}

# a fill
def ltw.fill(p: Limits.Spot, +t: L.Toggle, +k: L.Run, +a: L.Auth, +set: L.Lims, +ps: List<&2, L.Lims>, +own: L.Lims, +m: Nat, +rest: String, +s: String, fit: {Limits.sp_fit_req(FL.QFill{t, k, a, set, ps, own}) == True{} : Bool}, fu: {LawsBase.wire_fits(Limits.sp_unknown(p, m)) == True{} : Bool}, at: {Limits.sp_w_fill_cut(p, t, k, a, set, ps, own, Wr.put_nat(Limits.sp_unknown(p, m), rest)) == Some{s} : Maybe<&2, String>}) -> {FL.ffi(s) == Wr.err("limits: malformed request") : String}:
  match p:
    case Limits.AtReq{}:
      %ltw.some_inj(String, Wr.put_nat(8n+m, rest), s, at) : {FL.ffi(_) == Wr.err("limits: malformed request") : String}
      PUnknownTag.lut.req(m, rest, fu)
    case Limits.AtKind{}:
      %ltw.some_inj(String, Wr.put_nat(0n, Wr.put_bool(Limits.sp_on(t), Wr.put_nat(6n+m, rest))), s, at) : {FL.ffi(_) == Wr.err("limits: malformed request") : String}
      %BE.be.nat(0n, Wr.put_bool(Limits.sp_on(t), Wr.put_nat(6n+m, rest)), {==}) : {FL.ffi.got(FL.get_req.n(_)) == Wr.err("limits: malformed request") : String}
      %PEntryAnswers.lpe.toggle(t, Wr.put_nat(6n+m, rest)) : {FL.ffi.got(FL.get_fill.t(_)) == Wr.err("limits: malformed request") : String}
      %ltw.kind(m, rest, fu) : {FL.ffi.got(FL.get_fill.k(t, _)) == Wr.err("limits: malformed request") : String}
      {==}
    case Limits.AtAuth{}:
      %ltw.some_inj(String, Wr.put_nat(0n, Wr.put_bool(Limits.sp_on(t), Wr.put_nat(Limits.sp_kind_tag(k), Wr.put_nat(3n+m, rest)))), s, at) : {FL.ffi(_) == Wr.err("limits: malformed request") : String}
      %BE.be.nat(0n, Wr.put_bool(Limits.sp_on(t), Wr.put_nat(Limits.sp_kind_tag(k), Wr.put_nat(3n+m, rest))), {==}) : {FL.ffi.got(FL.get_req.n(_)) == Wr.err("limits: malformed request") : String}
      %PEntryAnswers.lpe.toggle(t, Wr.put_nat(Limits.sp_kind_tag(k), Wr.put_nat(3n+m, rest))) : {FL.ffi.got(FL.get_fill.t(_)) == Wr.err("limits: malformed request") : String}
      %PEntryAnswers.lpe.kind(k, Wr.put_nat(3n+m, rest)) : {FL.ffi.got(FL.get_fill.k(t, _)) == Wr.err("limits: malformed request") : String}
      %ltw.auth(m, rest, fu) : {FL.ffi.got(FL.get_fill.a(t, k, _)) == Wr.err("limits: malformed request") : String}
      {==}
    case Limits.AtScale{}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)
    case Limits.InLims{+d}:
      +b3 = Bool.and(Limits.sp_fit_limss(ps), Limits.sp_fit_lims(own))
      +b2 = Bool.and(LawsBase.wire_fits(List.length(&2, L.Lims, ps)), b3)
      +fs = BE.be.and_l(Limits.sp_fit_lims(set), b2, fit)
      +cut = Limits.sp_w_lims_cut(set, d, Wr.put_nat(3n+m, rest))
      %ltw.some_inj(String, Limits.sp_w_fill_head(t, k, a, cut), s, at) : {FL.ffi(_) == Wr.err("limits: malformed request") : String}
      %ltw.fill_head(t, k, a, cut) : {_ == Wr.err("limits: malformed request") : String}
      %ltw.lims(set, d, Wr.put_nat(3n+m, rest), fs, ltw.val(m, rest, fu)) : {FL.ffi.got(FL.get_fill.set(t, k, a, _)) == Wr.err("limits: malformed request") : String}
      {==}
    case Limits.InPreset{+j, +d}:
      +h0 = fit
      +b3 = Bool.and(Limits.sp_fit_limss(ps), Limits.sp_fit_lims(own))
      +b2 = Bool.and(LawsBase.wire_fits(List.length(&2, L.Lims, ps)), b3)
      +fs = BE.be.and_l(Limits.sp_fit_lims(set), b2, h0)
      +h1 = BE.be.and_r(Limits.sp_fit_lims(set), b2, h0)
      +fc = BE.be.and_l(LawsBase.wire_fits(List.length(&2, L.Lims, ps)), b3, h1)
      +h2 = BE.be.and_r(LawsBase.wire_fits(List.length(&2, L.Lims, ps)), b3, h1)
      +fp = BE.be.and_l(Limits.sp_fit_limss(ps), Limits.sp_fit_lims(own), h2)
      +bad = Wr.put_nat(3n+m, rest)
      ltw.fill_ps(Limits.sp_w_items_cut(ps, j, d, bad), t, k, a, set, List.length(&2, L.Lims, ps), s, fs, fc, ltw.items(ps, j, d, bad, fp, ltw.val(m, rest, fu)), at)
    case Limits.InOwn{+d}:
      +h0 = fit
      +b3 = Bool.and(Limits.sp_fit_limss(ps), Limits.sp_fit_lims(own))
      +b2 = Bool.and(LawsBase.wire_fits(List.length(&2, L.Lims, ps)), b3)
      +fs = BE.be.and_l(Limits.sp_fit_lims(set), b2, h0)
      +h1 = BE.be.and_r(Limits.sp_fit_lims(set), b2, h0)
      +fc = BE.be.and_l(LawsBase.wire_fits(List.length(&2, L.Lims, ps)), b3, h1)
      +h2 = BE.be.and_r(LawsBase.wire_fits(List.length(&2, L.Lims, ps)), b3, h1)
      +fp = BE.be.and_l(Limits.sp_fit_limss(ps), Limits.sp_fit_lims(own), h2)
      +fo = BE.be.and_r(Limits.sp_fit_limss(ps), Limits.sp_fit_lims(own), h2)
      +cut = Limits.sp_w_lims_cut(own, d, Wr.put_nat(3n+m, rest))
      +x = Limits.sp_w_lims(set, Wr.put_list(~L.Lims, ~Limits.sp_w_lims, ps, cut))
      %ltw.some_inj(String, Limits.sp_w_fill_head(t, k, a, x), s, at) : {FL.ffi(_) == Wr.err("limits: malformed request") : String}
      %ltw.fill_head(t, k, a, x) : {_ == Wr.err("limits: malformed request") : String}
      %PEntryAnswers.lpe.lims(set, Wr.put_list(~L.Lims, ~Limits.sp_w_lims, ps, cut), fs) : {FL.ffi.got(FL.get_fill.set(t, k, a, _)) == Wr.err("limits: malformed request") : String}
      %PEntryAnswers.lpe.limss(ps, cut, fc, fp) : {FL.ffi.got(FL.get_fill.ps(t, k, a, set, _)) == Wr.err("limits: malformed request") : String}
      %ltw.lims(own, d, Wr.put_nat(3n+m, rest), fo, ltw.val(m, rest, fu)) : {FL.ffi.got(FL.get_fill.own(t, k, a, set, ps, _)) == Wr.err("limits: malformed request") : String}
      {==}

# a request with no tag but its own
def ltw.only(p: Limits.Spot, +m: Nat, +rest: String, +s: String, fu: {LawsBase.wire_fits(Limits.sp_unknown(p, m)) == True{} : Bool}, at: {Limits.sp_w_only_cut(p, Wr.put_nat(Limits.sp_unknown(p, m), rest)) == Some{s} : Maybe<&2, String>}) -> {FL.ffi(s) == Wr.err("limits: malformed request") : String}:
  match p:
    case Limits.AtReq{}:
      %ltw.some_inj(String, Wr.put_nat(8n+m, rest), s, at) : {FL.ffi(_) == Wr.err("limits: malformed request") : String}
      PUnknownTag.lut.req(m, rest, fu)
    case Limits.AtKind{}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)
    case Limits.AtAuth{}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)
    case Limits.AtScale{}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)
    case Limits.InLims{d}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)
    case Limits.InPreset{j, d}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)
    case Limits.InOwn{d}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)

# a profile
def ltw.profile(p: Limits.Spot, +k: L.Run, -a: L.Auth, +m: Nat, +rest: String, +s: String, fu: {LawsBase.wire_fits(Limits.sp_unknown(p, m)) == True{} : Bool}, at: {Limits.sp_w_req_cut(FL.QProfile{k, a}, p, Wr.put_nat(Limits.sp_unknown(p, m), rest)) == Some{s} : Maybe<&2, String>}) -> {FL.ffi(s) == Wr.err("limits: malformed request") : String}:
  match p:
    case Limits.AtReq{}:
      %ltw.some_inj(String, Wr.put_nat(8n+m, rest), s, at) : {FL.ffi(_) == Wr.err("limits: malformed request") : String}
      PUnknownTag.lut.req(m, rest, fu)
    case Limits.AtKind{}:
      %ltw.some_inj(String, Wr.put_nat(1n, Wr.put_nat(6n+m, rest)), s, at) : {FL.ffi(_) == Wr.err("limits: malformed request") : String}
      PUnknownTag.lut.kind(m, rest, fu)
    case Limits.AtAuth{}:
      %ltw.some_inj(String, Wr.put_nat(1n, Wr.put_nat(Limits.sp_kind_tag(k), Wr.put_nat(3n+m, rest))), s, at) : {FL.ffi(_) == Wr.err("limits: malformed request") : String}
      PUnknownTag.lut.auth(k, m, rest, fu)
    case Limits.AtScale{}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)
    case Limits.InLims{d}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)
    case Limits.InPreset{j, d}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)
    case Limits.InOwn{d}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)

# a preset
def ltw.preset(p: Limits.Spot, +c: L.Scale, +k: L.Run, -a: L.Auth, +m: Nat, +rest: String, +s: String, fu: {LawsBase.wire_fits(Limits.sp_unknown(p, m)) == True{} : Bool}, at: {Limits.sp_w_req_cut(FL.QPreset{c, k, a}, p, Wr.put_nat(Limits.sp_unknown(p, m), rest)) == Some{s} : Maybe<&2, String>}) -> {FL.ffi(s) == Wr.err("limits: malformed request") : String}:
  match p:
    case Limits.AtReq{}:
      %ltw.some_inj(String, Wr.put_nat(8n+m, rest), s, at) : {FL.ffi(_) == Wr.err("limits: malformed request") : String}
      PUnknownTag.lut.req(m, rest, fu)
    case Limits.AtKind{}:
      %ltw.some_inj(String, Wr.put_nat(2n, Wr.put_nat(Limits.sp_scale_tag(c), Wr.put_nat(6n+m, rest))), s, at) : {FL.ffi(_) == Wr.err("limits: malformed request") : String}
      %BE.be.nat(2n, Wr.put_nat(Limits.sp_scale_tag(c), Wr.put_nat(6n+m, rest)), {==}) : {FL.ffi.got(FL.get_req.n(_)) == Wr.err("limits: malformed request") : String}
      %PEntryAnswers.lpe.scale(c, Wr.put_nat(6n+m, rest)) : {FL.ffi.got(FL.get_preset.c(_)) == Wr.err("limits: malformed request") : String}
      %ltw.kind(m, rest, fu) : {FL.ffi.got(FL.get_preset.k(c, _)) == Wr.err("limits: malformed request") : String}
      {==}
    case Limits.AtAuth{}:
      %ltw.some_inj(String, Wr.put_nat(2n, Wr.put_nat(Limits.sp_scale_tag(c), Wr.put_nat(Limits.sp_kind_tag(k), Wr.put_nat(3n+m, rest)))), s, at) : {FL.ffi(_) == Wr.err("limits: malformed request") : String}
      %BE.be.nat(2n, Wr.put_nat(Limits.sp_scale_tag(c), Wr.put_nat(Limits.sp_kind_tag(k), Wr.put_nat(3n+m, rest))), {==}) : {FL.ffi.got(FL.get_req.n(_)) == Wr.err("limits: malformed request") : String}
      %PEntryAnswers.lpe.scale(c, Wr.put_nat(Limits.sp_kind_tag(k), Wr.put_nat(3n+m, rest))) : {FL.ffi.got(FL.get_preset.c(_)) == Wr.err("limits: malformed request") : String}
      %PEntryAnswers.lpe.kind(k, Wr.put_nat(3n+m, rest)) : {FL.ffi.got(FL.get_preset.k(c, _)) == Wr.err("limits: malformed request") : String}
      %ltw.auth(m, rest, fu) : {FL.ffi.got(FL.get_preset.a(c, k, _)) == Wr.err("limits: malformed request") : String}
      {==}
    case Limits.AtScale{}:
      %ltw.some_inj(String, Wr.put_nat(2n, Wr.put_nat(2n+m, rest)), s, at) : {FL.ffi(_) == Wr.err("limits: malformed request") : String}
      PUnknownTag.lut.scale(m, rest, fu)
    case Limits.InLims{d}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)
    case Limits.InPreset{j, d}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)
    case Limits.InOwn{d}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)

# a floor
def ltw.floor(p: Limits.Spot, +l: L.Lims, -c: B.Ask, -keep: B.Ask, +m: Nat, +rest: String, +s: String, fit: {Limits.sp_fit_req(FL.QFloor{l, c, keep}) == True{} : Bool}, fu: {LawsBase.wire_fits(Limits.sp_unknown(p, m)) == True{} : Bool}, at: {Limits.sp_w_req_cut(FL.QFloor{l, c, keep}, p, Wr.put_nat(Limits.sp_unknown(p, m), rest)) == Some{s} : Maybe<&2, String>}) -> {FL.ffi(s) == Wr.err("limits: malformed request") : String}:
  match p:
    case Limits.AtReq{}:
      %ltw.some_inj(String, Wr.put_nat(8n+m, rest), s, at) : {FL.ffi(_) == Wr.err("limits: malformed request") : String}
      PUnknownTag.lut.req(m, rest, fu)
    case Limits.AtKind{}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)
    case Limits.AtAuth{}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)
    case Limits.AtScale{}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)
    case Limits.InLims{+d}:
      +fl = BE.be.and_l(Limits.sp_fit_lims(l), Bool.and(Budget.sp_fit_ask(c), Budget.sp_fit_ask(keep)), fit)
      +cut = Limits.sp_w_lims_cut(l, d, Wr.put_nat(3n+m, rest))
      %ltw.some_inj(String, Wr.put_nat(5n, cut), s, at) : {FL.ffi(_) == Wr.err("limits: malformed request") : String}
      %BE.be.nat(5n, cut, {==}) : {FL.ffi.got(FL.get_req.n(_)) == Wr.err("limits: malformed request") : String}
      %ltw.lims(l, d, Wr.put_nat(3n+m, rest), fl, ltw.val(m, rest, fu)) : {FL.ffi.got(FL.get_floor.l(_)) == Wr.err("limits: malformed request") : String}
      {==}
    case Limits.InPreset{j, d}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)
    case Limits.InOwn{d}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)

# a renewal
def ltw.renew(p: Limits.Spot, +l: L.Lims, -mark: B.Amt, -now: Nat, -a: B.Acct, +m: Nat, +rest: String, +s: String, fit: {Limits.sp_fit_req(FL.QRenew{l, mark, now, a}) == True{} : Bool}, fu: {LawsBase.wire_fits(Limits.sp_unknown(p, m)) == True{} : Bool}, at: {Limits.sp_w_req_cut(FL.QRenew{l, mark, now, a}, p, Wr.put_nat(Limits.sp_unknown(p, m), rest)) == Some{s} : Maybe<&2, String>}) -> {FL.ffi(s) == Wr.err("limits: malformed request") : String}:
  match p:
    case Limits.AtReq{}:
      %ltw.some_inj(String, Wr.put_nat(8n+m, rest), s, at) : {FL.ffi(_) == Wr.err("limits: malformed request") : String}
      PUnknownTag.lut.req(m, rest, fu)
    case Limits.AtKind{}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)
    case Limits.AtAuth{}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)
    case Limits.AtScale{}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)
    case Limits.InLims{+d}:
      +fl = BE.be.and_l(Limits.sp_fit_lims(l), Bool.and(Budget.sp_fit_amt(mark), Bool.and(LawsBase.wire_fits(now), Budget.sp_fit_acct(a))), fit)
      +cut = Limits.sp_w_lims_cut(l, d, Wr.put_nat(3n+m, rest))
      %ltw.some_inj(String, Wr.put_nat(6n, cut), s, at) : {FL.ffi(_) == Wr.err("limits: malformed request") : String}
      %BE.be.nat(6n, cut, {==}) : {FL.ffi.got(FL.get_req.n(_)) == Wr.err("limits: malformed request") : String}
      %ltw.lims(l, d, Wr.put_nat(3n+m, rest), fl, ltw.val(m, rest, fu)) : {FL.ffi.got(FL.get_renew.l(_)) == Wr.err("limits: malformed request") : String}
      {==}
    case Limits.InPreset{j, d}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)
    case Limits.InOwn{d}:
      ltw.none_some(String, s, {FL.ffi(s) == Wr.err("limits: malformed request") : String}, at)

def Limits.limits_entry_tag_anywhere(q, p, m, rest, s, fit, fu, at):
  match q:
    case FL.QFill{t, k, a, set, ps, own}:
      ltw.fill(p, t, k, a, set, ps, own, m, rest, s, fit, fu, at)
    case FL.QProfile{k, a}:
      ltw.profile(p, k, a, m, rest, s, fu, at)
    case FL.QPreset{c, k, a}:
      ltw.preset(p, c, k, a, m, rest, s, fu, at)
    case FL.QWraps{us, r}:
      ltw.only(p, m, rest, s, fu, at)
    case FL.QNotice{ws, r, told}:
      ltw.only(p, m, rest, s, fu, at)
    case FL.QFloor{l, c, keep}:
      ltw.floor(p, l, c, keep, m, rest, s, fit, fu, at)
    case FL.QRenew{l, mark, now, a}:
      ltw.renew(p, l, mark, now, a, m, rest, s, fit, fu, at)
    case FL.QPrefix{text, ns}:
      ltw.only(p, m, rest, s, fu, at)
