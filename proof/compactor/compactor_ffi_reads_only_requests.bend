# eukhe: the proof of LAW compactor_ffi_reads_only_requests
# The entry answers other than its error form only when its decoder read
# a whole request: a known tag, every field, nothing left. Each Nat it read
# is spelled and fits (wire_nat_exact, wire_nat_decoded_fits), so the
# input, stage by stage (cro.*, each carrying the input spelled up to its
# field: `pre`), is the laws' spelling of that request: a line opens; a
# reply (a best reply and a reply text of the lengths read, one-byte
# characters, cro.ones) to a line; a call of a pending line ended. Every
# other branch answers the error form, which the premise rules out.

import Base
import ../../bend/compactor.bend as C
import ../../bend/ffi_compactor.bend as FC
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/compactor.bend as Compactor
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA

def cro.E() -> String:
  Wr.err("compactor: malformed request")

def cro.G(s: String) -> Type:
  Sigma<&1, &1, Compactor.Ask, a => {(s, Compactor.ask_fits(a)) == (Compactor.spell_ask(a), True{}) : String & Bool}>

# the error form is not other than itself
def cro.no(-s: String, other: {True{} == False{} : Bool}) -> cro.G(s):
  LLogicLogic.pt.absurd(cro.G(s), other)

def cro.pack(-s: String, -x: String, -b: Bool, e1: {s == x : String}, e2: {b == True{} : Bool}) -> {(s, b) == (x, True{}) : String & Bool}:
  %Equal.sym(Bool, b, True{}, e2) : {(s, _) == (x, True{}) : String & Bool}
  %Equal.sym(String, s, x, e1) : {(_, True{}) == (x, True{}) : String & Bool}
  {==}

# s is the tag t then s1, and s1 is x: s is the tag t then x
def cro.after(-s: String, +t: Nat, -s1: String, -x: String, pre: {s == Wr.put_nat(t, s1) : String}, e: {s1 == x : String}) -> {s == Wr.put_nat(t, x) : String}:
  Equal.trans(String, s, Wr.put_nat(t, s1), Wr.put_nat(t, x), pre, Equal.cong(String, String, z => Wr.put_nat(t, z), s1, x, e))

# a text of n one-byte characters, of n bytes
def cro.ones(n: Nat) -> List<&2, C.W>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      C.W1{} <> cro.ones(k)

def cro.ones_bytes(n: Nat) -> {Compactor.bytes(cro.ones(n)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %cro.ones_bytes(k) : {1n+Compactor.bytes(cro.ones(k)) == 1n+_ : Nat}
      {==}

# A line opens
# ------------

def cro.open(-s: String, +s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}, other: {String.eq(FC.run(FC.get_open(d)), cro.E()) == False{} : Bool}) -> cro.G(s):
  match d:
    case Wr.Got{+n, SNil{}}:
      +e = cro.after(s, 0n, s1, Wr.put_nat(n, ""), pre, Wire.wire_nat_exact(s1, n, "", ed))
      (Compactor.AOpen{n}, cro.pack(s, Compactor.spell_open(n), LawsBase.wire_fits(n), e, Wire.wire_nat_decoded_fits(s1, n, "", ed)))
    case Wr.Got{n, SCon{c, r}}:
      cro.no(s, other)
    case Wr.Bad{}:
      cro.no(s, other)

# A reply to a line
# -----------------

# the request's fields: tag 1, tries left, calls made, node, then x
def cro.pre(l: Nat, m: Nat, n: Nat, x: String) -> String:
  Wr.put_nat(1n, Wr.put_nat(l, Wr.put_nat(m, Wr.put_nat(n, x))))

# the best reply's length as the entry holds it
def cro.mb(b: Maybe<&2, List<&2, C.W>>, bl: Nat) -> Maybe<&2, Nat>:
  match b:
    case None{}:
      None{}
    case Some{t}:
      Some{bl}

# the fields up to the best reply, then x
def cro.at(l: Nat, m: Nat, n: Nat, b: Maybe<&2, List<&2, C.W>>, bl: Nat, x: String) -> String:
  cro.pre(l, m, n, Compactor.spell_best(b, bl, x))

# the numbers before the reply fit
def cro.F(l: Nat, m: Nat, n: Nat, b: Maybe<&2, List<&2, C.W>>, bl: Nat) -> Type:
  {LawsBase.wire_fits(l) == True{} : Bool} & {LawsBase.wire_fits(m) == True{} : Bool} & {LawsBase.wire_fits(n) == True{} : Bool} & {Compactor.best_fits(b, bl) == True{} : Bool}

def cro.fits(+l: Nat, +m: Nat, +n: Nat, +b: Maybe<&2, List<&2, C.W>>, +bl: Nat, +r: C.Reply, f: cro.F(l, m, n, b, bl), hr: {Compactor.reply_fits(r) == True{} : Bool}) -> {Compactor.step_fits(C.Lst{l, m, n, b, bl, Nil{}}, r) == True{} : Bool}:
  (fl, fr1) = f
  (fm, fr2) = fr1
  (fn, fb) = fr2
  LA.pc.and_true(LawsBase.wire_fits(l), Bool.and(LawsBase.wire_fits(m), Bool.and(LawsBase.wire_fits(n), Bool.and(Compactor.best_fits(b, bl), Compactor.reply_fits(r)))), fl,
    LA.pc.and_true(LawsBase.wire_fits(m), Bool.and(LawsBase.wire_fits(n), Bool.and(Compactor.best_fits(b, bl), Compactor.reply_fits(r))), fm,
      LA.pc.and_true(LawsBase.wire_fits(n), Bool.and(Compactor.best_fits(b, bl), Compactor.reply_fits(r)), fn,
        LA.pc.and_true(Compactor.best_fits(b, bl), Compactor.reply_fits(r), fb, hr))))

# the reply's length: nothing may follow it
def cro.says(-s: String, +l: Nat, +m: Nat, +n: Nat, +b: Maybe<&2, List<&2, C.W>>, +bl: Nat, +sy: String, pre: {s == cro.at(l, m, n, b, bl, Wr.put_nat(1n, sy)) : String}, f: cro.F(l, m, n, b, bl), d: Wr.Dec<Nat>, +ed: {Wr.get_nat(sy) == d : Wr.Dec<Nat>}, other: {String.eq(FC.run(FC.get_step.says(l, m, n, cro.mb(b, bl), d)), cro.E()) == False{} : Bool}) -> cro.G(s):
  match d:
    case Wr.Got{+len, SNil{}}:
      +r = {C.Says{cro.ones(len)} : C.Reply}
      +x = Wr.put_nat(len, "")
      +y = Wr.put_nat(Compactor.bytes(cro.ones(len)), "")
      +ex = Equal.trans(String, sy, x, y, Wire.wire_nat_exact(sy, len, "", ed), Equal.cong(Nat, String, z => Wr.put_nat(z, ""), len, Compactor.bytes(cro.ones(len)), Equal.sym(Nat, Compactor.bytes(cro.ones(len)), len, cro.ones_bytes(len))))
      +e = Equal.trans(String, s, cro.at(l, m, n, b, bl, Wr.put_nat(1n, sy)), cro.at(l, m, n, b, bl, Wr.put_nat(1n, y)), pre, Equal.cong(String, String, z => cro.at(l, m, n, b, bl, Wr.put_nat(1n, z)), sy, y, ex))
      +hr = Equal.trans(Bool, LawsBase.wire_fits(Compactor.bytes(cro.ones(len))), LawsBase.wire_fits(len), True{}, Equal.cong(Nat, Bool, z => LawsBase.wire_fits(z), Compactor.bytes(cro.ones(len)), len, cro.ones_bytes(len)), Wire.wire_nat_decoded_fits(sy, len, "", ed))
      +st = {C.Lst{l, m, n, b, bl, Nil{}} : C.Lst}
      (Compactor.AStep{st, r}, cro.pack(s, Compactor.spell_step(st, r), Compactor.step_fits(st, r), e, cro.fits(l, m, n, b, bl, r, f, hr)))
    case Wr.Got{len, SCon{c, t}}:
      cro.no(s, other)
    case Wr.Bad{}:
      cro.no(s, other)

# the reply: 0 an error (nothing may follow) | 1 a text's length
def cro.rep(-s: String, +l: Nat, +m: Nat, +n: Nat, +b: Maybe<&2, List<&2, C.W>>, +bl: Nat, +sx: String, pre: {s == cro.at(l, m, n, b, bl, sx) : String}, f: cro.F(l, m, n, b, bl), d: Wr.Dec<Nat>, +ed: {Wr.get_nat(sx) == d : Wr.Dec<Nat>}, other: {String.eq(FC.run(FC.get_step.tag(l, m, n, cro.mb(b, bl), d)), cro.E()) == False{} : Bool}) -> cro.G(s):
  match d:
    case Wr.Got{+t, +sy}:
      match t:
        case 0n:
          match sy:
            case SNil{}:
              +e = Equal.trans(String, s, cro.at(l, m, n, b, bl, sx), cro.at(l, m, n, b, bl, Wr.put_nat(0n, "")), pre, Equal.cong(String, String, z => cro.at(l, m, n, b, bl, z), sx, Wr.put_nat(0n, ""), Wire.wire_nat_exact(sx, 0n, "", ed)))
              +st = {C.Lst{l, m, n, b, bl, Nil{}} : C.Lst}
              (Compactor.AStep{st, C.Erred{}}, cro.pack(s, Compactor.spell_step(st, C.Erred{}), Compactor.step_fits(st, C.Erred{}), e, cro.fits(l, m, n, b, bl, C.Erred{}, f, {==})))
            case SCon{c, r}:
              cro.no(s, other)
        case 1n:
          +e = Equal.trans(String, s, cro.at(l, m, n, b, bl, sx), cro.at(l, m, n, b, bl, Wr.put_nat(1n, sy)), pre, Equal.cong(String, String, z => cro.at(l, m, n, b, bl, z), sx, Wr.put_nat(1n, sy), Wire.wire_nat_exact(sx, 1n, sy, ed)))
          cro.says(s, l, m, n, b, bl, sy, e, f, Wr.get_nat(sy), {==}, other)
        case 2n+q:
          cro.no(s, other)
    case Wr.Bad{}:
      cro.no(s, other)

# a best reply's length (Maybe tag 1)
def cro.some(-s: String, +l: Nat, +m: Nat, +n: Nat, +s5: String, pre: {s == cro.pre(l, m, n, Wr.put_nat(1n, s5)) : String}, fl: {LawsBase.wire_fits(l) == True{} : Bool}, fm: {LawsBase.wire_fits(m) == True{} : Bool}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s5) == d : Wr.Dec<Nat>}, other: {String.eq(FC.run(FC.get_step.kind(l, m, n, FC.get_mnat.some(d))), cro.E()) == False{} : Bool}) -> cro.G(s):
  match d:
    case Wr.Got{+bl, +s6}:
      +b = {Some{cro.ones(bl)} : Maybe<&2, List<&2, C.W>>}
      +e = Equal.trans(String, s, cro.pre(l, m, n, Wr.put_nat(1n, s5)), cro.at(l, m, n, b, bl, s6), pre, Equal.cong(String, String, z => cro.pre(l, m, n, Wr.put_nat(1n, z)), s5, Wr.put_nat(bl, s6), Wire.wire_nat_exact(s5, bl, s6, ed)))
      cro.rep(s, l, m, n, b, bl, s6, e, (fl, (fm, (fn, Wire.wire_nat_decoded_fits(s5, bl, s6, ed)))), Wr.get_nat(s6), {==}, other)
    case Wr.Bad{}:
      cro.no(s, other)

# the best reply: 0 none | 1 and its length
def cro.best(-s: String, +l: Nat, +m: Nat, +n: Nat, +s4: String, pre: {s == cro.pre(l, m, n, s4) : String}, fl: {LawsBase.wire_fits(l) == True{} : Bool}, fm: {LawsBase.wire_fits(m) == True{} : Bool}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s4) == d : Wr.Dec<Nat>}, other: {String.eq(FC.run(FC.get_step.kind(l, m, n, FC.get_mnat(d))), cro.E()) == False{} : Bool}) -> cro.G(s):
  match d:
    case Wr.Got{+t, +s5}:
      match t:
        case 0n:
          +e = Equal.trans(String, s, cro.pre(l, m, n, s4), cro.at(l, m, n, None{}, 0n, s5), pre, Equal.cong(String, String, z => cro.pre(l, m, n, z), s4, Wr.put_nat(0n, s5), Wire.wire_nat_exact(s4, 0n, s5, ed)))
          cro.rep(s, l, m, n, None{}, 0n, s5, e, (fl, (fm, (fn, {==}))), Wr.get_nat(s5), {==}, other)
        case 1n:
          +e = Equal.trans(String, s, cro.pre(l, m, n, s4), cro.pre(l, m, n, Wr.put_nat(1n, s5)), pre, Equal.cong(String, String, z => cro.pre(l, m, n, z), s4, Wr.put_nat(1n, s5), Wire.wire_nat_exact(s4, 1n, s5, ed)))
          cro.some(s, l, m, n, s5, e, fl, fm, fn, Wr.get_nat(s5), {==}, other)
        case 2n+q:
          cro.no(s, other)
    case Wr.Bad{}:
      cro.no(s, other)

# the node's size
def cro.node(-s: String, +l: Nat, +m: Nat, +s3: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(l, Wr.put_nat(m, s3))) : String}, fl: {LawsBase.wire_fits(l) == True{} : Bool}, fm: {LawsBase.wire_fits(m) == True{} : Bool}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s3) == d : Wr.Dec<Nat>}, other: {String.eq(FC.run(FC.get_step.node(l, m, d)), cro.E()) == False{} : Bool}) -> cro.G(s):
  match d:
    case Wr.Got{+n, +s4}:
      +e = Equal.trans(String, s, Wr.put_nat(1n, Wr.put_nat(l, Wr.put_nat(m, s3))), cro.pre(l, m, n, s4), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(l, Wr.put_nat(m, z))), s3, Wr.put_nat(n, s4), Wire.wire_nat_exact(s3, n, s4, ed)))
      cro.best(s, l, m, n, s4, e, fl, fm, Wire.wire_nat_decoded_fits(s3, n, s4, ed), Wr.get_nat(s4), {==}, other)
    case Wr.Bad{}:
      cro.no(s, other)

# the calls made
def cro.made(-s: String, +l: Nat, +s2: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(l, s2)) : String}, fl: {LawsBase.wire_fits(l) == True{} : Bool}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}, other: {String.eq(FC.run(FC.get_step.made(l, d)), cro.E()) == False{} : Bool}) -> cro.G(s):
  match d:
    case Wr.Got{+m, +s3}:
      +e = Equal.trans(String, s, Wr.put_nat(1n, Wr.put_nat(l, s2)), Wr.put_nat(1n, Wr.put_nat(l, Wr.put_nat(m, s3))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(l, z)), s2, Wr.put_nat(m, s3), Wire.wire_nat_exact(s2, m, s3, ed)))
      cro.node(s, l, m, s3, e, fl, Wire.wire_nat_decoded_fits(s2, m, s3, ed), Wr.get_nat(s3), {==}, other)
    case Wr.Bad{}:
      cro.no(s, other)

# the tries left
def cro.step(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}, other: {String.eq(FC.run(FC.get_step(d)), cro.E()) == False{} : Bool}) -> cro.G(s):
  match d:
    case Wr.Got{+l, +s2}:
      cro.made(s, l, s2, cro.after(s, 1n, s1, Wr.put_nat(l, s2), pre, Wire.wire_nat_exact(s1, l, s2, ed)), Wire.wire_nat_decoded_fits(s1, l, s2, ed), Wr.get_nat(s2), {==}, other)
    case Wr.Bad{}:
      cro.no(s, other)

# A call of a pending line ended
# ------------------------------

def cro.pfits(-n: Nat, f: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Compactor.pend_fits(C.Owed{n}) == True{} : Bool}:
  f

def cro.ended(-s: String, +p: C.Pend, +o: C.Outcome, +sx: String, pre: {s == Wr.put_nat(2n, Compactor.spell_pend(p, sx)) : String}, fp: {Compactor.pend_fits(p) == True{} : Bool}, e: {sx == Compactor.spell_outcome(o) : String}) -> cro.G(s):
  +e2 = Equal.trans(String, s, Wr.put_nat(2n, Compactor.spell_pend(p, sx)), Compactor.spell_after(p, o), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Compactor.spell_pend(p, z)), sx, Compactor.spell_outcome(o), e))
  (Compactor.AAfter{p, o}, cro.pack(s, Compactor.spell_after(p, o), Compactor.pend_fits(p), e2, fp))

# how the call ended: a known tag, nothing after it
def cro.how(-s: String, +p: C.Pend, +sx: String, pre: {s == Wr.put_nat(2n, Compactor.spell_pend(p, sx)) : String}, fp: {Compactor.pend_fits(p) == True{} : Bool}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(sx) == d : Wr.Dec<Nat>}, other: {String.eq(FC.run(FC.get_after.how(p, d)), cro.E()) == False{} : Bool}) -> cro.G(s):
  match d:
    case Wr.Got{+t, +s4}:
      match t:
        case 0n:
          match s4:
            case SNil{}:
              cro.ended(s, p, C.Built{}, sx, pre, fp, Wire.wire_nat_exact(sx, 0n, "", ed))
            case SCon{c, r}:
              cro.no(s, other)
        case 1n:
          match s4:
            case SNil{}:
              cro.ended(s, p, C.Failed{}, sx, pre, fp, Wire.wire_nat_exact(sx, 1n, "", ed))
            case SCon{c, r}:
              cro.no(s, other)
        case 2n:
          match s4:
            case SNil{}:
              cro.ended(s, p, C.Disk{}, sx, pre, fp, Wire.wire_nat_exact(sx, 2n, "", ed))
            case SCon{c, r}:
              cro.no(s, other)
        case 3n:
          match s4:
            case SNil{}:
              cro.ended(s, p, C.Stopped{}, sx, pre, fp, Wire.wire_nat_exact(sx, 3n, "", ed))
            case SCon{c, r}:
              cro.no(s, other)
        case 4n+q:
          cro.no(s, other)
    case Wr.Bad{}:
      cro.no(s, other)

# an owed line: the failures it has left
def cro.owed(-s: String, +s2: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(1n, s2)) : String}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}, other: {String.eq(FC.run(FC.get_after.owed(d)), cro.E()) == False{} : Bool}) -> cro.G(s):
  match d:
    case Wr.Got{+n, +s3}:
      +e = Equal.trans(String, s, Wr.put_nat(2n, Wr.put_nat(1n, s2)), Wr.put_nat(2n, Compactor.spell_pend(C.Owed{n}, s3)), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_nat(1n, z)), s2, Wr.put_nat(n, s3), Wire.wire_nat_exact(s2, n, s3, ed)))
      cro.how(s, C.Owed{n}, s3, e, cro.pfits(n, Wire.wire_nat_decoded_fits(s2, n, s3, ed)), Wr.get_nat(s3), {==}, other)
    case Wr.Bad{}:
      cro.no(s, other)

# the line: 0 built | 1 owed
def cro.pend(-s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}, other: {String.eq(FC.run(FC.get_after(d)), cro.E()) == False{} : Bool}) -> cro.G(s):
  match d:
    case Wr.Got{+t, +s2}:
      match t:
        case 0n:
          cro.how(s, C.Made{}, s2, cro.after(s, 2n, s1, Wr.put_nat(0n, s2), pre, Wire.wire_nat_exact(s1, 0n, s2, ed)), {==}, Wr.get_nat(s2), {==}, other)
        case 1n:
          cro.owed(s, s2, cro.after(s, 2n, s1, Wr.put_nat(1n, s2), pre, Wire.wire_nat_exact(s1, 1n, s2, ed)), Wr.get_nat(s2), {==}, other)
        case 2n+q:
          cro.no(s, other)
    case Wr.Bad{}:
      cro.no(s, other)

# The request's tag
# -----------------

def cro.top(+s: String, d: Wr.Dec<Nat>, +ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, other: {String.eq(FC.run(FC.get_req.go(d)), cro.E()) == False{} : Bool}) -> cro.G(s):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          cro.open(s, s1, Wire.wire_nat_exact(s, 0n, s1, ed), Wr.get_nat(s1), {==}, other)
        case 1n:
          cro.step(s, s1, Wire.wire_nat_exact(s, 1n, s1, ed), Wr.get_nat(s1), {==}, other)
        case 2n:
          cro.pend(s, s1, Wire.wire_nat_exact(s, 2n, s1, ed), Wr.get_nat(s1), {==}, other)
        case 3n+q:
          cro.no(s, other)
    case Wr.Bad{}:
      cro.no(s, other)

def Compactor.compactor_ffi_reads_only_requests(s, other):
  cro.top(s, Wr.get_nat(s), {==}, other)
