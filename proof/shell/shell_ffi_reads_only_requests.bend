# eukhe: the proof of LAW shell_ffi_reads_only_requests
#
# PROOF: each decoder stage answers Got only for the spelling of what it
# read so far, every number within the wire (shx.*: wire_nat_exact,
# wire_list_exact, wire_bool_exact with their fits); a flat part list that
# reads back is the flat spelling of the lists it reads
# (shell_unflat_exact), and lists that read as parts are the spelling of
# those parts (shx.parts); a value is answered only for a request read
# whole, nothing left (shx.top).

import Base
import ../../bend/ffi_shell.bend as FSh
import ../../bend/tools.bend as Tl
import ../../bend/wire.bend as Wr
import ../../bend/wire_flat.bend as Fl
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/shell.bend as Shell
import ../base/bool.bend as LBool
import ../base/staging.bend as LStg
import ../glob/base/entry.bend as LGlobEntry
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_list_exact.bend as PWireListExact
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ./shell_unflat_exact.bend as PShellUnflatExact

# Parts read back are spelled
# ---------------------------

def shx.PartOk(xs: List<&2, Nat>, m: Maybe<&2, Tl.Part>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{p}:
      {xs == Shell.spell_part(p) : List<&2, Nat>}

def shx.part(xs: List<&2, Nat>) -> shx.PartOk(xs, FSh.part.of(xs)):
  match xs:
    case Nil{}:
      Unit{}
    case f <> o:
      match f:
        case 0n:
          {==}
        case 1n+g:
          match g:
            case 0n:
              {==}
            case 1n+h:
              Unit{}

def shx.PartsOk(xss: List<&2, List<&2, Nat>>, m: Maybe<&2, List<&2, Tl.Part>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{ps}:
      {xss == Shell.spell_parts(ps) : List<&2, List<&2, Nat>>}

def shx.cons(xs: List<&2, Nat>, rest: List<&2, List<&2, Nat>>, m: Maybe<&2, Tl.Part>, hp: shx.PartOk(xs, m), ms: Maybe<&2, List<&2, Tl.Part>>, hs: shx.PartsOk(rest, ms)) -> shx.PartsOk(xs <> rest, FSh.parts.cons(m, ms)):
  match m:
    case None{}:
      Unit{}
    case Some{+p}:
      match ms:
        case None{}:
          Unit{}
        case Some{+ps}:
          %hp : {xs <> rest == _ <> Shell.spell_parts(ps) : List<&2, List<&2, Nat>>}
          %hs : {xs <> rest == xs <> _ : List<&2, List<&2, Nat>>}
          {==}

def shx.parts(xss: List<&2, List<&2, Nat>>) -> shx.PartsOk(xss, FSh.parts.of(xss)):
  match xss:
    case Nil{}:
      {==}
    case +xs <> +rest:
      shx.cons(xs, rest, FSh.part.of(xs), shx.part(xs), FSh.parts.of(rest), shx.parts(rest))

# Requests read back are spelled
# ------------------------------

# what a request decoder answers is the spelling of a request that fits,
# then its rest
def shx.Q(s: String, d: Wr.Dec<FSh.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == Shell.spell_req(q, r) : String} & {Shell.req_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def shx.step_ps(-s: String, +a: List<&2, Nat>, -ns: List<&2, Nat>, +s3: String, -xss: List<&2, List<&2, Nat>>, pre: {s == Wr.put_nat(0n, Shell.spell_ns(a, Shell.spell_ns(ns, s3))) : String}, fa: {Shell.ns_fit(a) == True{} : Bool}, fn: {Shell.ns_fit(ns) == True{} : Bool}, en: {ns == Fl.flat(xss) : List<&2, Nat>}, m: Maybe<&2, List<&2, Tl.Part>>, hm: shx.PartsOk(xss, m)) -> shx.Q(s, FSh.get_step.parts(a, m, s3)):
  match m:
    case None{}:
      Unit{}
    case Some{+ps}:
      +e = Equal.trans(List<&2, Nat>, ns, Fl.flat(xss), Fl.flat(Shell.spell_parts(ps)), en, Equal.cong(List<&2, List<&2, Nat>>, List<&2, Nat>, z => Fl.flat(z), xss, Shell.spell_parts(ps), hm))
      +f = Fl.flat(Shell.spell_parts(ps))
      (Equal.trans(String, s, Wr.put_nat(0n, Shell.spell_ns(a, Shell.spell_ns(ns, s3))), Wr.put_nat(0n, Shell.spell_ns(a, Shell.spell_ns(f, s3))), pre, Equal.cong(List<&2, Nat>, String, z => Wr.put_nat(0n, Shell.spell_ns(a, Shell.spell_ns(z, s3))), ns, f, e)),
        LBool.cb_and_intro(Shell.ns_fit(a), Shell.ns_fit(f), fa, Equal.trans(Bool, Shell.ns_fit(f), Shell.ns_fit(ns), True{}, Equal.cong(List<&2, Nat>, Bool, z => Shell.ns_fit(z), f, ns, Equal.sym(List<&2, Nat>, ns, f, e)), fn)))

def shx.step_flat(-s: String, +a: List<&2, Nat>, +ns: List<&2, Nat>, +s3: String, pre: {s == Wr.put_nat(0n, Shell.spell_ns(a, Shell.spell_ns(ns, s3))) : String}, fa: {Shell.ns_fit(a) == True{} : Bool}, fn: {Shell.ns_fit(ns) == True{} : Bool}, mx: Maybe<&2, List<&2, List<&2, Nat>>>, ex: {Fl.unflat(ns) == mx : Maybe<&2, List<&2, List<&2, Nat>>>}) -> shx.Q(s, FSh.get_step.parts(a, FSh.parts.flat(mx), s3)):
  match mx:
    case None{}:
      Unit{}
    case Some{+xss}:
      shx.step_ps(s, a, ns, s3, xss, pre, fa, fn, Shell.shell_unflat_exact(ns, xss, ex), FSh.parts.of(xss), shx.parts(xss))

def shx.step_ns(+s: String, +a: List<&2, Nat>, +s2: String, pre: {s == Wr.put_nat(0n, Shell.spell_ns(a, s2)) : String}, fa: {Shell.ns_fit(a) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s2) == d : Wr.Dec<List<&2, Nat>>}) -> shx.Q(s, FSh.get_step.flat(a, d)):
  match d:
    case Wr.Got{+ns, +s3}:
      +ee = ed
      +e = Wire.wire_list_exact(s2, ns, s3, ee)
      +pre2 = Equal.trans(String, s, Wr.put_nat(0n, Shell.spell_ns(a, s2)), Wr.put_nat(0n, Shell.spell_ns(a, Shell.spell_ns(ns, s3))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Shell.spell_ns(a, z)), s2, Shell.spell_ns(ns, s3), e))
      shx.step_flat(s, a, ns, s3, pre2, fa, LGlobEntry.ge.nats_fit(s2, ns, s3, ee), Fl.unflat(ns), {==})
    case Wr.Bad{}:
      Unit{}

def shx.step(+s: String, +s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s1) == d : Wr.Dec<List<&2, Nat>>}) -> shx.Q(s, FSh.get_step(d)):
  match d:
    case Wr.Got{+a, +s2}:
      +ee = ed
      +e = Wire.wire_list_exact(s1, a, s2, ee)
      +pre2 = Equal.trans(String, s, Wr.put_nat(0n, s1), Wr.put_nat(0n, Shell.spell_ns(a, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, Shell.spell_ns(a, s2), e))
      shx.step_ns(s, a, s2, pre2, LGlobEntry.ge.nats_fit(s1, a, s2, ee), Wr.get_list(~Nat, ~Wr.get_nat, s2), {==})
    case Wr.Bad{}:
      Unit{}

def shx.allows_es(+s: String, +a: List<&2, Nat>, +s2: String, pre: {s == Wr.put_nat(1n, Shell.spell_ns(a, s2)) : String}, fa: {Shell.ns_fit(a) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s2) == d : Wr.Dec<List<&2, Nat>>}) -> shx.Q(s, FSh.get_allows.effs(a, d)):
  match d:
    case Wr.Got{+es, +s3}:
      +ee = ed
      +e = Wire.wire_list_exact(s2, es, s3, ee)
      (Equal.trans(String, s, Wr.put_nat(1n, Shell.spell_ns(a, s2)), Wr.put_nat(1n, Shell.spell_ns(a, Shell.spell_ns(es, s3))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Shell.spell_ns(a, z)), s2, Shell.spell_ns(es, s3), e)),
        LBool.cb_and_intro(Shell.ns_fit(a), Shell.ns_fit(es), fa, LGlobEntry.ge.nats_fit(s2, es, s3, ee)))
    case Wr.Bad{}:
      Unit{}

def shx.allows(+s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s1) == d : Wr.Dec<List<&2, Nat>>}) -> shx.Q(s, FSh.get_allows(d)):
  match d:
    case Wr.Got{+a, +s2}:
      +ee = ed
      +e = Wire.wire_list_exact(s1, a, s2, ee)
      +pre2 = Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Shell.spell_ns(a, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Shell.spell_ns(a, s2), e))
      shx.allows_es(s, a, s2, pre2, LGlobEntry.ge.nats_fit(s1, a, s2, ee), Wr.get_list(~Nat, ~Wr.get_nat, s2), {==})
    case Wr.Bad{}:
      Unit{}

def shx.answer_yes(+s: String, +i: Nat, +s2: String, pre: {s == Wr.put_nat(2n, Wr.put_nat(i, s2)) : String}, fi: {LawsBase.wire_fits(i) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s2) == d : Wr.Dec<Bool>}) -> shx.Q(s, FSh.get_answer.yes(i, d)):
  match d:
    case Wr.Got{+y, +s3}:
      +e = Wire.wire_bool_exact(s2, y, s3, ed)
      (Equal.trans(String, s, Wr.put_nat(2n, Wr.put_nat(i, s2)), Wr.put_nat(2n, Wr.put_nat(i, Wr.put_bool(y, s3))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_nat(i, z)), s2, Wr.put_bool(y, s3), e)), fi)
    case Wr.Bad{}:
      Unit{}

def shx.answer(+s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> shx.Q(s, FSh.get_answer(d)):
  match d:
    case Wr.Got{+i, +s2}:
      +ee = ed
      +e = Wire.wire_nat_exact(s1, i, s2, ee)
      +pre2 = Equal.trans(String, s, Wr.put_nat(2n, s1), Wr.put_nat(2n, Wr.put_nat(i, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(2n, z), s1, Wr.put_nat(i, s2), e))
      shx.answer_yes(s, i, s2, pre2, Wire.wire_nat_decoded_fits(s1, i, s2, ee), Wr.get_bool(s2), {==})
    case Wr.Bad{}:
      Unit{}

def shx.tag_at(+s: String, t: Nat, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> shx.Q(s, FSh.get_req.tag(t, s1)):
  match t:
    case 0n:
      shx.step(s, s1, pre, Wr.get_list(~Nat, ~Wr.get_nat, s1), {==})
    case 1n:
      shx.allows(s, s1, pre, Wr.get_list(~Nat, ~Wr.get_nat, s1), {==})
    case 2n:
      shx.answer(s, s1, pre, Wr.get_nat(s1), {==})
    case 3n+u:
      Unit{}

def shx.tag(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> shx.Q(s, FSh.get_req.go(d)):
  match d:
    case Wr.Got{+t, +s1}:
      shx.tag_at(s, t, s1, Wire.wire_nat_exact(s, t, s1, ed))
    case Wr.Bad{}:
      Unit{}

def shx.T(s: String) -> Type:
  Sigma<&1, &1, FSh.Req, q => {s == Shell.spell_req(q, "") : String} & {Shell.req_fits(q) == True{} : Bool}>

# a value answered: a request read whole, nothing left
def shx.top(-s: String, d: Wr.Dec<FSh.Req>, hq: shx.Q(s, d), ok: {LawsBase.wire_opens_err(FSh.run(d)) == False{} : Bool}) -> shx.T(s):
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, hq)
        case SCon{x, y}:
          LStg.stg.absurd(shx.T(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(shx.T(s), ok)

def Shell.shell_ffi_reads_only_requests(s, ok):
  shx.top(s, FSh.get_req(s), shx.tag(s, Wr.get_nat(s), {==}), ok)
