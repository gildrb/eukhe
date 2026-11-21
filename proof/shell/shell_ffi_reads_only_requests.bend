# eukhe: the proof of LAW shell_ffi_reads_only_requests
#
# PROOF: each decoder stage answers Got only for the spelling of what it
# read so far, every number within the wire (shx.*: wire_nat_exact,
# wire_list_exact with their fits); a flat part list that reads back is
# the flat spelling of the lists it reads (shell_unflat_exact), and lists
# that read as pieces are the spelling of those pieces (shx.pieces); a
# value is answered only for a request read whole, nothing left (shx.top).

import Base
import ../../bend/ffi_shell.bend as FSh
import ../../bend/tools.bend as Tl
import ../../bend/wire.bend as Wr
import ../../bend/wire_flat.bend as Fl
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/shell.bend as Shell
import ../base/staging.bend as LStg
import ../glob/base/entry.bend as LGlobEntry
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_list_exact.bend as PWireListExact
import ./shell_unflat_exact.bend as PShellUnflatExact

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

# Parts of the verdict question read back are spelled
# ---------------------------------------------------

def shx.PieceOk(xs: List<&2, Nat>, m: Maybe<&2, Tl.Piece>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{p}:
      {xs == Shell.spell_piece(p) : List<&2, Nat>}

def shx.piece(xs: List<&2, Nat>) -> shx.PieceOk(xs, FSh.piece.of(xs)):
  match xs:
    case Nil{}:
      Unit{}
    case f <> rest:
      match f:
        case 0n:
          match rest:
            case Nil{}:
              Unit{}
            case w <> o:
              match w:
                case 0n:
                  {==}
                case 1n+g:
                  match g:
                    case 0n:
                      {==}
                    case 1n+h:
                      Unit{}
        case 1n+g0:
          match g0:
            case 0n:
              match rest:
                case Nil{}:
                  Unit{}
                case w <> o:
                  match w:
                    case 0n:
                      {==}
                    case 1n+g:
                      match g:
                        case 0n:
                          {==}
                        case 1n+h:
                          Unit{}
            case 1n+h0:
              Unit{}

def shx.PiecesOk(xss: List<&2, List<&2, Nat>>, m: Maybe<&2, List<&2, Tl.Piece>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{ps}:
      {xss == Shell.spell_pieces(ps) : List<&2, List<&2, Nat>>}

def shx.pcons(xs: List<&2, Nat>, rest: List<&2, List<&2, Nat>>, m: Maybe<&2, Tl.Piece>, hp: shx.PieceOk(xs, m), ms: Maybe<&2, List<&2, Tl.Piece>>, hs: shx.PiecesOk(rest, ms)) -> shx.PiecesOk(xs <> rest, FSh.pieces.cons(m, ms)):
  match m:
    case None{}:
      Unit{}
    case Some{+p}:
      match ms:
        case None{}:
          Unit{}
        case Some{+ps}:
          %hp : {xs <> rest == _ <> Shell.spell_pieces(ps) : List<&2, List<&2, Nat>>}
          %hs : {xs <> rest == xs <> _ : List<&2, List<&2, Nat>>}
          {==}

def shx.pieces(xss: List<&2, List<&2, Nat>>) -> shx.PiecesOk(xss, FSh.pieces.of(xss)):
  match xss:
    case Nil{}:
      {==}
    case +xs <> +rest:
      shx.pcons(xs, rest, FSh.piece.of(xs), shx.piece(xs), FSh.pieces.of(rest), shx.pieces(rest))

def shx.verdict_ps(-s: String, -ns: List<&2, Nat>, +s2: String, -xss: List<&2, List<&2, Nat>>, pre: {s == Wr.put_nat(3n, Shell.spell_ns(ns, s2)) : String}, fn: {Shell.ns_fit(ns) == True{} : Bool}, en: {ns == Fl.flat(xss) : List<&2, Nat>}, m: Maybe<&2, List<&2, Tl.Piece>>, hm: shx.PiecesOk(xss, m)) -> shx.Q(s, FSh.get_verdict.pieces(m, s2)):
  match m:
    case None{}:
      Unit{}
    case Some{+ps}:
      +e = Equal.trans(List<&2, Nat>, ns, Fl.flat(xss), Fl.flat(Shell.spell_pieces(ps)), en, Equal.cong(List<&2, List<&2, Nat>>, List<&2, Nat>, z => Fl.flat(z), xss, Shell.spell_pieces(ps), hm))
      +f = Fl.flat(Shell.spell_pieces(ps))
      (Equal.trans(String, s, Wr.put_nat(3n, Shell.spell_ns(ns, s2)), Wr.put_nat(3n, Shell.spell_ns(f, s2)), pre, Equal.cong(List<&2, Nat>, String, z => Wr.put_nat(3n, Shell.spell_ns(z, s2)), ns, f, e)),
        Equal.trans(Bool, Shell.ns_fit(f), Shell.ns_fit(ns), True{}, Equal.cong(List<&2, Nat>, Bool, z => Shell.ns_fit(z), f, ns, Equal.sym(List<&2, Nat>, ns, f, e)), fn))

def shx.verdict_flat(-s: String, +ns: List<&2, Nat>, +s2: String, pre: {s == Wr.put_nat(3n, Shell.spell_ns(ns, s2)) : String}, fn: {Shell.ns_fit(ns) == True{} : Bool}, mx: Maybe<&2, List<&2, List<&2, Nat>>>, ex: {Fl.unflat(ns) == mx : Maybe<&2, List<&2, List<&2, Nat>>>}) -> shx.Q(s, FSh.get_verdict.pieces(FSh.pieces.flat(mx), s2)):
  match mx:
    case None{}:
      Unit{}
    case Some{+xss}:
      shx.verdict_ps(s, ns, s2, xss, pre, fn, Shell.shell_unflat_exact(ns, xss, ex), FSh.pieces.of(xss), shx.pieces(xss))

def shx.verdict(+s: String, +s1: String, pre: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s1) == d : Wr.Dec<List<&2, Nat>>}) -> shx.Q(s, FSh.get_verdict(d)):
  match d:
    case Wr.Got{+ns, +s2}:
      +ee = ed
      +e = Wire.wire_list_exact(s1, ns, s2, ee)
      +pre2 = Equal.trans(String, s, Wr.put_nat(3n, s1), Wr.put_nat(3n, Shell.spell_ns(ns, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(3n, z), s1, Shell.spell_ns(ns, s2), e))
      shx.verdict_flat(s, ns, s2, pre2, LGlobEntry.ge.nats_fit(s1, ns, s2, ee), Fl.unflat(ns), {==})
    case Wr.Bad{}:
      Unit{}

def shx.tag_at(+s: String, t: Nat, +s1: String, pre: {s == Wr.put_nat(t, s1) : String}) -> shx.Q(s, FSh.get_req.tag(t, s1)):
  match t:
    case 0n:
      Unit{}
    case 1n:
      Unit{}
    case 2n:
      Unit{}
    case 3n:
      shx.verdict(s, s1, pre, Wr.get_list(~Nat, ~Wr.get_nat, s1), {==})
    case 4n+u:
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
