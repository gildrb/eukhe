# eukhe: lemmas the proofs of area shell share

import Base
import ../../bend/ffi_shell.bend as FSh
import ../../bend/tools.bend as Tl
import ../../bend/wire.bend as Wr
import ../../bend/wire_flat.bend as Fl
import ../../laws/shell.bend as Shell
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire

# The entry answers as the laws spell the model's decision
# --------------------------------------------------------

def sh.verdict_put(v: Tl.Verdict) -> {Wr.put_nat(Shell.spell_verdict(v), "") == FSh.put_verdict(v, "") : String}:
  match v:
    case Tl.Runs{}:
      {==}
    case Tl.Refused{}:
      {==}

def sh.reply(q: FSh.Req) -> {FSh.answer(q) == Shell.spell_answer(q) : String}:
  match q:
    case FSh.QVerdict{+ps}:
      %sh.verdict_put(Tl.verdict(ps)) : {Wr.put_list(~Nat, ~Wr.put_nat, Tl.pieces.effs(ps), _) == Shell.spell_answer(FSh.QVerdict{ps}) : String}
      {==}

# The reader reads back what Rust writes
# --------------------------------------

def sh.pieces_cons(+p: Tl.Piece, +t: List<&2, Tl.Piece>, e: {FSh.pieces.of(Shell.spell_pieces(t)) == Some{t} : Maybe<&2, List<&2, Tl.Piece>>}) -> {FSh.pieces.of(Shell.spell_pieces(p <> t)) == Some{p <> t} : Maybe<&2, List<&2, Tl.Piece>>}:
  match p:
    case Tl.Piece{+o, s, m}:
      match s m:
        case True{} True{}:
          %Equal.sym(Maybe<&2, List<&2, Tl.Piece>>, FSh.pieces.of(Shell.spell_pieces(t)), Some{t}, e) : {FSh.pieces.cons(Some{Tl.Piece{o, True{}, True{}}}, _) == Some{Tl.Piece{o, True{}, True{}} <> t} : Maybe<&2, List<&2, Tl.Piece>>}
          {==}
        case True{} False{}:
          %Equal.sym(Maybe<&2, List<&2, Tl.Piece>>, FSh.pieces.of(Shell.spell_pieces(t)), Some{t}, e) : {FSh.pieces.cons(Some{Tl.Piece{o, True{}, False{}}}, _) == Some{Tl.Piece{o, True{}, False{}} <> t} : Maybe<&2, List<&2, Tl.Piece>>}
          {==}
        case False{} True{}:
          %Equal.sym(Maybe<&2, List<&2, Tl.Piece>>, FSh.pieces.of(Shell.spell_pieces(t)), Some{t}, e) : {FSh.pieces.cons(Some{Tl.Piece{o, False{}, True{}}}, _) == Some{Tl.Piece{o, False{}, True{}} <> t} : Maybe<&2, List<&2, Tl.Piece>>}
          {==}
        case False{} False{}:
          %Equal.sym(Maybe<&2, List<&2, Tl.Piece>>, FSh.pieces.of(Shell.spell_pieces(t)), Some{t}, e) : {FSh.pieces.cons(Some{Tl.Piece{o, False{}, False{}}}, _) == Some{Tl.Piece{o, False{}, False{}} <> t} : Maybe<&2, List<&2, Tl.Piece>>}
          {==}

def sh.pieces_rt(ps: List<&2, Tl.Piece>) -> {FSh.pieces.of(Shell.spell_pieces(ps)) == Some{ps} : Maybe<&2, List<&2, Tl.Piece>>}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      sh.pieces_cons(p, t, sh.pieces_rt(t))

def sh.rt_verdict(+ps: List<&2, Tl.Piece>, +rest: String, fits: {Shell.req_fits(FSh.QVerdict{ps}) == True{} : Bool}) -> {FSh.get_req(Shell.spell_req(FSh.QVerdict{ps}, rest)) == Wr.Got{FSh.QVerdict{ps}, rest} : Wr.Dec<FSh.Req>}:
  +sp = Shell.spell_pieces(ps)
  +f = Fl.flat(sp)
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Shell.spell_ns(f, rest)), Wr.Got{f, rest}, Wire.wire_list_round_trip(f, rest, fits)) : {FSh.get_verdict(_) == Wr.Got{FSh.QVerdict{ps}, rest} : Wr.Dec<FSh.Req>}
  %Equal.sym(Maybe<&2, List<&2, List<&2, Nat>>>, Fl.unflat(f), Some{sp}, LWire.fe.unflat_flat(sp)) : {FSh.get_verdict.pieces(FSh.pieces.flat(_), rest) == Wr.Got{FSh.QVerdict{ps}, rest} : Wr.Dec<FSh.Req>}
  %Equal.sym(Maybe<&2, List<&2, Tl.Piece>>, FSh.pieces.of(sp), Some{ps}, sh.pieces_rt(ps)) : {FSh.get_verdict.pieces(_, rest) == Wr.Got{FSh.QVerdict{ps}, rest} : Wr.Dec<FSh.Req>}
  {==}

def sh.rt(q: FSh.Req, +rest: String, fits: {Shell.req_fits(q) == True{} : Bool}) -> {FSh.get_req(Shell.spell_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FSh.Req>}:
  match q:
    case FSh.QVerdict{ps}:
      sh.rt_verdict(ps, rest, fits)

# Lists and Bools
# ---------------

def sh.app_nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, Nil{}) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %sh.app_nil(A, t) : {x <> List.append(&2, A, t, Nil{}) == x <> _ : List<&2, A>}
      {==}

def sh.app_assoc(-A: Data, xs: List<&2, A>, +ys: List<&2, A>, +zs: List<&2, A>) -> {List.append(&2, A, List.append(&2, A, xs, ys), zs) == List.append(&2, A, xs, List.append(&2, A, ys, zs)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      %sh.app_assoc(A, t, ys, zs) : {x <> List.append(&2, A, List.append(&2, A, t, ys), zs) == x <> _ : List<&2, A>}
      {==}
