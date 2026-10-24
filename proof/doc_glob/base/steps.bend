# eukhe: the glob stepper's events, spelled by the spec spellers, read
# back (the wire's round trips, LAW wire_nat_round_trip and
# wire_str_round_trip), and each step from the state of a ranking R

import Base
import ../../../bend/doc_glob.bend as Gb
import ../../../bend/ffi_doc_glob.bend as FGb
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/doc_glob.bend as DocGlob
import ../../../laws/wire.bend as Wire
import ../../base/wire.bend as LWire
import ./rank.bend as GR
import ./keep.bend as GK
import ./state.bend as GS

# Reading back
# ------------

def gp.met_ev(+m: Nat, hm: {LawsBase.wire_fits(m) == True{} : Bool}) -> {FGb.ev(Wr.get_nat(Wr.put_nat(0n, Wr.put_nat(m, "")))) == Some{FGb.Met{m}} : Maybe<&2, FGb.Ev>}:
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, Wr.put_nat(m, ""))), Wr.Got{0n, Wr.put_nat(m, "")}, Wire.wire_nat_round_trip(0n, Wr.put_nat(m, ""), {==})) : {FGb.ev(_) == Some{FGb.Met{m}} : Maybe<&2, FGb.Ev>}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(m, "")), Wr.Got{m, ""}, Wire.wire_nat_round_trip(m, "", hm)) : {FGb.ev.met(_) == Some{FGb.Met{m}} : Maybe<&2, FGb.Ev>}
  {==}

def gp.add_ev(+m: Nat, +p: String, hm: {LawsBase.wire_fits(m) == True{} : Bool}, hp: {LawsBase.wire_fits(String.length(p)) == True{} : Bool}) -> {FGb.ev(Wr.get_nat(Wr.put_nat(1n, Wr.put_nat(m, Wr.put_str(p, ""))))) == Some{FGb.Add{m, p}} : Maybe<&2, FGb.Ev>}:
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, Wr.put_nat(m, Wr.put_str(p, "")))), Wr.Got{1n, Wr.put_nat(m, Wr.put_str(p, ""))}, Wire.wire_nat_round_trip(1n, Wr.put_nat(m, Wr.put_str(p, "")), {==})) : {FGb.ev(_) == Some{FGb.Add{m, p}} : Maybe<&2, FGb.Ev>}
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(m, Wr.put_str(p, ""))), Wr.Got{m, Wr.put_str(p, "")}, Wire.wire_nat_round_trip(m, Wr.put_str(p, ""), hm)) : {FGb.ev.add(_) == Some{FGb.Add{m, p}} : Maybe<&2, FGb.Ev>}
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(p, "")), Wr.Got{p, ""}, Wire.wire_str_round_trip(p, "", hp)) : {FGb.ev.path(m, _) == Some{FGb.Add{m, p}} : Maybe<&2, FGb.Ev>}
  {==}

def gp.show_ev() -> {FGb.ev(Wr.get_nat(Wr.put_nat(2n, ""))) == Some{FGb.Show{}} : Maybe<&2, FGb.Ev>}:
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n, "")), Wr.Got{2n, ""}, Wire.wire_nat_round_trip(2n, "", {==})) : {FGb.ev(_) == Some{FGb.Show{}} : Maybe<&2, FGb.Ev>}
  {==}

# Steps
# -----

# a time: the spec's Wants, the state kept
def gp.s_met(+s: Nat, +k: Nat, +R: List<&2, DocGlob.glob.Hit>, +m: Nat, +p: String, hm: {LawsBase.wire_fits(m) == True{} : Bool}) -> {FGb.step(GS.gp.St(s, k, R), DocGlob.glob.spell_met(DocGlob.glob.Hit{m, p})) == (GS.gp.St(s, k, R), Wr.put_bool(DocGlob.glob.Wants(DocGlob.glob.Hit{m, p}, 1n+Nat.add(s, k), R), "")) : FGb.St & String}:
  %Equal.sym(Maybe<&2, FGb.Ev>, FGb.ev(Wr.get_nat(Wr.put_nat(0n, Wr.put_nat(m, "")))), Some{FGb.Met{m}}, gp.met_ev(m, hm)) : {FGb.step.ev(GS.gp.St(s, k, R), _) == (GS.gp.St(s, k, R), Wr.put_bool(DocGlob.glob.Wants(DocGlob.glob.Hit{m, p}, 1n+Nat.add(s, k), R), "")) : FGb.St & String}
  {==}

# a hit whole: the state of the ranking with it put in
def gp.s_add(+s: Nat, +k: Nat, +R: List<&2, DocGlob.glob.Hit>, +m: Nat, +p: String, hm: {LawsBase.wire_fits(m) == True{} : Bool}, hp: {LawsBase.wire_fits(String.length(p)) == True{} : Bool}) -> {FGb.step(GS.gp.St(s, k, R), DocGlob.glob.spell_add(DocGlob.glob.Hit{m, p})) == (GS.gp.St(s, k, DocGlob.glob.Put(DocGlob.glob.Hit{m, p}, R)), "") : FGb.St & String}:
  +x = {DocGlob.glob.Hit{m, p} : DocGlob.glob.Hit}
  +c = {1n+Nat.add(s, k) : Nat}
  +F = {DocGlob.glob.First(R, c) : List<&2, DocGlob.glob.Hit>}
  +G = {DocGlob.glob.First(DocGlob.glob.Put(x, F), c) : List<&2, DocGlob.glob.Hit>}
  %Equal.sym(Maybe<&2, FGb.Ev>, FGb.ev(Wr.get_nat(Wr.put_nat(1n, Wr.put_nat(m, Wr.put_str(p, ""))))), Some{FGb.Add{m, p}}, gp.add_ev(m, p, hm, hp)) : {FGb.step.ev(GS.gp.St(s, k, R), _) == (GS.gp.St(s, k, DocGlob.glob.Put(x, R)), "") : FGb.St & String}
  %Equal.sym(List<&2, Gb.It>, Gb.ins(GR.gp.it(x), GR.gp.its(F)), GR.gp.its(DocGlob.glob.Put(x, F)), GR.gp.ins(x, F)) : {FGb.step.fin(s, k, c, Gb.fin(_, c)) == (GS.gp.St(s, k, DocGlob.glob.Put(x, R)), "") : FGb.St & String}
  %Equal.sym(Gb.Fin, Gb.fin(GR.gp.its(DocGlob.glob.Put(x, F)), c), Gb.Fin{GR.gp.its(G), DocGlob.glob.Len(G), DocGlob.glob.Low(G)}, GS.gp.fin(DocGlob.glob.Put(x, F), c)) : {FGb.step.fin(s, k, c, _) == (GS.gp.St(s, k, DocGlob.glob.Put(x, R)), "") : FGb.St & String}
  Equal.cong(List<&2, DocGlob.glob.Hit>, FGb.St & String, L => (FGb.Gl{s, k, c, DocGlob.glob.Len(L), DocGlob.glob.Low(L), GR.gp.its(L)}, ""), G, DocGlob.glob.First(DocGlob.glob.Put(x, R), c), GK.gp.put_first(x, R, c))

# the page: the spec's page of the ranking
def gp.s_show(+s: Nat, +k: Nat, +R: List<&2, DocGlob.glob.Hit>) -> {FGb.step(GS.gp.St(s, k, R), DocGlob.glob.spell_show()) == (GS.gp.St(s, k, R), DocGlob.glob.spell_page(R, s, k)) : FGb.St & String}:
  +c = {1n+Nat.add(s, k) : Nat}
  +F = {DocGlob.glob.First(R, c) : List<&2, DocGlob.glob.Hit>}
  +W = {DocGlob.glob.Window(R, s, k) : List<&2, DocGlob.glob.Hit>}
  +n = {DocGlob.glob.Len(R) : Nat}
  %Equal.sym(Maybe<&2, FGb.Ev>, FGb.ev(Wr.get_nat(Wr.put_nat(2n, ""))), Some{FGb.Show{}}, gp.show_ev()) : {FGb.step.ev(GS.gp.St(s, k, R), _) == (GS.gp.St(s, k, R), DocGlob.glob.spell_page(R, s, k)) : FGb.St & String}
  %Equal.sym(List<&2, Gb.It>, Gb.page(GR.gp.its(F), s, k), GR.gp.its(W), GS.gp.page(R, s, k)) : {(GS.gp.St(s, k, R), FGb.put_opt(Gb.next(s, k, DocGlob.glob.Len(F)), FGb.put_opt(Gb.past(s, DocGlob.glob.Len(F)), Wr.put_list(~Gb.It, ~FGb.put_it, _, "")))) == (GS.gp.St(s, k, R), DocGlob.glob.spell_page(R, s, k)) : FGb.St & String}
  %Equal.sym(String, Wr.put_list(~Gb.It, ~FGb.put_it, GR.gp.its(W), ""), Wr.put_list(~DocGlob.glob.Hit, ~DocGlob.glob.spell_hit, W, ""), GS.gp.list_map(W)) : {(GS.gp.St(s, k, R), FGb.put_opt(Gb.next(s, k, DocGlob.glob.Len(F)), FGb.put_opt(Gb.past(s, DocGlob.glob.Len(F)), _))) == (GS.gp.St(s, k, R), DocGlob.glob.spell_page(R, s, k)) : FGb.St & String}
  %Equal.sym(Maybe<&2, Nat>, Gb.past(s, DocGlob.glob.Len(F)), DocGlob.glob.Past(n, s), GS.gp.past(s, k, R)) : {(GS.gp.St(s, k, R), FGb.put_opt(Gb.next(s, k, DocGlob.glob.Len(F)), FGb.put_opt(_, Wr.put_list(~DocGlob.glob.Hit, ~DocGlob.glob.spell_hit, W, "")))) == (GS.gp.St(s, k, R), DocGlob.glob.spell_page(R, s, k)) : FGb.St & String}
  %Equal.sym(Maybe<&2, Nat>, Gb.next(s, k, DocGlob.glob.Len(F)), DocGlob.glob.More(n, s, k), GS.gp.next(s, k, R)) : {(GS.gp.St(s, k, R), FGb.put_opt(_, FGb.put_opt(DocGlob.glob.Past(n, s), Wr.put_list(~DocGlob.glob.Hit, ~DocGlob.glob.spell_hit, W, "")))) == (GS.gp.St(s, k, R), DocGlob.glob.spell_page(R, s, k)) : FGb.St & String}
  %Equal.sym(String, FGb.put_opt(DocGlob.glob.Past(n, s), Wr.put_list(~DocGlob.glob.Hit, ~DocGlob.glob.spell_hit, W, "")), DocGlob.glob.spell_opt(DocGlob.glob.Past(n, s), Wr.put_list(~DocGlob.glob.Hit, ~DocGlob.glob.spell_hit, W, "")), GS.gp.opt(DocGlob.glob.Past(n, s), Wr.put_list(~DocGlob.glob.Hit, ~DocGlob.glob.spell_hit, W, ""))) : {(GS.gp.St(s, k, R), FGb.put_opt(DocGlob.glob.More(n, s, k), _)) == (GS.gp.St(s, k, R), DocGlob.glob.spell_page(R, s, k)) : FGb.St & String}
  %Equal.sym(String, FGb.put_opt(DocGlob.glob.More(n, s, k), DocGlob.glob.spell_opt(DocGlob.glob.Past(n, s), Wr.put_list(~DocGlob.glob.Hit, ~DocGlob.glob.spell_hit, W, ""))), DocGlob.glob.spell_opt(DocGlob.glob.More(n, s, k), DocGlob.glob.spell_opt(DocGlob.glob.Past(n, s), Wr.put_list(~DocGlob.glob.Hit, ~DocGlob.glob.spell_hit, W, ""))), GS.gp.opt(DocGlob.glob.More(n, s, k), DocGlob.glob.spell_opt(DocGlob.glob.Past(n, s), Wr.put_list(~DocGlob.glob.Hit, ~DocGlob.glob.spell_hit, W, "")))) : {(GS.gp.St(s, k, R), _) == (GS.gp.St(s, k, R), DocGlob.glob.spell_page(R, s, k)) : FGb.St & String}
  {==}

# the open: the state of no hit
def gp.open_lim(+s: Nat, lim: Maybe<&2, Nat>, hl: {LawsBase.core_mfits(lim) == True{} : Bool}) -> {FGb.open.lim(s, FGb.lim.tag(Wr.get_nat(DocGlob.glob.spell_opt(lim, "")))) == (GS.gp.St(s, DocGlob.glob.Size(lim), Nil{}), "") : FGb.St & String}:
  match lim:
    case None{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, "")), Wr.Got{0n, ""}, Wire.wire_nat_round_trip(0n, "", {==})) : {FGb.open.lim(s, FGb.lim.tag(_)) == (GS.gp.St(s, 200n, Nil{}), "") : FGb.St & String}
      {==}
    case Some{+l}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, Wr.put_nat(l, ""))), Wr.Got{1n, Wr.put_nat(l, "")}, Wire.wire_nat_round_trip(1n, Wr.put_nat(l, ""), {==})) : {FGb.open.lim(s, FGb.lim.tag(_)) == (GS.gp.St(s, Nat.min(l, 200n), Nil{}), "") : FGb.St & String}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(l, "")), Wr.Got{l, ""}, Wire.wire_nat_round_trip(l, "", hl)) : {FGb.open.lim(s, FGb.lim.one(_)) == (GS.gp.St(s, Nat.min(l, 200n), Nil{}), "") : FGb.St & String}
      {==}

def gp.open(+s: Nat, +lim: Maybe<&2, Nat>, hs: {LawsBase.wire_fits(s) == True{} : Bool}, hl: {LawsBase.core_mfits(lim) == True{} : Bool}) -> {FGb.open(DocGlob.glob.spell_open(s, lim)) == (GS.gp.St(s, DocGlob.glob.Size(lim), Nil{}), "") : FGb.St & String}:
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(s, DocGlob.glob.spell_opt(lim, ""))), Wr.Got{s, DocGlob.glob.spell_opt(lim, "")}, Wire.wire_nat_round_trip(s, DocGlob.glob.spell_opt(lim, ""), hs)) : {FGb.open.got(_) == (GS.gp.St(s, DocGlob.glob.Size(lim), Nil{}), "") : FGb.St & String}
  gp.open_lim(s, lim, hl)
