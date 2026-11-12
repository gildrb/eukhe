# eukhe: the proof of LAW facts_ffi_exact
# The entry's decoder reads every input as the laws' reader does, stage by
# stage (fe.*: the entry's seq chains against the laws' readers); its
# decisions are the laws' decisions (the laws of laws/facts/), and it
# spells the reply as the laws' speller does.

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_facts.bend as FFx
import ../../bend/wire.bend as Wr
import ../../laws/facts/model.bend as Facts
import ../../laws/facts/entry.bend as FactsEntry
import ./facts_cap_keeps_the_want.bend as PCapKeeps
import ./facts_cap_shrinks_on_conflict.bend as PCapShrinks
import ./facts_cap_omits_only_the_default.bend as PCapOmits
import ./facts_aux_cap_within.bend as PAuxWithin
import ./base.bend as LA
import ./facts_ffi_exact/model.bend as FEM
import ../base/logic/logic.bend as LLogicLogic

# Reading: the single fields
# --------------------------

def fe.mnat_some(r: Wr.Dec<Nat>) -> {FFx.get_mnat.some(r) == FactsEntry.fr.mnat.some(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def fe.mnat_tag(t: Nat, +s: String) -> {FFx.get_mnat.tag(t, s) == FactsEntry.fr.mnat.tag(t, s) : Wr.Dec<Maybe<&2, Nat>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      fe.mnat_some(Wr.get_nat(s))
    case 2n+p:
      {==}

def fe.mnat_go(r: Wr.Dec<Nat>) -> {FFx.get_mnat.go(r) == FactsEntry.fr.mnat(r) : Wr.Dec<Maybe<&2, Nat>>}:
  match r:
    case Wr.Got{t, +s}:
      fe.mnat_tag(t, s)
    case Wr.Bad{}:
      {==}

def fe.elv_tag(t: Nat, -s: String) -> {FFx.get_elv.tag(t, s) == FactsEntry.fr.elv.tag(t, s) : Wr.Dec<Fx.ELv>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n+p:
      {==}

def fe.elv_go(r: Wr.Dec<Nat>) -> {FFx.get_elv.go(r) == FactsEntry.fr.elv(r) : Wr.Dec<Fx.ELv>}:
  match r:
    case Wr.Got{t, s}:
      fe.elv_tag(t, s)
    case Wr.Bad{}:
      {==}

def fe.lv_tag(t: Nat, -s: String) -> {FFx.get_lv.tag(t, s) == FactsEntry.fr.lv.tag(t, s) : Wr.Dec<Fx.Lv>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n+p:
      {==}

def fe.lv_go(r: Wr.Dec<Nat>) -> {FFx.get_lv.go(r) == FactsEntry.fr.lv(r) : Wr.Dec<Fx.Lv>}:
  match r:
    case Wr.Got{t, s}:
      fe.lv_tag(t, s)
    case Wr.Bad{}:
      {==}

# Reading: the records (the entry's seq chains)
# ---------------------------------------------

def fe.customs4(+mi: Maybe<&2, Nat>, +lo: Maybe<&2, Nat>, +me: Maybe<&2, Nat>, d: Wr.Dec<Maybe<&2, Nat>>) -> {FFx.get_customs.of(FFx.seq.fin(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, FFx.P2{FFx.P2{mi, lo}, me}, d)) == FactsEntry.fr.customs.hi(mi, lo, me, d) : Wr.Dec<Fx.Customs>}:
  match d:
    case Wr.Got{hi, s}:
      {==}
    case Wr.Bad{}:
      {==}

def fe.customs3(+mi: Maybe<&2, Nat>, +lo: Maybe<&2, Nat>, d: Wr.Dec<Maybe<&2, Nat>>) -> {FFx.get_customs.of(FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, FFx.seq.fin(~FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, FFx.P2{mi, lo}, d))) == FactsEntry.fr.customs.me(mi, lo, d) : Wr.Dec<Fx.Customs>}:
  match d:
    case Wr.Got{+me, +s}:
      %fe.mnat_go(Wr.get_nat(s)) : {FFx.get_customs.of(FFx.seq.fin(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, FFx.P2{FFx.P2{mi, lo}, me}, FFx.get_mnat(s))) == FactsEntry.fr.customs.hi(mi, lo, me, _) : Wr.Dec<Fx.Customs>}
      fe.customs4(mi, lo, me, FFx.get_mnat(s))
    case Wr.Bad{}:
      {==}

def fe.customs2(+mi: Maybe<&2, Nat>, d: Wr.Dec<Maybe<&2, Nat>>) -> {FFx.get_customs.of(FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, FFx.seq(~FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, FFx.seq.fin(~Maybe<&2, Nat>, ~Maybe<&2, Nat>, mi, d)))) == FactsEntry.fr.customs.lo(mi, d) : Wr.Dec<Fx.Customs>}:
  match d:
    case Wr.Got{+lo, +s}:
      %fe.mnat_go(Wr.get_nat(s)) : {FFx.get_customs.of(FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, FFx.seq.fin(~FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, FFx.P2{mi, lo}, FFx.get_mnat(s)))) == FactsEntry.fr.customs.me(mi, lo, _) : Wr.Dec<Fx.Customs>}
      fe.customs3(mi, lo, FFx.get_mnat(s))
    case Wr.Bad{}:
      {==}

def fe.customs1(d: Wr.Dec<Maybe<&2, Nat>>) -> {FFx.get_customs.of(FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, FFx.seq(~FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, FFx.seq(~Maybe<&2, Nat>, ~Maybe<&2, Nat>, ~FFx.get_mnat, d)))) == FactsEntry.fr.customs.mi(d) : Wr.Dec<Fx.Customs>}:
  match d:
    case Wr.Got{+mi, +s}:
      %fe.mnat_go(Wr.get_nat(s)) : {FFx.get_customs.of(FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, FFx.seq(~FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, FFx.seq.fin(~Maybe<&2, Nat>, ~Maybe<&2, Nat>, mi, FFx.get_mnat(s))))) == FactsEntry.fr.customs.lo(mi, _) : Wr.Dec<Fx.Customs>}
      fe.customs2(mi, FFx.get_mnat(s))
    case Wr.Bad{}:
      {==}

def fe.budgets4(+mi: Nat, +lo: Nat, +me: Nat, d: Wr.Dec<Nat>) -> {FFx.get_budgets.of(FFx.seq.fin(~FFx.P2<FFx.P2<Nat, Nat>, Nat>, ~Nat, FFx.P2{FFx.P2{mi, lo}, me}, d)) == FactsEntry.fr.budgets.hi(mi, lo, me, d) : Wr.Dec<Fx.Budgets>}:
  match d:
    case Wr.Got{hi, s}:
      {==}
    case Wr.Bad{}:
      {==}

def fe.budgets3(+mi: Nat, +lo: Nat, d: Wr.Dec<Nat>) -> {FFx.get_budgets.of(FFx.seq(~FFx.P2<FFx.P2<Nat, Nat>, Nat>, ~Nat, ~Wr.get_nat, FFx.seq.fin(~FFx.P2<Nat, Nat>, ~Nat, FFx.P2{mi, lo}, d))) == FactsEntry.fr.budgets.me(mi, lo, d) : Wr.Dec<Fx.Budgets>}:
  match d:
    case Wr.Got{+me, +s}:
      fe.budgets4(mi, lo, me, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def fe.budgets2(+mi: Nat, d: Wr.Dec<Nat>) -> {FFx.get_budgets.of(FFx.seq(~FFx.P2<FFx.P2<Nat, Nat>, Nat>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<Nat, Nat>, ~Nat, ~Wr.get_nat, FFx.seq.fin(~Nat, ~Nat, mi, d)))) == FactsEntry.fr.budgets.lo(mi, d) : Wr.Dec<Fx.Budgets>}:
  match d:
    case Wr.Got{+lo, +s}:
      fe.budgets3(mi, lo, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def fe.budgets1(d: Wr.Dec<Nat>) -> {FFx.get_budgets.of(FFx.seq(~FFx.P2<FFx.P2<Nat, Nat>, Nat>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<Nat, Nat>, ~Nat, ~Wr.get_nat, FFx.seq(~Nat, ~Nat, ~Wr.get_nat, d)))) == FactsEntry.fr.budgets.mi(d) : Wr.Dec<Fx.Budgets>}:
  match d:
    case Wr.Got{+mi, +s}:
      fe.budgets2(mi, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def fe.win5(+w: Nat, +p: Nat, +sf: Nat, +f: Nat, d: Wr.Dec<Bool>) -> {FFx.get_win.of(FFx.seq.fin(~FFx.P2<FFx.P2<FFx.P2<Nat, Nat>, Nat>, Nat>, ~Bool, FFx.P2{FFx.P2{FFx.P2{w, p}, sf}, f}, d)) == FactsEntry.fr.win.st(w, p, sf, f, d) : Wr.Dec<Fx.Win>}:
  match d:
    case Wr.Got{st, s}:
      {==}
    case Wr.Bad{}:
      {==}

def fe.win4(+w: Nat, +p: Nat, +sf: Nat, d: Wr.Dec<Nat>) -> {FFx.get_win.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Nat, Nat>, Nat>, Nat>, ~Bool, ~Wr.get_bool, FFx.seq.fin(~FFx.P2<FFx.P2<Nat, Nat>, Nat>, ~Nat, FFx.P2{FFx.P2{w, p}, sf}, d))) == FactsEntry.fr.win.f(w, p, sf, d) : Wr.Dec<Fx.Win>}:
  match d:
    case Wr.Got{+f, +s}:
      fe.win5(w, p, sf, f, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def fe.win3(+w: Nat, +p: Nat, d: Wr.Dec<Nat>) -> {FFx.get_win.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Nat, Nat>, Nat>, Nat>, ~Bool, ~Wr.get_bool, FFx.seq(~FFx.P2<FFx.P2<Nat, Nat>, Nat>, ~Nat, ~Wr.get_nat, FFx.seq.fin(~FFx.P2<Nat, Nat>, ~Nat, FFx.P2{w, p}, d)))) == FactsEntry.fr.win.sf(w, p, d) : Wr.Dec<Fx.Win>}:
  match d:
    case Wr.Got{+sf, +s}:
      fe.win4(w, p, sf, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def fe.win2(+w: Nat, d: Wr.Dec<Nat>) -> {FFx.get_win.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Nat, Nat>, Nat>, Nat>, ~Bool, ~Wr.get_bool, FFx.seq(~FFx.P2<FFx.P2<Nat, Nat>, Nat>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<Nat, Nat>, ~Nat, ~Wr.get_nat, FFx.seq.fin(~Nat, ~Nat, w, d))))) == FactsEntry.fr.win.p(w, d) : Wr.Dec<Fx.Win>}:
  match d:
    case Wr.Got{+p, +s}:
      fe.win3(w, p, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def fe.win1(d: Wr.Dec<Nat>) -> {FFx.get_win.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Nat, Nat>, Nat>, Nat>, ~Bool, ~Wr.get_bool, FFx.seq(~FFx.P2<FFx.P2<Nat, Nat>, Nat>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<Nat, Nat>, ~Nat, ~Wr.get_nat, FFx.seq(~Nat, ~Nat, ~Wr.get_nat, d))))) == FactsEntry.fr.win.w(d) : Wr.Dec<Fx.Win>}:
  match d:
    case Wr.Got{+w, +s}:
      fe.win2(w, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def fe.customs(+s: String) -> {FFx.get_customs(s) == FactsEntry.fr.customs(s) : Wr.Dec<Fx.Customs>}:
  %fe.mnat_go(Wr.get_nat(s)) : {FFx.get_customs(s) == FactsEntry.fr.customs.mi(_) : Wr.Dec<Fx.Customs>}
  fe.customs1(FFx.get_mnat(s))

def fe.budgets(+s: String) -> {FFx.get_budgets(s) == FactsEntry.fr.budgets(s) : Wr.Dec<Fx.Budgets>}:
  fe.budgets1(Wr.get_nat(s))

def fe.win(+s: String) -> {FFx.get_win(s) == FactsEntry.fr.win(s) : Wr.Dec<Fx.Win>}:
  fe.win1(Wr.get_nat(s))

def fe.mbudgets_some(r: Wr.Dec<Fx.Budgets>) -> {FFx.get_mbudgets.some(r) == FactsEntry.fr.mbudgets.some(r) : Wr.Dec<Maybe<&2, Fx.Budgets>>}:
  match r:
    case Wr.Got{b, s}:
      {==}
    case Wr.Bad{}:
      {==}

def fe.mbudgets_tag(t: Nat, +s: String) -> {FFx.get_mbudgets.tag(t, s) == FactsEntry.fr.mbudgets.tag(t, s) : Wr.Dec<Maybe<&2, Fx.Budgets>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      %fe.budgets(s) : {FFx.get_mbudgets.some(FFx.get_budgets(s)) == FactsEntry.fr.mbudgets.some(_) : Wr.Dec<Maybe<&2, Fx.Budgets>>}
      fe.mbudgets_some(FFx.get_budgets(s))
    case 2n+p:
      {==}

def fe.mbudgets_go(r: Wr.Dec<Nat>) -> {FFx.get_mbudgets.go(r) == FactsEntry.fr.mbudgets(r) : Wr.Dec<Maybe<&2, Fx.Budgets>>}:
  match r:
    case Wr.Got{t, +s}:
      fe.mbudgets_tag(t, s)
    case Wr.Bad{}:
      {==}

def fe.level3(+l: Fx.ELv, +c: Fx.Customs, d: Wr.Dec<Fx.Budgets>) -> {FFx.get_level.of(FFx.seq.fin(~FFx.P2<Fx.ELv, Fx.Customs>, ~Fx.Budgets, FFx.P2{l, c}, d)) == FactsEntry.fr.level.d(l, c, d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{dd, s}:
      {==}
    case Wr.Bad{}:
      {==}

def fe.level2(+l: Fx.ELv, d: Wr.Dec<Fx.Customs>) -> {FFx.get_level.of(FFx.seq(~FFx.P2<Fx.ELv, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.seq.fin(~Fx.ELv, ~Fx.Customs, l, d))) == FactsEntry.fr.level.c(l, d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{+c, +s}:
      %fe.budgets(s) : {FFx.get_level.of(FFx.seq.fin(~FFx.P2<Fx.ELv, Fx.Customs>, ~Fx.Budgets, FFx.P2{l, c}, FFx.get_budgets(s))) == FactsEntry.fr.level.d(l, c, _) : Wr.Dec<FFx.Req>}
      fe.level3(l, c, FFx.get_budgets(s))
    case Wr.Bad{}:
      {==}

def fe.level1(d: Wr.Dec<Fx.ELv>) -> {FFx.get_level.of(FFx.seq(~FFx.P2<Fx.ELv, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.seq(~Fx.ELv, ~Fx.Customs, ~FFx.get_customs, d))) == FactsEntry.fr.level(d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{+l, +s}:
      %fe.customs(s) : {FFx.get_level.of(FFx.seq(~FFx.P2<Fx.ELv, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.seq.fin(~Fx.ELv, ~Fx.Customs, l, FFx.get_customs(s)))) == FactsEntry.fr.level.c(l, _) : Wr.Dec<FFx.Req>}
      fe.level2(l, FFx.get_customs(s))
    case Wr.Bad{}:
      {==}

def fe.room3(+b: Nat, +m: Nat, d: Wr.Dec<Nat>) -> {FFx.get_room.of(FFx.seq.fin(~FFx.P2<Nat, Nat>, ~Nat, FFx.P2{b, m}, d)) == FactsEntry.fr.room.a(b, m, d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def fe.room2(+b: Nat, d: Wr.Dec<Nat>) -> {FFx.get_room.of(FFx.seq(~FFx.P2<Nat, Nat>, ~Nat, ~Wr.get_nat, FFx.seq.fin(~Nat, ~Nat, b, d))) == FactsEntry.fr.room.m(b, d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{+m, +s}:
      fe.room3(b, m, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def fe.room1(d: Wr.Dec<Nat>) -> {FFx.get_room.of(FFx.seq(~FFx.P2<Nat, Nat>, ~Nat, ~Wr.get_nat, FFx.seq(~Nat, ~Nat, ~Wr.get_nat, d))) == FactsEntry.fr.room(d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{+b, +s}:
      fe.room2(b, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def fe.adjust7(+base: Maybe<&2, Nat>, +mm: Nat, +l: Fx.ELv, +c: Fx.Customs, +dd: Fx.Budgets, +a: Nat, d: Wr.Dec<Fx.Win>) -> {FFx.get_adjust.of(FFx.seq.fin(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, Nat>, ~Fx.Win, FFx.P2{FFx.P2{FFx.P2{FFx.P2{FFx.P2{base, mm}, l}, c}, dd}, a}, d)) == FactsEntry.fr.adjust.w(base, mm, l, c, dd, a, d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{w, s}:
      {==}
    case Wr.Bad{}:
      {==}

def fe.adjust6(+base: Maybe<&2, Nat>, +mm: Nat, +l: Fx.ELv, +c: Fx.Customs, +dd: Fx.Budgets, d: Wr.Dec<Nat>) -> {FFx.get_adjust.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, Nat>, ~Fx.Win, ~FFx.get_win, FFx.seq.fin(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, ~Nat, FFx.P2{FFx.P2{FFx.P2{FFx.P2{base, mm}, l}, c}, dd}, d))) == FactsEntry.fr.adjust.a(base, mm, l, c, dd, d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{+a, +s}:
      %fe.win(s) : {FFx.get_adjust.of(FFx.seq.fin(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, Nat>, ~Fx.Win, FFx.P2{FFx.P2{FFx.P2{FFx.P2{FFx.P2{base, mm}, l}, c}, dd}, a}, FFx.get_win(s))) == FactsEntry.fr.adjust.w(base, mm, l, c, dd, a, _) : Wr.Dec<FFx.Req>}
      fe.adjust7(base, mm, l, c, dd, a, FFx.get_win(s))
    case Wr.Bad{}:
      {==}

def fe.adjust5(+base: Maybe<&2, Nat>, +mm: Nat, +l: Fx.ELv, +c: Fx.Customs, d: Wr.Dec<Fx.Budgets>) -> {FFx.get_adjust.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, Nat>, ~Fx.Win, ~FFx.get_win, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.seq.fin(~FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, ~Fx.Budgets, FFx.P2{FFx.P2{FFx.P2{base, mm}, l}, c}, d)))) == FactsEntry.fr.adjust.d(base, mm, l, c, d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{+dd, +s}:
      fe.adjust6(base, mm, l, c, dd, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def fe.adjust4(+base: Maybe<&2, Nat>, +mm: Nat, +l: Fx.ELv, d: Wr.Dec<Fx.Customs>) -> {FFx.get_adjust.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, Nat>, ~Fx.Win, ~FFx.get_win, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.seq.fin(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, ~Fx.Customs, FFx.P2{FFx.P2{base, mm}, l}, d))))) == FactsEntry.fr.adjust.c(base, mm, l, d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{+c, +s}:
      %fe.budgets(s) : {FFx.get_adjust.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, Nat>, ~Fx.Win, ~FFx.get_win, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.seq.fin(~FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, ~Fx.Budgets, FFx.P2{FFx.P2{FFx.P2{base, mm}, l}, c}, FFx.get_budgets(s))))) == FactsEntry.fr.adjust.d(base, mm, l, c, _) : Wr.Dec<FFx.Req>}
      fe.adjust5(base, mm, l, c, FFx.get_budgets(s))
    case Wr.Bad{}:
      {==}

def fe.adjust3(+base: Maybe<&2, Nat>, +mm: Nat, d: Wr.Dec<Fx.ELv>) -> {FFx.get_adjust.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, Nat>, ~Fx.Win, ~FFx.get_win, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, ~Fx.Customs, ~FFx.get_customs, FFx.seq.fin(~FFx.P2<Maybe<&2, Nat>, Nat>, ~Fx.ELv, FFx.P2{base, mm}, d)))))) == FactsEntry.fr.adjust.l(base, mm, d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{+l, +s}:
      %fe.customs(s) : {FFx.get_adjust.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, Nat>, ~Fx.Win, ~FFx.get_win, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.seq.fin(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, ~Fx.Customs, FFx.P2{FFx.P2{base, mm}, l}, FFx.get_customs(s)))))) == FactsEntry.fr.adjust.c(base, mm, l, _) : Wr.Dec<FFx.Req>}
      fe.adjust4(base, mm, l, FFx.get_customs(s))
    case Wr.Bad{}:
      {==}

def fe.adjust2(+base: Maybe<&2, Nat>, d: Wr.Dec<Nat>) -> {FFx.get_adjust.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, Nat>, ~Fx.Win, ~FFx.get_win, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, ~Fx.Customs, ~FFx.get_customs, FFx.seq(~FFx.P2<Maybe<&2, Nat>, Nat>, ~Fx.ELv, ~FFx.get_elv, FFx.seq.fin(~Maybe<&2, Nat>, ~Nat, base, d))))))) == FactsEntry.fr.adjust.mm(base, d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{+mm, +s}:
      %fe.elv_go(Wr.get_nat(s)) : {FFx.get_adjust.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, Nat>, ~Fx.Win, ~FFx.get_win, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, ~Fx.Customs, ~FFx.get_customs, FFx.seq.fin(~FFx.P2<Maybe<&2, Nat>, Nat>, ~Fx.ELv, FFx.P2{base, mm}, FFx.get_elv(s))))))) == FactsEntry.fr.adjust.l(base, mm, _) : Wr.Dec<FFx.Req>}
      fe.adjust3(base, mm, FFx.get_elv(s))
    case Wr.Bad{}:
      {==}

def fe.adjust1(d: Wr.Dec<Maybe<&2, Nat>>) -> {FFx.get_adjust.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, Nat>, ~Fx.Win, ~FFx.get_win, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, ~Fx.Customs, ~FFx.get_customs, FFx.seq(~FFx.P2<Maybe<&2, Nat>, Nat>, ~Fx.ELv, ~FFx.get_elv, FFx.seq(~Maybe<&2, Nat>, ~Nat, ~Wr.get_nat, d))))))) == FactsEntry.fr.adjust(d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{+base, +s}:
      fe.adjust2(base, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def fe.google3(+rule: Maybe<&2, Fx.Budgets>, +c: Fx.Customs, d: Wr.Dec<Fx.Lv>) -> {FFx.get_google.of(FFx.seq.fin(~FFx.P2<Maybe<&2, Fx.Budgets>, Fx.Customs>, ~Fx.Lv, FFx.P2{rule, c}, d)) == FactsEntry.fr.google.l(rule, c, d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{l, s}:
      {==}
    case Wr.Bad{}:
      {==}

def fe.google2(+rule: Maybe<&2, Fx.Budgets>, d: Wr.Dec<Fx.Customs>) -> {FFx.get_google.of(FFx.seq(~FFx.P2<Maybe<&2, Fx.Budgets>, Fx.Customs>, ~Fx.Lv, ~FFx.get_lv, FFx.seq.fin(~Maybe<&2, Fx.Budgets>, ~Fx.Customs, rule, d))) == FactsEntry.fr.google.c(rule, d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{+c, +s}:
      %fe.lv_go(Wr.get_nat(s)) : {FFx.get_google.of(FFx.seq.fin(~FFx.P2<Maybe<&2, Fx.Budgets>, Fx.Customs>, ~Fx.Lv, FFx.P2{rule, c}, FFx.get_lv(s))) == FactsEntry.fr.google.l(rule, c, _) : Wr.Dec<FFx.Req>}
      fe.google3(rule, c, FFx.get_lv(s))
    case Wr.Bad{}:
      {==}

def fe.google1(d: Wr.Dec<Maybe<&2, Fx.Budgets>>) -> {FFx.get_google.of(FFx.seq(~FFx.P2<Maybe<&2, Fx.Budgets>, Fx.Customs>, ~Fx.Lv, ~FFx.get_lv, FFx.seq(~Maybe<&2, Fx.Budgets>, ~Fx.Customs, ~FFx.get_customs, d))) == FactsEntry.fr.google(d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{+rule, +s}:
      %fe.customs(s) : {FFx.get_google.of(FFx.seq(~FFx.P2<Maybe<&2, Fx.Budgets>, Fx.Customs>, ~Fx.Lv, ~FFx.get_lv, FFx.seq.fin(~Maybe<&2, Fx.Budgets>, ~Fx.Customs, rule, FFx.get_customs(s)))) == FactsEntry.fr.google.c(rule, _) : Wr.Dec<FFx.Req>}
      fe.google2(rule, FFx.get_customs(s))
    case Wr.Bad{}:
      {==}

def fe.aux4(+c: Fx.Customs, +dd: Fx.Budgets, +a: Nat, d: Wr.Dec<Nat>) -> {FFx.get_aux.of(FFx.seq.fin(~FFx.P2<FFx.P2<Fx.Customs, Fx.Budgets>, Nat>, ~Nat, FFx.P2{FFx.P2{c, dd}, a}, d)) == FactsEntry.fr.aux.top(c, dd, a, d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{top, s}:
      {==}
    case Wr.Bad{}:
      {==}

def fe.aux3(+c: Fx.Customs, +dd: Fx.Budgets, d: Wr.Dec<Nat>) -> {FFx.get_aux.of(FFx.seq(~FFx.P2<FFx.P2<Fx.Customs, Fx.Budgets>, Nat>, ~Nat, ~Wr.get_nat, FFx.seq.fin(~FFx.P2<Fx.Customs, Fx.Budgets>, ~Nat, FFx.P2{c, dd}, d))) == FactsEntry.fr.aux.a(c, dd, d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{+a, +s}:
      fe.aux4(c, dd, a, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def fe.aux2(+c: Fx.Customs, d: Wr.Dec<Fx.Budgets>) -> {FFx.get_aux.of(FFx.seq(~FFx.P2<FFx.P2<Fx.Customs, Fx.Budgets>, Nat>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<Fx.Customs, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.seq.fin(~Fx.Customs, ~Fx.Budgets, c, d)))) == FactsEntry.fr.aux.d(c, d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{+dd, +s}:
      fe.aux3(c, dd, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def fe.aux1(d: Wr.Dec<Fx.Customs>) -> {FFx.get_aux.of(FFx.seq(~FFx.P2<FFx.P2<Fx.Customs, Fx.Budgets>, Nat>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<Fx.Customs, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.seq(~Fx.Customs, ~Fx.Budgets, ~FFx.get_budgets, d)))) == FactsEntry.fr.aux(d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{+c, +s}:
      %fe.budgets(s) : {FFx.get_aux.of(FFx.seq(~FFx.P2<FFx.P2<Fx.Customs, Fx.Budgets>, Nat>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<Fx.Customs, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.seq.fin(~Fx.Customs, ~Fx.Budgets, c, FFx.get_budgets(s))))) == FactsEntry.fr.aux.d(c, _) : Wr.Dec<FFx.Req>}
      fe.aux2(c, FFx.get_budgets(s))
    case Wr.Bad{}:
      {==}

def fe.cap4(+x: Maybe<&2, Nat>, +mm: Nat, +n: Bool, d: Wr.Dec<Fx.Win>) -> {FFx.get_cap.of(FFx.seq.fin(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Bool>, ~Fx.Win, FFx.P2{FFx.P2{x, mm}, n}, d)) == FactsEntry.fr.cap.w(x, mm, n, d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{w, s}:
      {==}
    case Wr.Bad{}:
      {==}

def fe.cap3(+x: Maybe<&2, Nat>, +mm: Nat, d: Wr.Dec<Bool>) -> {FFx.get_cap.of(FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Bool>, ~Fx.Win, ~FFx.get_win, FFx.seq.fin(~FFx.P2<Maybe<&2, Nat>, Nat>, ~Bool, FFx.P2{x, mm}, d))) == FactsEntry.fr.cap.n(x, mm, d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{+n, +s}:
      %fe.win(s) : {FFx.get_cap.of(FFx.seq.fin(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Bool>, ~Fx.Win, FFx.P2{FFx.P2{x, mm}, n}, FFx.get_win(s))) == FactsEntry.fr.cap.w(x, mm, n, _) : Wr.Dec<FFx.Req>}
      fe.cap4(x, mm, n, FFx.get_win(s))
    case Wr.Bad{}:
      {==}

def fe.cap2(+x: Maybe<&2, Nat>, d: Wr.Dec<Nat>) -> {FFx.get_cap.of(FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Bool>, ~Fx.Win, ~FFx.get_win, FFx.seq(~FFx.P2<Maybe<&2, Nat>, Nat>, ~Bool, ~Wr.get_bool, FFx.seq.fin(~Maybe<&2, Nat>, ~Nat, x, d)))) == FactsEntry.fr.cap.mm(x, d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{+mm, +s}:
      fe.cap3(x, mm, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def fe.cap1(d: Wr.Dec<Maybe<&2, Nat>>) -> {FFx.get_cap.of(FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Bool>, ~Fx.Win, ~FFx.get_win, FFx.seq(~FFx.P2<Maybe<&2, Nat>, Nat>, ~Bool, ~Wr.get_bool, FFx.seq(~Maybe<&2, Nat>, ~Nat, ~Wr.get_nat, d)))) == FactsEntry.fr.cap(d) : Wr.Dec<FFx.Req>}:
  match d:
    case Wr.Got{+x, +s}:
      fe.cap2(x, Wr.get_nat(s))
    case Wr.Bad{}:
      {==}

def fe.req_tag(t: Nat, +s: String) -> {FFx.get_req.tag(t, s) == FactsEntry.fr.req.tag(t, s) : Wr.Dec<FFx.Req>}:
  match t:
    case 0n:
      %fe.elv_go(Wr.get_nat(s)) : {FFx.get_req.tag(0n, s) == FactsEntry.fr.level(_) : Wr.Dec<FFx.Req>}
      fe.level1(FFx.get_elv(s))
    case 1n:
      fe.room1(Wr.get_nat(s))
    case 2n:
      %fe.mnat_go(Wr.get_nat(s)) : {FFx.get_req.tag(2n, s) == FactsEntry.fr.adjust(_) : Wr.Dec<FFx.Req>}
      fe.adjust1(FFx.get_mnat(s))
    case 3n:
      %fe.mbudgets_go(Wr.get_nat(s)) : {FFx.get_req.tag(3n, s) == FactsEntry.fr.google(_) : Wr.Dec<FFx.Req>}
      fe.google1(FFx.get_mbudgets(s))
    case 4n:
      %fe.customs(s) : {FFx.get_req.tag(4n, s) == FactsEntry.fr.aux(_) : Wr.Dec<FFx.Req>}
      fe.aux1(FFx.get_customs(s))
    case 5n:
      %fe.mnat_go(Wr.get_nat(s)) : {FFx.get_req.tag(5n, s) == FactsEntry.fr.cap(_) : Wr.Dec<FFx.Req>}
      fe.cap1(FFx.get_mnat(s))
    case 6n+p:
      {==}

def fe.req(r: Wr.Dec<Nat>) -> {FFx.get_req.go(r) == FactsEntry.fr.req(r) : Wr.Dec<FFx.Req>}:
  match r:
    case Wr.Got{t, +s}:
      fe.req_tag(t, s)
    case Wr.Bad{}:
      {==}

# Decisions
# ---------

def fe.lv(l: Fx.ELv) -> {Fx.Lv.of(l) == FactsEntry.fs.lv(l) : Fx.Lv}:
  match l:
    case Fx.EMinimal{}:
      {==}
    case Fx.ELow{}:
      {==}
    case Fx.EMedium{}:
      {==}
    case Fx.EHigh{}:
      {==}
    case Fx.EXhigh{}:
      {==}
    case Fx.EMax{}:
      {==}

def fe.budget(c: Fx.Customs, d: Fx.Budgets, l: Fx.Lv) -> {Fx.budget(c, d, l) == FactsEntry.fs.budget(c, d, l) : Nat}:
  match c d l:
    case Fx.Customs{cmi, clo, cme, chi} Fx.Budgets{mi, lo, me, hi} Fx.Minimal{}:
      {==}
    case Fx.Customs{cmi, clo, cme, chi} Fx.Budgets{mi, lo, me, hi} Fx.Low{}:
      {==}
    case Fx.Customs{cmi, clo, cme, chi} Fx.Budgets{mi, lo, me, hi} Fx.Medium{}:
      {==}
    case Fx.Customs{cmi, clo, cme, chi} Fx.Budgets{mi, lo, me, hi} Fx.High{}:
      {==}

# the cap Some{y} is the cap Some{z}: y is z
def fe.some_inj(-y: Nat, -z: Nat, e: {Some{y} == Some{z} : Maybe<&2, Nat>}) -> {y == z : Nat}:
  Equal.cong(Maybe<&2, Nat>, Nat, m => Maybe.default(&2, Nat, m, 0n), Some{y}, Some{z}, e)

def fe.shrink_at(+x: Nat, +win: Fx.Win, c: Bool, e: {Facts.cap_conflict(x, win) == c : Bool}) -> {Fx.cap.shrink(x, win) == FactsEntry.fs.shrink.at(c, x, win) : Nat}:
  match c:
    case True{}:
      fe.some_inj(Fx.cap.shrink(x, win), Facts.cap_room(win), Facts.facts_cap_shrinks_on_conflict(Some{x}, 0n, False{}, win, {==}, e))
    case False{}:
      fe.some_inj(Fx.cap.shrink(x, win), x, Facts.facts_cap_keeps_the_want(Some{x}, 0n, False{}, win, {==}, e))

def fe.shrink(+x: Nat, +win: Fx.Win) -> {Fx.cap.shrink(x, win) == FactsEntry.fs.shrink(x, win) : Nat}:
  fe.shrink_at(x, win, Facts.cap_conflict(x, win), {==})

def fe.fit(base: Maybe<&2, Nat>, +mm: Nat, +b: Nat, +a: Nat, +win: Fx.Win) -> {Fx.fit(base, mm, b, a, win) == FactsEntry.fs.fit(base, mm, b, a, win) : Fx.Fit}:
  match base:
    case None{}:
      %fe.shrink(mm, win) : {Fx.fit(None{}, mm, b, a, win) == Facts.budgets.fit(_, b, a) : Fx.Fit}
      FEM.fem.fit_model(mm, b, a, win)
    case Some{+x}:
      %fe.shrink(Nat.min(Nat.add(x, b), mm), win) : {Fx.fit(Some{x}, mm, b, a, win) == Facts.budgets.fit(_, b, a) : Fx.Fit}
      FEM.fem.fit_caller(x, mm, b, a, win)

def fe.free(m: Maybe<&2, Nat>) -> {Fx.gbudget.free(m) == FactsEntry.fs.gb.free(m) : Fx.GB}:
  match m:
    case Some{n}:
      {==}
    case None{}:
      {==}

def fe.ordered(b: Fx.Budgets) -> {Fx.Budgets.ordered(b) == FactsEntry.fs.ordered(b) : Bool}:
  match b:
    case Fx.Budgets{mi, lo, me, hi}:
      {==}

def fe.at(b: Fx.Budgets, l: Fx.Lv) -> {Fx.Budgets.at(b, l) == FactsEntry.fs.at(b, l) : Nat}:
  match b l:
    case Fx.Budgets{mi, lo, me, hi} Fx.Minimal{}:
      {==}
    case Fx.Budgets{mi, lo, me, hi} Fx.Low{}:
      {==}
    case Fx.Budgets{mi, lo, me, hi} Fx.Medium{}:
      {==}
    case Fx.Budgets{mi, lo, me, hi} Fx.High{}:
      {==}

def fe.minimal(b: Fx.Budgets) -> {Fx.Budgets.minimal(b) == FactsEntry.fs.minimal(b) : Nat}:
  match b:
    case Fx.Budgets{mi, lo, me, hi}:
      {==}

def fe.high(b: Fx.Budgets) -> {Fx.Budgets.high(b) == FactsEntry.fs.high(b) : Nat}:
  match b:
    case Fx.Budgets{mi, lo, me, hi}:
      {==}

def fe.rule(+b: Fx.Budgets, +c: Fx.Customs, +l: Fx.Lv, ok: Bool, e: {Fx.Budgets.ordered(b) == ok : Bool}) -> {Fx.gbudget.rule(ok, b, c, l) == FactsEntry.fs.gb.rule(ok, b, c, l) : Fx.GB}:
  match ok:
    case True{}:
      %LA.fg.at(c, l) : {Fx.Tokens{Fx.gtokens(b, c, l)} == Fx.Tokens{Facts.budgets.held(Maybe.default(&2, Nat, _, FactsEntry.fs.at(b, l)), FactsEntry.fs.minimal(b), FactsEntry.fs.high(b))} : Fx.GB}
      %fe.at(b, l) : {Fx.Tokens{Fx.gtokens(b, c, l)} == Fx.Tokens{Facts.budgets.held(Maybe.default(&2, Nat, Fx.Customs.at(c, l), _), FactsEntry.fs.minimal(b), FactsEntry.fs.high(b))} : Fx.GB}
      %fe.minimal(b) : {Fx.Tokens{Fx.gtokens(b, c, l)} == Fx.Tokens{Facts.budgets.held(Maybe.default(&2, Nat, Fx.Customs.at(c, l), Fx.Budgets.at(b, l)), _, FactsEntry.fs.high(b))} : Fx.GB}
      %fe.high(b) : {Fx.Tokens{Fx.gtokens(b, c, l)} == Fx.Tokens{Facts.budgets.held(Maybe.default(&2, Nat, Fx.Customs.at(c, l), Fx.Budgets.at(b, l)), Fx.Budgets.minimal(b), _)} : Fx.GB}
      %FEM.fem.held(b, c, l, e) : {Fx.Tokens{Fx.gtokens(b, c, l)} == Fx.Tokens{_} : Fx.GB}
      {==}
    case False{}:
      {==}

def fe.gb(rule: Maybe<&2, Fx.Budgets>, +c: Fx.Customs, +l: Fx.Lv) -> {Fx.gbudget(rule, c, l) == FactsEntry.fs.gb(rule, c, l) : Fx.GB}:
  match rule:
    case None{}:
      %LA.fg.at(c, l) : {Fx.gbudget.free(Fx.Customs.at(c, l)) == FactsEntry.fs.gb.free(_) : Fx.GB}
      fe.free(Fx.Customs.at(c, l))
    case Some{+b}:
      %fe.ordered(b) : {Fx.gbudget.rule(Fx.Budgets.ordered(b), b, c, l) == FactsEntry.fs.gb.rule(_, b, c, l) : Fx.GB}
      fe.rule(b, c, l, Fx.Budgets.ordered(b), {==})

def fe.aux(+c: Fx.Customs, +d: Fx.Budgets, +a: Nat, +top: Nat) -> {Fx.aux(c, d, a, top) == FactsEntry.fs.aux(c, d, a, top) : Nat}:
  %fe.budget(c, d, Fx.High{}) : {Fx.aux(c, d, a, top) == Nat.min(Nat.add(_, a), top) : Nat}
  Facts.facts_aux_cap_within(Fx.budget(c, d, Fx.High{}), a, top)

def fe.cap_conf(+caller: Maybe<&2, Nat>, +mm: Nat, +needs: Bool, +win: Fx.Win, h1: {Facts.cap_left_out(caller, needs) == False{} : Bool}, c: Bool, e: {Facts.cap_conflict(Facts.cap_want(caller, mm), win) == c : Bool}) -> {Fx.cap(caller, mm, needs, win) == Some{FactsEntry.fs.shrink.at(c, Facts.cap_want(caller, mm), win)} : Maybe<&2, Nat>}:
  match c:
    case True{}:
      Facts.facts_cap_shrinks_on_conflict(caller, mm, needs, win, h1, e)
    case False{}:
      Facts.facts_cap_keeps_the_want(caller, mm, needs, win, h1, e)

# a cap that is not present is none
def fe.absent(m: Maybe<&2, Nat>, e: {Facts.cap_present(m) == False{} : Bool}) -> {m == None{} : Maybe<&2, Nat>}:
  match m:
    case Some{x}:
      LLogicLogic.pf.absurd_tf({Some{x} == None{} : Maybe<&2, Nat>}, e)
    case None{}:
      {==}

# a cap that is left out (e) is none
def fe.cap_out(+caller: Maybe<&2, Nat>, +mm: Nat, +needs: Bool, +win: Fx.Win, e: {Facts.cap_left_out(caller, needs) == True{} : Bool}) -> {Fx.cap(caller, mm, needs, win) == None{} : Maybe<&2, Nat>}:
  match caller needs:
    case Some{+x} True{}:
      LLogicLogic.pq.absurdF({Fx.cap(Some{x}, mm, True{}, win) == None{} : Maybe<&2, Nat>}, e)
    case Some{+x} False{}:
      LLogicLogic.pq.absurdF({Fx.cap(Some{x}, mm, False{}, win) == None{} : Maybe<&2, Nat>}, e)
    case None{} True{}:
      LLogicLogic.pq.absurdF({Fx.cap(None{}, mm, True{}, win) == None{} : Maybe<&2, Nat>}, e)
    case None{} False{}:
      fe.absent(Fx.cap(None{}, mm, False{}, win), Facts.facts_cap_omits_only_the_default(None{}, mm, win))

def fe.cap_at(+caller: Maybe<&2, Nat>, +mm: Nat, +needs: Bool, +win: Fx.Win, u: Bool, e: {Facts.cap_left_out(caller, needs) == u : Bool}) -> {Fx.cap(caller, mm, needs, win) == FactsEntry.fs.cap.at(u, caller, mm, win) : Maybe<&2, Nat>}:
  match u:
    case True{}:
      fe.cap_out(caller, mm, needs, win, e)
    case False{}:
      fe.cap_conf(caller, mm, needs, win, e, Facts.cap_conflict(Facts.cap_want(caller, mm), win), {==})

def fe.cap(+caller: Maybe<&2, Nat>, +mm: Nat, +needs: Bool, +win: Fx.Win) -> {Fx.cap(caller, mm, needs, win) == FactsEntry.fs.cap(caller, mm, needs, win) : Maybe<&2, Nat>}:
  fe.cap_at(caller, mm, needs, win, Facts.cap_left_out(caller, needs), {==})

# Spelling
# --------

def fe.put_mnat(m: Maybe<&2, Nat>, -rest: String) -> {FFx.put_mnat(m, rest) == FactsEntry.fs.put_mnat(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      {==}

def fe.put_gb(g: Fx.GB, -rest: String) -> {FFx.put_gb(g, rest) == FactsEntry.fs.put_gb(g, rest) : String}:
  match g:
    case Fx.Dynamic{}:
      {==}
    case Fx.Tokens{n}:
      {==}
    case Fx.Unordered{}:
      {==}

def fe.put_fit(f: Fx.Fit, -rest: String) -> {FFx.put_fit(f, rest) == FactsEntry.fs.put_fit(f, rest) : String}:
  match f:
    case Fx.Fit{m, b}:
      {==}

def fe.answer(q: FFx.Req) -> {FFx.answer(q) == FactsEntry.fs.reply(q) : String}:
  match q:
    case FFx.Level{+l, +c, +d}:
      %fe.lv(l) : {Wr.put_nat(Fx.budget(c, d, Fx.Lv.of(l)), "") == Wr.put_nat(FactsEntry.fs.budget(c, d, _), "") : String}
      %fe.budget(c, d, Fx.Lv.of(l)) : {Wr.put_nat(Fx.budget(c, d, Fx.Lv.of(l)), "") == Wr.put_nat(_, "") : String}
      {==}
    case FFx.Room{b, m, a}:
      {==}
    case FFx.Adjust{+base, +mm, +l, +c, +d, +a, +w}:
      %fe.lv(l) : {FFx.put_fit(Fx.adjust(base, mm, l, c, d, a, w), "") == FactsEntry.fs.put_fit(FactsEntry.fs.fit(base, mm, FactsEntry.fs.budget(c, d, _), a, w), "") : String}
      %fe.budget(c, d, Fx.Lv.of(l)) : {FFx.put_fit(Fx.adjust(base, mm, l, c, d, a, w), "") == FactsEntry.fs.put_fit(FactsEntry.fs.fit(base, mm, _, a, w), "") : String}
      %fe.fit(base, mm, Fx.budget(c, d, Fx.Lv.of(l)), a, w) : {FFx.put_fit(Fx.adjust(base, mm, l, c, d, a, w), "") == FactsEntry.fs.put_fit(_, "") : String}
      fe.put_fit(Fx.adjust(base, mm, l, c, d, a, w), "")
    case FFx.Google{+rule, +c, +l}:
      %fe.gb(rule, c, l) : {FFx.put_gb(Fx.gbudget(rule, c, l), "") == FactsEntry.fs.put_gb(_, "") : String}
      fe.put_gb(Fx.gbudget(rule, c, l), "")
    case FFx.Aux{+c, +d, +a, +top}:
      %fe.aux(c, d, a, top) : {Wr.put_nat(Fx.aux(c, d, a, top), "") == Wr.put_nat(_, "") : String}
      {==}
    case FFx.Cap{+x, +mm, +n, +w}:
      %fe.cap(x, mm, n, w) : {FFx.put_mnat(Fx.cap(x, mm, n, w), "") == FactsEntry.fs.put_mnat(_, "") : String}
      fe.put_mnat(Fx.cap(x, mm, n, w), "")

# The entry
# ---------

def fe.end(b: Bool, q: FFx.Req) -> {FFx.ffi.done(b, q) == FactsEntry.fs.end(b, q) : String}:
  match b:
    case True{}:
      fe.answer(q)
    case False{}:
      {==}

def fe.run(r: Wr.Dec<FFx.Req>) -> {FFx.ffi.go(r) == FactsEntry.fs.run(r) : String}:
  match r:
    case Wr.Got{q, +s}:
      fe.end(Wr.end(s), q)
    case Wr.Bad{}:
      {==}

def FactsEntry.facts_ffi_exact(s):
  %fe.req(Wr.get_nat(s)) : {FFx.ffi.go(FFx.get_req(s)) == FactsEntry.fs.run(_) : String}
  fe.run(FFx.get_req(s))
