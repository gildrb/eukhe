# eukhe: lemmas of LAW metric_line_reads: the parser reads back the
# parts of every line the METRIC grammar spells, stage by stage

import Base
import ../../../bend/autoresearch/line.bend as L
import ../../../spec/autoresearch/decimal.bend as SD
import ../../../spec/autoresearch/metric_line.bend as SL
import ../base/line.bend as AL

# a line ends in trailing blanks: the take succeeds
def alr.take_ok(+s: String, -p: L.Parts, h: {SL.all_trail(s) == True{} : Bool}) -> {L.take_if(L.trail_all(s), p) == Some{p} : Maybe<&2, L.Parts>}:
  %Equal.sym(Bool, L.trail_all(s), True{}, Equal.trans(Bool, L.trail_all(s), SL.all_trail(s), True{}, AL.al.trail_eq(s), h)) : {L.take_if(_, p) == Some{p} : Maybe<&2, L.Parts>}
  {==}

# the digits stop where the fraction or the trailing blanks start
def alr.stop_frac(frac: Maybe<&2, List<&2, Nat>>, +trail: String, h: {SL.all_trail(trail) == True{} : Bool}) -> {L.span_d(SL.spell_frac(frac, trail)) == (Nil{}, SL.spell_frac(frac, trail)) : List<&2, Nat> & String}:
  match frac:
    case None{}:
      AL.al.stop_d_trail(trail, h)
    case Some{fs}:
      {==}

# after the integer digits: the fraction, then the trailing blanks
def alr.frac(-sp: String, -name: String, -neg: Bool, -int: List<&2, Nat>, frac: Maybe<&2, List<&2, Nat>>, +trail: String, hf: {SL.frac_ok(frac) == True{} : Bool}, +ht: {SL.all_trail(trail) == True{} : Bool}) -> {L.pl.frac(sp, name, neg, int, SL.spell_frac(frac, trail)) == Some{L.Parts{sp, name, neg, int, frac, trail}} : Maybe<&2, L.Parts>}:
  match frac:
    case None{}:
      match trail:
        case SNil{}:
          {==}
        case SCon{+c, +t}:
          %Equal.sym(Bool, L.same_char(c, '.'), False{}, AL.al.trail_not_dot(c, AL.al.and_l(SL.is_trail(SL.code(c)), SL.all_trail(t), ht))) : {L.pl.point(_, sp, name, neg, int, c, t) == Some{L.Parts{sp, name, neg, int, None{}, SCon{c, t}}} : Maybe<&2, L.Parts>}
          alr.take_ok(SCon{c, t}, L.Parts{sp, name, neg, int, None{}, SCon{c, t}}, ht)
    case Some{fs}:
      match fs:
        case Nil{}:
          AL.al.absurd({L.pl.frac(sp, name, neg, int, SL.spell_frac(Some{Nil{}}, trail)) == Some{L.Parts{sp, name, neg, int, Some{Nil{}}, trail}} : Maybe<&2, L.Parts>}, hf)
        case +f <> +fr:
          %Equal.sym(List<&2, Nat> & String, L.span_d(SL.spell_ds(f <> fr, trail)), (f <> fr, trail), AL.al.span_d_app(f <> fr, trail, hf, AL.al.stop_d_trail(trail, ht))) : {L.pl.frac.got(sp, name, neg, int, _) == Some{L.Parts{sp, name, neg, int, Some{f <> fr}, trail}} : Maybe<&2, L.Parts>}
          alr.take_ok(trail, L.Parts{sp, name, neg, int, Some{f <> fr}, trail}, ht)

# the integer digits, then the rest
def alr.int(-sp: String, -name: String, -neg: Bool, int: List<&2, Nat>, +frac: Maybe<&2, List<&2, Nat>>, +trail: String, hi: {Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)) == True{} : Bool}, hf: {SL.frac_ok(frac) == True{} : Bool}, +ht: {SL.all_trail(trail) == True{} : Bool}) -> {L.pl.int(sp, name, neg, L.span_d(SL.spell_ds(int, SL.spell_frac(frac, trail)))) == Some{L.Parts{sp, name, neg, int, frac, trail}} : Maybe<&2, L.Parts>}:
  match int:
    case Nil{}:
      AL.al.absurd({L.pl.int(sp, name, neg, L.span_d(SL.spell_ds(Nil{}, SL.spell_frac(frac, trail)))) == Some{L.Parts{sp, name, neg, Nil{}, frac, trail}} : Maybe<&2, L.Parts>}, hi)
    case +d <> +t:
      %Equal.sym(List<&2, Nat> & String, L.span_d(SL.spell_ds(d <> t, SL.spell_frac(frac, trail))), (d <> t, SL.spell_frac(frac, trail)), AL.al.span_d_app(d <> t, SL.spell_frac(frac, trail), hi, alr.stop_frac(frac, trail, ht))) : {L.pl.int(sp, name, neg, _) == Some{L.Parts{sp, name, neg, d <> t, frac, trail}} : Maybe<&2, L.Parts>}
      alr.frac(sp, name, neg, d <> t, frac, trail, hf, ht)

# after '=': the sign, then the integer digits
def alr.sign(-sp: String, -name: String, neg: Bool, +int: List<&2, Nat>, +frac: Maybe<&2, List<&2, Nat>>, +trail: String, +hi: {Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)) == True{} : Bool}, hf: {SL.frac_ok(frac) == True{} : Bool}, +ht: {SL.all_trail(trail) == True{} : Bool}) -> {L.pl.sign(sp, name, SL.spell_sign(neg, SL.spell_ds(int, SL.spell_frac(frac, trail)))) == Some{L.Parts{sp, name, neg, int, frac, trail}} : Maybe<&2, L.Parts>}:
  match neg:
    case True{}:
      alr.int(sp, name, True{}, int, frac, trail, hi, hf, ht)
    case False{}:
      match int:
        case Nil{}:
          AL.al.absurd({L.pl.sign(sp, name, SL.spell_sign(False{}, SL.spell_ds(Nil{}, SL.spell_frac(frac, trail)))) == Some{L.Parts{sp, name, False{}, Nil{}, frac, trail}} : Maybe<&2, L.Parts>}, hi)
        case +d <> +t:
          %Equal.sym(Bool, L.same_char(SL.char(Nat.add(48n, d)), '-'), False{}, AL.al.df3(d, AL.al.and_l(Nat.is_lt(d, 10n), SD.digits_ok(t), hi))) : {L.pl.sign.at(_, sp, name, SL.char(Nat.add(48n, d)), SL.spell_ds(t, SL.spell_frac(frac, trail))) == Some{L.Parts{sp, name, False{}, d <> t, frac, trail}} : Maybe<&2, L.Parts>}
          alr.int(sp, name, False{}, d <> t, frac, trail, hi, hf, ht)

# the name, then '='
def alr.name(-sp: String, name: String, +neg: Bool, +int: List<&2, Nat>, +frac: Maybe<&2, List<&2, Nat>>, +trail: String, hn: {Bool.and(SL.nonempty(name), SL.all_name(name)) == True{} : Bool}, hi: {Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)) == True{} : Bool}, hf: {SL.frac_ok(frac) == True{} : Bool}, ht: {SL.all_trail(trail) == True{} : Bool}) -> {L.pl.name(sp, L.span_n(String.append(name, SCon{'=', SL.spell_sign(neg, SL.spell_ds(int, SL.spell_frac(frac, trail)))}))) == Some{L.Parts{sp, name, neg, int, frac, trail}} : Maybe<&2, L.Parts>}:
  match name:
    case SNil{}:
      AL.al.absurd({L.pl.name(sp, L.span_n(String.append(SNil{}, SCon{'=', SL.spell_sign(neg, SL.spell_ds(int, SL.spell_frac(frac, trail)))}))) == Some{L.Parts{sp, SNil{}, neg, int, frac, trail}} : Maybe<&2, L.Parts>}, hn)
    case SCon{+c, +t}:
      %Equal.sym(String & String, L.span_n(String.append(SCon{c, t}, SCon{'=', SL.spell_sign(neg, SL.spell_ds(int, SL.spell_frac(frac, trail)))})), (SCon{c, t}, SCon{'=', SL.spell_sign(neg, SL.spell_ds(int, SL.spell_frac(frac, trail)))}), AL.al.span_n_app(SCon{c, t}, SCon{'=', SL.spell_sign(neg, SL.spell_ds(int, SL.spell_frac(frac, trail)))}, hn, {==})) : {L.pl.name(sp, _) == Some{L.Parts{sp, SCon{c, t}, neg, int, frac, trail}} : Maybe<&2, L.Parts>}
      alr.sign(sp, SCon{c, t}, neg, int, frac, trail, hi, hf, ht)

# the blanks after METRIC, then the name
def alr.sp(sp: String, +name: String, +neg: Bool, +int: List<&2, Nat>, +frac: Maybe<&2, List<&2, Nat>>, +trail: String, hs: {Bool.and(SL.nonempty(sp), SL.all_blank(sp)) == True{} : Bool}, +hn: {Bool.and(SL.nonempty(name), SL.all_name(name)) == True{} : Bool}, hi: {Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)) == True{} : Bool}, hf: {SL.frac_ok(frac) == True{} : Bool}, ht: {SL.all_trail(trail) == True{} : Bool}) -> {L.pl.sp(L.span_b(String.append(sp, String.append(name, SCon{'=', SL.spell_sign(neg, SL.spell_ds(int, SL.spell_frac(frac, trail)))})))) == Some{L.Parts{sp, name, neg, int, frac, trail}} : Maybe<&2, L.Parts>}:
  match sp:
    case SNil{}:
      AL.al.absurd({L.pl.sp(L.span_b(String.append(SNil{}, String.append(name, SCon{'=', SL.spell_sign(neg, SL.spell_ds(int, SL.spell_frac(frac, trail)))})))) == Some{L.Parts{SNil{}, name, neg, int, frac, trail}} : Maybe<&2, L.Parts>}, hs)
    case SCon{+c, +t}:
      %Equal.sym(String & String, L.span_b(String.append(SCon{c, t}, String.append(name, SCon{'=', SL.spell_sign(neg, SL.spell_ds(int, SL.spell_frac(frac, trail)))}))), (SCon{c, t}, String.append(name, SCon{'=', SL.spell_sign(neg, SL.spell_ds(int, SL.spell_frac(frac, trail)))})), AL.al.span_b_app(SCon{c, t}, String.append(name, SCon{'=', SL.spell_sign(neg, SL.spell_ds(int, SL.spell_frac(frac, trail)))}), hs, AL.al.stop_b_name(name, SCon{'=', SL.spell_sign(neg, SL.spell_ds(int, SL.spell_frac(frac, trail)))}, AL.al.and_l(SL.nonempty(name), SL.all_name(name), hn), AL.al.and_r(SL.nonempty(name), SL.all_name(name), hn)))) : {L.pl.sp(_) == Some{L.Parts{SCon{c, t}, name, neg, int, frac, trail}} : Maybe<&2, L.Parts>}
      alr.name(SCon{c, t}, name, neg, int, frac, trail, hn, hi, hf, ht)

# the parser reads back the parts of every well-formed line
def alr.parse_line(+p: L.Parts, +ok: {SL.ok(p) == True{} : Bool}) -> {L.parse(SL.line(p)) == Some{p} : Maybe<&2, L.Parts>}:
  match p:
    case L.Parts{+sp, +name, +neg, +int, +frac, +trail}:
      +r1 = AL.al.and_r(Bool.and(SL.nonempty(sp), SL.all_blank(sp)), Bool.and(Bool.and(SL.nonempty(name), SL.all_name(name)), Bool.and(Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)), Bool.and(SL.frac_ok(frac), SL.all_trail(trail)))), ok)
      +r2 = AL.al.and_r(Bool.and(SL.nonempty(name), SL.all_name(name)), Bool.and(Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)), Bool.and(SL.frac_ok(frac), SL.all_trail(trail))), r1)
      +r3 = AL.al.and_r(Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)), Bool.and(SL.frac_ok(frac), SL.all_trail(trail)), r2)
      alr.sp(sp, name, neg, int, frac, trail, AL.al.and_l(Bool.and(SL.nonempty(sp), SL.all_blank(sp)), Bool.and(Bool.and(SL.nonempty(name), SL.all_name(name)), Bool.and(Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)), Bool.and(SL.frac_ok(frac), SL.all_trail(trail)))), ok), AL.al.and_l(Bool.and(SL.nonempty(name), SL.all_name(name)), Bool.and(Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)), Bool.and(SL.frac_ok(frac), SL.all_trail(trail))), r1), AL.al.and_l(Bool.and(SL.nonempty_ds(int), SD.digits_ok(int)), Bool.and(SL.frac_ok(frac), SL.all_trail(trail)), r2), AL.al.and_l(SL.frac_ok(frac), SL.all_trail(trail), r3), AL.al.and_r(SL.frac_ok(frac), SL.all_trail(trail), r3))
