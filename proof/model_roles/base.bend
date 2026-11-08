# eukhe: lemmas the proofs of area model_roles share

import Base
import ../../bend/model_roles.bend as Mr
import ../../bend/ffi_model_roles.bend as FMr
import ../../bend/wire.bend as Wr
import ../../laws/model_roles.bend as ModelRoles
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire

# ---- model_roles_wire ----

# a Nat that fits reads back (Laws.wire_nat_round_trip, turned around)
def pmr.nat(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

def ModelRoles.mrw_choice_round_trip(c, rest, h):
  match c:
    case Mr.Unset{}:
      {==}
    case Mr.Sel{+n}:
      %pmr.nat(n, rest, h) : {FMr.get_choice.n(_) == Wr.Got{Mr.Sel{n}, rest} : Wr.Dec<Mr.Choice>}
      {==}

# a setting reads back (turned around for rewriting)
def pmr.choice(+c: Mr.Choice, +rest: String, h: {ModelRoles.mrw_choice_fits(c) == True{} : Bool}) -> {Wr.Got{c, rest} == FMr.get_choice(FMr.put_choice(c, rest)) : Wr.Dec<Mr.Choice>}:
  Equal.sym(Wr.Dec<Mr.Choice>, FMr.get_choice(FMr.put_choice(c, rest)), Wr.Got{c, rest}, ModelRoles.mrw_choice_round_trip(c, rest, h))

def ModelRoles.mrw_owns_round_trip(o, rest, h):
  match o:
    case Mr.Owns{+chat, +memory, +auxiliary, +image, +subagent, +worker, +gateway, +query, +titles, +judge, +translate, +speech, +dictation}:
      +z = rest
      +h0 = h
      +h1 = LLogicBool.wr_and_r(ModelRoles.mrw_choice_fits(chat), Bool.and(ModelRoles.mrw_choice_fits(memory), Bool.and(ModelRoles.mrw_choice_fits(auxiliary), Bool.and(ModelRoles.mrw_choice_fits(image), Bool.and(ModelRoles.mrw_choice_fits(subagent), Bool.and(ModelRoles.mrw_choice_fits(worker), Bool.and(ModelRoles.mrw_choice_fits(gateway), Bool.and(ModelRoles.mrw_choice_fits(query), Bool.and(ModelRoles.mrw_choice_fits(titles), Bool.and(ModelRoles.mrw_choice_fits(judge), Bool.and(ModelRoles.mrw_choice_fits(translate), Bool.and(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation)))))))))))), h0)
      +h2 = LLogicBool.wr_and_r(ModelRoles.mrw_choice_fits(memory), Bool.and(ModelRoles.mrw_choice_fits(auxiliary), Bool.and(ModelRoles.mrw_choice_fits(image), Bool.and(ModelRoles.mrw_choice_fits(subagent), Bool.and(ModelRoles.mrw_choice_fits(worker), Bool.and(ModelRoles.mrw_choice_fits(gateway), Bool.and(ModelRoles.mrw_choice_fits(query), Bool.and(ModelRoles.mrw_choice_fits(titles), Bool.and(ModelRoles.mrw_choice_fits(judge), Bool.and(ModelRoles.mrw_choice_fits(translate), Bool.and(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation))))))))))), h1)
      +h3 = LLogicBool.wr_and_r(ModelRoles.mrw_choice_fits(auxiliary), Bool.and(ModelRoles.mrw_choice_fits(image), Bool.and(ModelRoles.mrw_choice_fits(subagent), Bool.and(ModelRoles.mrw_choice_fits(worker), Bool.and(ModelRoles.mrw_choice_fits(gateway), Bool.and(ModelRoles.mrw_choice_fits(query), Bool.and(ModelRoles.mrw_choice_fits(titles), Bool.and(ModelRoles.mrw_choice_fits(judge), Bool.and(ModelRoles.mrw_choice_fits(translate), Bool.and(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation)))))))))), h2)
      +h4 = LLogicBool.wr_and_r(ModelRoles.mrw_choice_fits(image), Bool.and(ModelRoles.mrw_choice_fits(subagent), Bool.and(ModelRoles.mrw_choice_fits(worker), Bool.and(ModelRoles.mrw_choice_fits(gateway), Bool.and(ModelRoles.mrw_choice_fits(query), Bool.and(ModelRoles.mrw_choice_fits(titles), Bool.and(ModelRoles.mrw_choice_fits(judge), Bool.and(ModelRoles.mrw_choice_fits(translate), Bool.and(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation))))))))), h3)
      +h5 = LLogicBool.wr_and_r(ModelRoles.mrw_choice_fits(subagent), Bool.and(ModelRoles.mrw_choice_fits(worker), Bool.and(ModelRoles.mrw_choice_fits(gateway), Bool.and(ModelRoles.mrw_choice_fits(query), Bool.and(ModelRoles.mrw_choice_fits(titles), Bool.and(ModelRoles.mrw_choice_fits(judge), Bool.and(ModelRoles.mrw_choice_fits(translate), Bool.and(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation)))))))), h4)
      +h6 = LLogicBool.wr_and_r(ModelRoles.mrw_choice_fits(worker), Bool.and(ModelRoles.mrw_choice_fits(gateway), Bool.and(ModelRoles.mrw_choice_fits(query), Bool.and(ModelRoles.mrw_choice_fits(titles), Bool.and(ModelRoles.mrw_choice_fits(judge), Bool.and(ModelRoles.mrw_choice_fits(translate), Bool.and(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation))))))), h5)
      +h7 = LLogicBool.wr_and_r(ModelRoles.mrw_choice_fits(gateway), Bool.and(ModelRoles.mrw_choice_fits(query), Bool.and(ModelRoles.mrw_choice_fits(titles), Bool.and(ModelRoles.mrw_choice_fits(judge), Bool.and(ModelRoles.mrw_choice_fits(translate), Bool.and(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation)))))), h6)
      +h8 = LLogicBool.wr_and_r(ModelRoles.mrw_choice_fits(query), Bool.and(ModelRoles.mrw_choice_fits(titles), Bool.and(ModelRoles.mrw_choice_fits(judge), Bool.and(ModelRoles.mrw_choice_fits(translate), Bool.and(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation))))), h7)
      +h9 = LLogicBool.wr_and_r(ModelRoles.mrw_choice_fits(titles), Bool.and(ModelRoles.mrw_choice_fits(judge), Bool.and(ModelRoles.mrw_choice_fits(translate), Bool.and(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation)))), h8)
      +h10 = LLogicBool.wr_and_r(ModelRoles.mrw_choice_fits(judge), Bool.and(ModelRoles.mrw_choice_fits(translate), Bool.and(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation))), h9)
      +h11 = LLogicBool.wr_and_r(ModelRoles.mrw_choice_fits(translate), Bool.and(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation)), h10)
      +h12 = LLogicBool.wr_and_r(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation), h11)
      %pmr.choice(chat, FMr.put_choice(memory, FMr.put_choice(auxiliary, FMr.put_choice(image, FMr.put_choice(subagent, FMr.put_choice(worker, FMr.put_choice(gateway, FMr.put_choice(query, FMr.put_choice(titles, FMr.put_choice(judge, FMr.put_choice(translate, FMr.put_choice(speech, FMr.put_choice(dictation, z)))))))))))), LLogicBool.wr_and_l(ModelRoles.mrw_choice_fits(chat), Bool.and(ModelRoles.mrw_choice_fits(memory), Bool.and(ModelRoles.mrw_choice_fits(auxiliary), Bool.and(ModelRoles.mrw_choice_fits(image), Bool.and(ModelRoles.mrw_choice_fits(subagent), Bool.and(ModelRoles.mrw_choice_fits(worker), Bool.and(ModelRoles.mrw_choice_fits(gateway), Bool.and(ModelRoles.mrw_choice_fits(query), Bool.and(ModelRoles.mrw_choice_fits(titles), Bool.and(ModelRoles.mrw_choice_fits(judge), Bool.and(ModelRoles.mrw_choice_fits(translate), Bool.and(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation)))))))))))), h0)) : {FMr.get_owns.chat(_) == Wr.Got{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, z} : Wr.Dec<Mr.Owns>}
      %pmr.choice(memory, FMr.put_choice(auxiliary, FMr.put_choice(image, FMr.put_choice(subagent, FMr.put_choice(worker, FMr.put_choice(gateway, FMr.put_choice(query, FMr.put_choice(titles, FMr.put_choice(judge, FMr.put_choice(translate, FMr.put_choice(speech, FMr.put_choice(dictation, z))))))))))), LLogicBool.wr_and_l(ModelRoles.mrw_choice_fits(memory), Bool.and(ModelRoles.mrw_choice_fits(auxiliary), Bool.and(ModelRoles.mrw_choice_fits(image), Bool.and(ModelRoles.mrw_choice_fits(subagent), Bool.and(ModelRoles.mrw_choice_fits(worker), Bool.and(ModelRoles.mrw_choice_fits(gateway), Bool.and(ModelRoles.mrw_choice_fits(query), Bool.and(ModelRoles.mrw_choice_fits(titles), Bool.and(ModelRoles.mrw_choice_fits(judge), Bool.and(ModelRoles.mrw_choice_fits(translate), Bool.and(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation))))))))))), h1)) : {FMr.get_owns.memory(chat, _) == Wr.Got{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, z} : Wr.Dec<Mr.Owns>}
      %pmr.choice(auxiliary, FMr.put_choice(image, FMr.put_choice(subagent, FMr.put_choice(worker, FMr.put_choice(gateway, FMr.put_choice(query, FMr.put_choice(titles, FMr.put_choice(judge, FMr.put_choice(translate, FMr.put_choice(speech, FMr.put_choice(dictation, z)))))))))), LLogicBool.wr_and_l(ModelRoles.mrw_choice_fits(auxiliary), Bool.and(ModelRoles.mrw_choice_fits(image), Bool.and(ModelRoles.mrw_choice_fits(subagent), Bool.and(ModelRoles.mrw_choice_fits(worker), Bool.and(ModelRoles.mrw_choice_fits(gateway), Bool.and(ModelRoles.mrw_choice_fits(query), Bool.and(ModelRoles.mrw_choice_fits(titles), Bool.and(ModelRoles.mrw_choice_fits(judge), Bool.and(ModelRoles.mrw_choice_fits(translate), Bool.and(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation)))))))))), h2)) : {FMr.get_owns.auxiliary(chat, memory, _) == Wr.Got{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, z} : Wr.Dec<Mr.Owns>}
      %pmr.choice(image, FMr.put_choice(subagent, FMr.put_choice(worker, FMr.put_choice(gateway, FMr.put_choice(query, FMr.put_choice(titles, FMr.put_choice(judge, FMr.put_choice(translate, FMr.put_choice(speech, FMr.put_choice(dictation, z))))))))), LLogicBool.wr_and_l(ModelRoles.mrw_choice_fits(image), Bool.and(ModelRoles.mrw_choice_fits(subagent), Bool.and(ModelRoles.mrw_choice_fits(worker), Bool.and(ModelRoles.mrw_choice_fits(gateway), Bool.and(ModelRoles.mrw_choice_fits(query), Bool.and(ModelRoles.mrw_choice_fits(titles), Bool.and(ModelRoles.mrw_choice_fits(judge), Bool.and(ModelRoles.mrw_choice_fits(translate), Bool.and(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation))))))))), h3)) : {FMr.get_owns.image(chat, memory, auxiliary, _) == Wr.Got{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, z} : Wr.Dec<Mr.Owns>}
      %pmr.choice(subagent, FMr.put_choice(worker, FMr.put_choice(gateway, FMr.put_choice(query, FMr.put_choice(titles, FMr.put_choice(judge, FMr.put_choice(translate, FMr.put_choice(speech, FMr.put_choice(dictation, z)))))))), LLogicBool.wr_and_l(ModelRoles.mrw_choice_fits(subagent), Bool.and(ModelRoles.mrw_choice_fits(worker), Bool.and(ModelRoles.mrw_choice_fits(gateway), Bool.and(ModelRoles.mrw_choice_fits(query), Bool.and(ModelRoles.mrw_choice_fits(titles), Bool.and(ModelRoles.mrw_choice_fits(judge), Bool.and(ModelRoles.mrw_choice_fits(translate), Bool.and(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation)))))))), h4)) : {FMr.get_owns.subagent(chat, memory, auxiliary, image, _) == Wr.Got{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, z} : Wr.Dec<Mr.Owns>}
      %pmr.choice(worker, FMr.put_choice(gateway, FMr.put_choice(query, FMr.put_choice(titles, FMr.put_choice(judge, FMr.put_choice(translate, FMr.put_choice(speech, FMr.put_choice(dictation, z))))))), LLogicBool.wr_and_l(ModelRoles.mrw_choice_fits(worker), Bool.and(ModelRoles.mrw_choice_fits(gateway), Bool.and(ModelRoles.mrw_choice_fits(query), Bool.and(ModelRoles.mrw_choice_fits(titles), Bool.and(ModelRoles.mrw_choice_fits(judge), Bool.and(ModelRoles.mrw_choice_fits(translate), Bool.and(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation))))))), h5)) : {FMr.get_owns.worker(chat, memory, auxiliary, image, subagent, _) == Wr.Got{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, z} : Wr.Dec<Mr.Owns>}
      %pmr.choice(gateway, FMr.put_choice(query, FMr.put_choice(titles, FMr.put_choice(judge, FMr.put_choice(translate, FMr.put_choice(speech, FMr.put_choice(dictation, z)))))), LLogicBool.wr_and_l(ModelRoles.mrw_choice_fits(gateway), Bool.and(ModelRoles.mrw_choice_fits(query), Bool.and(ModelRoles.mrw_choice_fits(titles), Bool.and(ModelRoles.mrw_choice_fits(judge), Bool.and(ModelRoles.mrw_choice_fits(translate), Bool.and(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation)))))), h6)) : {FMr.get_owns.gateway(chat, memory, auxiliary, image, subagent, worker, _) == Wr.Got{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, z} : Wr.Dec<Mr.Owns>}
      %pmr.choice(query, FMr.put_choice(titles, FMr.put_choice(judge, FMr.put_choice(translate, FMr.put_choice(speech, FMr.put_choice(dictation, z))))), LLogicBool.wr_and_l(ModelRoles.mrw_choice_fits(query), Bool.and(ModelRoles.mrw_choice_fits(titles), Bool.and(ModelRoles.mrw_choice_fits(judge), Bool.and(ModelRoles.mrw_choice_fits(translate), Bool.and(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation))))), h7)) : {FMr.get_owns.query(chat, memory, auxiliary, image, subagent, worker, gateway, _) == Wr.Got{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, z} : Wr.Dec<Mr.Owns>}
      %pmr.choice(titles, FMr.put_choice(judge, FMr.put_choice(translate, FMr.put_choice(speech, FMr.put_choice(dictation, z)))), LLogicBool.wr_and_l(ModelRoles.mrw_choice_fits(titles), Bool.and(ModelRoles.mrw_choice_fits(judge), Bool.and(ModelRoles.mrw_choice_fits(translate), Bool.and(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation)))), h8)) : {FMr.get_owns.titles(chat, memory, auxiliary, image, subagent, worker, gateway, query, _) == Wr.Got{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, z} : Wr.Dec<Mr.Owns>}
      %pmr.choice(judge, FMr.put_choice(translate, FMr.put_choice(speech, FMr.put_choice(dictation, z))), LLogicBool.wr_and_l(ModelRoles.mrw_choice_fits(judge), Bool.and(ModelRoles.mrw_choice_fits(translate), Bool.and(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation))), h9)) : {FMr.get_owns.judge(chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, _) == Wr.Got{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, z} : Wr.Dec<Mr.Owns>}
      %pmr.choice(translate, FMr.put_choice(speech, FMr.put_choice(dictation, z)), LLogicBool.wr_and_l(ModelRoles.mrw_choice_fits(translate), Bool.and(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation)), h10)) : {FMr.get_owns.translate(chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, _) == Wr.Got{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, z} : Wr.Dec<Mr.Owns>}
      %pmr.choice(speech, FMr.put_choice(dictation, z), LLogicBool.wr_and_l(ModelRoles.mrw_choice_fits(speech), ModelRoles.mrw_choice_fits(dictation), h11)) : {FMr.get_owns.speech(chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, _) == Wr.Got{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, z} : Wr.Dec<Mr.Owns>}
      %pmr.choice(dictation, z, h12) : {FMr.get_owns.dictation(chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, _) == Wr.Got{Mr.Owns{chat, memory, auxiliary, image, subagent, worker, gateway, query, titles, judge, translate, speech, dictation}, z} : Wr.Dec<Mr.Owns>}
      {==}

# the own settings read back (turned around for rewriting)
def pmr.owns(+o: Mr.Owns, +rest: String, h: {ModelRoles.mrw_owns_fits(o) == True{} : Bool}) -> {Wr.Got{o, rest} == FMr.get_owns(FMr.put_owns(o, rest)) : Wr.Dec<Mr.Owns>}:
  Equal.sym(Wr.Dec<Mr.Owns>, FMr.get_owns(FMr.put_owns(o, rest)), Wr.Got{o, rest}, ModelRoles.mrw_owns_round_trip(o, rest, h))

def ModelRoles.mrw_in_round_trip(x, rest, h):
  match x:
    case Mr.In{+owns, +all}:
      +z = rest
      +hh = h
      %pmr.owns(owns, FMr.put_choice(all, z), LLogicBool.wr_and_l(ModelRoles.mrw_owns_fits(owns), ModelRoles.mrw_choice_fits(all), hh)) : {FMr.get_in.go(_) == Wr.Got{Mr.In{owns, all}, z} : Wr.Dec<Mr.In>}
      %pmr.choice(all, z, LLogicBool.wr_and_r(ModelRoles.mrw_owns_fits(owns), ModelRoles.mrw_choice_fits(all), hh)) : {FMr.get_in.all(owns, _) == Wr.Got{Mr.In{owns, all}, z} : Wr.Dec<Mr.In>}
      {==}

# a request reads back (turned around for rewriting)
def pmr.in(+x: Mr.In, +rest: String, h: {ModelRoles.mrw_in_fits(x) == True{} : Bool}) -> {Wr.Got{x, rest} == FMr.get_in(FMr.put_in(x, rest)) : Wr.Dec<Mr.In>}:
  Equal.sym(Wr.Dec<Mr.In>, FMr.get_in(FMr.put_in(x, rest)), Wr.Got{x, rest}, ModelRoles.mrw_in_round_trip(x, rest, h))

# ---- model_roles ----

# the row of role r in the table is the role's source
def pmr.at(-o: Mr.Owns, -all: Mr.Choice, r: Mr.Role) -> {ModelRoles.mr_at(Mr.resolve(Mr.In{o, all}), r) == Some{Mr.source(r, Mr.own(o, r), all)} : Maybe<&2, Mr.Src>}:
  match r:
    case Mr.Chat{}:
      {==}
    case Mr.Memory{}:
      {==}
    case Mr.Auxiliary{}:
      {==}
    case Mr.Image{}:
      {==}
    case Mr.Subagent{}:
      {==}
    case Mr.Worker{}:
      {==}
    case Mr.Gateway{}:
      {==}
    case Mr.Query{}:
      {==}
    case Mr.Titles{}:
      {==}
    case Mr.Judge{}:
      {==}
    case Mr.Translate{}:
      {==}
    case Mr.Speech{}:
      {==}
    case Mr.Dictation{}:
      {==}

# the row of role r in the table, turned around for rewriting
def pmr.at_sym(-o: Mr.Owns, -all: Mr.Choice, r: Mr.Role) -> {Some{Mr.source(r, Mr.own(o, r), all)} == ModelRoles.mr_at(Mr.resolve(Mr.In{o, all}), r) : Maybe<&2, Mr.Src>}:
  Equal.sym(Maybe<&2, Mr.Src>, ModelRoles.mr_at(Mr.resolve(Mr.In{o, all}), r), Some{Mr.source(r, Mr.own(o, r), all)}, pmr.at(o, all, r))
