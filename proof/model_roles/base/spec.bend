# eukhe: lemmas of area model_roles: the entry's encoders spell what the
# spec spellers of laws/model_roles.bend (R8) spell, and its table is the
# spec's table

import Base
import ../../../bend/model_roles.bend as Mr
import ../../../bend/ffi_model_roles.bend as FMr
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/model_roles.bend as ModelRoles
import ../own_is_field.bend as POwnIsField
import ../../wire/wire_list_spells_items.bend as PWireListSpellsItems

# Requests
# --------

# a setting is spelled as the spec spells it
def mrb.ch(c: Mr.Choice, -rest: String) -> {FMr.put_choice(c, rest) == ModelRoles.mrs_w_choice(c, rest) : String}:
  match c:
    case Mr.Unset{}:
      {==}
    case Mr.Sel{n}:
      {==}

# a request is spelled as the spec spells it
def mrb.in(x: Mr.In, +rest: String) -> {FMr.put_in(x, rest) == ModelRoles.mrs_w_in(x, rest) : String}:
  match x:
    case Mr.In{o, +al}:
      match o:
        case Mr.Owns{+c0, +c1, +c2, +c3, +c4, +c5, +c6, +c7, +c8, +c9, +c10, +c11, +c12}:
          %mrb.ch(al, rest) : {FMr.put_in(Mr.In{Mr.Owns{c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12}, al}, rest) == ModelRoles.mrs_w_choice(c0, ModelRoles.mrs_w_choice(c1, ModelRoles.mrs_w_choice(c2, ModelRoles.mrs_w_choice(c3, ModelRoles.mrs_w_choice(c4, ModelRoles.mrs_w_choice(c5, ModelRoles.mrs_w_choice(c6, ModelRoles.mrs_w_choice(c7, ModelRoles.mrs_w_choice(c8, ModelRoles.mrs_w_choice(c9, ModelRoles.mrs_w_choice(c10, ModelRoles.mrs_w_choice(c11, ModelRoles.mrs_w_choice(c12, _))))))))))))) : String}
          %mrb.ch(c12, FMr.put_choice(al, rest)) : {FMr.put_in(Mr.In{Mr.Owns{c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12}, al}, rest) == ModelRoles.mrs_w_choice(c0, ModelRoles.mrs_w_choice(c1, ModelRoles.mrs_w_choice(c2, ModelRoles.mrs_w_choice(c3, ModelRoles.mrs_w_choice(c4, ModelRoles.mrs_w_choice(c5, ModelRoles.mrs_w_choice(c6, ModelRoles.mrs_w_choice(c7, ModelRoles.mrs_w_choice(c8, ModelRoles.mrs_w_choice(c9, ModelRoles.mrs_w_choice(c10, ModelRoles.mrs_w_choice(c11, _)))))))))))) : String}
          %mrb.ch(c11, FMr.put_choice(c12, FMr.put_choice(al, rest))) : {FMr.put_in(Mr.In{Mr.Owns{c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12}, al}, rest) == ModelRoles.mrs_w_choice(c0, ModelRoles.mrs_w_choice(c1, ModelRoles.mrs_w_choice(c2, ModelRoles.mrs_w_choice(c3, ModelRoles.mrs_w_choice(c4, ModelRoles.mrs_w_choice(c5, ModelRoles.mrs_w_choice(c6, ModelRoles.mrs_w_choice(c7, ModelRoles.mrs_w_choice(c8, ModelRoles.mrs_w_choice(c9, ModelRoles.mrs_w_choice(c10, _))))))))))) : String}
          %mrb.ch(c10, FMr.put_choice(c11, FMr.put_choice(c12, FMr.put_choice(al, rest)))) : {FMr.put_in(Mr.In{Mr.Owns{c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12}, al}, rest) == ModelRoles.mrs_w_choice(c0, ModelRoles.mrs_w_choice(c1, ModelRoles.mrs_w_choice(c2, ModelRoles.mrs_w_choice(c3, ModelRoles.mrs_w_choice(c4, ModelRoles.mrs_w_choice(c5, ModelRoles.mrs_w_choice(c6, ModelRoles.mrs_w_choice(c7, ModelRoles.mrs_w_choice(c8, ModelRoles.mrs_w_choice(c9, _)))))))))) : String}
          %mrb.ch(c9, FMr.put_choice(c10, FMr.put_choice(c11, FMr.put_choice(c12, FMr.put_choice(al, rest))))) : {FMr.put_in(Mr.In{Mr.Owns{c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12}, al}, rest) == ModelRoles.mrs_w_choice(c0, ModelRoles.mrs_w_choice(c1, ModelRoles.mrs_w_choice(c2, ModelRoles.mrs_w_choice(c3, ModelRoles.mrs_w_choice(c4, ModelRoles.mrs_w_choice(c5, ModelRoles.mrs_w_choice(c6, ModelRoles.mrs_w_choice(c7, ModelRoles.mrs_w_choice(c8, _))))))))) : String}
          %mrb.ch(c8, FMr.put_choice(c9, FMr.put_choice(c10, FMr.put_choice(c11, FMr.put_choice(c12, FMr.put_choice(al, rest)))))) : {FMr.put_in(Mr.In{Mr.Owns{c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12}, al}, rest) == ModelRoles.mrs_w_choice(c0, ModelRoles.mrs_w_choice(c1, ModelRoles.mrs_w_choice(c2, ModelRoles.mrs_w_choice(c3, ModelRoles.mrs_w_choice(c4, ModelRoles.mrs_w_choice(c5, ModelRoles.mrs_w_choice(c6, ModelRoles.mrs_w_choice(c7, _)))))))) : String}
          %mrb.ch(c7, FMr.put_choice(c8, FMr.put_choice(c9, FMr.put_choice(c10, FMr.put_choice(c11, FMr.put_choice(c12, FMr.put_choice(al, rest))))))) : {FMr.put_in(Mr.In{Mr.Owns{c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12}, al}, rest) == ModelRoles.mrs_w_choice(c0, ModelRoles.mrs_w_choice(c1, ModelRoles.mrs_w_choice(c2, ModelRoles.mrs_w_choice(c3, ModelRoles.mrs_w_choice(c4, ModelRoles.mrs_w_choice(c5, ModelRoles.mrs_w_choice(c6, _))))))) : String}
          %mrb.ch(c6, FMr.put_choice(c7, FMr.put_choice(c8, FMr.put_choice(c9, FMr.put_choice(c10, FMr.put_choice(c11, FMr.put_choice(c12, FMr.put_choice(al, rest)))))))) : {FMr.put_in(Mr.In{Mr.Owns{c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12}, al}, rest) == ModelRoles.mrs_w_choice(c0, ModelRoles.mrs_w_choice(c1, ModelRoles.mrs_w_choice(c2, ModelRoles.mrs_w_choice(c3, ModelRoles.mrs_w_choice(c4, ModelRoles.mrs_w_choice(c5, _)))))) : String}
          %mrb.ch(c5, FMr.put_choice(c6, FMr.put_choice(c7, FMr.put_choice(c8, FMr.put_choice(c9, FMr.put_choice(c10, FMr.put_choice(c11, FMr.put_choice(c12, FMr.put_choice(al, rest))))))))) : {FMr.put_in(Mr.In{Mr.Owns{c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12}, al}, rest) == ModelRoles.mrs_w_choice(c0, ModelRoles.mrs_w_choice(c1, ModelRoles.mrs_w_choice(c2, ModelRoles.mrs_w_choice(c3, ModelRoles.mrs_w_choice(c4, _))))) : String}
          %mrb.ch(c4, FMr.put_choice(c5, FMr.put_choice(c6, FMr.put_choice(c7, FMr.put_choice(c8, FMr.put_choice(c9, FMr.put_choice(c10, FMr.put_choice(c11, FMr.put_choice(c12, FMr.put_choice(al, rest)))))))))) : {FMr.put_in(Mr.In{Mr.Owns{c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12}, al}, rest) == ModelRoles.mrs_w_choice(c0, ModelRoles.mrs_w_choice(c1, ModelRoles.mrs_w_choice(c2, ModelRoles.mrs_w_choice(c3, _)))) : String}
          %mrb.ch(c3, FMr.put_choice(c4, FMr.put_choice(c5, FMr.put_choice(c6, FMr.put_choice(c7, FMr.put_choice(c8, FMr.put_choice(c9, FMr.put_choice(c10, FMr.put_choice(c11, FMr.put_choice(c12, FMr.put_choice(al, rest))))))))))) : {FMr.put_in(Mr.In{Mr.Owns{c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12}, al}, rest) == ModelRoles.mrs_w_choice(c0, ModelRoles.mrs_w_choice(c1, ModelRoles.mrs_w_choice(c2, _))) : String}
          %mrb.ch(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, FMr.put_choice(c6, FMr.put_choice(c7, FMr.put_choice(c8, FMr.put_choice(c9, FMr.put_choice(c10, FMr.put_choice(c11, FMr.put_choice(c12, FMr.put_choice(al, rest)))))))))))) : {FMr.put_in(Mr.In{Mr.Owns{c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12}, al}, rest) == ModelRoles.mrs_w_choice(c0, ModelRoles.mrs_w_choice(c1, _)) : String}
          %mrb.ch(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, FMr.put_choice(c6, FMr.put_choice(c7, FMr.put_choice(c8, FMr.put_choice(c9, FMr.put_choice(c10, FMr.put_choice(c11, FMr.put_choice(c12, FMr.put_choice(al, rest))))))))))))) : {FMr.put_in(Mr.In{Mr.Owns{c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12}, al}, rest) == ModelRoles.mrs_w_choice(c0, _) : String}
          %mrb.ch(c0, FMr.put_choice(c1, FMr.put_choice(c2, FMr.put_choice(c3, FMr.put_choice(c4, FMr.put_choice(c5, FMr.put_choice(c6, FMr.put_choice(c7, FMr.put_choice(c8, FMr.put_choice(c9, FMr.put_choice(c10, FMr.put_choice(c11, FMr.put_choice(c12, FMr.put_choice(al, rest)))))))))))))) : {FMr.put_in(Mr.In{Mr.Owns{c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12}, al}, rest) == _ : String}
          {==}

# the same, turned around for rewriting
def mrb.in_sym(+x: Mr.In, +rest: String) -> {ModelRoles.mrs_w_in(x, rest) == FMr.put_in(x, rest) : String}:
  Equal.sym(String, FMr.put_in(x, rest), ModelRoles.mrs_w_in(x, rest), mrb.in(x, rest))

# Replies
# -------

# a role's tag is the spec's
def mrb.tag(r: Mr.Role) -> {FMr.role_tag(r) == ModelRoles.mrs_tag(r) : Nat}:
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

# the code's source of a role, spelled, is the spec's source, spelled
def mrb.src(c: Mr.Choice, r: Mr.Role, all: Mr.Choice, -rest: String) -> {FMr.put_src(Mr.source(r, c, all), rest) == ModelRoles.mrs_w_src(ModelRoles.mrs_src(r, c, all), rest) : String}:
  match c:
    case Mr.Sel{n}:
      {==}
    case Mr.Unset{}:
      match r:
        case Mr.Chat{}:
          match all:
            case Mr.Unset{}:
              {==}
            case Mr.Sel{n}:
              {==}
        case Mr.Memory{}:
          match all:
            case Mr.Unset{}:
              {==}
            case Mr.Sel{n}:
              {==}
        case Mr.Auxiliary{}:
          match all:
            case Mr.Unset{}:
              {==}
            case Mr.Sel{n}:
              {==}
        case Mr.Image{}:
          match all:
            case Mr.Unset{}:
              {==}
            case Mr.Sel{n}:
              {==}
        case Mr.Subagent{}:
          match all:
            case Mr.Unset{}:
              {==}
            case Mr.Sel{n}:
              {==}
        case Mr.Worker{}:
          match all:
            case Mr.Unset{}:
              {==}
            case Mr.Sel{n}:
              {==}
        case Mr.Gateway{}:
          match all:
            case Mr.Unset{}:
              {==}
            case Mr.Sel{n}:
              {==}
        case Mr.Query{}:
          match all:
            case Mr.Unset{}:
              {==}
            case Mr.Sel{n}:
              {==}
        case Mr.Titles{}:
          match all:
            case Mr.Unset{}:
              {==}
            case Mr.Sel{n}:
              {==}
        case Mr.Judge{}:
          match all:
            case Mr.Unset{}:
              {==}
            case Mr.Sel{n}:
              {==}
        case Mr.Translate{}:
          match all:
            case Mr.Unset{}:
              {==}
            case Mr.Sel{n}:
              {==}
        case Mr.Speech{}:
          {==}
        case Mr.Dictation{}:
          {==}

# the rows of the roles rs, spelled by the item writer, are the spec's rows
def mrb.rows(rs: List<&2, Mr.Role>, +o: Mr.Owns, +all: Mr.Choice, +rest: String) -> {LawsBase.wire_put_items(~Mr.Row, ~FMr.put_row, Mr.rows(rs, o, all), rest) == ModelRoles.mrs_w_rows(rs, o, all, rest) : String}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +t:
      %mrb.rows(t, o, all, rest) : {Wr.put_nat(FMr.role_tag(r), FMr.put_src(Mr.source(r, Mr.own(o, r), all), LawsBase.wire_put_items(~Mr.Row, ~FMr.put_row, Mr.rows(t, o, all), rest))) == Wr.put_nat(ModelRoles.mrs_tag(r), ModelRoles.mrs_w_src(ModelRoles.mrs_src(r, ModelRoles.mr_own(o, r), all), _)) : String}
      %ModelRoles.own_is_field(o, r) : {Wr.put_nat(FMr.role_tag(r), FMr.put_src(Mr.source(r, Mr.own(o, r), all), LawsBase.wire_put_items(~Mr.Row, ~FMr.put_row, Mr.rows(t, o, all), rest))) == Wr.put_nat(ModelRoles.mrs_tag(r), ModelRoles.mrs_w_src(ModelRoles.mrs_src(r, _, all), LawsBase.wire_put_items(~Mr.Row, ~FMr.put_row, Mr.rows(t, o, all), rest))) : String}
      %mrb.src(Mr.own(o, r), r, all, LawsBase.wire_put_items(~Mr.Row, ~FMr.put_row, Mr.rows(t, o, all), rest)) : {Wr.put_nat(FMr.role_tag(r), FMr.put_src(Mr.source(r, Mr.own(o, r), all), LawsBase.wire_put_items(~Mr.Row, ~FMr.put_row, Mr.rows(t, o, all), rest))) == Wr.put_nat(ModelRoles.mrs_tag(r), _) : String}
      %mrb.tag(r) : {Wr.put_nat(FMr.role_tag(r), FMr.put_src(Mr.source(r, Mr.own(o, r), all), LawsBase.wire_put_items(~Mr.Row, ~FMr.put_row, Mr.rows(t, o, all), rest))) == Wr.put_nat(_, FMr.put_src(Mr.source(r, Mr.own(o, r), all), LawsBase.wire_put_items(~Mr.Row, ~FMr.put_row, Mr.rows(t, o, all), rest))) : String}
      {==}

# the code's table, spelled, is the spec's reply
def mrb.reply(x: Mr.In) -> {FMr.put_res(Mr.resolve(x), "") == ModelRoles.mrs_w_reply(x) : String}:
  match x:
    case Mr.In{+o, +all}:
      %Equal.sym(String, Wr.put_list(~Mr.Row, ~FMr.put_row, Mr.rows(Mr.roles(), o, all), ""), LawsBase.wire_dec(List.length(&2, Mr.Row, Mr.rows(Mr.roles(), o, all)), LawsBase.wire_put_items(~Mr.Row, ~FMr.put_row, Mr.rows(Mr.roles(), o, all), "")), Wire.wire_list_spells_items(~Mr.Row, ~FMr.put_row, Mr.rows(Mr.roles(), o, all), "")) : {_ == ModelRoles.mrs_w_reply(Mr.In{o, all}) : String}
      %Equal.sym(String, LawsBase.wire_put_items(~Mr.Row, ~FMr.put_row, Mr.rows(Mr.roles(), o, all), ""), ModelRoles.mrs_w_rows(Mr.roles(), o, all, ""), mrb.rows(Mr.roles(), o, all, "")) : {LawsBase.wire_dec(List.length(&2, Mr.Row, Mr.rows(Mr.roles(), o, all)), _) == ModelRoles.mrs_w_reply(Mr.In{o, all}) : String}
      {==}
