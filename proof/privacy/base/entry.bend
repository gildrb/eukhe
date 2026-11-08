# eukhe: lemmas shared by the proofs of area privacy, section entry: the
# entry's decoders read back what the laws spell, and its replies are the
# laws' spellings

import Base
import ../../../bend/privacy/ip.bend as Ip
import ../../../bend/privacy/token.bend as Tk
import ../../../bend/ffi_privacy.bend as FP
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/privacy/entry.bend as PE

def pen.and_i(a: Bool, -b: Bool, +ea: {a == True{} : Bool}, +eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      ea
# The call
# --------

def pen.code(m: Maybe<&2, Nat>) -> {FP.code(m) == PE.answer(m) : Nat}:
  match m:
    case None{}:
      {==}
    case Some{n}:
      {==}

# the entry's answers are the laws' answers
def pen.answers(cs: List<&2, FP.Cand>) -> {FP.answers(cs) == PE.answers(cs) : List<&2, Nat>}:
  match cs:
    case Nil{}:
      {==}
    case c <> rest:
      match c:
        case FP.Cand{+b, +r}:
          %Equal.sym(Nat, FP.code(Ip.ip(b, r)), PE.answer(Ip.ip(b, r)), pen.code(Ip.ip(b, r))) : {_ <> FP.answers(rest) == PE.answer(Ip.ip(b, r)) <> PE.answers(rest) : List<&2, Nat>}
          %Equal.sym(List<&2, Nat>, FP.answers(rest), PE.answers(rest), pen.answers(rest)) : {PE.answer(Ip.ip(b, r)) <> _ == PE.answer(Ip.ip(b, r)) <> PE.answers(rest) : List<&2, Nat>}
          {==}

# the strings of the candidates pair back into them
def pen.pairs(cs: List<&2, FP.Cand>) -> {FP.pairs(PE.cand_strs(cs)) == Some{cs} : Maybe<&2, List<&2, FP.Cand>>}:
  match cs:
    case Nil{}:
      {==}
    case c <> rest:
      match c:
        case FP.Cand{+b, +r}:
          %Equal.sym(Maybe<&2, List<&2, FP.Cand>>, FP.pairs(PE.cand_strs(rest)), Some{rest}, pen.pairs(rest)) : {FP.pairs.cons(FP.Cand{b, r}, _) == Some{FP.Cand{b, r} <> rest} : Maybe<&2, List<&2, FP.Cand>>}
          {==}

# an odd count of strings pairs into nothing
def pen.pairs_odd(cs: List<&2, FP.Cand>, -x: String) -> {FP.pairs(List.append(&2, String, PE.cand_strs(cs), [x])) == None{} : Maybe<&2, List<&2, FP.Cand>>}:
  match cs:
    case Nil{}:
      {==}
    case c <> rest:
      match c:
        case FP.Cand{+b, +r}:
          %Equal.sym(Maybe<&2, List<&2, FP.Cand>>, FP.pairs(List.append(&2, String, PE.cand_strs(rest), [x])), None{}, pen.pairs_odd(rest, x)) : {FP.pairs.cons(FP.Cand{b, r}, _) == None{} : Maybe<&2, List<&2, FP.Cand>>}
          {==}

# Classes
# -------

def pen.tag_fit(c: Tk.Class) -> {LawsBase.wire_fits(Tk.Class.tag(c)) == True{} : Bool}:
  match c:
    case Tk.Person{}:
      {==}
    case Tk.Email{}:
      {==}
    case Tk.Phone{}:
      {==}
    case Tk.Ip{}:
      {==}
    case Tk.Id{}:
      {==}
    case Tk.ApiKey{}:
      {==}
    case Tk.Card{}:
      {==}
    case Tk.Iban{}:
      {==}

def pen.of_tag(c: Tk.Class) -> {Tk.Class.of(Tk.Class.tag(c)) == Some{c} : Maybe<&2, Tk.Class>}:
  match c:
    case Tk.Person{}:
      {==}
    case Tk.Email{}:
      {==}
    case Tk.Phone{}:
      {==}
    case Tk.Ip{}:
      {==}
    case Tk.Id{}:
      {==}
    case Tk.ApiKey{}:
      {==}
    case Tk.Card{}:
      {==}
    case Tk.Iban{}:
      {==}

# Scrub
# -----

def pen.len_tags(vs: List<&2, Tk.Val>) -> {List.length(&2, Nat, PE.val_tags(vs)) == List.length(&2, Tk.Val, vs) : Nat}:
  match vs:
    case Nil{}:
      {==}
    case v <> rest:
      match v:
        case Tk.Val{c, x}:
          %pen.len_tags(rest) : {1n+List.length(&2, Nat, PE.val_tags(rest)) == 1n+_ : Nat}
          {==}

def pen.tags_fit(vs: List<&2, Tk.Val>) -> {LawsBase.wire_nats_fit(PE.val_tags(vs)) == True{} : Bool}:
  match vs:
    case Nil{}:
      {==}
    case v <> rest:
      match v:
        case Tk.Val{+c, x}:
          pen.and_i(LawsBase.wire_fits(Tk.Class.tag(c)), LawsBase.wire_nats_fit(PE.val_tags(rest)), pen.tag_fit(c), pen.tags_fit(rest))

def pen.vals_tags_fit(+vs: List<&2, Tk.Val>, +h: {LawsBase.wire_fits(List.length(&2, Tk.Val, vs)) == True{} : Bool}) -> {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, PE.val_tags(vs))), LawsBase.wire_nats_fit(PE.val_tags(vs))) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Nat, PE.val_tags(vs)), List.length(&2, Tk.Val, vs), pen.len_tags(vs)) : {Bool.and(LawsBase.wire_fits(_), LawsBase.wire_nats_fit(PE.val_tags(vs))) == True{} : Bool}
  pen.and_i(LawsBase.wire_fits(List.length(&2, Tk.Val, vs)), LawsBase.wire_nats_fit(PE.val_tags(vs)), h, pen.tags_fit(vs))

def pen.zip_vals(vs: List<&2, Tk.Val>) -> {FP.zip_vals(PE.val_tags(vs), PE.val_texts(vs)) == Some{vs} : Maybe<&2, List<&2, Tk.Val>>}:
  match vs:
    case Nil{}:
      {==}
    case v <> rest:
      match v:
        case Tk.Val{+c, +x}:
          %Equal.sym(Maybe<&2, Tk.Class>, Tk.Class.of(Tk.Class.tag(c)), Some{c}, pen.of_tag(c)) : {FP.zip_vals.cons(_, x, FP.zip_vals(PE.val_tags(rest), PE.val_texts(rest))) == Some{Tk.Val{c, x} <> rest} : Maybe<&2, List<&2, Tk.Val>>}
          %Equal.sym(Maybe<&2, List<&2, Tk.Val>>, FP.zip_vals(PE.val_tags(rest), PE.val_texts(rest)), Some{rest}, pen.zip_vals(rest)) : {FP.zip_vals.cons(Some{c}, x, _) == Some{Tk.Val{c, x} <> rest} : Maybe<&2, List<&2, Tk.Val>>}
          {==}

def pen.tok_code(t: Tk.Tok) -> {FP.tok_code(t) == PE.tok_code(t) : Nat}:
  match t:
    case Tk.Mapped{i}:
      {==}
    case Tk.OneWay{}:
      {==}

def pen.tok_codes(ts: List<&2, Tk.Tok>) -> {FP.tok_codes(ts) == PE.tok_codes(ts) : List<&2, Nat>}:
  match ts:
    case Nil{}:
      {==}
    case +t <> rest:
      %Equal.sym(Nat, FP.tok_code(t), PE.tok_code(t), pen.tok_code(t)) : {_ <> FP.tok_codes(rest) == PE.tok_code(t) <> PE.tok_codes(rest) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, FP.tok_codes(rest), PE.tok_codes(rest), pen.tok_codes(rest)) : {PE.tok_code(t) <> _ == PE.tok_code(t) <> PE.tok_codes(rest) : List<&2, Nat>}
      {==}

# the entry's reply to a Scrub is the laws'
def pen.reply(r: Tk.Toks) -> {FP.step.scrub(r) == PE.scrub_reply(r) : FP.St & String}:
  match r:
    case Tk.Toks{b, +ts}:
      %Equal.sym(List<&2, Nat>, FP.tok_codes(ts), PE.tok_codes(ts), pen.tok_codes(ts)) : {(FP.Live{b}, Wr.put_list(~Nat, ~Wr.put_nat, _, "")) == PE.scrub_reply(Tk.Toks{b, ts}) : FP.St & String}
      {==}

# Restore
# -------

def pen.len_rtags(rs: List<&2, Tk.Ref>) -> {List.length(&2, Nat, PE.ref_tags(rs)) == List.length(&2, Tk.Ref, rs) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case r <> rest:
      match r:
        case Tk.Ref{c, i}:
          %pen.len_rtags(rest) : {1n+List.length(&2, Nat, PE.ref_tags(rest)) == 1n+_ : Nat}
          {==}

def pen.len_idx(rs: List<&2, Tk.Ref>) -> {List.length(&2, Nat, PE.ref_indexes(rs)) == List.length(&2, Tk.Ref, rs) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case r <> rest:
      match r:
        case Tk.Ref{c, i}:
          %pen.len_idx(rest) : {1n+List.length(&2, Nat, PE.ref_indexes(rest)) == 1n+_ : Nat}
          {==}

def pen.rtags_fit(rs: List<&2, Tk.Ref>) -> {LawsBase.wire_nats_fit(PE.ref_tags(rs)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case r <> rest:
      match r:
        case Tk.Ref{+c, i}:
          pen.and_i(LawsBase.wire_fits(Tk.Class.tag(c)), LawsBase.wire_nats_fit(PE.ref_tags(rest)), pen.tag_fit(c), pen.rtags_fit(rest))

def pen.refs_tags_fit(+rs: List<&2, Tk.Ref>, +h: {LawsBase.wire_fits(List.length(&2, Tk.Ref, rs)) == True{} : Bool}) -> {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, PE.ref_tags(rs))), LawsBase.wire_nats_fit(PE.ref_tags(rs))) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Nat, PE.ref_tags(rs)), List.length(&2, Tk.Ref, rs), pen.len_rtags(rs)) : {Bool.and(LawsBase.wire_fits(_), LawsBase.wire_nats_fit(PE.ref_tags(rs))) == True{} : Bool}
  pen.and_i(LawsBase.wire_fits(List.length(&2, Tk.Ref, rs)), LawsBase.wire_nats_fit(PE.ref_tags(rs)), h, pen.rtags_fit(rs))

def pen.refs_idx_fit(+rs: List<&2, Tk.Ref>, +h: {LawsBase.wire_fits(List.length(&2, Tk.Ref, rs)) == True{} : Bool}, +hi: {LawsBase.wire_nats_fit(PE.ref_indexes(rs)) == True{} : Bool}) -> {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, PE.ref_indexes(rs))), LawsBase.wire_nats_fit(PE.ref_indexes(rs))) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Nat, PE.ref_indexes(rs)), List.length(&2, Tk.Ref, rs), pen.len_idx(rs)) : {Bool.and(LawsBase.wire_fits(_), LawsBase.wire_nats_fit(PE.ref_indexes(rs))) == True{} : Bool}
  pen.and_i(LawsBase.wire_fits(List.length(&2, Tk.Ref, rs)), LawsBase.wire_nats_fit(PE.ref_indexes(rs)), h, hi)

def pen.zip_refs(rs: List<&2, Tk.Ref>) -> {FP.zip_refs(PE.ref_tags(rs), PE.ref_indexes(rs)) == Some{rs} : Maybe<&2, List<&2, Tk.Ref>>}:
  match rs:
    case Nil{}:
      {==}
    case r <> rest:
      match r:
        case Tk.Ref{+c, +i}:
          %Equal.sym(Maybe<&2, Tk.Class>, Tk.Class.of(Tk.Class.tag(c)), Some{c}, pen.of_tag(c)) : {FP.zip_refs.cons(_, i, FP.zip_refs(PE.ref_tags(rest), PE.ref_indexes(rest))) == Some{Tk.Ref{c, i} <> rest} : Maybe<&2, List<&2, Tk.Ref>>}
          %Equal.sym(Maybe<&2, List<&2, Tk.Ref>>, FP.zip_refs(PE.ref_tags(rest), PE.ref_indexes(rest)), Some{rest}, pen.zip_refs(rest)) : {FP.zip_refs.cons(Some{c}, i, _) == Some{Tk.Ref{c, i} <> rest} : Maybe<&2, List<&2, Tk.Ref>>}
          {==}

# the values found, as the entry spells them and as the laws do
def pen.found(fs: List<&2, Maybe<&2, String>>) -> {FP.put_found.items(fs, "") == PE.found_items(fs) : String}:
  match fs:
    case Nil{}:
      {==}
    case f <> more:
      match f:
        case None{}:
          %Equal.sym(String, FP.put_found.items(more, ""), PE.found_items(more), pen.found(more)) : {Wr.put_nat(0n, _) == Wr.put_nat(0n, PE.found_items(more)) : String}
          {==}
        case Some{+v}:
          %Equal.sym(String, FP.put_found.items(more, ""), PE.found_items(more), pen.found(more)) : {Wr.put_nat(1n, Wr.put_str(v, _)) == Wr.put_nat(1n, Wr.put_str(v, PE.found_items(more))) : String}
          {==}
