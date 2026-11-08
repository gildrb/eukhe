# eukhe: the proof of LAW privacy_entry_step_spec
#
# PROOF: the entry decodes the tag, the codes, then the texts or indexes
# with the same wire decoders the laws' reader uses; its classes and its
# zips are the laws' (pst.class_of, pst.vals, pst.refs); a whole event is
# applied as the laws apply it (pen.reply, pen.found) and anything else
# keeps the map with the malformed form (pst.of).

import Base
import ../../bend/privacy/token.bend as Tk
import ../../bend/ffi_privacy.bend as FP
import ../../bend/wire.bend as Wr
import ./base/entry.bend as LPE
import ../../laws/privacy/entry.bend as PrivacyEntry

# Classes and zips
# ----------------

def pst.class_of(n: Nat) -> {Tk.Class.of(n) == PrivacyEntry.read_class(n) : Maybe<&2, Tk.Class>}:
  match n:
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
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n+u:
      {==}

def pst.vals_cons(k: Maybe<&2, Tk.Class>, v: String, m: Maybe<&2, List<&2, Tk.Val>>) -> {FP.zip_vals.cons(k, v, m) == PrivacyEntry.read_vals.cons(k, v, m) : Maybe<&2, List<&2, Tk.Val>>}:
  match k:
    case None{}:
      {==}
    case Some{c}:
      match m:
        case None{}:
          {==}
        case Some{vs}:
          {==}

def pst.vals(cs: List<&2, Nat>, xs: List<&2, String>) -> {FP.zip_vals(cs, xs) == PrivacyEntry.read_vals(cs, xs) : Maybe<&2, List<&2, Tk.Val>>}:
  match cs:
    case Nil{}:
      match xs:
        case Nil{}:
          {==}
        case x <> xt:
          {==}
    case +c <> +ct:
      match xs:
        case Nil{}:
          {==}
        case +x <> +xt:
          %Equal.sym(Maybe<&2, Tk.Class>, Tk.Class.of(c), PrivacyEntry.read_class(c), pst.class_of(c)) : {FP.zip_vals.cons(_, x, FP.zip_vals(ct, xt)) == PrivacyEntry.read_vals.cons(PrivacyEntry.read_class(c), x, PrivacyEntry.read_vals(ct, xt)) : Maybe<&2, List<&2, Tk.Val>>}
          %Equal.sym(Maybe<&2, List<&2, Tk.Val>>, FP.zip_vals(ct, xt), PrivacyEntry.read_vals(ct, xt), pst.vals(ct, xt)) : {FP.zip_vals.cons(PrivacyEntry.read_class(c), x, _) == PrivacyEntry.read_vals.cons(PrivacyEntry.read_class(c), x, PrivacyEntry.read_vals(ct, xt)) : Maybe<&2, List<&2, Tk.Val>>}
          pst.vals_cons(PrivacyEntry.read_class(c), x, PrivacyEntry.read_vals(ct, xt))

def pst.refs_cons(k: Maybe<&2, Tk.Class>, i: Nat, m: Maybe<&2, List<&2, Tk.Ref>>) -> {FP.zip_refs.cons(k, i, m) == PrivacyEntry.read_refs.cons(k, i, m) : Maybe<&2, List<&2, Tk.Ref>>}:
  match k:
    case None{}:
      {==}
    case Some{c}:
      match m:
        case None{}:
          {==}
        case Some{rs}:
          {==}

def pst.refs(cs: List<&2, Nat>, ns: List<&2, Nat>) -> {FP.zip_refs(cs, ns) == PrivacyEntry.read_refs(cs, ns) : Maybe<&2, List<&2, Tk.Ref>>}:
  match cs:
    case Nil{}:
      match ns:
        case Nil{}:
          {==}
        case i <> it:
          {==}
    case +c <> +ct:
      match ns:
        case Nil{}:
          {==}
        case +i <> +it:
          %Equal.sym(Maybe<&2, Tk.Class>, Tk.Class.of(c), PrivacyEntry.read_class(c), pst.class_of(c)) : {FP.zip_refs.cons(_, i, FP.zip_refs(ct, it)) == PrivacyEntry.read_refs.cons(PrivacyEntry.read_class(c), i, PrivacyEntry.read_refs(ct, it)) : Maybe<&2, List<&2, Tk.Ref>>}
          %Equal.sym(Maybe<&2, List<&2, Tk.Ref>>, FP.zip_refs(ct, it), PrivacyEntry.read_refs(ct, it), pst.refs(ct, it)) : {FP.zip_refs.cons(PrivacyEntry.read_class(c), i, _) == PrivacyEntry.read_refs.cons(PrivacyEntry.read_class(c), i, PrivacyEntry.read_refs(ct, it)) : Maybe<&2, List<&2, Tk.Ref>>}
          pst.refs_cons(PrivacyEntry.read_class(c), i, PrivacyEntry.read_refs(ct, it))

def pst.scrub_of(m: Maybe<&2, List<&2, Tk.Val>>) -> {FP.scrub.of(m) == PrivacyEntry.read_ev.scrub_of(m) : Maybe<&2, FP.Ev>}:
  match m:
    case Some{vs}:
      {==}
    case None{}:
      {==}

def pst.restore_of(m: Maybe<&2, List<&2, Tk.Ref>>) -> {FP.restore.of(m) == PrivacyEntry.read_ev.restore_of(m) : Maybe<&2, FP.Ev>}:
  match m:
    case Some{rs}:
      {==}
    case None{}:
      {==}

# The event applied
# -----------------

def pst.apply(+b: Tk.Book, e: FP.Ev) -> {FP.apply(b, e) == PrivacyEntry.ev_reply(b, Some{e}) : FP.St & String}:
  match e:
    case FP.Scrub{+vs}:
      LPE.pen.reply(Tk.scrub_vals(vs, b))
    case FP.Restore{+rs}:
      %Equal.sym(String, FP.put_found.items(Tk.restore_toks(rs, b), ""), PrivacyEntry.found_items(Tk.restore_toks(rs, b)), LPE.pen.found(Tk.restore_toks(rs, b))) : {(FP.Live{b}, Wr.put_nat(List.length(&2, Maybe<&2, String>, Tk.restore_toks(rs, b)), _)) == PrivacyEntry.ev_reply(b, Some{FP.Restore{rs}}) : FP.St & String}
      {==}

def pst.end(w: Bool, +b: Tk.Book, e: FP.Ev) -> {FP.step.end(w, b, e) == PrivacyEntry.ev_reply(b, PrivacyEntry.read_ev.end(w, Some{e})) : FP.St & String}:
  match w:
    case True{}:
      pst.apply(b, e)
    case False{}:
      {==}

def pst.none(w: Bool, +b: Tk.Book) -> {(FP.Live{b}, Wr.err("privacy: malformed event")) == PrivacyEntry.ev_reply(b, PrivacyEntry.read_ev.end(w, None{})) : FP.St & String}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

# an event read, then input s: answered as the laws say
def pst.of(+b: Tk.Book, m: Maybe<&2, FP.Ev>, +s: String) -> {FP.step.ev(b, FP.ev.of(m, s)) == PrivacyEntry.ev_reply(b, PrivacyEntry.read_ev.end(Wr.end(s), m)) : FP.St & String}:
  match m:
    case Some{e}:
      pst.end(Wr.end(s), b, e)
    case None{}:
      pst.none(Wr.end(s), b)

# The decoders
# ------------

def pst.texts(+b: Tk.Book, +cs: List<&2, Nat>, d: Wr.Dec<List<&2, String>>) -> {FP.step.ev(b, FP.get_scrub.vals(cs, d)) == PrivacyEntry.ev_reply(b, PrivacyEntry.read_ev.texts(cs, d)) : FP.St & String}:
  match d:
    case Wr.Got{+xs, +s}:
      %Equal.sym(Maybe<&2, List<&2, Tk.Val>>, FP.zip_vals(cs, xs), PrivacyEntry.read_vals(cs, xs), pst.vals(cs, xs)) : {FP.step.ev(b, FP.ev.of(FP.scrub.of(_), s)) == PrivacyEntry.ev_reply(b, PrivacyEntry.read_ev.end(Wr.end(s), PrivacyEntry.read_ev.scrub_of(PrivacyEntry.read_vals(cs, xs)))) : FP.St & String}
      %Equal.sym(Maybe<&2, FP.Ev>, FP.scrub.of(PrivacyEntry.read_vals(cs, xs)), PrivacyEntry.read_ev.scrub_of(PrivacyEntry.read_vals(cs, xs)), pst.scrub_of(PrivacyEntry.read_vals(cs, xs))) : {FP.step.ev(b, FP.ev.of(_, s)) == PrivacyEntry.ev_reply(b, PrivacyEntry.read_ev.end(Wr.end(s), PrivacyEntry.read_ev.scrub_of(PrivacyEntry.read_vals(cs, xs)))) : FP.St & String}
      pst.of(b, PrivacyEntry.read_ev.scrub_of(PrivacyEntry.read_vals(cs, xs)), s)
    case Wr.Bad{}:
      {==}

def pst.indexes(+b: Tk.Book, +cs: List<&2, Nat>, d: Wr.Dec<List<&2, Nat>>) -> {FP.step.ev(b, FP.get_restore.refs(cs, d)) == PrivacyEntry.ev_reply(b, PrivacyEntry.read_ev.indexes(cs, d)) : FP.St & String}:
  match d:
    case Wr.Got{+ns, +s}:
      %Equal.sym(Maybe<&2, List<&2, Tk.Ref>>, FP.zip_refs(cs, ns), PrivacyEntry.read_refs(cs, ns), pst.refs(cs, ns)) : {FP.step.ev(b, FP.ev.of(FP.restore.of(_), s)) == PrivacyEntry.ev_reply(b, PrivacyEntry.read_ev.end(Wr.end(s), PrivacyEntry.read_ev.restore_of(PrivacyEntry.read_refs(cs, ns)))) : FP.St & String}
      %Equal.sym(Maybe<&2, FP.Ev>, FP.restore.of(PrivacyEntry.read_refs(cs, ns)), PrivacyEntry.read_ev.restore_of(PrivacyEntry.read_refs(cs, ns)), pst.restore_of(PrivacyEntry.read_refs(cs, ns))) : {FP.step.ev(b, FP.ev.of(_, s)) == PrivacyEntry.ev_reply(b, PrivacyEntry.read_ev.end(Wr.end(s), PrivacyEntry.read_ev.restore_of(PrivacyEntry.read_refs(cs, ns)))) : FP.St & String}
      pst.of(b, PrivacyEntry.read_ev.restore_of(PrivacyEntry.read_refs(cs, ns)), s)
    case Wr.Bad{}:
      {==}

def pst.scrub(+b: Tk.Book, d: Wr.Dec<List<&2, Nat>>) -> {FP.step.ev(b, FP.get_scrub(d)) == PrivacyEntry.ev_reply(b, PrivacyEntry.read_ev.scrub(d)) : FP.St & String}:
  match d:
    case Wr.Got{cs, s}:
      pst.texts(b, cs, Wr.get_list(~String, ~Wr.get_str, s))
    case Wr.Bad{}:
      {==}

def pst.restore(+b: Tk.Book, d: Wr.Dec<List<&2, Nat>>) -> {FP.step.ev(b, FP.get_restore(d)) == PrivacyEntry.ev_reply(b, PrivacyEntry.read_ev.restore(d)) : FP.St & String}:
  match d:
    case Wr.Got{cs, s}:
      pst.indexes(b, cs, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      {==}

def pst.tag(+b: Tk.Book, d: Wr.Dec<Nat>) -> {FP.step.ev(b, FP.get_ev.tag(d)) == PrivacyEntry.ev_reply(b, PrivacyEntry.read_ev.tag(d)) : FP.St & String}:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          pst.scrub(b, Wr.get_list(~Nat, ~Wr.get_nat, s))
        case 1n:
          pst.restore(b, Wr.get_list(~Nat, ~Wr.get_nat, s))
        case 2n+u:
          {==}
    case Wr.Bad{}:
      {==}

def PrivacyEntry.privacy_entry_step_spec(b, s):
  pst.tag(b, Wr.get_nat(s))
