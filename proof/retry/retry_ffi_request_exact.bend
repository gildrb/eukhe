# eukhe: the proof of LAW retry_ffi_request_exact

import Base
import ../../bend/ffi_retry.bend as Fr
import ../../bend/retry.bend as R
import ../../bend/wire.bend as Wr
import ../../laws/retry.bend as Retry
import ../../laws/wire.bend as Wire
import ./base.bend as LA
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_bool_exact.bend as PWireBoolExact

# ---- retry_ffi ----

# proof_retry_ffi: the laws of LAWS.bend section retry, R7 (the entry of
# bend/ffi_retry.bend). Round trip: each field reads back by the wire laws
# (wire_nat_round_trip, wire_bool_round_trip), a Maybe and a Cause by their
# tag, a list of attempts item by item (rw.list_rt). Exactness: each
# decoder layer that answers Got gives the prefix of the encoding
# (wire_nat_exact, wire_bool_exact), down to the request. The entry laws
# rewrite the decoded request into the entry. The list lemmas follow the
# failover pilot of the infrastructure slice (ff_list_rt, ff_list_ex).

# Decoder answers
# ---------------

def rw.DG(-A: Data, d: Wr.Dec<A>, G: Type) -> Type:
  match d:
    case Wr.Got{v, r}:
      G
    case Wr.Bad{}:
      Unit

def rw.val(-A: Data, d: Wr.Dec<A>, x: A) -> A:
  match d:
    case Wr.Got{v, r}:
      v
    case Wr.Bad{}:
      x

def rw.rst(-A: Data, d: Wr.Dec<A>) -> String:
  match d:
    case Wr.Got{v, r}:
      r
    case Wr.Bad{}:
      ""

def rw.bad_got(-A: Data, -G: Type, -x: A, -s: String, e: {Wr.Bad{} == Wr.Got{x, s} : Wr.Dec<A>}) -> G:
  %e : rw.DG(A, _, G)
  Unit{}

def rw.got_v(-A: Data, +a: A, -b: A, -s: String, -r: String, e: {Wr.Got{a, s} == Wr.Got{b, r} : Wr.Dec<A>}) -> {a == b : A}:
  Equal.cong(Wr.Dec<A>, A, d => rw.val(A, d, a), Wr.Got{a, s}, Wr.Got{b, r}, e)

def rw.got_r(-A: Data, -a: A, -b: A, -s: String, -r: String, e: {Wr.Got{a, s} == Wr.Got{b, r} : Wr.Dec<A>}) -> {s == r : String}:
  Equal.cong(Wr.Dec<A>, String, d => rw.rst(A, d), Wr.Got{a, s}, Wr.Got{b, r}, e)

# Exactness
# ---------

def rw.nex(+s: String, +n: Nat, +rest: String, h: {Wr.get_nat(s) == Wr.Got{n, rest} : Wr.Dec<Nat>}) -> {Wr.put_nat(n, rest) == s : String}:
  Equal.sym(String, s, Wr.put_nat(n, rest), Wire.wire_nat_exact(s, n, rest, h))

def rw.bex(+s: String, +b: Bool, +rest: String, h: {Wr.get_bool(s) == Wr.Got{b, rest} : Wr.Dec<Bool>}) -> {Wr.put_bool(b, rest) == s : String}:
  Equal.sym(String, s, Wr.put_bool(b, rest), Wire.wire_bool_exact(s, b, rest, h))

# Maybe<Nat>

def rw.mnex_some(dn: Wr.Dec<Nat>, +s1: String, +w: Maybe<&2, Nat>, +rest: String, ed: {Wr.get_nat(s1) == dn : Wr.Dec<Nat>}, +h: {Fr.get_mnat.some(dn) == Wr.Got{w, rest} : Wr.Dec<Maybe<&2, Nat>>}) -> {Wr.put_nat(1n, s1) == Fr.put_mnat(w, rest) : String}:
  match dn:
    case Wr.Got{+n, +s2}:
      %rw.got_v(Maybe<&2, Nat>, Some{n}, w, s2, rest, h) : {Wr.put_nat(1n, s1) == Fr.put_mnat(_, rest) : String}
      %rw.got_r(Maybe<&2, Nat>, Some{n}, w, s2, rest, h) : {Wr.put_nat(1n, s1) == Fr.put_mnat(Some{n}, _) : String}
      %rw.nex(s1, n, s2, ed) : {Wr.put_nat(1n, _) == Fr.put_mnat(Some{n}, s2) : String}
      {==}
    case Wr.Bad{}:
      rw.bad_got(Maybe<&2, Nat>, {Wr.put_nat(1n, s1) == Fr.put_mnat(w, rest) : String}, w, rest, h)

def rw.mnex_tag(d: Wr.Dec<Nat>, +s: String, +w: Maybe<&2, Nat>, +rest: String, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, +h: {Fr.get_mnat.tag(d) == Wr.Got{w, rest} : Wr.Dec<Maybe<&2, Nat>>}) -> {s == Fr.put_mnat(w, rest) : String}:
  match d:
    case Wr.Got{+tg, +s1}:
      match tg:
        case 0n:
          %rw.got_v(Maybe<&2, Nat>, None{}, w, s1, rest, h) : {s == Fr.put_mnat(_, rest) : String}
          %rw.got_r(Maybe<&2, Nat>, None{}, w, s1, rest, h) : {s == Fr.put_mnat(None{}, _) : String}
          Wire.wire_nat_exact(s, 0n, s1, ed)
        case 1n:
          Equal.trans(String, s, Wr.put_nat(1n, s1), Fr.put_mnat(w, rest), Wire.wire_nat_exact(s, 1n, s1, ed), rw.mnex_some(Wr.get_nat(s1), s1, w, rest, {==}, h))
        case 2n+k:
          rw.bad_got(Maybe<&2, Nat>, {s == Fr.put_mnat(w, rest) : String}, w, rest, h)
    case Wr.Bad{}:
      rw.bad_got(Maybe<&2, Nat>, {s == Fr.put_mnat(w, rest) : String}, w, rest, h)

def rw.mnat_ex(+s: String, +w: Maybe<&2, Nat>, +rest: String, h: {Fr.get_mnat(s) == Wr.Got{w, rest} : Wr.Dec<Maybe<&2, Nat>>}) -> {Fr.put_mnat(w, rest) == s : String}:
  Equal.sym(String, s, Fr.put_mnat(w, rest), rw.mnex_tag(Wr.get_nat(s), s, w, rest, {==}, h))

# Maybe<Cause>

def rw.some_c(+a: R.Cause, -b: R.Cause, e: {Some{a} == Some{b} : Maybe<&2, R.Cause>}) -> {a == b : R.Cause}:
  Equal.cong(Maybe<&2, R.Cause>, R.Cause, m => Maybe.default(&2, R.Cause, m, a), Some{a}, Some{b}, e)

def rw.MS(m: Maybe<&2, R.Cause>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

def rw.none_some(-k: R.Cause, -G: Type, e: {None{} == Some{k} : Maybe<&2, R.Cause>}) -> G:
  %e : rw.MS(_, G)
  Unit{}

# a tag a cause decodes from is that cause's tag
def rw.cause_inv(t: Nat, +k: R.Cause, e: {Fr.cause.of(t) == Some{k} : Maybe<&2, R.Cause>}) -> {t == Fr.cause.tag(k) : Nat}:
  match t:
    case 0n:
      %rw.some_c(R.Refusal{}, k, e) : {0n == Fr.cause.tag(_) : Nat}
      {==}
    case 1n:
      %rw.some_c(R.Safety{}, k, e) : {1n == Fr.cause.tag(_) : Nat}
      {==}
    case 2n:
      %rw.some_c(R.PaymentRequired{}, k, e) : {2n == Fr.cause.tag(_) : Nat}
      {==}
    case 3n:
      %rw.some_c(R.Overloaded{}, k, e) : {3n == Fr.cause.tag(_) : Nat}
      {==}
    case 4n:
      %rw.some_c(R.RateLimit{}, k, e) : {4n == Fr.cause.tag(_) : Nat}
      {==}
    case 5n:
      %rw.some_c(R.ServerError{}, k, e) : {5n == Fr.cause.tag(_) : Nat}
      {==}
    case 6n:
      %rw.some_c(R.Auth{}, k, e) : {6n == Fr.cause.tag(_) : Nat}
      {==}
    case 7n:
      %rw.some_c(R.Permission{}, k, e) : {7n == Fr.cause.tag(_) : Nat}
      {==}
    case 8n:
      %rw.some_c(R.InvalidRequest{}, k, e) : {8n == Fr.cause.tag(_) : Nat}
      {==}
    case 9n:
      %rw.some_c(R.MalformedResponse{}, k, e) : {9n == Fr.cause.tag(_) : Nat}
      {==}
    case 10n:
      %rw.some_c(R.StreamDrop{}, k, e) : {10n == Fr.cause.tag(_) : Nat}
      {==}
    case 11n:
      %rw.some_c(R.StreamStalled{}, k, e) : {11n == Fr.cause.tag(_) : Nat}
      {==}
    case 12n:
      %rw.some_c(R.StreamRepeating{}, k, e) : {12n == Fr.cause.tag(_) : Nat}
      {==}
    case 13n:
      %rw.some_c(R.Unknown{}, k, e) : {13n == Fr.cause.tag(_) : Nat}
      {==}
    case 14n+u:
      rw.none_some(k, {14n+u == Fr.cause.tag(k) : Nat}, e)

def rw.mcex_known(co: Maybe<&2, R.Cause>, +t: Nat, +s2: String, +m: Maybe<&2, R.Cause>, +rest: String, eco: {Fr.cause.of(t) == co : Maybe<&2, R.Cause>}, +h: {Fr.get_mcause.known(co, s2) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, R.Cause>>}) -> {Wr.put_nat(1n, Wr.put_nat(t, s2)) == Fr.put_mcause(m, rest) : String}:
  match co:
    case Some{+k}:
      %rw.got_v(Maybe<&2, R.Cause>, Some{k}, m, s2, rest, h) : {Wr.put_nat(1n, Wr.put_nat(t, s2)) == Fr.put_mcause(_, rest) : String}
      %rw.got_r(Maybe<&2, R.Cause>, Some{k}, m, s2, rest, h) : {Wr.put_nat(1n, Wr.put_nat(t, s2)) == Fr.put_mcause(Some{k}, _) : String}
      %rw.cause_inv(t, k, eco) : {Wr.put_nat(1n, Wr.put_nat(t, s2)) == Wr.put_nat(1n, Wr.put_nat(_, s2)) : String}
      {==}
    case None{}:
      rw.bad_got(Maybe<&2, R.Cause>, {Wr.put_nat(1n, Wr.put_nat(t, s2)) == Fr.put_mcause(m, rest) : String}, m, rest, h)

def rw.mcex_some(dn: Wr.Dec<Nat>, +s1: String, +m: Maybe<&2, R.Cause>, +rest: String, ed: {Wr.get_nat(s1) == dn : Wr.Dec<Nat>}, +h: {Fr.get_mcause.some(dn) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, R.Cause>>}) -> {Wr.put_nat(1n, s1) == Fr.put_mcause(m, rest) : String}:
  match dn:
    case Wr.Got{+t, +s2}:
      %rw.nex(s1, t, s2, ed) : {Wr.put_nat(1n, _) == Fr.put_mcause(m, rest) : String}
      rw.mcex_known(Fr.cause.of(t), t, s2, m, rest, {==}, h)
    case Wr.Bad{}:
      rw.bad_got(Maybe<&2, R.Cause>, {Wr.put_nat(1n, s1) == Fr.put_mcause(m, rest) : String}, m, rest, h)

def rw.mcex_tag(d: Wr.Dec<Nat>, +s: String, +m: Maybe<&2, R.Cause>, +rest: String, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, +h: {Fr.get_mcause.tag(d) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, R.Cause>>}) -> {s == Fr.put_mcause(m, rest) : String}:
  match d:
    case Wr.Got{+tg, +s1}:
      match tg:
        case 0n:
          %rw.got_v(Maybe<&2, R.Cause>, None{}, m, s1, rest, h) : {s == Fr.put_mcause(_, rest) : String}
          %rw.got_r(Maybe<&2, R.Cause>, None{}, m, s1, rest, h) : {s == Fr.put_mcause(None{}, _) : String}
          Wire.wire_nat_exact(s, 0n, s1, ed)
        case 1n:
          Equal.trans(String, s, Wr.put_nat(1n, s1), Fr.put_mcause(m, rest), Wire.wire_nat_exact(s, 1n, s1, ed), rw.mcex_some(Wr.get_nat(s1), s1, m, rest, {==}, h))
        case 2n+k:
          rw.bad_got(Maybe<&2, R.Cause>, {s == Fr.put_mcause(m, rest) : String}, m, rest, h)
    case Wr.Bad{}:
      rw.bad_got(Maybe<&2, R.Cause>, {s == Fr.put_mcause(m, rest) : String}, m, rest, h)

def rw.mcause_ex(+s: String, +m: Maybe<&2, R.Cause>, +rest: String, h: {Fr.get_mcause(s) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, R.Cause>>}) -> {Fr.put_mcause(m, rest) == s : String}:
  Equal.sym(String, s, Fr.put_mcause(m, rest), rw.mcex_tag(Wr.get_nat(s), s, m, rest, {==}, h))

# Facts

def rw.fx_text(+p: Bool, +l: Bool, +st: Maybe<&2, Nat>, +k: Maybe<&2, R.Cause>, d: Wr.Dec<Bool>, +s4: String, +f: R.Facts, +rest: String, ed: {Wr.get_bool(s4) == d : Wr.Dec<Bool>}, +h: {Fr.get_facts.text(p, l, st, k, d) == Wr.Got{f, rest} : Wr.Dec<R.Facts>}) -> {Wr.put_bool(p, Wr.put_bool(l, Fr.put_mnat(st, Fr.put_mcause(k, s4)))) == Fr.put_facts(f, rest) : String}:
  match d:
    case Wr.Got{+t, +s5}:
      %rw.got_v(R.Facts, R.Facts{p, l, st, k, t}, f, s5, rest, h) : {Wr.put_bool(p, Wr.put_bool(l, Fr.put_mnat(st, Fr.put_mcause(k, s4)))) == Fr.put_facts(_, rest) : String}
      %rw.got_r(R.Facts, R.Facts{p, l, st, k, t}, f, s5, rest, h) : {Wr.put_bool(p, Wr.put_bool(l, Fr.put_mnat(st, Fr.put_mcause(k, s4)))) == Fr.put_facts(R.Facts{p, l, st, k, t}, _) : String}
      %rw.bex(s4, t, s5, ed) : {Wr.put_bool(p, Wr.put_bool(l, Fr.put_mnat(st, Fr.put_mcause(k, _)))) == Fr.put_facts(R.Facts{p, l, st, k, t}, s5) : String}
      {==}
    case Wr.Bad{}:
      rw.bad_got(R.Facts, {Wr.put_bool(p, Wr.put_bool(l, Fr.put_mnat(st, Fr.put_mcause(k, s4)))) == Fr.put_facts(f, rest) : String}, f, rest, h)

def rw.fx_kind(+p: Bool, +l: Bool, +st: Maybe<&2, Nat>, d: Wr.Dec<Maybe<&2, R.Cause>>, +s3: String, +f: R.Facts, +rest: String, ed: {Fr.get_mcause(s3) == d : Wr.Dec<Maybe<&2, R.Cause>>}, +h: {Fr.get_facts.kind(p, l, st, d) == Wr.Got{f, rest} : Wr.Dec<R.Facts>}) -> {Wr.put_bool(p, Wr.put_bool(l, Fr.put_mnat(st, s3))) == Fr.put_facts(f, rest) : String}:
  match d:
    case Wr.Got{+k, +s4}:
      %rw.mcause_ex(s3, k, s4, ed) : {Wr.put_bool(p, Wr.put_bool(l, Fr.put_mnat(st, _))) == Fr.put_facts(f, rest) : String}
      rw.fx_text(p, l, st, k, Wr.get_bool(s4), s4, f, rest, {==}, h)
    case Wr.Bad{}:
      rw.bad_got(R.Facts, {Wr.put_bool(p, Wr.put_bool(l, Fr.put_mnat(st, s3))) == Fr.put_facts(f, rest) : String}, f, rest, h)

def rw.fx_status(+p: Bool, +l: Bool, d: Wr.Dec<Maybe<&2, Nat>>, +s2: String, +f: R.Facts, +rest: String, ed: {Fr.get_mnat(s2) == d : Wr.Dec<Maybe<&2, Nat>>}, +h: {Fr.get_facts.status(p, l, d) == Wr.Got{f, rest} : Wr.Dec<R.Facts>}) -> {Wr.put_bool(p, Wr.put_bool(l, s2)) == Fr.put_facts(f, rest) : String}:
  match d:
    case Wr.Got{+st, +s3}:
      %rw.mnat_ex(s2, st, s3, ed) : {Wr.put_bool(p, Wr.put_bool(l, _)) == Fr.put_facts(f, rest) : String}
      rw.fx_kind(p, l, st, Fr.get_mcause(s3), s3, f, rest, {==}, h)
    case Wr.Bad{}:
      rw.bad_got(R.Facts, {Wr.put_bool(p, Wr.put_bool(l, s2)) == Fr.put_facts(f, rest) : String}, f, rest, h)

def rw.fx_limit(+p: Bool, d: Wr.Dec<Bool>, +s1: String, +f: R.Facts, +rest: String, ed: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}, +h: {Fr.get_facts.limit(p, d) == Wr.Got{f, rest} : Wr.Dec<R.Facts>}) -> {Wr.put_bool(p, s1) == Fr.put_facts(f, rest) : String}:
  match d:
    case Wr.Got{+l, +s2}:
      %rw.bex(s1, l, s2, ed) : {Wr.put_bool(p, _) == Fr.put_facts(f, rest) : String}
      rw.fx_status(p, l, Fr.get_mnat(s2), s2, f, rest, {==}, h)
    case Wr.Bad{}:
      rw.bad_got(R.Facts, {Wr.put_bool(p, s1) == Fr.put_facts(f, rest) : String}, f, rest, h)

def rw.fx_parked(d: Wr.Dec<Bool>, +s: String, +f: R.Facts, +rest: String, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}, +h: {Fr.get_facts.parked(d) == Wr.Got{f, rest} : Wr.Dec<R.Facts>}) -> {s == Fr.put_facts(f, rest) : String}:
  match d:
    case Wr.Got{+p, +s1}:
      %rw.bex(s, p, s1, ed) : {_ == Fr.put_facts(f, rest) : String}
      rw.fx_limit(p, Wr.get_bool(s1), s1, f, rest, {==}, h)
    case Wr.Bad{}:
      rw.bad_got(R.Facts, {s == Fr.put_facts(f, rest) : String}, f, rest, h)

def rw.facts_ex(+s: String, +f: R.Facts, +rest: String, h: {Fr.get_facts(s) == Wr.Got{f, rest} : Wr.Dec<R.Facts>}) -> {Fr.put_facts(f, rest) == s : String}:
  Equal.sym(String, s, Fr.put_facts(f, rest), rw.fx_parked(Wr.get_bool(s), s, f, rest, {==}, h))

# Tried and lists of them (after the failover pilot's ff_tried_ex, ff_list_ex)

def rw.tex_wait(+at: Nat, dw: Wr.Dec<Maybe<&2, Nat>>, +s1: String, +t: R.Tried, +rest: String, ew: {Fr.get_mnat(s1) == dw : Wr.Dec<Maybe<&2, Nat>>}, +h: {Fr.get_tried.wait(at, dw) == Wr.Got{t, rest} : Wr.Dec<R.Tried>}) -> {Wr.put_nat(at, s1) == Fr.put_tried(t, rest) : String}:
  match dw:
    case Wr.Got{+w, +s2}:
      %rw.got_v(R.Tried, R.Tried{at, w}, t, s2, rest, h) : {Wr.put_nat(at, s1) == Fr.put_tried(_, rest) : String}
      %rw.got_r(R.Tried, R.Tried{at, w}, t, s2, rest, h) : {Wr.put_nat(at, s1) == Fr.put_tried(R.Tried{at, w}, _) : String}
      %rw.mnat_ex(s1, w, s2, ew) : {Wr.put_nat(at, _) == Fr.put_tried(R.Tried{at, w}, s2) : String}
      {==}
    case Wr.Bad{}:
      rw.bad_got(R.Tried, {Wr.put_nat(at, s1) == Fr.put_tried(t, rest) : String}, t, rest, h)

def rw.tex_at(d: Wr.Dec<Nat>, +s: String, +t: R.Tried, +rest: String, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, +h: {Fr.get_tried.at(d) == Wr.Got{t, rest} : Wr.Dec<R.Tried>}) -> {s == Fr.put_tried(t, rest) : String}:
  match d:
    case Wr.Got{+at, +s1}:
      Equal.trans(String, s, Wr.put_nat(at, s1), Fr.put_tried(t, rest), Wire.wire_nat_exact(s, at, s1, ed), rw.tex_wait(at, Fr.get_mnat(s1), s1, t, rest, {==}, h))
    case Wr.Bad{}:
      rw.bad_got(R.Tried, {s == Fr.put_tried(t, rest) : String}, t, rest, h)

def rw.tried_ex(+s: String, +t: R.Tried, +rest: String, h: {Fr.get_tried(s) == Wr.Got{t, rest} : Wr.Dec<R.Tried>}) -> {s == Fr.put_tried(t, rest) : String}:
  rw.tex_at(Wr.get_nat(s), s, t, rest, {==}, h)

# what the items after a count of 1+m read: their encoding, and 1+m of them
def rw.LexOK(m: Nat, s1: String, ts: List<&2, R.Tried>, rest: String) -> Type:
  {s1 == LA.rw.items(ts, rest) : String} & {R.length(ts) == 1n+m : Nat}

def rw.lex_pair(+t: R.Tried, -s1: String, +s2: String, +ts2: List<&2, R.Tried>, +rest2: String, -m: Nat, es1: {s1 == Fr.put_tried(t, s2) : String}, g: rw.LexOK(m, s2, ts2, rest2)) -> rw.LexOK(1n+m, s1, t <> ts2, rest2):
  (a, b) = g
  (Equal.trans(String, s1, Fr.put_tried(t, s2), Fr.put_tried(t, LA.rw.items(ts2, rest2)), es1, Equal.cong(String, String, x => Fr.put_tried(t, x), s2, LA.rw.items(ts2, rest2), a)), Equal.cong(Nat, Nat, x => 1n+x, R.length(ts2), 1n+m, b))

def rw.lex_cons(dl: Wr.Dec<List<&2, R.Tried>>, +t: R.Tried, +s1: String, +s2: String, +ts: List<&2, R.Tried>, +rest: String, -m: Nat, ed: {Wr.get_list.go(~R.Tried, ~Fr.get_tried, m, Fr.get_tried(s2)) == dl : Wr.Dec<List<&2, R.Tried>>}, +h: {Wr.get_list.cons(R.Tried, t, dl) == Wr.Got{ts, rest} : Wr.Dec<List<&2, R.Tried>>}, es1: {s1 == Fr.put_tried(t, s2) : String}, ih: @ts2: List<&2, R.Tried> -> @rest2: String -> {Wr.get_list.go(~R.Tried, ~Fr.get_tried, m, Fr.get_tried(s2)) == Wr.Got{ts2, rest2} : Wr.Dec<List<&2, R.Tried>>} -> rw.LexOK(m, s2, ts2, rest2)) -> rw.LexOK(1n+m, s1, ts, rest):
  match dl:
    case Wr.Got{+ts2, +rest2}:
      %rw.got_v(List<&2, R.Tried>, t <> ts2, ts, rest2, rest, h) : rw.LexOK(1n+m, s1, _, rest)
      %rw.got_r(List<&2, R.Tried>, t <> ts2, ts, rest2, rest, h) : rw.LexOK(1n+m, s1, t <> ts2, _)
      rw.lex_pair(t, s1, s2, ts2, rest2, m, es1, ih(ts2, rest2, ed))
    case Wr.Bad{}:
      rw.bad_got(List<&2, R.Tried>, rw.LexOK(1n+m, s1, ts, rest), ts, rest, h)

def rw.lex_go(m: Nat, cur: Wr.Dec<R.Tried>, +s1: String, +ts: List<&2, R.Tried>, +rest: String, ec: {Fr.get_tried(s1) == cur : Wr.Dec<R.Tried>}, +h: {Wr.get_list.go(~R.Tried, ~Fr.get_tried, m, cur) == Wr.Got{ts, rest} : Wr.Dec<List<&2, R.Tried>>}) -> rw.LexOK(m, s1, ts, rest):
  match m:
    case 0n:
      match cur:
        case Wr.Got{+t, +s2}:
          %rw.got_v(List<&2, R.Tried>, [t], ts, s2, rest, h) : rw.LexOK(0n, s1, _, rest)
          %rw.got_r(List<&2, R.Tried>, [t], ts, s2, rest, h) : rw.LexOK(0n, s1, [t], _)
          (rw.tried_ex(s1, t, s2, ec), {==})
        case Wr.Bad{}:
          rw.bad_got(List<&2, R.Tried>, rw.LexOK(0n, s1, ts, rest), ts, rest, h)
    case 1n++k:
      match cur:
        case Wr.Got{+t, +s2}:
          rw.lex_cons(Wr.get_list.go(~R.Tried, ~Fr.get_tried, k, Fr.get_tried(s2)), t, s1, s2, ts, rest, k, {==}, h, rw.tried_ex(s1, t, s2, ec), ts2 => rest2 => e => rw.lex_go(k, Fr.get_tried(s2), s2, ts2, rest2, {==}, e))
        case Wr.Bad{}:
          rw.bad_got(List<&2, R.Tried>, rw.LexOK(1n+k, s1, ts, rest), ts, rest, h)

def rw.lex_fin(+s: String, +m: Nat, +s1: String, +ts: List<&2, R.Tried>, +rest: String, es: {s == Wr.put_nat(1n+m, s1) : String}, g: rw.LexOK(m, s1, ts, rest)) -> {s == Wr.put_list(~R.Tried, ~Fr.put_tried, ts, rest) : String}:
  (a, b) = g
  %Equal.sym(String, Wr.put_list(~R.Tried, ~Fr.put_tried, ts, rest), Wr.put_nat(R.length(ts), LA.rw.items(ts, rest)), LA.rw.put_list(ts, rest)) : {s == _ : String}
  %Equal.sym(Nat, R.length(ts), 1n+m, b) : {s == Wr.put_nat(_, LA.rw.items(ts, rest)) : String}
  %a : {s == Wr.put_nat(1n+m, _) : String}
  es

def rw.lex_start(d: Wr.Dec<Nat>, +s: String, +ts: List<&2, R.Tried>, +rest: String, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, +h: {Wr.get_list.start(~R.Tried, ~Fr.get_tried, d) == Wr.Got{ts, rest} : Wr.Dec<List<&2, R.Tried>>}) -> {s == Wr.put_list(~R.Tried, ~Fr.put_tried, ts, rest) : String}:
  match d:
    case Wr.Got{+n, +s1}:
      match n:
        case 0n:
          %rw.got_v(List<&2, R.Tried>, Nil{}, ts, s1, rest, h) : {s == Wr.put_list(~R.Tried, ~Fr.put_tried, _, rest) : String}
          %rw.got_r(List<&2, R.Tried>, Nil{}, ts, s1, rest, h) : {s == Wr.put_list(~R.Tried, ~Fr.put_tried, Nil{}, _) : String}
          Wire.wire_nat_exact(s, 0n, s1, ed)
        case 1n++m:
          rw.lex_fin(s, m, s1, ts, rest, Wire.wire_nat_exact(s, 1n+m, s1, ed), rw.lex_go(m, Fr.get_tried(s1), s1, ts, rest, {==}, h))
    case Wr.Bad{}:
      rw.bad_got(List<&2, R.Tried>, {s == Wr.put_list(~R.Tried, ~Fr.put_tried, ts, rest) : String}, ts, rest, h)

def rw.list_ex(+s: String, +ts: List<&2, R.Tried>, +rest: String, h: {Wr.get_list(~R.Tried, ~Fr.get_tried, s) == Wr.Got{ts, rest} : Wr.Dec<List<&2, R.Tried>>}) -> {Wr.put_list(~R.Tried, ~Fr.put_tried, ts, rest) == s : String}:
  Equal.sym(String, s, Wr.put_list(~R.Tried, ~Fr.put_tried, ts, rest), rw.lex_start(Wr.get_nat(s), s, ts, rest, {==}, h))

# Requests: classify

def rw.qx_classify(d: Wr.Dec<R.Facts>, +s1: String, +q: Fr.Req, +rest: String, ed: {Fr.get_facts(s1) == d : Wr.Dec<R.Facts>}, +h: {Fr.get_classify(d) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}) -> {Wr.put_nat(0n, s1) == Fr.put_req(q, rest) : String}:
  match d:
    case Wr.Got{+f, +s2}:
      %rw.got_v(Fr.Req, Fr.QClassify{f}, q, s2, rest, h) : {Wr.put_nat(0n, s1) == Fr.put_req(_, rest) : String}
      %rw.got_r(Fr.Req, Fr.QClassify{f}, q, s2, rest, h) : {Wr.put_nat(0n, s1) == Fr.put_req(Fr.QClassify{f}, _) : String}
      %rw.facts_ex(s1, f, s2, ed) : {Wr.put_nat(0n, _) == Fr.put_req(Fr.QClassify{f}, s2) : String}
      {==}
    case Wr.Bad{}:
      rw.bad_got(Fr.Req, {Wr.put_nat(0n, s1) == Fr.put_req(q, rest) : String}, q, rest, h)

# Requests: wait

def rw.wx_server(+b: Nat, +a: Nat, +c: Nat, +dr: Nat, d: Wr.Dec<Maybe<&2, Nat>>, +s5: String, +q: Fr.Req, +rest: String, ed: {Fr.get_mnat(s5) == d : Wr.Dec<Maybe<&2, Nat>>}, +h: {Fr.get_wait.server(b, a, c, dr, d) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}) -> {Wr.put_nat(1n, Wr.put_nat(b, Wr.put_nat(a, Wr.put_nat(c, Wr.put_nat(dr, s5))))) == Fr.put_req(q, rest) : String}:
  match d:
    case Wr.Got{+sv, +s6}:
      %rw.got_v(Fr.Req, Fr.QWait{b, a, c, dr, sv}, q, s6, rest, h) : {Wr.put_nat(1n, Wr.put_nat(b, Wr.put_nat(a, Wr.put_nat(c, Wr.put_nat(dr, s5))))) == Fr.put_req(_, rest) : String}
      %rw.got_r(Fr.Req, Fr.QWait{b, a, c, dr, sv}, q, s6, rest, h) : {Wr.put_nat(1n, Wr.put_nat(b, Wr.put_nat(a, Wr.put_nat(c, Wr.put_nat(dr, s5))))) == Fr.put_req(Fr.QWait{b, a, c, dr, sv}, _) : String}
      %rw.mnat_ex(s5, sv, s6, ed) : {Wr.put_nat(1n, Wr.put_nat(b, Wr.put_nat(a, Wr.put_nat(c, Wr.put_nat(dr, _))))) == Fr.put_req(Fr.QWait{b, a, c, dr, sv}, s6) : String}
      {==}
    case Wr.Bad{}:
      rw.bad_got(Fr.Req, {Wr.put_nat(1n, Wr.put_nat(b, Wr.put_nat(a, Wr.put_nat(c, Wr.put_nat(dr, s5))))) == Fr.put_req(q, rest) : String}, q, rest, h)

def rw.wx_draw(+b: Nat, +a: Nat, +c: Nat, d: Wr.Dec<Nat>, +s4: String, +q: Fr.Req, +rest: String, ed: {Wr.get_nat(s4) == d : Wr.Dec<Nat>}, +h: {Fr.get_wait.draw(b, a, c, d) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}) -> {Wr.put_nat(1n, Wr.put_nat(b, Wr.put_nat(a, Wr.put_nat(c, s4)))) == Fr.put_req(q, rest) : String}:
  match d:
    case Wr.Got{+dr, +s5}:
      %rw.nex(s4, dr, s5, ed) : {Wr.put_nat(1n, Wr.put_nat(b, Wr.put_nat(a, Wr.put_nat(c, _)))) == Fr.put_req(q, rest) : String}
      rw.wx_server(b, a, c, dr, Fr.get_mnat(s5), s5, q, rest, {==}, h)
    case Wr.Bad{}:
      rw.bad_got(Fr.Req, {Wr.put_nat(1n, Wr.put_nat(b, Wr.put_nat(a, Wr.put_nat(c, s4)))) == Fr.put_req(q, rest) : String}, q, rest, h)

def rw.wx_cap(+b: Nat, +a: Nat, d: Wr.Dec<Nat>, +s3: String, +q: Fr.Req, +rest: String, ed: {Wr.get_nat(s3) == d : Wr.Dec<Nat>}, +h: {Fr.get_wait.cap(b, a, d) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}) -> {Wr.put_nat(1n, Wr.put_nat(b, Wr.put_nat(a, s3))) == Fr.put_req(q, rest) : String}:
  match d:
    case Wr.Got{+c, +s4}:
      %rw.nex(s3, c, s4, ed) : {Wr.put_nat(1n, Wr.put_nat(b, Wr.put_nat(a, _))) == Fr.put_req(q, rest) : String}
      rw.wx_draw(b, a, c, Wr.get_nat(s4), s4, q, rest, {==}, h)
    case Wr.Bad{}:
      rw.bad_got(Fr.Req, {Wr.put_nat(1n, Wr.put_nat(b, Wr.put_nat(a, s3))) == Fr.put_req(q, rest) : String}, q, rest, h)

def rw.wx_attempt(+b: Nat, d: Wr.Dec<Nat>, +s2: String, +q: Fr.Req, +rest: String, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}, +h: {Fr.get_wait.attempt(b, d) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}) -> {Wr.put_nat(1n, Wr.put_nat(b, s2)) == Fr.put_req(q, rest) : String}:
  match d:
    case Wr.Got{+a, +s3}:
      %rw.nex(s2, a, s3, ed) : {Wr.put_nat(1n, Wr.put_nat(b, _)) == Fr.put_req(q, rest) : String}
      rw.wx_cap(b, a, Wr.get_nat(s3), s3, q, rest, {==}, h)
    case Wr.Bad{}:
      rw.bad_got(Fr.Req, {Wr.put_nat(1n, Wr.put_nat(b, s2)) == Fr.put_req(q, rest) : String}, q, rest, h)

def rw.wx_base(d: Wr.Dec<Nat>, +s1: String, +q: Fr.Req, +rest: String, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}, +h: {Fr.get_wait(d) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}) -> {Wr.put_nat(1n, s1) == Fr.put_req(q, rest) : String}:
  match d:
    case Wr.Got{+b, +s2}:
      %rw.nex(s1, b, s2, ed) : {Wr.put_nat(1n, _) == Fr.put_req(q, rest) : String}
      rw.wx_attempt(b, Wr.get_nat(s2), s2, q, rest, {==}, h)
    case Wr.Bad{}:
      rw.bad_got(Fr.Req, {Wr.put_nat(1n, s1) == Fr.put_req(q, rest) : String}, q, rest, h)

# Requests: failover

def rw.fx_policy_max(+len: Nat, +ts: List<&2, R.Tried>, +sw: Nat, +b: Nat, d: Wr.Dec<Nat>, +s5: String, +q: Fr.Req, +rest: String, ed: {Wr.get_nat(s5) == d : Wr.Dec<Nat>}, +h: {Fr.get_failover.policy(len, ts, Fr.get_policy.max(sw, b, d)) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}) -> {Wr.put_nat(2n, Wr.put_nat(len, Wr.put_list(~R.Tried, ~Fr.put_tried, ts, Wr.put_nat(sw, Wr.put_nat(b, s5))))) == Fr.put_req(q, rest) : String}:
  match d:
    case Wr.Got{+m, +s6}:
      +Q = {Fr.QFailover{len, ts, R.Policy{sw, b, m}} : Fr.Req}
      %rw.got_v(Fr.Req, Q, q, s6, rest, h) : {Wr.put_nat(2n, Wr.put_nat(len, Wr.put_list(~R.Tried, ~Fr.put_tried, ts, Wr.put_nat(sw, Wr.put_nat(b, s5))))) == Fr.put_req(_, rest) : String}
      %rw.got_r(Fr.Req, Q, q, s6, rest, h) : {Wr.put_nat(2n, Wr.put_nat(len, Wr.put_list(~R.Tried, ~Fr.put_tried, ts, Wr.put_nat(sw, Wr.put_nat(b, s5))))) == Fr.put_req(Q, _) : String}
      %rw.nex(s5, m, s6, ed) : {Wr.put_nat(2n, Wr.put_nat(len, Wr.put_list(~R.Tried, ~Fr.put_tried, ts, Wr.put_nat(sw, Wr.put_nat(b, _))))) == Fr.put_req(Q, s6) : String}
      {==}
    case Wr.Bad{}:
      rw.bad_got(Fr.Req, {Wr.put_nat(2n, Wr.put_nat(len, Wr.put_list(~R.Tried, ~Fr.put_tried, ts, Wr.put_nat(sw, Wr.put_nat(b, s5))))) == Fr.put_req(q, rest) : String}, q, rest, h)

def rw.fx_policy_base(+len: Nat, +ts: List<&2, R.Tried>, +sw: Nat, d: Wr.Dec<Nat>, +s4: String, +q: Fr.Req, +rest: String, ed: {Wr.get_nat(s4) == d : Wr.Dec<Nat>}, +h: {Fr.get_failover.policy(len, ts, Fr.get_policy.base(sw, d)) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}) -> {Wr.put_nat(2n, Wr.put_nat(len, Wr.put_list(~R.Tried, ~Fr.put_tried, ts, Wr.put_nat(sw, s4)))) == Fr.put_req(q, rest) : String}:
  match d:
    case Wr.Got{+b, +s5}:
      %rw.nex(s4, b, s5, ed) : {Wr.put_nat(2n, Wr.put_nat(len, Wr.put_list(~R.Tried, ~Fr.put_tried, ts, Wr.put_nat(sw, _)))) == Fr.put_req(q, rest) : String}
      rw.fx_policy_max(len, ts, sw, b, Wr.get_nat(s5), s5, q, rest, {==}, h)
    case Wr.Bad{}:
      rw.bad_got(Fr.Req, {Wr.put_nat(2n, Wr.put_nat(len, Wr.put_list(~R.Tried, ~Fr.put_tried, ts, Wr.put_nat(sw, s4)))) == Fr.put_req(q, rest) : String}, q, rest, h)

def rw.fx_policy(+len: Nat, +ts: List<&2, R.Tried>, d: Wr.Dec<Nat>, +s3: String, +q: Fr.Req, +rest: String, ed: {Wr.get_nat(s3) == d : Wr.Dec<Nat>}, +h: {Fr.get_failover.policy(len, ts, Fr.get_policy.switches(d)) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}) -> {Wr.put_nat(2n, Wr.put_nat(len, Wr.put_list(~R.Tried, ~Fr.put_tried, ts, s3))) == Fr.put_req(q, rest) : String}:
  match d:
    case Wr.Got{+sw, +s4}:
      %rw.nex(s3, sw, s4, ed) : {Wr.put_nat(2n, Wr.put_nat(len, Wr.put_list(~R.Tried, ~Fr.put_tried, ts, _))) == Fr.put_req(q, rest) : String}
      rw.fx_policy_base(len, ts, sw, Wr.get_nat(s4), s4, q, rest, {==}, h)
    case Wr.Bad{}:
      rw.bad_got(Fr.Req, {Wr.put_nat(2n, Wr.put_nat(len, Wr.put_list(~R.Tried, ~Fr.put_tried, ts, s3))) == Fr.put_req(q, rest) : String}, q, rest, h)

def rw.fx_tried(+len: Nat, d: Wr.Dec<List<&2, R.Tried>>, +s2: String, +q: Fr.Req, +rest: String, ed: {Wr.get_list(~R.Tried, ~Fr.get_tried, s2) == d : Wr.Dec<List<&2, R.Tried>>}, +h: {Fr.get_failover.tried(len, d) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}) -> {Wr.put_nat(2n, Wr.put_nat(len, s2)) == Fr.put_req(q, rest) : String}:
  match d:
    case Wr.Got{+ts, +s3}:
      %rw.list_ex(s2, ts, s3, ed) : {Wr.put_nat(2n, Wr.put_nat(len, _)) == Fr.put_req(q, rest) : String}
      rw.fx_policy(len, ts, Wr.get_nat(s3), s3, q, rest, {==}, h)
    case Wr.Bad{}:
      rw.bad_got(Fr.Req, {Wr.put_nat(2n, Wr.put_nat(len, s2)) == Fr.put_req(q, rest) : String}, q, rest, h)

def rw.fx_len(d: Wr.Dec<Nat>, +s1: String, +q: Fr.Req, +rest: String, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}, +h: {Fr.get_failover(d) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}) -> {Wr.put_nat(2n, s1) == Fr.put_req(q, rest) : String}:
  match d:
    case Wr.Got{+len, +s2}:
      %rw.nex(s1, len, s2, ed) : {Wr.put_nat(2n, _) == Fr.put_req(q, rest) : String}
      rw.fx_tried(len, Wr.get_list(~R.Tried, ~Fr.get_tried, s2), s2, q, rest, {==}, h)
    case Wr.Bad{}:
      rw.bad_got(Fr.Req, {Wr.put_nat(2n, s1) == Fr.put_req(q, rest) : String}, q, rest, h)

# Requests: stall

def rw.sx(d: Wr.Dec<Nat>, +s1: String, +q: Fr.Req, +rest: String, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}, +h: {Fr.get_stall(d) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}) -> {Wr.put_nat(3n, s1) == Fr.put_req(q, rest) : String}:
  match d:
    case Wr.Got{+i, +s2}:
      %rw.got_v(Fr.Req, Fr.QStall{i}, q, s2, rest, h) : {Wr.put_nat(3n, s1) == Fr.put_req(_, rest) : String}
      %rw.got_r(Fr.Req, Fr.QStall{i}, q, s2, rest, h) : {Wr.put_nat(3n, s1) == Fr.put_req(Fr.QStall{i}, _) : String}
      %rw.nex(s1, i, s2, ed) : {Wr.put_nat(3n, _) == Fr.put_req(Fr.QStall{i}, s2) : String}
      {==}
    case Wr.Bad{}:
      rw.bad_got(Fr.Req, {Wr.put_nat(3n, s1) == Fr.put_req(q, rest) : String}, q, rest, h)

# Requests: the tag

def rw.qx_tag(t: Nat, +s1: String, +q: Fr.Req, +rest: String, +h: {Fr.get_req.tag(t, s1) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}) -> {Wr.put_nat(t, s1) == Fr.put_req(q, rest) : String}:
  match t:
    case 0n:
      rw.qx_classify(Fr.get_facts(s1), s1, q, rest, {==}, h)
    case 1n:
      rw.wx_base(Wr.get_nat(s1), s1, q, rest, {==}, h)
    case 2n:
      rw.fx_len(Wr.get_nat(s1), s1, q, rest, {==}, h)
    case 3n:
      rw.sx(Wr.get_nat(s1), s1, q, rest, {==}, h)
    case 4n+u:
      rw.bad_got(Fr.Req, {Wr.put_nat(4n+u, s1) == Fr.put_req(q, rest) : String}, q, rest, h)

def rw.qx_start(d: Wr.Dec<Nat>, +s: String, +q: Fr.Req, +rest: String, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, +h: {Fr.get_req.start(d) == Wr.Got{q, rest} : Wr.Dec<Fr.Req>}) -> {s == Fr.put_req(q, rest) : String}:
  match d:
    case Wr.Got{+t, +s1}:
      Equal.trans(String, s, Wr.put_nat(t, s1), Fr.put_req(q, rest), Wire.wire_nat_exact(s, t, s1, ed), rw.qx_tag(t, s1, q, rest, h))
    case Wr.Bad{}:
      rw.bad_got(Fr.Req, {s == Fr.put_req(q, rest) : String}, q, rest, h)

def Retry.retry_ffi_request_exact(s, q, rest, h):
  rw.qx_start(Wr.get_nat(s), s, q, rest, {==}, h)
