# eukhe: lemmas shared by the proofs of area mcp_url: each function of
# bend/mcp_url.bend is the spec helper of laws/mcp_url.bend that states
# its requirement (by induction on the text or list it reads, case by case
# on the Bool or constructor it matches)

import Base
import ../../bend/mcp_url.bend as Mu
import ../../laws/mcp_url.bend as McpUrl

# Text
# ----

def mub.lead_open.at(b: Bool, c: Char, t: String, r: String) -> {Mu.drop_open.at(b, c, t, r) == McpUrl.mu_lead.at(b, c, t, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def mub.lead_open(s: String) -> {Mu.drop_open(s) == McpUrl.mu_lead(s, '[') : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Mu.drop_open(t), McpUrl.mu_lead(t, '['), mub.lead_open(t)) : {Mu.drop_open.at(Char.is_eq(c, '['), c, t, _) == McpUrl.mu_lead.at(Char.is_eq(c, '['), c, t, McpUrl.mu_lead(t, '[')) : String}
      mub.lead_open.at(Char.is_eq(c, '['), c, t, McpUrl.mu_lead(t, '['))

def mub.lead_zero.at(b: Bool, c: Char, t: String, r: String) -> {Mu.drop_zeros.at(b, c, t, r) == McpUrl.mu_lead.at(b, c, t, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def mub.lead_zero(s: String) -> {Mu.drop_zeros(s) == McpUrl.mu_lead(s, '0') : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Mu.drop_zeros(t), McpUrl.mu_lead(t, '0'), mub.lead_zero(t)) : {Mu.drop_zeros.at(Char.is_eq(c, '0'), c, t, _) == McpUrl.mu_lead.at(Char.is_eq(c, '0'), c, t, McpUrl.mu_lead(t, '0')) : String}
      mub.lead_zero.at(Char.is_eq(c, '0'), c, t, McpUrl.mu_lead(t, '0'))

def mub.trail.at(b: Bool, c: Char, r: String) -> {Mu.drop_close.at(b, c, r) == McpUrl.mu_trail.at(b, c, r) : String}:
  match b:
    case True{}:
      match r:
        case SNil{}:
          {==}
        case SCon{x, u}:
          {==}
    case False{}:
      {==}

def mub.trail(s: String) -> {Mu.drop_close(s) == McpUrl.mu_trail(s, ']') : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Mu.drop_close(t), McpUrl.mu_trail(t, ']'), mub.trail(t)) : {Mu.drop_close.at(Char.is_eq(c, ']'), c, _) == McpUrl.mu_trail.at(Char.is_eq(c, ']'), c, McpUrl.mu_trail(t, ']')) : String}
      mub.trail.at(Char.is_eq(c, ']'), c, McpUrl.mu_trail(t, ']'))

def mub.bare(+h: String) -> {Mu.bare(h) == McpUrl.mu_bare(h) : String}:
  %Equal.sym(String, Mu.drop_open(h), McpUrl.mu_lead(h, '['), mub.lead_open(h)) : {String.to_lower(Mu.drop_close(_)) == McpUrl.mu_bare(h) : String}
  %Equal.sym(String, Mu.drop_close(McpUrl.mu_lead(h, '[')), McpUrl.mu_trail(McpUrl.mu_lead(h, '['), ']'), mub.trail(McpUrl.mu_lead(h, '['))) : {String.to_lower(_) == McpUrl.mu_bare(h) : String}
  {==}

def mub.plus.at(b: Bool, c: Char, t: String) -> {Mu.unsigned.at(b, c, t) == McpUrl.mu_plus.at(b, c, t) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def mub.plus(s: String) -> {Mu.unsigned(s) == McpUrl.mu_plus(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      mub.plus.at(Char.is_eq(c, '+'), c, t)

# Digits
# ------

def mub.decs(s: String) -> {Mu.all_dec(s) == McpUrl.mu_decs(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Mu.all_dec(t), McpUrl.mu_decs(t), mub.decs(t)) : {Bool.and(Char.is_digit(c), _) == Bool.and(Char.is_digit(c), McpUrl.mu_decs(t)) : Bool}
      {==}

def mub.hex_char(c: Char) -> {Mu.is_hex(c) == McpUrl.mu_hex_char(c) : Bool}:
  match c:
    case Chr{x}:
      {==}

def mub.hexs(s: String) -> {Mu.all_hex(s) == McpUrl.mu_hexs(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Mu.all_hex(t), McpUrl.mu_hexs(t), mub.hexs(t)) : {Bool.and(Mu.is_hex(c), _) == Bool.and(McpUrl.mu_hex_char(c), McpUrl.mu_hexs(t)) : Bool}
      %Equal.sym(Bool, Mu.is_hex(c), McpUrl.mu_hex_char(c), mub.hex_char(c)) : {Bool.and(_, McpUrl.mu_hexs(t)) == Bool.and(McpUrl.mu_hex_char(c), McpUrl.mu_hexs(t)) : Bool}
      {==}

def mub.dval(s: String, v: U32) -> {Mu.dec(s, v) == McpUrl.mu_dval(s, v) : U32}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      mub.dval(t, U32.add(U32.mul(v, 10), U32.sub(Char.to_u32(c), 48)))

def mub.hdigit.at(b: Bool, x: U32) -> {Mu.hex_digit.at(b, x) == McpUrl.mu_hdigit.at(b, x) : U32}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def mub.hdigit(c: Char) -> {Mu.hex_digit(c) == McpUrl.mu_hdigit(c) : U32}:
  match c:
    case Chr{+x}:
      mub.hdigit.at(U32.is_le(x, 57), x)

def mub.hval(s: String, +v: U32) -> {Mu.hex(s, v) == McpUrl.mu_hval(s, v) : U32}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      %Equal.sym(U32, Mu.hex_digit(c), McpUrl.mu_hdigit(c), mub.hdigit(c)) : {Mu.hex(t, U32.add(U32.mul(v, 16), _)) == McpUrl.mu_hval(t, U32.add(U32.mul(v, 16), McpUrl.mu_hdigit(c))) : U32}
      mub.hval(t, U32.add(U32.mul(v, 16), McpUrl.mu_hdigit(c)))

# Parts
# -----

def mub.small(b: Bool, v: U32) -> {Mu.part.small(b, v) == McpUrl.mu_sig.val(b, v) : Mu.Part}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def mub.big(b: Bool) -> {Mu.part.big(b) == McpUrl.mu_sig.ten(b) : Mu.Part}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def mub.long(b: Bool, +g: String) -> {Mu.part.long(b, g) == McpUrl.mu_sig.mid(b, g) : Mu.Part}:
  match b:
    case True{}:
      {==}
    case False{}:
      mub.big(Bool.and(Nat.is_eq(String.length(g), 10n), String.is_le(g, "4294967295")))

def mub.short(b: Bool, +g: String) -> {Mu.part.short(b, g) == McpUrl.mu_sig.short(b, g) : Mu.Part}:
  match b:
    case True{}:
      %Equal.sym(U32, Mu.dec(g, 0), McpUrl.mu_dval(g, 0), mub.dval(g, 0)) : {Mu.part.small(U32.is_le(_, 255), _) == McpUrl.mu_sig.val(U32.is_le(McpUrl.mu_dval(g, 0), 255), McpUrl.mu_dval(g, 0)) : Mu.Part}
      mub.small(U32.is_le(McpUrl.mu_dval(g, 0), 255), McpUrl.mu_dval(g, 0))
    case False{}:
      mub.long(Nat.is_le(String.length(g), 9n), g)

def mub.digits(b: Bool, +d: String) -> {Mu.part.digits(b, d) == McpUrl.mu_part.at(b, d) : Mu.Part}:
  match b:
    case True{}:
      %Equal.sym(String, Mu.drop_zeros(d), McpUrl.mu_lead(d, '0'), mub.lead_zero(d)) : {Mu.part.sig(_) == McpUrl.mu_sig(McpUrl.mu_lead(d, '0')) : Mu.Part}
      mub.short(Nat.is_le(String.length(McpUrl.mu_lead(d, '0')), 3n), McpUrl.mu_lead(d, '0'))
    case False{}:
      {==}

def mub.part(+s: String) -> {Mu.part(s) == McpUrl.mu_part(s) : Mu.Part}:
  %Equal.sym(String, Mu.unsigned(s), McpUrl.mu_plus(s), mub.plus(s)) : {Mu.part.digits(Bool.and(Bool.not(String.is_empty(_)), Mu.all_dec(_)), _) == McpUrl.mu_part(s) : Mu.Part}
  %Equal.sym(Bool, Mu.all_dec(McpUrl.mu_plus(s)), McpUrl.mu_decs(McpUrl.mu_plus(s)), mub.decs(McpUrl.mu_plus(s))) : {Mu.part.digits(Bool.and(Bool.not(String.is_empty(McpUrl.mu_plus(s))), _), McpUrl.mu_plus(s)) == McpUrl.mu_part(s) : Mu.Part}
  mub.digits(Bool.and(Bool.not(String.is_empty(McpUrl.mu_plus(s))), McpUrl.mu_decs(McpUrl.mu_plus(s))), McpUrl.mu_plus(s))

# IPv4
# ----

def mub.quad(p: Mu.Part, q: Mu.Part, r: Mu.Part, s: Mu.Part) -> {Mu.quad(p, q, r, s) == McpUrl.mu_quad(p, q, r, s) : Mu.V4}:
  match p:
    case Mu.POct{a}:
      match q:
        case Mu.POct{b}:
          match r:
            case Mu.POct{c}:
              match s:
                case Mu.POct{d}:
                  {==}
                case Mu.PBig{}:
                  {==}
                case Mu.PNone{}:
                  {==}
            case Mu.PBig{}:
              {==}
            case Mu.PNone{}:
              {==}
        case Mu.PBig{}:
          {==}
        case Mu.PNone{}:
          {==}
    case Mu.PBig{}:
      {==}
    case Mu.PNone{}:
      {==}

def mub.four(+p: String, +q: String, +r: String, +s: String) -> {Mu.quad(Mu.part(p), Mu.part(q), Mu.part(r), Mu.part(s)) == McpUrl.mu_quad(McpUrl.mu_part(p), McpUrl.mu_part(q), McpUrl.mu_part(r), McpUrl.mu_part(s)) : Mu.V4}:
  %Equal.sym(Mu.Part, Mu.part(p), McpUrl.mu_part(p), mub.part(p)) : {Mu.quad(_, Mu.part(q), Mu.part(r), Mu.part(s)) == McpUrl.mu_quad(McpUrl.mu_part(p), McpUrl.mu_part(q), McpUrl.mu_part(r), McpUrl.mu_part(s)) : Mu.V4}
  %Equal.sym(Mu.Part, Mu.part(q), McpUrl.mu_part(q), mub.part(q)) : {Mu.quad(McpUrl.mu_part(p), _, Mu.part(r), Mu.part(s)) == McpUrl.mu_quad(McpUrl.mu_part(p), McpUrl.mu_part(q), McpUrl.mu_part(r), McpUrl.mu_part(s)) : Mu.V4}
  %Equal.sym(Mu.Part, Mu.part(r), McpUrl.mu_part(r), mub.part(r)) : {Mu.quad(McpUrl.mu_part(p), McpUrl.mu_part(q), _, Mu.part(s)) == McpUrl.mu_quad(McpUrl.mu_part(p), McpUrl.mu_part(q), McpUrl.mu_part(r), McpUrl.mu_part(s)) : Mu.V4}
  %Equal.sym(Mu.Part, Mu.part(s), McpUrl.mu_part(s), mub.part(s)) : {Mu.quad(McpUrl.mu_part(p), McpUrl.mu_part(q), McpUrl.mu_part(r), _) == McpUrl.mu_quad(McpUrl.mu_part(p), McpUrl.mu_part(q), McpUrl.mu_part(r), McpUrl.mu_part(s)) : Mu.V4}
  mub.quad(McpUrl.mu_part(p), McpUrl.mu_part(q), McpUrl.mu_part(r), McpUrl.mu_part(s))

def mub.v4(ps: List<&2, String>) -> {Mu.v4.parts(ps) == McpUrl.mu_v4.parts(ps) : Mu.V4}:
  match ps:
    case Nil{}:
      {==}
    case p <> t1:
      match t1:
        case Nil{}:
          {==}
        case q <> t2:
          match t2:
            case Nil{}:
              {==}
            case r <> t3:
              match t3:
                case Nil{}:
                  {==}
                case s <> t4:
                  match t4:
                    case Nil{}:
                      mub.four(p, q, r, s)
                    case x <> t5:
                      {==}

# IPv6
# ----

def mub.word.sig(b: Bool, +g: String) -> {Mu.word.sig(b, g) == McpUrl.mu_word.sig(b, g) : Maybe<&2, U32>}:
  match b:
    case True{}:
      %Equal.sym(U32, Mu.hex(g, 0), McpUrl.mu_hval(g, 0), mub.hval(g, 0)) : {Some{_} == Some{McpUrl.mu_hval(g, 0)} : Maybe<&2, U32>}
      {==}
    case False{}:
      {==}

def mub.word.at(b: Bool, +d: String) -> {Mu.word.digits(b, d) == McpUrl.mu_word.at(b, d) : Maybe<&2, U32>}:
  match b:
    case True{}:
      %Equal.sym(String, Mu.drop_zeros(d), McpUrl.mu_lead(d, '0'), mub.lead_zero(d)) : {Mu.word.sig(Nat.is_le(String.length(_), 4n), _) == McpUrl.mu_word.sig(Nat.is_le(String.length(McpUrl.mu_lead(d, '0')), 4n), McpUrl.mu_lead(d, '0')) : Maybe<&2, U32>}
      mub.word.sig(Nat.is_le(String.length(McpUrl.mu_lead(d, '0')), 4n), McpUrl.mu_lead(d, '0'))
    case False{}:
      {==}

def mub.word(s: String) -> {Mu.word(s) == McpUrl.mu_word(s) : Maybe<&2, U32>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      +d = {SCon{c, t} : String}
      %Equal.sym(String, Mu.unsigned(d), McpUrl.mu_plus(d), mub.plus(d)) : {Mu.word.digits(Bool.and(Bool.not(String.is_empty(_)), Mu.all_hex(_)), _) == McpUrl.mu_word(d) : Maybe<&2, U32>}
      %Equal.sym(Bool, Mu.all_hex(McpUrl.mu_plus(d)), McpUrl.mu_hexs(McpUrl.mu_plus(d)), mub.hexs(McpUrl.mu_plus(d))) : {Mu.word.digits(Bool.and(Bool.not(String.is_empty(McpUrl.mu_plus(d))), _), McpUrl.mu_plus(d)) == McpUrl.mu_word(d) : Maybe<&2, U32>}
      mub.word.at(Bool.and(Bool.not(String.is_empty(McpUrl.mu_plus(d))), McpUrl.mu_hexs(McpUrl.mu_plus(d))), McpUrl.mu_plus(d))

def mub.cons(m: Maybe<&2, U32>, r: Maybe<&2, List<&2, U32>>) -> {Mu.words.cons(m, r) == McpUrl.mu_words.cons(m, r) : Maybe<&2, List<&2, U32>>}:
  match m:
    case None{}:
      {==}
    case Some{w}:
      match r:
        case None{}:
          {==}
        case Some{ws}:
          {==}

def mub.words(ps: List<&2, String>) -> {Mu.words(ps) == McpUrl.mu_words(ps) : Maybe<&2, List<&2, U32>>}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      %Equal.sym(Maybe<&2, U32>, Mu.word(p), McpUrl.mu_word(p), mub.word(p)) : {Mu.words.cons(_, Mu.words(t)) == McpUrl.mu_words.cons(McpUrl.mu_word(p), McpUrl.mu_words(t)) : Maybe<&2, List<&2, U32>>}
      %Equal.sym(Maybe<&2, List<&2, U32>>, Mu.words(t), McpUrl.mu_words(t), mub.words(t)) : {Mu.words.cons(McpUrl.mu_word(p), _) == McpUrl.mu_words.cons(McpUrl.mu_word(p), McpUrl.mu_words(t)) : Maybe<&2, List<&2, U32>>}
      mub.cons(McpUrl.mu_word(p), McpUrl.mu_words(t))

def mub.zeros(n: Nat) -> {Mu.zeros(n) == McpUrl.mu_zeros(n) : List<&2, U32>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(List<&2, U32>, Mu.zeros(p), McpUrl.mu_zeros(p), mub.zeros(p)) : {0 <> _ == 0 <> McpUrl.mu_zeros(p) : List<&2, U32>}
      {==}

def mub.any_empty(ps: List<&2, String>) -> {Mu.any_empty(ps) == McpUrl.mu_any_empty(ps) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +t:
      %Equal.sym(Bool, Mu.any_empty(t), McpUrl.mu_any_empty(t), mub.any_empty(t)) : {Bool.or(String.is_empty(p), _) == Bool.or(String.is_empty(p), McpUrl.mu_any_empty(t)) : Bool}
      {==}

def mub.push(c: Char, h: Mu.Halves) -> {Mu.halves.push(c, h) == McpUrl.mu_halves.push(c, h) : Mu.Halves}:
  match h:
    case Mu.One{a}:
      {==}
    case Mu.Two{a, b}:
      {==}

def mub.halves.at(b: Bool, c: Char, t: String, r: Mu.Halves) -> {Mu.halves.at(b, c, t, r) == McpUrl.mu_halves.at(b, c, t, r) : Mu.Halves}:
  match b:
    case True{}:
      {==}
    case False{}:
      mub.push(c, r)

def mub.halves(s: String) -> {Mu.halves(s) == McpUrl.mu_halves(s) : Mu.Halves}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Mu.Halves, Mu.halves(t), McpUrl.mu_halves(t), mub.halves(t)) : {Mu.halves.at(Bool.and(Char.is_eq(c, ':'), String.starts_with(t, ":")), c, t, _) == McpUrl.mu_halves.at(Bool.and(Char.is_eq(c, ':'), String.starts_with(t, ":")), c, t, McpUrl.mu_halves(t)) : Mu.Halves}
      mub.halves.at(Bool.and(Char.is_eq(c, ':'), String.starts_with(t, ":")), c, t, McpUrl.mu_halves(t))

def mub.side(s: String) -> {Mu.side(s) == McpUrl.mu_side(s) : List<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      {==}

def mub.join(a: Maybe<&2, List<&2, U32>>, z: List<&2, U32>, b: Maybe<&2, List<&2, U32>>) -> {Mu.join3(a, z, b) == McpUrl.mu_join(a, z, b) : Maybe<&2, List<&2, U32>>}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      match b:
        case None{}:
          {==}
        case Some{y}:
          {==}

def mub.two.at(b: Bool, +hp: List<&2, String>, +tp: List<&2, String>, +n: Nat) -> {Mu.expand.two.at(b, hp, tp, n) == McpUrl.mu_two.at(b, hp, tp, n) : Maybe<&2, List<&2, U32>>}:
  match b:
    case True{}:
      %Equal.sym(Maybe<&2, List<&2, U32>>, Mu.words(hp), McpUrl.mu_words(hp), mub.words(hp)) : {Mu.join3(_, Mu.zeros(Nat.sub(8n, n)), Mu.words(tp)) == McpUrl.mu_join(McpUrl.mu_words(hp), McpUrl.mu_zeros(Nat.sub(8n, n)), McpUrl.mu_words(tp)) : Maybe<&2, List<&2, U32>>}
      %Equal.sym(Maybe<&2, List<&2, U32>>, Mu.words(tp), McpUrl.mu_words(tp), mub.words(tp)) : {Mu.join3(McpUrl.mu_words(hp), Mu.zeros(Nat.sub(8n, n)), _) == McpUrl.mu_join(McpUrl.mu_words(hp), McpUrl.mu_zeros(Nat.sub(8n, n)), McpUrl.mu_words(tp)) : Maybe<&2, List<&2, U32>>}
      %Equal.sym(List<&2, U32>, Mu.zeros(Nat.sub(8n, n)), McpUrl.mu_zeros(Nat.sub(8n, n)), mub.zeros(Nat.sub(8n, n))) : {Mu.join3(McpUrl.mu_words(hp), _, McpUrl.mu_words(tp)) == McpUrl.mu_join(McpUrl.mu_words(hp), McpUrl.mu_zeros(Nat.sub(8n, n)), McpUrl.mu_words(tp)) : Maybe<&2, List<&2, U32>>}
      mub.join(McpUrl.mu_words(hp), McpUrl.mu_zeros(Nat.sub(8n, n)), McpUrl.mu_words(tp))
    case False{}:
      {==}

def mub.one.at(b: Bool, ps: List<&2, String>) -> {Mu.expand.one.at(b, ps) == McpUrl.mu_one.at(b, ps) : Maybe<&2, List<&2, U32>>}:
  match b:
    case True{}:
      mub.words(ps)
    case False{}:
      {==}

def mub.one(+ps: List<&2, String>) -> {Mu.expand.one(ps) == McpUrl.mu_one(ps) : Maybe<&2, List<&2, U32>>}:
  %Equal.sym(Bool, Mu.any_empty(ps), McpUrl.mu_any_empty(ps), mub.any_empty(ps)) : {Mu.expand.one.at(Bool.and(Nat.is_eq(List.length(&2, String, ps), 8n), Bool.not(_)), ps) == McpUrl.mu_one(ps) : Maybe<&2, List<&2, U32>>}
  mub.one.at(Bool.and(Nat.is_eq(List.length(&2, String, ps), 8n), Bool.not(McpUrl.mu_any_empty(ps))), ps)

def mub.expand.of(h: Mu.Halves) -> {Mu.expand.of(h) == McpUrl.mu_expand.of(h) : Maybe<&2, List<&2, U32>>}:
  match h:
    case Mu.One{+a}:
      %Equal.sym(List<&2, String>, Mu.side(a), McpUrl.mu_side(a), mub.side(a)) : {Mu.expand.one(_) == McpUrl.mu_one(McpUrl.mu_side(a)) : Maybe<&2, List<&2, U32>>}
      mub.one(McpUrl.mu_side(a))
    case Mu.Two{+a, +b}:
      %Equal.sym(List<&2, String>, Mu.side(a), McpUrl.mu_side(a), mub.side(a)) : {Mu.expand.two(_, Mu.side(b)) == McpUrl.mu_two(McpUrl.mu_side(a), McpUrl.mu_side(b)) : Maybe<&2, List<&2, U32>>}
      %Equal.sym(List<&2, String>, Mu.side(b), McpUrl.mu_side(b), mub.side(b)) : {Mu.expand.two(McpUrl.mu_side(a), _) == McpUrl.mu_two(McpUrl.mu_side(a), McpUrl.mu_side(b)) : Maybe<&2, List<&2, U32>>}
      +hp = McpUrl.mu_side(a)
      +tp = McpUrl.mu_side(b)
      mub.two.at(Nat.is_le(Nat.add(List.length(&2, String, hp), List.length(&2, String, tp)), 7n), hp, tp, Nat.add(List.length(&2, String, hp), List.length(&2, String, tp)))

def mub.expand(+s: String) -> {Mu.expand(s) == McpUrl.mu_expand(s) : Maybe<&2, List<&2, U32>>}:
  %Equal.sym(Mu.Halves, Mu.halves(s), McpUrl.mu_halves(s), mub.halves(s)) : {Mu.expand.of(_) == McpUrl.mu_expand.of(McpUrl.mu_halves(s)) : Maybe<&2, List<&2, U32>>}
  mub.expand.of(McpUrl.mu_halves(s))

def mub.eight(ws: List<&2, U32>) -> {Mu.v6.words(ws) == McpUrl.mu_eight(ws) : Bool}:
  match ws:
    case Nil{}:
      {==}
    case w0 <> t0:
      match t0:
        case Nil{}:
          {==}
        case w1 <> t1:
          match t1:
            case Nil{}:
              {==}
            case w2 <> t2:
              match t2:
                case Nil{}:
                  {==}
                case w3 <> t3:
                  match t3:
                    case Nil{}:
                      {==}
                    case w4 <> t4:
                      match t4:
                        case Nil{}:
                          {==}
                        case w5 <> t5:
                          match t5:
                            case Nil{}:
                              {==}
                            case w6 <> t6:
                              match t6:
                                case Nil{}:
                                  {==}
                                case w7 <> t7:
                                  match t7:
                                    case Nil{}:
                                      {==}
                                    case x <> t8:
                                      {==}

def mub.v6.of(m: Maybe<&2, List<&2, U32>>) -> {Mu.v6.of(m) == McpUrl.mu_v6(m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{ws}:
      mub.eight(ws)

def mub.v6(b: Bool, +s: String) -> {Mu.v6(b, s) == McpUrl.mu_v6.at(b, s) : Bool}:
  match b:
    case True{}:
      %Equal.sym(Maybe<&2, List<&2, U32>>, Mu.expand(s), McpUrl.mu_expand(s), mub.expand(s)) : {Mu.v6.of(_) == McpUrl.mu_v6(McpUrl.mu_expand(s)) : Bool}
      mub.v6.of(McpUrl.mu_expand(s))
    case False{}:
      {==}

def mub.after(v: Mu.V4, +s: String) -> {Mu.after_v4(v, s) == McpUrl.mu_after(v, s) : Bool}:
  match v:
    case Mu.V4No{}:
      mub.v6(String.contains(s, ":"), s)
    case Mu.V4Bad{}:
      {==}
    case Mu.V4Quad{a, b, c, d}:
      {==}

def mub.refused.at(b: Bool, +s: String) -> {Mu.refused.at(b, s) == McpUrl.mu_refused.at(b, s) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Mu.V4, Mu.v4.parts(String.split(s, '.')), McpUrl.mu_v4.parts(String.split(s, '.')), mub.v4(String.split(s, '.'))) : {Mu.after_v4(_, s) == McpUrl.mu_after(McpUrl.mu_v4.parts(String.split(s, '.')), s) : Bool}
      mub.after(McpUrl.mu_v4.parts(String.split(s, '.')), s)
