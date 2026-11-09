# eukhe: the laws of area dash

import Base
import ../bend/dash.bend as Da
import ../bend/ffi_dash.bend as FDa
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# ---- dashboard_auth ----

# LAWS (D2): the dashboard's pairing choices. Each law is an open claim
# about bend/dash.bend section 1 and the call of bend/ffi_dash.bend;
# PROOF.bend proves them (as Dash.<law>) with the lemmas of proof/dash/.
# The socket stepper's laws are laws/dash_conn.bend.

# (D2) The host's choices
# -----------------------
# bend/dash.bend section 1, run as the compiled core by bend/ffi_dash.bend
# (crates/eukhe-dashboard pairing.rs, http.rs, bridge.rs). Every input is
# free: any presented text (or one too long for the wire), any token file (missing, unreadable, any text,
# too long for the wire), any first frame, any rotation and file mode,
# any result of Rust's constant-time comparison.
#
# R1: a token is exactly 64 hex digits (either case), read two by two as
#     its 32 bytes; nothing else is a token (a sign, a 63rd or 65th digit,
#     a space, a text too long for the wire). A presented empty text
#     presents no token.
# R2: the file holds a token when its text, trimmed of Rust's whitespace
#     (the Unicode White_Space set) at both ends, is a token; a missing,
#     unreadable or too long file holds none.
# R3: a socket opens only when its first frame is a pairing whose text is
#     a token, the file holds a token, and Rust found both equal. Else it
#     is refused with exactly one of three texts: no pairing or an empty
#     token: pairing needed; a text that is no token, or another token:
#     not valid any more; a file with no token: no pairing token.
# R4: a later frame runs only while the file holds a token that Rust
#     found equal to the presented one; else it is refused (the socket
#     closes) with the text of R3.
# R5: at its start `eukhe dashboard` stores a new token when it rotates or
#     no file exists; it fails on an unreadable file and on a file that
#     holds no token (never replaces it unasked); it narrows a kept file
#     whose mode gives the group or others any bit to 0600.
# R6: the call answers each request Rust writes with the choice of R1, R2
#     or R5, reads exactly the request and nothing after it, and answers
#     any other input with the exact error form.

# Spec helpers
# ------------

def sp_at.hit(b: Bool, n: Nat, r: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{n}
    case False{}:
      r

def sp_at(+c: Char, ds: String, +n: Nat) -> Maybe<&2, Nat>:
  match ds:
    case SNil{}:
      None{}
    case SCon{d, rest}:
      sp_at.hit(Char.is_eq(c, d), n, sp_at(c, rest, 1n+n))

def sp_low(+c: Char) -> Maybe<&2, Nat>:
  sp_at(c, "0123456789abcdef", 0n)

def sp_up(+c: Char) -> Maybe<&2, Nat>:
  sp_at(c, "0123456789ABCDEF", 0n)

def sp_digit.or(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match a:
    case Some{x}:
      Some{x}
    case None{}:
      b

# R1: the value of a hex digit
def sp_digit(+c: Char) -> Maybe<&2, Nat>:
  sp_digit.or(sp_low(c), sp_up(c))

def sp_pair(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match a:
    case None{}:
      None{}
    case Some{h}:
      match b:
        case None{}:
          None{}
        case Some{l}:
          Some{Nat.add(Nat.mul(16n, h), l)}

def sp_cons(m: Maybe<&2, Nat>, r: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      match r:
        case None{}:
          None{}
        case Some{xs}:
          Some{x <> xs}

# the bytes of a text of hex digit pairs (None: an odd count or a non-digit)
def sp_hex(s: String) -> Maybe<&2, List<&2, Nat>>:
  match s:
    case SNil{}:
      Some{Nil{}}
    case SCon{a, t}:
      match t:
        case SNil{}:
          None{}
        case SCon{b, u}:
          sp_cons(sp_pair(sp_digit(a), sp_digit(b)), sp_hex(u))

def sp_len64.is(b: Bool, bs: List<&2, Nat>) -> Maybe<&2, List<&2, Nat>>:
  match b:
    case True{}:
      Some{bs}
    case False{}:
      None{}

def sp_len64(m: Maybe<&2, List<&2, Nat>>) -> Maybe<&2, List<&2, Nat>>:
  match m:
    case None{}:
      None{}
    case Some{+bs}:
      sp_len64.is(Nat.is_eq(List.length(&2, Nat, bs), 32n), bs)

# R1: the token a text spells
def sp_token(s: String) -> Maybe<&2, List<&2, Nat>>:
  sp_len64(sp_hex(s))

def sp_shown.of(m: Maybe<&2, List<&2, Nat>>, e: Bool) -> Da.Shown:
  match m:
    case Some{bs}:
      Da.Hex{bs}
    case None{}:
      match e:
        case True{}:
          Da.Blank{}
        case False{}:
          Da.Junk{}

# R1
def sp_shown(x: Da.Said) -> Da.Shown:
  match x:
    case Da.Spoken{+s}:
      sp_shown.of(sp_token(s), String.is_empty(s))
    case Da.Overlong{}:
      Da.Junk{}

# R2: the code points of Rust's whitespace (char::is_whitespace)
def sp_spaces() -> List<&2, U32>:
  [9, 10, 11, 12, 13, 32, 133, 160, 5760, 8192, 8193, 8194, 8195, 8196, 8197, 8198, 8199, 8200, 8201, 8202, 8232, 8233, 8239, 8287, 12288]

def sp_in(+x: U32, xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(U32.is_eq(x, y), sp_in(x, rest))

def sp_space(c: Char) -> Bool:
  sp_in(Char.to_u32(c), sp_spaces())

def sp_rstrip.if(b: Bool, c: Char, t: String, r: String) -> String:
  match b:
    case True{}:
      SCon{c, t}
    case False{}:
      r

# s without its trailing whitespace: a char stays unless it and all after
# it are whitespace
def sp_rstrip(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      +r = sp_rstrip(t)
      sp_rstrip.if(Bool.not(Bool.and(sp_space(c), String.is_empty(r))), c, r, SNil{})

# s without its leading whitespace: the first char that is no whitespace
# and all after it
def sp_lstrip(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      sp_rstrip.if(Bool.not(sp_space(c)), c, t, sp_lstrip(t))

# R2
def sp_stored(f: Da.Disk) -> Maybe<&2, List<&2, Nat>>:
  match f:
    case Da.NoFile{}:
      None{}
    case Da.Unread{}:
      None{}
    case Da.Holds{s}:
      sp_token(sp_rstrip(sp_lstrip(s)))
    case Da.Huge{}:
      None{}

def sp_missing() -> String:
  "pairing needed: open the link that `eukhe dashboard` prints"

def sp_wrong() -> String:
  "this pairing link is not valid any more: open the link that `eukhe dashboard` prints"

def sp_unset() -> String:
  "the dashboard has no pairing token: restart `eukhe dashboard`"

# whether a token or a text is there
def sp_has(m: Maybe<&2, List<&2, Nat>>) -> Bool:
  Maybe.is_some(&2, List<&2, Nat>, m)

# The spelling of a request and of its reply, from the wire primitives
# (R6).

def sp_w_disk(f: Da.Disk, rest: String) -> String:
  match f:
    case Da.NoFile{}:
      Wr.put_nat(0n, rest)
    case Da.Unread{}:
      Wr.put_nat(1n, rest)
    case Da.Holds{s}:
      Wr.put_nat(2n, Wr.put_str(s, rest))
    case Da.Huge{}:
      Wr.put_nat(3n, rest)

def sp_w_said(x: Da.Said, rest: String) -> String:
  match x:
    case Da.Spoken{t}:
      Wr.put_nat(0n, Wr.put_str(t, rest))
    case Da.Overlong{}:
      Wr.put_nat(1n, rest)

def sp_w_first(x: Da.First, rest: String) -> String:
  match x:
    case Da.NoText{}:
      Wr.put_nat(0n, rest)
    case Da.NotPairing{}:
      Wr.put_nat(1n, rest)
    case Da.Pair{t}:
      Wr.put_nat(2n, sp_w_said(t, rest))

def sp_w_rotation(o: Da.Rotation) -> Nat:
  match o:
    case Da.KeepToken{}:
      0n
    case Da.RotateToken{}:
      1n

def sp_w_req(q: FDa.Req, rest: String) -> String:
  match q:
    case FDa.QToken{t}:
      Wr.put_nat(0n, sp_w_said(t, rest))
    case FDa.QStored{f}:
      Wr.put_nat(1n, sp_w_disk(f, rest))
    case FDa.QKeep{o, f, m}:
      Wr.put_nat(2n, Wr.put_nat(sp_w_rotation(o), sp_w_disk(f, Wr.put_nat(m, rest))))

def sp_w_bytes(bs: List<&2, Nat>) -> String:
  Wr.put_nat(0n, Wr.put_list(~Nat, ~Wr.put_nat, bs, ""))

def sp_w_token(x: Da.Shown) -> String:
  match x:
    case Da.Hex{bs}:
      sp_w_bytes(bs)
    case Da.Blank{}:
      Wr.put_nat(1n, "")
    case Da.Junk{}:
      Wr.put_nat(2n, "")

def sp_w_stored(m: Maybe<&2, List<&2, Nat>>) -> String:
  match m:
    case Some{bs}:
      sp_w_bytes(bs)
    case None{}:
      Wr.put_nat(1n, "")

def sp_w_keep(k: Da.Keep) -> Nat:
  match k:
    case Da.Mint{}:
      0n
    case Da.Reuse{}:
      1n
    case Da.Restrict{}:
      2n
    case Da.Unreadable{}:
      3n
    case Da.Tokenless{}:
      4n

# the reply Rust reads: the spelled choice of R1 and R2 (sp_shown,
# sp_stored), and of R5 as the model decides it (Da.keep, pinned by the
# dash_keep_* laws)
def sp_w_reply(q: FDa.Req) -> String:
  match q:
    case FDa.QToken{t}:
      sp_w_token(sp_shown(t))
    case FDa.QStored{f}:
      sp_w_stored(sp_stored(f))
    case FDa.QKeep{o, f, m}:
      Wr.put_nat(sp_w_keep(Da.keep(o, f, m)), "")

def sp_fit_disk(f: Da.Disk) -> Bool:
  match f:
    case Da.NoFile{}:
      True{}
    case Da.Unread{}:
      True{}
    case Da.Holds{s}:
      LawsBase.wire_fits(String.length(s))
    case Da.Huge{}:
      True{}

def sp_fit_said(x: Da.Said) -> Bool:
  match x:
    case Da.Spoken{t}:
      LawsBase.wire_fits(String.length(t))
    case Da.Overlong{}:
      True{}

def sp_fit_first(x: Da.First) -> Bool:
  match x:
    case Da.NoText{}:
      True{}
    case Da.NotPairing{}:
      True{}
    case Da.Pair{t}:
      sp_fit_said(t)

# every number and length of the request fits the wire
def sp_fit_req(q: FDa.Req) -> Bool:
  match q:
    case FDa.QToken{t}:
      sp_fit_said(t)
    case FDa.QStored{f}:
      sp_fit_disk(f)
    case FDa.QKeep{o, f, m}:
      Bool.and(sp_fit_disk(f), LawsBase.wire_fits(m))

# Laws: the choices
# -----------------

# LAW dash_token_spec (R1): what a presented text is: a token (its bytes),
# blank, or junk
# EXCLUDES: a 63- or 65-digit token, a signed or spaced digit pair read
#   as a byte (`u8::from_str_radix` takes "+a"), one case refused, bytes
#   misread (nibbles swapped), an empty text taken for a wrong token
law dash_token_spec:
  for +x: Da.Said
  {Da.shown(x) == sp_shown(x) : Da.Shown}

# LAW dash_stored_spec (R2): the token the file holds
# EXCLUDES: a file with a newline or spaces around the token refused, a
#   token with whitespace inside accepted, a missing or damaged file taken
#   for a token
law dash_stored_spec:
  for +f: Da.Disk
  {Da.stored(f) == sp_stored(f) : Maybe<&2, List<&2, Nat>>}

# LAW dash_gate_needs_pairing (R3): a first frame that is no pairing (no
# text in time, a binary frame, a text that is no pairing) or a pairing
# with an empty text is refused with "pairing needed", whatever the file
# holds and whatever Rust reported
# EXCLUDES: a socket opened, or told another text, without a pairing or on
#   an empty token
law dash_gate_needs_pairing:
  for +f: Da.Disk
  for +b: Bool
  {Da.gate(Da.NoText{}, f, b) == Da.Refuse{sp_missing()} : Da.Pass} & {Da.gate(Da.NotPairing{}, f, b) == Da.Refuse{sp_missing()} : Da.Pass} & {Da.gate(Da.Pair{Da.Spoken{""}}, f, b) == Da.Refuse{sp_missing()} : Da.Pass}

# LAW dash_gate_not_token (R1, R3): a pairing whose text is not empty and
# is no token (R1: sp_token), or too long for the wire, is refused with
# "not valid any more", whatever the file holds and whatever Rust reported
# EXCLUDES: a socket opened on a 63- or 65-digit, signed or spaced text;
#   such a text told "pairing needed" or "no pairing token"
law dash_gate_not_token:
  for +t: String
  for +f: Da.Disk
  for +b: Bool
  for junk: {sp_has(sp_token(t)) == False{} : Bool}
  for said: {String.is_empty(t) == False{} : Bool}
  {Da.gate(Da.Pair{Da.Spoken{t}}, f, b) == Da.Refuse{sp_wrong()} : Da.Pass} & {Da.gate(Da.Pair{Da.Overlong{}}, f, b) == Da.Refuse{sp_wrong()} : Da.Pass}

# LAW dash_gate_no_stored (R2, R3): a pairing that presents a token (R1)
# while the file holds none (R2: missing, unreadable, too long, or no
# token once trimmed) is refused with "no pairing token", whatever Rust
# reported
# EXCLUDES: a socket opened on a file with no token (a missing or damaged
#   file taken for an open door); the refusal told as a wrong link
law dash_gate_no_stored:
  for +t: String
  for +f: Da.Disk
  for +b: Bool
  for token: {sp_has(sp_token(t)) == True{} : Bool}
  for none: {sp_has(sp_stored(f)) == False{} : Bool}
  {Da.gate(Da.Pair{Da.Spoken{t}}, f, b) == Da.Refuse{sp_unset()} : Da.Pass}

# LAW dash_gate_token_stored (R1-R3): a pairing that presents a token (R1)
# while the file holds one (R2) opens the socket when Rust found both
# equal, and is refused with "not valid any more" when it did not
# EXCLUDES: a socket opened on a token Rust found different (an old link
#   after a rotation); a valid tab refused its pairing
law dash_gate_token_stored:
  for +t: String
  for +f: Da.Disk
  for token: {sp_has(sp_token(t)) == True{} : Bool}
  for holds: {sp_has(sp_stored(f)) == True{} : Bool}
  {Da.gate(Da.Pair{Da.Spoken{t}}, f, True{}) == Da.Admit{} : Da.Pass} & {Da.gate(Da.Pair{Da.Spoken{t}}, f, False{}) == Da.Refuse{sp_wrong()} : Da.Pass}

# LAW dash_frame_stored (R2, R4): while the file, read at the frame, holds
# a token (R2), a later frame runs when Rust found it equal to the
# socket's token, and is refused with "not valid any more" when it did not
# EXCLUDES: a frame run after a rotation (Rust's comparison failed); a
#   frame of a current tab refused
law dash_frame_stored:
  for +f: Da.Disk
  for holds: {sp_has(sp_stored(f)) == True{} : Bool}
  {Da.frame(f, True{}) == Da.Admit{} : Da.Pass} & {Da.frame(f, False{}) == Da.Refuse{sp_wrong()} : Da.Pass}

# LAW dash_frame_no_stored (R2, R4): when the file, read at the frame,
# holds no token (missing, unreadable, too long, damaged), a later frame is
# refused with "no pairing token", whatever Rust reported
# EXCLUDES: a frame run with the file gone or damaged
law dash_frame_no_stored:
  for +f: Da.Disk
  for +b: Bool
  for none: {sp_has(sp_stored(f)) == False{} : Bool}
  {Da.frame(f, b) == Da.Refuse{sp_unset()} : Da.Pass}

# LAW dash_keep_mints (R5): `eukhe dashboard` stores a new token when it
# rotates, whatever the file and its mode, and when no file exists
# EXCLUDES: a rotation that keeps the old token; a missing file an error
law dash_keep_mints:
  for +f: Da.Disk
  for +m: Nat
  {Da.keep(Da.RotateToken{}, f, m) == Da.Mint{} : Da.Keep} & {Da.keep(Da.KeepToken{}, Da.NoFile{}, m) == Da.Mint{} : Da.Keep}

# LAW dash_keep_fails (R2, R5): without a rotation, an unreadable file
# fails as unreadable, and a file that holds no token (R2: no token once
# trimmed, or too long for the wire) fails as tokenless, whatever its
# mode: the file is never replaced unasked
# EXCLUDES: a damaged file silently replaced by a new token (every paired
#   tab locked out), an unreadable file taken for a missing one
law dash_keep_fails:
  for +s: String
  for +m: Nat
  for none: {sp_has(sp_stored(Da.Holds{s})) == False{} : Bool}
  {Da.keep(Da.KeepToken{}, Da.Unread{}, m) == Da.Unreadable{} : Da.Keep} & {Da.keep(Da.KeepToken{}, Da.Holds{s}, m) == Da.Tokenless{} : Da.Keep} & {Da.keep(Da.KeepToken{}, Da.Huge{}, m) == Da.Tokenless{} : Da.Keep}

# LAW dash_keep_private_reused (R5): without a rotation, a file that holds
# a token (R2) and whose mode gives the group and others no bit (a mode of
# 64 u: any owner bits and file type above the low six bits) is used as it
# is
# EXCLUDES: a private file chmodded or replaced; a mode test that looks at
#   the owner's bits or the file type
law dash_keep_private_reused:
  for +s: String
  for +u: Nat
  for holds: {sp_has(sp_stored(Da.Holds{s})) == True{} : Bool}
  {Da.keep(Da.KeepToken{}, Da.Holds{s}, Nat.mul(u, 64n)) == Da.Reuse{} : Da.Keep}

# LAW dash_keep_open_narrowed (R5): without a rotation, a file that holds
# a token (R2) and whose mode gives the group or others any bit (a mode of
# 64 u + 8 g + o, g and o octal digits, not both 0: chmod(2)'s group and
# other bits) is used and narrowed to 0600
# EXCLUDES: a group- or world-readable token file left as it is; a test
#   of only the others' bits or only the read bits
law dash_keep_open_narrowed:
  for +s: String
  for +u: Nat
  for +g: Nat
  for +o: Nat
  for holds: {sp_has(sp_stored(Da.Holds{s})) == True{} : Bool}
  for gd: {Nat.is_lt(g, 8n) == True{} : Bool}
  for od: {Nat.is_lt(o, 8n) == True{} : Bool}
  for open: {Nat.is_eq(Nat.add(g, o), 0n) == False{} : Bool}
  {Da.keep(Da.KeepToken{}, Da.Holds{s}, Nat.add(Nat.mul(u, 64n), Nat.add(Nat.mul(g, 8n), o))) == Da.Restrict{} : Da.Keep}

# LAW dash_token_example (R1, R2): anchor: tokens in both cases, an empty
# text, a 63- and a 65-digit text, a signed pair, a stored token with its newline and a
# stored one with a space inside
# EXCLUDES: a spec that accepts any of the near misses
law dash_token_example:
  {[Da.shown(Da.Spoken{"00112233445566778899aabbccddeeff00112233445566778899AABBCCDDEEFF"}), Da.shown(Da.Spoken{""}), Da.shown(Da.Spoken{"0011223344556677889900112233445566778899aabbccddeeff0011223344556"}), Da.shown(Da.Spoken{"00112233445566778899001122334455667788990aabbccddeeff0011223344"}), Da.shown(Da.Spoken{"+a112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"})] == [Da.Hex{[0n, 17n, 34n, 51n, 68n, 85n, 102n, 119n, 136n, 153n, 170n, 187n, 204n, 221n, 238n, 255n, 0n, 17n, 34n, 51n, 68n, 85n, 102n, 119n, 136n, 153n, 170n, 187n, 204n, 221n, 238n, 255n]}, Da.Blank{}, Da.Junk{}, Da.Junk{}, Da.Junk{}] : List<&2, Da.Shown>} & {[Maybe.is_some(&2, List<&2, Nat>, Da.stored(Da.Holds{" 00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff\n"})), Maybe.is_some(&2, List<&2, Nat>, Da.stored(Da.Holds{"00112233445566778899aabbccddeeff 00112233445566778899aabbccddeeff"}))] == [True{}, False{}] : List<&2, Bool>}

# Laws: the entry (R6)
# --------------------

# LAW dash_entry_answers (R6): the dash entry answers every request Rust
# spells, every number and length within the wire, with the spelled
# choice of R1, R2 (sp_shown, sp_stored) and of the model's R5 choice
# (Da.keep)
# EXCLUDES: a field misread, swapped or dropped; a request answered with
#   another request's choice, a default, or a reply spelled otherwise
law dash_entry_answers:
  for +q: FDa.Req
  for h: {sp_fit_req(q) == True{} : Bool}
  {FDa.ffi(sp_w_req(q, "")) == sp_w_reply(q) : String}

# LAW dash_entry_reads (R6): the entry's decoder reads a spelled request
# back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law dash_entry_reads:
  for +q: FDa.Req
  for +rest: String
  for h: {sp_fit_req(q) == True{} : Bool}
  {FDa.get_req(sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FDa.Req>}

# LAW dash_entry_exact (R6): every input the entry does not answer with
# the error form is a spelled request that fits the wire
# EXCLUDES: a choice made on input that is no request (an unknown tag, a
#   malformed field, input left over)
law dash_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FDa.ffi(s)) == False{} : Bool}
  exs r: FDa.Req
  {s == sp_w_req(r, "") : String} & {sp_fit_req(r) == True{} : Bool}

# LAW dash_entry_refuses (R6): every error the entry answers is exactly
# `E dash: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law dash_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FDa.ffi(s)) == True{} : Bool}
  {FDa.ffi(s) == Wr.err("dash: malformed request") : String}

# LAW dash_entry_example (R6): anchor: the wire strings Rust sends and the
# replies it reads; an unknown tag and input left over
# EXCLUDES: tags in another order, a field order other than Rust's
law dash_entry_example:
  {[FDa.ffi("0,0,0,"), FDa.ffi("0,0,3,xyz"), FDa.ffi("0,1,"), FDa.ffi("1,1,"), FDa.ffi("2,0,2,65,00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff\n420,"), FDa.ffi("2,1,1,0,"), FDa.ffi("3,"), FDa.ffi("1,1,x")] == ["1,", "2,", "2,", "1,", "2,", "0,", Wr.err("dash: malformed request"), Wr.err("dash: malformed request")] : List<&2, String>}
