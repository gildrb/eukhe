# eukhe: the laws of area mcp_url

import Base
import ../bend/mcp_url.bend as Mu
import ../bend/ffi_mcp_url.bend as FMu
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (D1) A URL host the MCP catalog refuses
# ---------------------------------------
# bend/mcp_url.bend, run as the compiled core by bend/ffi_mcp_url.bend
# (eukhe-bend rules/mcp_url.rs; asked by eukhe-core's MCP catalog validator
# for the host of every HTTPS endpoint, as the url crate gives it). Every
# input is free: any host text.
#
# R1: the host is read without all its leading `[` and then all its
#     trailing `]`, its ASCII letters lowercased (Rust
#     `trim_start_matches`, `trim_end_matches`, `to_ascii_lowercase`).
# R2: `localhost`, and a name that ends with `.localhost`, is refused.
# R3: a part is read as a Rust u32 (`str::parse::<u32>`): an optional
#     leading `+` with something after it, then decimal digits only (at
#     least one), worth at most 4294967295 (leading zeros allowed).
#     Without its leading zeros: at most 3 digits is the value (an octet
#     when at most 255); 4 to 9 digits, or 10 digits at most 4294967295,
#     is past 255; else no u32.
# R4: a host that splits at `.` into exactly four parts is IPv4 when the
#     parts, read in order up to the first that is no octet (0-255), are
#     octets: the first part past 255 refuses the host; the first part
#     that is no u32 makes it no IPv4 address. An IPv4 address is refused
#     when its first octet is 0, 10 or 127, or its first two are
#     169.254, 172.16-31 or 192.168.
# R5: another host that holds `:` is IPv6. It splits at its first `::`
#     into the text before and after (no `::`: one text). A side's parts
#     are its `:`-separated pieces (none for an empty side). Without `::`
#     there must be exactly 8 parts, none empty; with `::` at most 7 in
#     all, the missing ones zero words between the sides. A part is a word:
#     empty is 0, else a Rust u16 in radix 16 (`u16::from_str_radix`: an
#     optional leading `+` with something after it, then hex digits, at
#     most 4 without leading zeros). A malformed address is refused.
# R6: an IPv6 address is refused when it is :: or ::1, when it is
#     IPv4-mapped (five zero words, then ffff) and its last two words as
#     four octets are in R4's ranges, when its first word is in fe80-febf
#     (fe80::/10) or fc00-fdff (fc00::/7).
# R7: any other host passes.
# R8: the entry answers each request Rust writes (the host, its length
#     within the wire) with whether R1-R7 refuse it, reads exactly the
#     request and nothing after it, and answers any other input with the
#     exact error form `E mcp_url: malformed request`.
#
# Changed from the Rust it replaced (eukhe-core mcp/url_checks.rs): its
# IPv4-mapped test asked for six zero words and a sixth word ffff at once,
# so it never held, and `[::ffff:7f00:1]` (the url crate's spelling of
# `[::ffff:127.0.0.1]`) passed. R6 checks the mapped address as its
# comment meant.

# Spec helpers
# ------------

# R4: the dotted quad of octets a, b, c, d, each in decimal (Base Nat.show)
def mu_quad(a: Nat, b: Nat, c: Nat, d: Nat) -> String:
  String.append(Nat.show(a), SCon{'.', String.append(Nat.show(b), SCon{'.', String.append(Nat.show(c), SCon{'.', Nat.show(d)})})})

# R4: 2^n
def mu_pow2(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+p:
      Nat.mul(2n, mu_pow2(p))

# R4: the first two octets a, b lie in the block of network o1.o2.0.0 with
# prefix length len (8 to 16): their first len bits are the network's
def mu_block(+a: Nat, +b: Nat, o1: Nat, +o2: Nat, +len: Nat) -> Bool:
  +k = mu_pow2(Nat.sub(16n, len))
  Bool.and(Nat.is_eq(a, o1), Bool.or(Nat.is_le(len, 8n), Nat.is_eq(Nat.div(b, k), Nat.div(o2, k))))

# R4: the blocks R4 refuses, as RFC 6890's special-purpose address registry
# (section 2.2.2) lists them: 0.0.0.0/8 this network (RFC 1122), 10.0.0.0/8
# private-use (RFC 1918), 127.0.0.0/8 loopback (RFC 1122), 169.254.0.0/16
# link local (RFC 3927), 172.16.0.0/12 and 192.168.0.0/16 private-use (RFC
# 1918)
def mu_v4_reserved(+a: Nat, +b: Nat) -> Bool:
  Bool.or(mu_block(a, b, 0n, 0n, 8n), Bool.or(mu_block(a, b, 10n, 0n, 8n), Bool.or(mu_block(a, b, 127n, 0n, 8n), Bool.or(mu_block(a, b, 169n, 254n, 16n), Bool.or(mu_block(a, b, 172n, 16n, 12n), mu_block(a, b, 192n, 168n, 16n))))))

# R6: the char of a hex digit (lowercase)
def mu_hex_char(d: Nat) -> Char:
  match d:
    case 0n:
      '0'
    case 1n:
      '1'
    case 2n:
      '2'
    case 3n:
      '3'
    case 4n:
      '4'
    case 5n:
      '5'
    case 6n:
      '6'
    case 7n:
      '7'
    case 8n:
      '8'
    case 9n:
      '9'
    case 10n:
      'a'
    case 11n:
      'b'
    case 12n:
      'c'
    case 13n:
      'd'
    case 14n:
      'e'
    case 15n+p:
      'f'

# R6: a byte as two hex digits (a 16-bit word is two of them)
def mu_hex2(+n: Nat) -> String:
  SCon{mu_hex_char(Nat.div(n, 16n)), SCon{mu_hex_char(Nat.mod(n, 16n)), SNil{}}}

# R7: no char of s is c
def mu_lacks(s: String, +c: Char) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{x, t}:
      Bool.and(Bool.not(Char.is_eq(x, c)), mu_lacks(t, c))

# R8: the spelling of a request and its reply
def mu_w_req(h: String, rest: String) -> String:
  Wr.put_str(h, rest)

# the model's verdict on h, spelled (the laws of R1-R7 pin the verdict)
def mu_w_reply(h: String) -> String:
  Wr.put_bool(Mu.refused(h), "")

# Laws: the check (R1-R7)
# -----------------------
# R5's malformed addresses, R6's ::, ::1 and IPv4-mapped ranges, and the
# IPv6 addresses that pass are anchored only (mcp_url_refuses_example,
# mcp_url_passes_example): a law over printed words would have to check
# every 16-bit word one by one.

# LAW mcp_url_open_bracket (R1): a `[` before any host changes nothing of its verdict
# EXCLUDES: a leading bracket kept, only one leading bracket dropped
law mcp_url_open_bracket:
  for +h: String
  {Mu.refused(SCon{'[', h}) == Mu.refused(h) : Bool}

# LAW mcp_url_close_bracket (R1): a `]` after any host changes nothing of its verdict
# EXCLUDES: a trailing bracket kept, only one trailing bracket dropped
law mcp_url_close_bracket:
  for +h: String
  {Mu.refused(String.append(h, "]")) == Mu.refused(h) : Bool}

# LAW mcp_url_case (R1): two hosts that differ in one char only, the two chars no bracket and the same once ASCII-lowercased (Base Char.to_lower), get the same verdict
# EXCLUDES: a case-sensitive check (`LOCALHOST` or `FE80::1` passed), a
#   lowercasing that changes other chars
law mcp_url_case:
  for +a: String
  for +u: Char
  for +l: Char
  for +b: String
  for same: {Char.to_lower(u) == Char.to_lower(l) : Char}
  for nu: {Bool.or(Char.is_eq(u, '['), Char.is_eq(u, ']')) == False{} : Bool}
  for nl: {Bool.or(Char.is_eq(l, '['), Char.is_eq(l, ']')) == False{} : Bool}
  {Mu.refused(String.append(a, SCon{u, b})) == Mu.refused(String.append(a, SCon{l, b})) : Bool}

# LAW mcp_url_localhost (R2): every host that ends with `.localhost` is refused, whatever comes before it
# EXCLUDES: only `localhost` itself refused, a subdomain of localhost
#   passed, the suffix matched case-sensitively after brackets
law mcp_url_localhost:
  for +x: String
  {Mu.refused(String.append(x, ".localhost")) == True{} : Bool}

# LAW mcp_url_v4_table (R3, R4, R7): a dotted quad a.b.c.d of octets (each 0-255, in decimal) is refused exactly when a.b lies in one of R4's RFC 6890 blocks (mu_v4_reserved)
# EXCLUDES: a wrong range bound (172.15 or 172.32 refused, 172.31
#   passed), a missing block, a public address refused, the third or
#   fourth octet read into the decision, an octet misread
law mcp_url_v4_table:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for oct: {Bool.and(Nat.is_le(a, 255n), Bool.and(Nat.is_le(b, 255n), Bool.and(Nat.is_le(c, 255n), Nat.is_le(d, 255n)))) == True{} : Bool}
  {Mu.refused(mu_quad(a, b, c, d)) == mu_v4_reserved(a, b) : Bool}

# LAW mcp_url_v6_link_local (R5, R6): a host whose first word (four hex digits, then `:`) lies in fe80::/10 (RFC 4291 section 2.5.6: bytes fe, then 80 + k, k below 2^6) is refused, whatever follows the `:`
# EXCLUDES: fe80::/10 passed, a narrower range (fe80::/16 only), the
#   first word read past its `:`
law mcp_url_v6_link_local:
  for +k: Nat
  for +rest: String
  for blk: {Nat.is_lt(k, 64n) == True{} : Bool}
  {Mu.refused(String.append(mu_hex2(254n), String.append(mu_hex2(Nat.add(128n, k)), SCon{':', rest}))) == True{} : Bool}

# LAW mcp_url_v6_unique_local (R5, R6): a host whose first word (four hex digits, then `:`) lies in fc00::/7 (RFC 4193 section 3.1: bytes fc + i, i below 2, then any byte j) is refused, whatever follows the `:`
# EXCLUDES: fc00::/7 passed, fd00::/8 only
law mcp_url_v6_unique_local:
  for +i: Nat
  for +j: Nat
  for +rest: String
  for blk: {Bool.and(Nat.is_lt(i, 2n), Nat.is_le(j, 255n)) == True{} : Bool}
  {Mu.refused(String.append(mu_hex2(Nat.add(252n, i)), String.append(mu_hex2(j), SCon{':', rest}))) == True{} : Bool}

# LAW mcp_url_name_passes (R7): a lowercase host with no `[`, `]` or `:`, that is not `localhost` and does not end with `.localhost`, and whose `.`-separated parts are not exactly four, passes
# EXCLUDES: a public name refused (a name read as an address, a default
#   refusal)
law mcp_url_name_passes:
  for +x: String
  for plain: {Bool.and(mu_lacks(x, '['), Bool.and(mu_lacks(x, ']'), mu_lacks(x, ':'))) == True{} : Bool}
  for lower: {String.to_lower(x) == x : String}
  for named: {Bool.or(String.eq(x, "localhost"), String.ends_with(x, ".localhost")) == False{} : Bool}
  for parts: {Nat.is_eq(List.length(&2, String, String.split(x, '.')), 4n) == False{} : Bool}
  {Mu.refused(x) == False{} : Bool}

# Examples
# --------

# LAW mcp_url_refuses_example (R1-R6): anchor: hosts Rust refused, and the
# mapped loopback the fix refuses
# EXCLUDES: a spec that drifts from the Rust it replaced
law mcp_url_refuses_example:
  {[Mu.refused("localhost"), Mu.refused("LocalHost"), Mu.refused("a.localhost"), Mu.refused("127.0.0.1"), Mu.refused("10.0.0.5"), Mu.refused("0.0.0.0"), Mu.refused("172.16.1.2"), Mu.refused("192.168.0.1"), Mu.refused("169.254.1.1"), Mu.refused("999.1.1.1"), Mu.refused("[::1]"), Mu.refused("[::]"), Mu.refused("[fe80::1]"), Mu.refused("[fc00::1]"), Mu.refused("[fd12::1]"), Mu.refused("[zz::1]"), Mu.refused("[::ffff:7f00:1]")] == [True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}, True{}] : List<&2, Bool>}

# LAW mcp_url_passes_example (R3-R7): anchor: hosts Rust passed
# EXCLUDES: a spec that drifts from the Rust it replaced
law mcp_url_passes_example:
  {[Mu.refused("mcp.linear.app"), Mu.refused("8.8.8.8"), Mu.refused("172.32.0.1"), Mu.refused("[2606:4700::6810:85e5]"), Mu.refused("[2001:db8::1]"), Mu.refused("x.999.1.1"), Mu.refused("+8.8.8.8"), Mu.refused("[::ffff:808:808]")] == [False{}, False{}, False{}, False{}, False{}, False{}, False{}, False{}] : List<&2, Bool>}

# Laws: the entry (R8)
# --------------------

# LAW mcp_url_entry_answers (R8): the entry answers every host Rust
# spells, its length within the wire, with the model's verdict (pinned by
# the laws of R1-R7)
# EXCLUDES: another verdict, a verdict spelled otherwise, a default
law mcp_url_entry_answers:
  for +h: String
  for fit: {LawsBase.wire_fits(String.length(h)) == True{} : Bool}
  {FMu.ffi(mu_w_req(h, "")) == mu_w_reply(h) : String}

# LAW mcp_url_entry_exact (R8): every input the entry does not answer with
# the error form is a spelled host that fits the wire
# EXCLUDES: a verdict on input that is no request (a short host, input
#   left over)
law mcp_url_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FMu.ffi(s)) == False{} : Bool}
  exs h: String
  {s == mu_w_req(h, "") : String} & {LawsBase.wire_fits(String.length(h)) == True{} : Bool}

# LAW mcp_url_entry_refuses (R8): every error the entry answers is exactly
# `E mcp_url: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law mcp_url_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FMu.ffi(s)) == True{} : Bool}
  {FMu.ffi(s) == Wr.err("mcp_url: malformed request") : String}

# LAW mcp_url_entry_left_over (R8): a spelled host followed by more input
# answers the error form
# EXCLUDES: the input after the request ignored or read into the host
law mcp_url_entry_left_over:
  for +h: String
  for +c: Char
  for +t: String
  for fit: {LawsBase.wire_fits(String.length(h)) == True{} : Bool}
  {FMu.ffi(mu_w_req(h, SCon{c, t})) == Wr.err("mcp_url: malformed request") : String}

# LAW mcp_url_entry_example (R8): anchor: the wire strings Rust sends and
# the replies it reads; input left over and a malformed request
# EXCLUDES: another spelling of a request or of a reply
law mcp_url_entry_example:
  {[FMu.ffi("9,127.0.0.1"), FMu.ffi("7,8.8.8.8"), FMu.ffi("7,8.8.8.8x"), FMu.ffi("x")] == ["T", "F", Wr.err("mcp_url: malformed request"), Wr.err("mcp_url: malformed request")] : List<&2, String>}
