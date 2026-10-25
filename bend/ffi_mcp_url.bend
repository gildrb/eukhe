# ffi_mcp_url: the entry of the compiled Bend core for whether a URL host
# is a literal loopback, private, link-local or unspecified address or a
# `localhost` name (bend/mcp_url.bend; Rust: eukhe-bend rules/mcp_url.rs).
# Grammar: crates/eukhe-bend/WIRE.md.
#
#   request  the host (String)
#   reply    refused (Bool)
#
# Malformed input, or input left after the request, answers
# `E mcp_url: malformed request`, never a default.
# Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./mcp_url.bend as Mu

def ffi.done(h: String, end: Bool) -> String:
  match end:
    case True{}:
      W.put_bool(Mu.refused(h), "")
    case False{}:
      W.err("mcp_url: malformed request")

def ffi.got(r: W.Dec<String>) -> String:
  match r:
    case W.Got{h, +s}:
      ffi.done(h, W.end(s))
    case W.Bad{}:
      W.err("mcp_url: malformed request")

# the entry: decode the host, answer whether it is refused
def ffi(input: String) -> String:
  ffi.got(W.get_str(input))
