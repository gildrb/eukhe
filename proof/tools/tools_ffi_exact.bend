# eukhe: the proof of LAW tools_ffi_exact
# The entry's segment table is the spec's; its resolution is the spec's
# (path_resolve_spec); its reply speller is the spec's.

import Base
import ../../bend/ffi_tools.bend as FTl
import ../../bend/tools.bend as Tl
import ../../bend/wire.bend as Wr
import ../../laws/tools.bend as Tools
import ./path_resolve_spec.bend as PPathResolveSpec

def tfe.seg(c: Nat) -> {FTl.seg(c) == Tools.tp_seg(c) : Tl.Seg}:
  match c:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+n:
          {==}

def tfe.segs(cs: List<&2, Nat>) -> {FTl.segs(cs) == Tools.tp_segs(cs) : List<&2, Tl.Seg>}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +rest:
      %Equal.sym(List<&2, Tl.Seg>, FTl.segs(rest), Tools.tp_segs(rest), tfe.segs(rest)) : {FTl.seg(c) <> _ == Tools.tp_seg(c) <> Tools.tp_segs(rest) : List<&2, Tl.Seg>}
      %Equal.sym(Tl.Seg, FTl.seg(c), Tools.tp_seg(c), tfe.seg(c)) : {_ <> Tools.tp_segs(rest) == Tools.tp_seg(c) <> Tools.tp_segs(rest) : List<&2, Tl.Seg>}
      {==}

def tfe.reply(m: Maybe<&2, List<&2, Nat>>) -> {FTl.put_names(m, "") == Tools.tp_reply(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{ns}:
      {==}

def tfe.end(whole: Bool, +cs: List<&2, Nat>) -> {FTl.reply(whole, FTl.segs(cs)) == Tools.tp_entry.end(whole, cs) : String}:
  match whole:
    case True{}:
      +X = Tools.tp_segs(cs)
      %Equal.sym(List<&2, Tl.Seg>, FTl.segs(cs), X, tfe.segs(cs)) : {FTl.put_names(Tl.resolve(_), "") == Tools.tp_reply(Tools.tp_resolve(X)) : String}
      %Equal.sym(Maybe<&2, List<&2, Nat>>, Tl.resolve(X), Tools.tp_resolve(X), Tools.path_resolve_spec(X)) : {FTl.put_names(_, "") == Tools.tp_reply(Tools.tp_resolve(X)) : String}
      tfe.reply(Tools.tp_resolve(X))
    case False{}:
      {==}

def tfe.read(r: Wr.Dec<List<&2, Nat>>) -> {FTl.answer(FTl.get_req.of(r)) == Tools.tp_entry.read(r) : String}:
  match r:
    case Wr.Got{cs, s}:
      tfe.end(Wr.end(s), cs)
    case Wr.Bad{}:
      {==}

def Tools.tools_ffi_exact(s):
  tfe.read(Wr.get_list(~Nat, ~Wr.get_nat, s))
