# eukhe: the proof of LAW proto_one_reply_each

import Base
import ../../bend/sandbox.bend as Sb
import ../../laws/sandbox.bend as Sandbox

# 1. The protocol
# ---------------

def px.ids_add(g: Bool, +f: Sb.Frame, h: Sb.Host) -> {Sb.Frame.id(f) <> Sb.reply.ids(Sb.Host.replies(h)) == Sb.reply.ids(Sb.Host.replies(Sb.host.add(g, f, h))) : List<&2, Nat>}:
  match g:
    case True{}:
      match h:
        case Sb.Host{rs, xs}:
          {==}
    case False{}:
      match h:
        case Sb.Host{rs, xs}:
          {==}

def px.proto_one_reply_each(+fs: List<&2, Sb.Frame>, +max: Nat, +allowed: List<&2, Nat>) -> {Sb.reply.ids(Sb.Host.replies(Sb.serve(fs, max, allowed))) == Sb.frame.ids(fs) : List<&2, Nat>}:
  match fs:
    case Nil{}:
      {==}
    case f <> rest:
      %px.ids_add(Sb.accepts(max, allowed, f), f, Sb.serve(rest, max, allowed)) : {_ == Sb.Frame.id(f) <> Sb.frame.ids(rest) : List<&2, Nat>}
      %px.proto_one_reply_each(rest, max, allowed) : {Sb.Frame.id(f) <> Sb.reply.ids(Sb.Host.replies(Sb.serve(rest, max, allowed))) == Sb.Frame.id(f) <> _ : List<&2, Nat>}
      {==}

# (S3) The host and the sandbox

def Sandbox.proto_one_reply_each(fs, max, allowed):
  px.proto_one_reply_each(fs, max, allowed)
