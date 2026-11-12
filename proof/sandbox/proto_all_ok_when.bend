# eukhe: the proof of LAW proto_all_ok_when
#
# PROOF: by induction on the frames, deciding the first frame's acceptance
# (pao.at): a refused first frame is the witness; an accepted one leaves
# the rest not all accepted (pao.and_r), whose witness gets the first frame
# in front. No frames are all accepted.

import Base
import ../../bend/sandbox.bend as Sb
import ../../laws/sandbox.bend as Sandbox
import ./base.bend as LA

def pao.G(fs: List<&2, Sb.Frame>, +max: Nat, +allowed: List<&2, Nat>) -> Type:
  &pre: List<&2, Sb.Frame> -> &f: Sb.Frame -> &post: List<&2, Sb.Frame> -> {fs == List.append(&2, Sb.Frame, pre, f <> post) : List<&2, Sb.Frame>} & {Sb.accepts(max, allowed, f) == False{} : Bool}

# the acceptance of the first frame of fs (True for none)
def pao.at(fs: List<&2, Sb.Frame>, +max: Nat, +allowed: List<&2, Nat>) -> Bool:
  match fs:
    case Nil{}:
      True{}
    case g <> rest:
      Sb.accepts(max, allowed, g)

# an and that fails with a true left side fails by its right side
def pao.and_r(a: Bool, -b: Bool, ea: {a == True{} : Bool}, h: {Bool.and(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LA.px.absurdF({b == False{} : Bool}, ea)

def pao.cons(+g: Sb.Frame, +rest: List<&2, Sb.Frame>, +max: Nat, +allowed: List<&2, Nat>, r: pao.G(rest, max, allowed)) -> pao.G(g <> rest, max, allowed):
  (pre, r1) = r
  (f, r2) = r1
  (post, r3) = r2
  (e1, e2) = r3
  (g <> pre, (f, (post, (Equal.cong(List<&2, Sb.Frame>, List<&2, Sb.Frame>, z => g <> z, rest, List.append(&2, Sb.Frame, pre, f <> post), e1), e2))))

def pao.go(fs: List<&2, Sb.Frame>, +max: Nat, +allowed: List<&2, Nat>, t: Bool, et: {pao.at(fs, max, allowed) == t : Bool}, h: {Sb.all_ok(fs, max, allowed) == False{} : Bool}) -> pao.G(fs, max, allowed):
  match fs:
    case Nil{}:
      LA.px.absurdF(pao.G(Nil{}, max, allowed), Equal.sym(Bool, True{}, False{}, h))
    case +g <> +rest:
      match t:
        case False{}:
          (Nil{}, (g, (rest, ({==}, et))))
        case True{}:
          pao.cons(g, rest, max, allowed, pao.go(rest, max, allowed, pao.at(rest, max, allowed), {==}, pao.and_r(Sb.accepts(max, allowed, g), Sb.all_ok(rest, max, allowed), et, h)))

def Sandbox.proto_all_ok_when(fs, max, allowed, h):
  pao.go(fs, max, allowed, pao.at(fs, max, allowed), {==}, h)
