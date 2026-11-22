# eukhe: the proof of LAW secret_path_gives_secret
#
# PROOF: the part's effects start with 6, and an element of one part is
# an element of the step (LA.ps.step_holds_every_part).

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./base.bend as LA

# the effects of the parts pre ++ p <> post are those of pre, then p's,
# then those of post
def ps.effs_app(pre: List<&2, Tl.Part>, +p: Tl.Part, +post: List<&2, Tl.Part>) -> {Tl.parts.effs(List.append(&2, Tl.Part, pre, p <> post)) == List.append(&2, List<&2, Nat>, Tl.parts.effs(pre), Tl.part.effs(p) <> Tl.parts.effs(post)) : List<&2, List<&2, Nat>>}:
  match pre:
    case Nil{}:
      {==}
    case +q <> +pr:
      %ps.effs_app(pr, p, post) : {Tl.part.effs(q) <> Tl.parts.effs(List.append(&2, Tl.Part, pr, p <> post)) == Tl.part.effs(q) <> _ : List<&2, List<&2, Nat>>}
      {==}

def ps.secret_path_gives_secret(+pre: List<&2, Tl.Part>, +o: List<&2, Nat>, +post: List<&2, Tl.Part>) -> {Tl.elem(Tl.join(Tl.parts.effs(List.append(&2, Tl.Part, pre, Tl.Part{o, True{}} <> post))), 6n) == True{} : Bool}:
  %Equal.sym(List<&2, List<&2, Nat>>, Tl.parts.effs(List.append(&2, Tl.Part, pre, Tl.Part{o, True{}} <> post)), List.append(&2, List<&2, Nat>, Tl.parts.effs(pre), Tl.part.effs(Tl.Part{o, True{}}) <> Tl.parts.effs(post)), ps.effs_app(pre, Tl.Part{o, True{}}, post)) : {Tl.elem(Tl.join(_), 6n) == True{} : Bool}
  LA.ps.step_holds_every_part(Tl.parts.effs(pre), Tl.part.effs(Tl.Part{o, True{}}), Tl.parts.effs(post), 6n, {==})

def Tools.secret_path_gives_secret(pre, o, post):
  ps.secret_path_gives_secret(pre, o, post)
