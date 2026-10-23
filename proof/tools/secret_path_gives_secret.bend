# eukhe: the proof of LAW secret_path_gives_secret

import Base
import ../../bend/tools.bend as Tl
import ../../LAWS.bend as Laws
import ./base.bend as LA

# a part that names a secret path makes some part of the step name one
def ps.some_secret(+pre: List<&2, Tl.Part>, +p: Tl.Part, +post: List<&2, Tl.Part>, named: {Tl.Part.secret(p) == True{} : Bool}) -> {Tl.parts.secret(List.append(&2, Tl.Part, pre, p <> post)) == True{} : Bool}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, Tl.Part.secret(p), True{}, named) : {Bool.or(_, Tl.parts.secret(post)) == True{} : Bool}
      {==}
    case q <> pr:
      LA.shell.ps.or_tr(Tl.Part.secret(q), Tl.parts.secret(List.append(&2, Tl.Part, pr, p <> post)), ps.some_secret(pr, p, post, named))

def ps.secret_path_gives_secret(+pre: List<&2, Tl.Part>, +p: Tl.Part, +post: List<&2, Tl.Part>, named: {Tl.Part.secret(p) == True{} : Bool}) -> {Tl.elem(Tl.join(Tl.parts.effs(List.append(&2, Tl.Part, pre, p <> post))), 6n) == True{} : Bool}:
  +all = List.append(&2, Tl.Part, pre, p <> post)
  Equal.trans(Bool, Tl.elem(Tl.join(Tl.parts.effs(all)), 6n), Tl.parts.secret(all), True{}, LA.ps.secret_iff(all), ps.some_secret(pre, p, post, named))

def Laws.secret_path_gives_secret(pre, p, post, named):
  ps.secret_path_gives_secret(pre, p, post, named)
