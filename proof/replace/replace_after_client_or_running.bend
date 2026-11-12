# eukhe: the proof of LAW replace_after_client_or_running: with no daemon
# the client's build starts; on a running b the verdict picks the client's
# build (Replace) or b (Keep) (rac.pick)

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace

def rac.pick(v: Rp.Verdict, -c: Rp.Build, -b: Rp.Build) -> {Rp.after.put(v, c, b) == c : Rp.Build} | {Some{Rp.after.put(v, c, b)} == Some{b} : Maybe<&2, Rp.Build>}:
  match v:
    case Rp.Replace{}:
      Inl{{==}}
    case Rp.Keep{r}:
      Inr{{==}}

def rac.go(+c: Rp.Build, +k: Rp.Caller, d: Maybe<&2, Rp.Build>) -> {Rp.after(Rp.Start{c, k}, d) == c : Rp.Build} | {Some{Rp.after(Rp.Start{c, k}, d)} == d : Maybe<&2, Rp.Build>}:
  match d:
    case None{}:
      Inl{{==}}
    case Some{+b}:
      rac.pick(Rp.verdict(c, b, k), c, b)

def Replace.replace_after_client_or_running(c, k, d):
  rac.go(c, k, d)
