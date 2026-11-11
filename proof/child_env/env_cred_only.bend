# eukhe: the proof of LAW env_cred_only
#
# PROOF: the registry test fails, so the pattern test holds (LN.pcn.or_l_false); the model's list (the same list as env_secrets) has a pattern p the upper case of n holds (LN.pcn.matched_sound), so that upper case is a, p, c (LN.pcn.contains_sound), and n is a, p, c in ASCII upper case (LN.pcn.case_of).

import Base
import ../../bend/child_env.bend as Env
import ../../laws/child_env.bend as ChildEnv
import ./base/names.bend as LN

def pco.Goal(n: String) -> Type:
  &i: Nat -> &p: String -> &a: String -> &c: String -> ({List.get(&2, String, ChildEnv.env_secrets(), i) == Some{p} : Maybe<&2, String>} & ChildEnv.env_case_eq(n, String.append(a, String.append(p, c))))

def pco.mid(+n: String, +i: Nat, +p: String, g: {List.get(&2, String, ChildEnv.env_secrets(), i) == Some{p} : Maybe<&2, String>}, m: LN.pcn.Mid(p, Env.up(n))) -> pco.Goal(n):
  (a, r) = m
  (c, e) = r
  (i, (p, (a, (c, (g, LN.pcn.case_of(n, String.append(a, String.append(p, c)), e))))))

def pco.at(+n: String, i: Nat, +p: String, r: ({List.get(&2, String, Env.patterns(), i) == Some{p} : Maybe<&2, String>} & {String.contains(Env.up(n), p) == True{} : Bool})) -> pco.Goal(n):
  (g, k) = r
  pco.mid(n, i, p, g, LN.pcn.contains_sound(Env.up(n), p, k))

def pco.hit(+n: String, h: LN.pcn.Hit(Env.patterns(), Env.up(n))) -> pco.Goal(n):
  (i, r1) = h
  (p, r2) = r1
  pco.at(n, i, p, r2)

def ChildEnv.env_cred_only(reg, n, hc, hr):
  pco.hit(n, LN.pcn.matched_sound(Env.patterns(), Env.up(n), LN.pcn.or_l_false(Env.listed(reg, Env.up(n)), Env.matched(Env.patterns(), Env.up(n)), hr, hc)))
