# eukhe: the proof of LAW call_lift_table_steps_arrive
#
# PROOF: by induction on a table whose every family meets its obligation
# (clm.ta.Ok: a step out of a rev of that family makes the rev known in
# it): the first family named f is the one both Sp.current and
# Sp.steps_of pick (clm.ta.con, on the same String.eq), else the rest
# answers (the induction); no table, no step. The shipped table meets it
# family by family: a family without steps has no step to leave from
# (clm.ta.none); zoom's one step leaves rev 1 and arrives at its current
# rev 2 (clm.ta.zoom, split on whether r is 1 and whether r is 2).

import Base
import ../../bend/call_lift.bend as Cl
import ../../spec/harness/lift.bend as Sp
import ../../laws/call_lift.bend as CallLift

def clm.ta.If(m: Maybe<&2, Cl.Step>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

def clm.ta.absurd(-st: Cl.Step, -G: Type, e: {None{} == Some{st} : Maybe<&2, Cl.Step>}) -> G:
  %e : clm.ta.If(_, G)
  Unit{}

# what one family owes, for rev r and step st: a step out of r in the
# family makes r known in it
def clm.ta.Fam(+r: String, +st: Cl.Step, c: String, +s: List<&2, Cl.Step>) -> Type:
  {Sp.next(s, r) == Some{st} : Maybe<&2, Cl.Step>} -> {Sp.known.at(r, Some{c}, s) == True{} : Bool}

# what every family of t owes
def clm.ta.Ok(t: List<&2, Cl.Fam>, +r: String, +st: Cl.Step) -> Type:
  match t:
    case Nil{}:
      Unit
    case Con{x, rest}:
      match x:
        case Cl.Fam{n, c, s}:
          clm.ta.Fam(r, st, c, s) & clm.ta.Ok(rest, r, st)

# the first family named f answers both lookups, or the rest does
def clm.ta.pick(b: Bool, -c: String, -s: List<&2, Cl.Step>, -cr: Maybe<&2, String>, -sr: List<&2, Cl.Step>, -r: String, -st: Cl.Step, h: clm.ta.Fam(r, st, c, s), hr: {Sp.next(sr, r) == Some{st} : Maybe<&2, Cl.Step>} -> {Sp.known.at(r, cr, sr) == True{} : Bool}) -> {Sp.next(Sp.pick_steps(b, s, sr), r) == Some{st} : Maybe<&2, Cl.Step>} -> {Sp.known.at(r, Sp.pick_rev(b, c, cr), Sp.pick_steps(b, s, sr)) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      hr

def clm.ta.go(t: List<&2, Cl.Fam>, +f: String, +r: String, +st: Cl.Step, ok: clm.ta.Ok(t, r, st)) -> {Sp.next(Sp.steps_of(t, f), r) == Some{st} : Maybe<&2, Cl.Step>} -> {Sp.known.at(r, Sp.current(t, f), Sp.steps_of(t, f)) == True{} : Bool}:
  match t:
    case Nil{}:
      e => clm.ta.absurd(st, {Sp.known.at(r, None{}, []) == True{} : Bool}, e)
    case Con{x, rest}:
      match x:
        case Cl.Fam{+n, c, s}:
          (h, okr) = ok
          clm.ta.pick(String.eq(n, f), c, s, Sp.current(rest, f), Sp.steps_of(rest, f), r, st, h, clm.ta.go(rest, f, r, st, okr))

# a family without steps: no step leaves any rev
def clm.ta.none(-c: String, -r: String, -st: Cl.Step) -> clm.ta.Fam(r, st, c, []):
  e => clm.ta.absurd(st, {Sp.known.at(r, Some{c}, []) == True{} : Bool}, e)

def clm.ta.zoom.at(one: Bool, two: Bool, -st: Cl.Step) -> {Sp.pick_step(one, Cl.Step{"1", "2", []}, None{}) == Some{st} : Maybe<&2, Cl.Step>} -> {Bool.or(two, Sp.arrives(Sp.chain(1n, [Cl.Step{"1", "2", []}], "2", Sp.pick_step(one, Cl.Step{"1", "2", []}, None{})))) == True{} : Bool}:
  match one:
    case True{}:
      match two:
        case True{}:
          e => {==}
        case False{}:
          e => {==}
    case False{}:
      e => clm.ta.absurd(st, {Bool.or(two, Sp.arrives(Sp.chain(1n, [Cl.Step{"1", "2", []}], "2", None{}))) == True{} : Bool}, e)

# zoom: its one step leaves rev 1 and arrives at its current rev 2
def clm.ta.zoom(+r: String, -st: Cl.Step) -> clm.ta.Fam(r, st, "2", [Cl.Step{"1", "2", []}]):
  clm.ta.zoom.at(String.eq("1", r), String.eq(r, "2"), st)

def CallLift.call_lift_table_steps_arrive(f, r, st, step):
  clm.ta.go(Cl.table(), f, r, st, (clm.ta.none("1", r, st), (clm.ta.none("1", r, st), (clm.ta.none("1", r, st), (clm.ta.none("hl.1", r, st), (clm.ta.none("1", r, st), (clm.ta.none("1", r, st), (clm.ta.none("1", r, st), (clm.ta.none("1", r, st), (clm.ta.zoom(r, st), (clm.ta.none("1", r, st), (clm.ta.none("1", r, st), Unit{}))))))))))))(step)
