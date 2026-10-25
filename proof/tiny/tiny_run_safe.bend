# eukhe: the proof of LAW tiny_run_safe
#
# PROOF: each single reply is allowed (tr.allowed, a case per phase and
# outcome): a use answers only a pong whose tag is the run's (the code
# compares the texts as the spec does, LA.te.same, and uses on True), a
# shutdown only a pong of another tag (on False), a launch only a
# missing or hung-up socket or a shutdown answered bye or cut by the
# worker's exit; every other reply is allowed as it is. The walk is a
# conjunction of single replies, by induction on the outcomes.

import Base
import ../../bend/tiny.bend as Tn
import ../../laws/base.bend as LawsBase
import ../../laws/tiny/run.bend as TinyRun
import ./base.bend as LA

# a pong of tag t, which the spec compares to m as b
def tr.pong_elect(+m: String, +t: String, b: Bool, e: {LawsBase.text_same(t, m) == b : Bool}) -> {TinyRun.tr_allowed(m, Tn.Pinged{Tn.Pong{t}}, TinyRun.tr_do(Tn.run.elect(m, Tn.elect.pong(b)))) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, LawsBase.text_same(t, m), True{}, e) : {Bool.not(Bool.xor(_, True{})) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, LawsBase.text_same(t, m), False{}, e) : {Bool.not(Bool.xor(_, False{})) == True{} : Bool}
      {==}

def tr.pong_check(+m: String, +g: Tn.Got, +t: String, b: Bool, e: {LawsBase.text_same(t, m) == b : Bool}) -> {TinyRun.tr_allowed(m, Tn.Pinged{Tn.Pong{t}}, TinyRun.tr_do(Tn.run.check(m, g, Tn.confirm.pong(b)))) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, LawsBase.text_same(t, m), True{}, e) : {Bool.not(Bool.xor(_, True{})) == True{} : Bool}
      {==}
    case False{}:
      {==}

# the code's comparison, as the spec sees it
def tr.same(+t: String, +m: String) -> {LawsBase.text_same(t, m) == Tn.same(t, m) : Bool}:
  Equal.sym(Bool, Tn.same(t, m), LawsBase.text_same(t, m), LA.te.same(t, m))

def tr.probing(+m: String, s: Tn.Seen) -> {TinyRun.tr_allowed(m, s, TinyRun.tr_do(Tn.step_run(Tn.Run{m, Tn.Probing{}}, s))) == True{} : Bool}:
  match s:
    case Tn.Pinged{p}:
      match p:
        case Tn.Missing{}:
          {==}
        case Tn.Unreachable{}:
          {==}
        case Tn.Pong{+t}:
          tr.pong_elect(m, t, Tn.same(t, m), tr.same(t, m))
        case Tn.Odd{}:
          {==}
        case Tn.Garbled{}:
          {==}
        case Tn.Hung{}:
          {==}
    case Tn.ShutHeard{h}:
      {==}
    case Tn.Came{l}:
      {==}
    case Tn.NoSpawn{}:
      {==}
    case Tn.Locked{}:
      {==}

def tr.shutting(+m: String, s: Tn.Seen) -> {TinyRun.tr_allowed(m, s, TinyRun.tr_do(Tn.step_run(Tn.Run{m, Tn.Shutting{}}, s))) == True{} : Bool}:
  match s:
    case Tn.Pinged{p}:
      {==}
    case Tn.ShutHeard{h}:
      match h:
        case Tn.Bye{}:
          {==}
        case Tn.Other{}:
          {==}
        case Tn.Eof{}:
          {==}
        case Tn.Lost{}:
          {==}
    case Tn.Came{l}:
      {==}
    case Tn.NoSpawn{}:
      {==}
    case Tn.Locked{}:
      {==}

def tr.checking(+m: String, +g: Tn.Got, s: Tn.Seen) -> {TinyRun.tr_allowed(m, s, TinyRun.tr_do(Tn.step_run(Tn.Run{m, Tn.Checking{g}}, s))) == True{} : Bool}:
  match s:
    case Tn.Pinged{p}:
      match p:
        case Tn.Missing{}:
          {==}
        case Tn.Unreachable{}:
          {==}
        case Tn.Pong{+t}:
          tr.pong_check(m, g, t, Tn.same(t, m), tr.same(t, m))
        case Tn.Odd{}:
          {==}
        case Tn.Garbled{}:
          {==}
        case Tn.Hung{}:
          {==}
    case Tn.ShutHeard{h}:
      {==}
    case Tn.Came{l}:
      {==}
    case Tn.NoSpawn{}:
      {==}
    case Tn.Locked{}:
      {==}

def tr.seating(+m: String, s: Tn.Seen) -> {TinyRun.tr_allowed(m, s, TinyRun.tr_do(Tn.step_run(Tn.Run{m, Tn.Seating{}}, s))) == True{} : Bool}:
  match s:
    case Tn.Pinged{p}:
      match p:
        case Tn.Missing{}:
          {==}
        case Tn.Unreachable{}:
          {==}
        case Tn.Pong{t}:
          {==}
        case Tn.Odd{}:
          {==}
        case Tn.Garbled{}:
          {==}
        case Tn.Hung{}:
          {==}
    case Tn.ShutHeard{h}:
      {==}
    case Tn.Came{l}:
      {==}
    case Tn.NoSpawn{}:
      {==}
    case Tn.Locked{}:
      {==}

def tr.launching(+m: String, +f: Tn.Fresh, s: Tn.Seen) -> {TinyRun.tr_allowed(m, s, TinyRun.tr_do(Tn.step_run(Tn.Run{m, Tn.Launching{f}}, s))) == True{} : Bool}:
  match s:
    case Tn.Pinged{p}:
      {==}
    case Tn.ShutHeard{h}:
      {==}
    case Tn.Came{l}:
      {==}
    case Tn.NoSpawn{}:
      {==}
    case Tn.Locked{}:
      {==}

def tr.locking(+m: String, s: Tn.Seen) -> {TinyRun.tr_allowed(m, s, TinyRun.tr_do(Tn.step_run(Tn.Run{m, Tn.Locking{}}, s))) == True{} : Bool}:
  match s:
    case Tn.Pinged{p}:
      {==}
    case Tn.ShutHeard{h}:
      {==}
    case Tn.Came{l}:
      {==}
    case Tn.NoSpawn{}:
      {==}
    case Tn.Locked{}:
      {==}

# one reply of any run to any outcome is allowed
def tr.allowed(x: Tn.Run, +s: Tn.Seen) -> {TinyRun.tr_allowed(TinyRun.tr_mine(x), s, TinyRun.tr_do(Tn.step_run(x, s))) == True{} : Bool}:
  match x:
    case Tn.Run{+m, ph}:
      match ph:
        case Tn.Probing{}:
          tr.probing(m, s)
        case Tn.Shutting{}:
          tr.shutting(m, s)
        case Tn.Launching{f}:
          tr.launching(m, f, s)
        case Tn.Checking{g}:
          tr.checking(m, g, s)
        case Tn.Locking{}:
          tr.locking(m, s)
        case Tn.Seating{}:
          tr.seating(m, s)
        case Tn.Over{}:
          {==}

def tr.safe(ss: List<&2, Tn.Seen>, +x: Tn.Run) -> {TinyRun.tr_safe(ss, x) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case +s <> t:
      %Equal.sym(Bool, TinyRun.tr_allowed(TinyRun.tr_mine(x), s, TinyRun.tr_do(Tn.step_run(x, s))), True{}, tr.allowed(x, s)) : {Bool.and(_, TinyRun.tr_safe(t, TinyRun.tr_run(Tn.step_run(x, s)))) == True{} : Bool}
      tr.safe(t, TinyRun.tr_run(Tn.step_run(x, s)))

def TinyRun.tiny_run_safe(x, ss):
  tr.safe(ss, x)
