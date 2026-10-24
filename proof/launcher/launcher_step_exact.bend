# eukhe: the proof of LAW launcher_step_exact
# Per operation, the code's change of worker i is the spec's (one lemma
# per operation, by induction on i), the commit's test is "every gate is
# closed" and its count is the runs found (launcher_stop_counts_runs).

import Base
import ../../bend/launcher.bend as La
import ../../laws/launcher.bend as Launcher
import ./base.bend as LLa

def lse.prompt.go(-k: Nat, j: Nat, ws: List<&2, La.Wk>) -> {La.at(~La.prompt, j, ws) == Launcher.at_spec(La.Prompt{k}, j, ws) : List<&2, La.Wk>}:
  match j:
    case 0n:
      match ws:
        case Nil{}:
          {==}
        case La.Wk{b, c} <> t:
          match c:
            case True{}:
              {==}
            case False{}:
              {==}
    case 1n+m:
      match ws:
        case Nil{}:
          {==}
        case w <> t:
          %lse.prompt.go(k, m, t) : {w <> La.at(~La.prompt, m, t) == w <> _ : List<&2, La.Wk>}
          {==}

def lse.finish.go(-k: Nat, j: Nat, ws: List<&2, La.Wk>) -> {La.at(~La.finish, j, ws) == Launcher.at_spec(La.Finish{k}, j, ws) : List<&2, La.Wk>}:
  match j:
    case 0n:
      match ws:
        case Nil{}:
          {==}
        case La.Wk{b, c} <> t:
          {==}
    case 1n+m:
      match ws:
        case Nil{}:
          {==}
        case w <> t:
          %lse.finish.go(k, m, t) : {w <> La.at(~La.finish, m, t) == w <> _ : List<&2, La.Wk>}
          {==}

def lse.quiesce.go(-k: Nat, j: Nat, ws: List<&2, La.Wk>) -> {La.at(~La.quiesce, j, ws) == Launcher.at_spec(La.Quiesce{k}, j, ws) : List<&2, La.Wk>}:
  match j:
    case 0n:
      match ws:
        case Nil{}:
          {==}
        case La.Wk{b, c} <> t:
          match b:
            case True{}:
              {==}
            case False{}:
              {==}
    case 1n+m:
      match ws:
        case Nil{}:
          {==}
        case w <> t:
          %lse.quiesce.go(k, m, t) : {w <> La.at(~La.quiesce, m, t) == w <> _ : List<&2, La.Wk>}
          {==}

def lse.release.go(-k: Nat, j: Nat, ws: List<&2, La.Wk>) -> {La.at(~La.release, j, ws) == Launcher.at_spec(La.Release{k}, j, ws) : List<&2, La.Wk>}:
  match j:
    case 0n:
      match ws:
        case Nil{}:
          {==}
        case La.Wk{b, c} <> t:
          {==}
    case 1n+m:
      match ws:
        case Nil{}:
          {==}
        case w <> t:
          %lse.release.go(k, m, t) : {w <> La.at(~La.release, m, t) == w <> _ : List<&2, La.Wk>}
          {==}

def lse.closed(ws: List<&2, La.Wk>) -> {La.all_closed(ws) == Launcher.closed_spec(ws) : Bool}:
  match ws:
    case Nil{}:
      {==}
    case La.Wk{b, c} <> t:
      %lse.closed(t) : {Bool.and(c, La.all_closed(t)) == Bool.and(c, _) : Bool}
      {==}

def lse.commit(ok: Bool, +ws: List<&2, La.Wk>, a: Nat) -> {La.commit.put(ok, ws, a) == Launcher.commit_spec(ok, ws, a) : La.St}:
  match ok:
    case True{}:
      %LLa.la.busy(ws) : {La.St{ws, Nat.add(La.busy_count(ws), a), True{}} == La.St{ws, Nat.add(_, a), True{}} : La.St}
      {==}
    case False{}:
      {==}

def Launcher.launcher_step_exact(s, op):
  match s:
    case La.St{+ws, a, d}:
      match d:
        case True{}:
          {==}
        case False{}:
          match op:
            case La.Prompt{+i}:
              %lse.prompt.go(i, i, ws) : {La.St{La.at(~La.prompt, i, ws), a, False{}} == La.St{_, a, False{}} : La.St}
              {==}
            case La.Finish{+i}:
              %lse.finish.go(i, i, ws) : {La.St{La.at(~La.finish, i, ws), a, False{}} == La.St{_, a, False{}} : La.St}
              {==}
            case La.Quiesce{+i}:
              %lse.quiesce.go(i, i, ws) : {La.St{La.at(~La.quiesce, i, ws), a, False{}} == La.St{_, a, False{}} : La.St}
              {==}
            case La.Release{+i}:
              %lse.release.go(i, i, ws) : {La.St{La.at(~La.release, i, ws), a, False{}} == La.St{_, a, False{}} : La.St}
              {==}
            case La.Commit{}:
              %Equal.sym(Bool, La.all_closed(ws), Launcher.closed_spec(ws), lse.closed(ws)) : {La.commit.put(_, ws, a) == Launcher.commit_spec(Launcher.closed_spec(ws), ws, a) : La.St}
              lse.commit(Launcher.closed_spec(ws), ws, a)
