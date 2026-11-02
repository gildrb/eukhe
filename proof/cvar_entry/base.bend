# eukhe: lemmas of area cvar_entry: the entries' encoders write what the
# spec's spellers write and their decoders read what the spec's readers
# read (laws/cvar_entry.bend, cvs_*), on every input.

import Base
import ../../bend/cvar.bend as Cv
import ../../bend/ffi_cvar.bend as FCv
import ../../bend/wire.bend as Wr
import ../../laws/cvar.bend as Cvar
import ../../laws/cvar_entry.bend as CvarEntry
import ../cvar/alias_expand_exact.bend as PAE
import ../cvar/bind_press_exact.bend as PBP

# Encoders
# --------

def cve.val(v: Cv.Val, rest: String) -> {FCv.put_val(v, rest) == CvarEntry.cvs_spell_val(v, rest) : String}:
  match v:
    case Cv.VNat{n}:
      {==}
    case Cv.VBool{b}:
      {==}

def cve.cmd(c: Cv.Cmd, rest: String) -> {FCv.put_cmd(c, rest) == CvarEntry.cvs_spell_cmd(c, rest) : String}:
  match c:
    case Cv.CSet{i, v}:
      match v:
        case Cv.VNat{n}:
          {==}
        case Cv.VBool{b}:
          {==}
    case Cv.CToggle{i}:
      {==}
    case Cv.CRun{n}:
      {==}
    case Cv.CGone{n}:
      {==}

# Decoders
# --------

def cve.v_nat(d: Wr.Dec<Nat>) -> {FCv.get_val.nat(d) == CvarEntry.cvs_read_val.nat(d) : Wr.Dec<Cv.Val>}:
  match d:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cve.v_bool(d: Wr.Dec<Bool>) -> {FCv.get_val.bool(d) == CvarEntry.cvs_read_val.bool(d) : Wr.Dec<Cv.Val>}:
  match d:
    case Wr.Got{b, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cve.v_tag(t: Nat, +s: String) -> {FCv.get_val.tag(t, s) == CvarEntry.cvs_read_val.tag(t, s) : Wr.Dec<Cv.Val>}:
  match t:
    case 0n:
      cve.v_nat(Wr.get_nat(s))
    case 1n+a:
      match a:
        case 0n:
          cve.v_bool(Wr.get_bool(s))
        case 1n+b:
          {==}

def cve.v_go(d: Wr.Dec<Nat>) -> {FCv.get_val.go(d) == CvarEntry.cvs_read_val.go(d) : Wr.Dec<Cv.Val>}:
  match d:
    case Wr.Got{t, s}:
      cve.v_tag(t, s)
    case Wr.Bad{}:
      {==}

def cve.c_setv(i: Nat, d: Wr.Dec<Cv.Val>) -> {FCv.get_cmd.set.v(i, d) == CvarEntry.cvs_read_set.v(i, d) : Wr.Dec<Cv.Cmd>}:
  match d:
    case Wr.Got{v, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cve.c_set(d: Wr.Dec<Nat>) -> {FCv.get_cmd.set(d) == CvarEntry.cvs_read_set(d) : Wr.Dec<Cv.Cmd>}:
  match d:
    case Wr.Got{+i, +s}:
      %cve.v_go(Wr.get_nat(s)) : {FCv.get_cmd.set.v(i, FCv.get_val.go(Wr.get_nat(s))) == CvarEntry.cvs_read_set.v(i, _) : Wr.Dec<Cv.Cmd>}
      cve.c_setv(i, FCv.get_val.go(Wr.get_nat(s)))
    case Wr.Bad{}:
      {==}

def cve.c_toggle(d: Wr.Dec<Nat>) -> {FCv.get_cmd.toggle(d) == CvarEntry.cvs_read_toggle(d) : Wr.Dec<Cv.Cmd>}:
  match d:
    case Wr.Got{i, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cve.c_run(d: Wr.Dec<Nat>) -> {FCv.get_cmd.run(d) == CvarEntry.cvs_read_run(d) : Wr.Dec<Cv.Cmd>}:
  match d:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cve.c_gone(d: Wr.Dec<Nat>) -> {FCv.get_cmd.gone(d) == CvarEntry.cvs_read_gone(d) : Wr.Dec<Cv.Cmd>}:
  match d:
    case Wr.Got{n, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cve.c_tag(t: Nat, +s: String) -> {FCv.get_cmd.tag(t, s) == CvarEntry.cvs_read_cmd.tag(t, s) : Wr.Dec<Cv.Cmd>}:
  match t:
    case 0n:
      cve.c_set(Wr.get_nat(s))
    case 1n+a:
      match a:
        case 0n:
          cve.c_toggle(Wr.get_nat(s))
        case 1n+b:
          match b:
            case 0n:
              cve.c_run(Wr.get_nat(s))
            case 1n+c:
              match c:
                case 0n:
                  cve.c_gone(Wr.get_nat(s))
                case 1n+e:
                  {==}

def cve.c_go(d: Wr.Dec<Nat>) -> {FCv.get_cmd.go(d) == CvarEntry.cvs_read_cmd.go(d) : Wr.Dec<Cv.Cmd>}:
  match d:
    case Wr.Got{t, s}:
      cve.c_tag(t, s)
    case Wr.Bad{}:
      {==}

def cve.get_cmd(s: String) -> {FCv.get_cmd(s) == CvarEntry.cvs_read_cmd(s) : Wr.Dec<Cv.Cmd>}:
  cve.c_go(Wr.get_nat(s))

def cve.cmds_step(+x: Cv.Cmd, r: Nat & String) -> {Wr.put_list.step(~Cv.Cmd, ~FCv.put_cmd, x, r) == Wr.put_list.step(~Cv.Cmd, ~CvarEntry.cvs_spell_cmd, x, r) : Nat & String}:
  match r:
    case (n, +s):
      %cve.cmd(x, s) : {(1n+n, FCv.put_cmd(x, s)) == (1n+n, _) : Nat & String}
      {==}

def cve.cmds_go(xs: List<&2, Cv.Cmd>, +rest: String) -> {Wr.put_list.go(~Cv.Cmd, ~FCv.put_cmd, xs, rest) == Wr.put_list.go(~Cv.Cmd, ~CvarEntry.cvs_spell_cmd, xs, rest) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %cve.cmds_go(t, rest) : {Wr.put_list.step(~Cv.Cmd, ~FCv.put_cmd, x, Wr.put_list.go(~Cv.Cmd, ~FCv.put_cmd, t, rest)) == Wr.put_list.step(~Cv.Cmd, ~CvarEntry.cvs_spell_cmd, x, _) : Nat & String}
      cve.cmds_step(x, Wr.put_list.go(~Cv.Cmd, ~FCv.put_cmd, t, rest))

def cve.cmds_put(xs: List<&2, Cv.Cmd>, +rest: String) -> {Wr.put_list(~Cv.Cmd, ~FCv.put_cmd, xs, rest) == Wr.put_list(~Cv.Cmd, ~CvarEntry.cvs_spell_cmd, xs, rest) : String}:
  %cve.cmds_go(xs, rest) : {Wr.put_list.fin(Wr.put_list.go(~Cv.Cmd, ~FCv.put_cmd, xs, rest)) == Wr.put_list.fin(_) : String}
  {==}

def cve.cmds_lgo(n: Nat, cur: Wr.Dec<Cv.Cmd>) -> {Wr.get_list.go(~Cv.Cmd, ~FCv.get_cmd, n, cur) == Wr.get_list.go(~Cv.Cmd, ~CvarEntry.cvs_read_cmd, n, cur) : Wr.Dec<List<&2, Cv.Cmd>>}:
  match n cur:
    case 0n Wr.Got{x, s}:
      {==}
    case 0n Wr.Bad{}:
      {==}
    case 1n+m Wr.Got{+x, +s}:
      %cve.get_cmd(s) : {Wr.get_list.cons(Cv.Cmd, x, Wr.get_list.go(~Cv.Cmd, ~FCv.get_cmd, m, FCv.get_cmd(s))) == Wr.get_list.cons(Cv.Cmd, x, Wr.get_list.go(~Cv.Cmd, ~CvarEntry.cvs_read_cmd, m, _)) : Wr.Dec<List<&2, Cv.Cmd>>}
      %cve.cmds_lgo(m, FCv.get_cmd(s)) : {Wr.get_list.cons(Cv.Cmd, x, Wr.get_list.go(~Cv.Cmd, ~FCv.get_cmd, m, FCv.get_cmd(s))) == Wr.get_list.cons(Cv.Cmd, x, _) : Wr.Dec<List<&2, Cv.Cmd>>}
      {==}
    case 1n+m Wr.Bad{}:
      {==}

def cve.cmds_start(r: Wr.Dec<Nat>) -> {Wr.get_list.start(~Cv.Cmd, ~FCv.get_cmd, r) == Wr.get_list.start(~Cv.Cmd, ~CvarEntry.cvs_read_cmd, r) : Wr.Dec<List<&2, Cv.Cmd>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %cve.get_cmd(s) : {Wr.get_list.go(~Cv.Cmd, ~FCv.get_cmd, m, FCv.get_cmd(s)) == Wr.get_list.go(~Cv.Cmd, ~CvarEntry.cvs_read_cmd, m, _) : Wr.Dec<List<&2, Cv.Cmd>>}
          cve.cmds_lgo(m, FCv.get_cmd(s))
    case Wr.Bad{}:
      {==}

def cve.cmds_get(s: String) -> {Wr.get_list(~Cv.Cmd, ~FCv.get_cmd, s) == Wr.get_list(~Cv.Cmd, ~CvarEntry.cvs_read_cmd, s) : Wr.Dec<List<&2, Cv.Cmd>>}:
  cve.cmds_start(Wr.get_nat(s))

def cve.alias(a: Cv.Alias, +rest: String) -> {FCv.put_alias(a, rest) == CvarEntry.cvs_spell_alias(a, rest) : String}:
  match a:
    case Cv.Alias{+n, +b}:
      %cve.cmds_put(b, rest) : {Wr.put_nat(n, Wr.put_list(~Cv.Cmd, ~FCv.put_cmd, b, rest)) == Wr.put_nat(n, _) : String}
      {==}

def cve.bind(k: Cv.KeyBind, +rest: String) -> {FCv.put_bind(k, rest) == CvarEntry.cvs_spell_bind(k, rest) : String}:
  match k:
    case Cv.KeyBind{+n, +c}:
      %cve.cmds_put(c, rest) : {Wr.put_nat(n, Wr.put_list(~Cv.Cmd, ~FCv.put_cmd, c, rest)) == Wr.put_nat(n, _) : String}
      {==}

def cve.exp(e: Cv.Exp, +rest: String) -> {FCv.put_exp(e, rest) == CvarEntry.cvs_spell_exp(e, rest) : String}:
  match e:
    case Cv.Flat{+cs}:
      %cve.cmds_put(cs, rest) : {Wr.put_nat(0n, Wr.put_list(~Cv.Cmd, ~FCv.put_cmd, cs, rest)) == Wr.put_nat(0n, _) : String}
      {==}
    case Cv.Cycle{n}:
      {==}
    case Cv.Unknown{n}:
      {==}

def cve.a_body(n: Nat, d: Wr.Dec<List<&2, Cv.Cmd>>) -> {FCv.get_alias.body(n, d) == CvarEntry.cvs_read_alias.body(n, d) : Wr.Dec<Cv.Alias>}:
  match d:
    case Wr.Got{b, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cve.a_name(d: Wr.Dec<Nat>) -> {FCv.get_alias.name(d) == CvarEntry.cvs_read_alias.name(d) : Wr.Dec<Cv.Alias>}:
  match d:
    case Wr.Got{+n, +s}:
      %cve.cmds_get(s) : {FCv.get_alias.body(n, Wr.get_list(~Cv.Cmd, ~FCv.get_cmd, s)) == CvarEntry.cvs_read_alias.body(n, _) : Wr.Dec<Cv.Alias>}
      cve.a_body(n, Wr.get_list(~Cv.Cmd, ~FCv.get_cmd, s))
    case Wr.Bad{}:
      {==}

def cve.get_alias(s: String) -> {FCv.get_alias(s) == CvarEntry.cvs_read_alias(s) : Wr.Dec<Cv.Alias>}:
  cve.a_name(Wr.get_nat(s))

def cve.b_cmds(n: Nat, d: Wr.Dec<List<&2, Cv.Cmd>>) -> {FCv.get_bind.cmds(n, d) == CvarEntry.cvs_read_bind.cmds(n, d) : Wr.Dec<Cv.KeyBind>}:
  match d:
    case Wr.Got{c, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cve.b_key(d: Wr.Dec<Nat>) -> {FCv.get_bind.key(d) == CvarEntry.cvs_read_bind.key(d) : Wr.Dec<Cv.KeyBind>}:
  match d:
    case Wr.Got{+n, +s}:
      %cve.cmds_get(s) : {FCv.get_bind.cmds(n, Wr.get_list(~Cv.Cmd, ~FCv.get_cmd, s)) == CvarEntry.cvs_read_bind.cmds(n, _) : Wr.Dec<Cv.KeyBind>}
      cve.b_cmds(n, Wr.get_list(~Cv.Cmd, ~FCv.get_cmd, s))
    case Wr.Bad{}:
      {==}

def cve.get_bind(s: String) -> {FCv.get_bind(s) == CvarEntry.cvs_read_bind(s) : Wr.Dec<Cv.KeyBind>}:
  cve.b_key(Wr.get_nat(s))

def cve.aliases_step(+x: Cv.Alias, r: Nat & String) -> {Wr.put_list.step(~Cv.Alias, ~FCv.put_alias, x, r) == Wr.put_list.step(~Cv.Alias, ~CvarEntry.cvs_spell_alias, x, r) : Nat & String}:
  match r:
    case (n, +s):
      %cve.alias(x, s) : {(1n+n, FCv.put_alias(x, s)) == (1n+n, _) : Nat & String}
      {==}

def cve.aliases_go(xs: List<&2, Cv.Alias>, +rest: String) -> {Wr.put_list.go(~Cv.Alias, ~FCv.put_alias, xs, rest) == Wr.put_list.go(~Cv.Alias, ~CvarEntry.cvs_spell_alias, xs, rest) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %cve.aliases_go(t, rest) : {Wr.put_list.step(~Cv.Alias, ~FCv.put_alias, x, Wr.put_list.go(~Cv.Alias, ~FCv.put_alias, t, rest)) == Wr.put_list.step(~Cv.Alias, ~CvarEntry.cvs_spell_alias, x, _) : Nat & String}
      cve.aliases_step(x, Wr.put_list.go(~Cv.Alias, ~FCv.put_alias, t, rest))

def cve.aliases_put(xs: List<&2, Cv.Alias>, +rest: String) -> {Wr.put_list(~Cv.Alias, ~FCv.put_alias, xs, rest) == Wr.put_list(~Cv.Alias, ~CvarEntry.cvs_spell_alias, xs, rest) : String}:
  %cve.aliases_go(xs, rest) : {Wr.put_list.fin(Wr.put_list.go(~Cv.Alias, ~FCv.put_alias, xs, rest)) == Wr.put_list.fin(_) : String}
  {==}

def cve.aliases_lgo(n: Nat, cur: Wr.Dec<Cv.Alias>) -> {Wr.get_list.go(~Cv.Alias, ~FCv.get_alias, n, cur) == Wr.get_list.go(~Cv.Alias, ~CvarEntry.cvs_read_alias, n, cur) : Wr.Dec<List<&2, Cv.Alias>>}:
  match n cur:
    case 0n Wr.Got{x, s}:
      {==}
    case 0n Wr.Bad{}:
      {==}
    case 1n+m Wr.Got{+x, +s}:
      %cve.get_alias(s) : {Wr.get_list.cons(Cv.Alias, x, Wr.get_list.go(~Cv.Alias, ~FCv.get_alias, m, FCv.get_alias(s))) == Wr.get_list.cons(Cv.Alias, x, Wr.get_list.go(~Cv.Alias, ~CvarEntry.cvs_read_alias, m, _)) : Wr.Dec<List<&2, Cv.Alias>>}
      %cve.aliases_lgo(m, FCv.get_alias(s)) : {Wr.get_list.cons(Cv.Alias, x, Wr.get_list.go(~Cv.Alias, ~FCv.get_alias, m, FCv.get_alias(s))) == Wr.get_list.cons(Cv.Alias, x, _) : Wr.Dec<List<&2, Cv.Alias>>}
      {==}
    case 1n+m Wr.Bad{}:
      {==}

def cve.aliases_start(r: Wr.Dec<Nat>) -> {Wr.get_list.start(~Cv.Alias, ~FCv.get_alias, r) == Wr.get_list.start(~Cv.Alias, ~CvarEntry.cvs_read_alias, r) : Wr.Dec<List<&2, Cv.Alias>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %cve.get_alias(s) : {Wr.get_list.go(~Cv.Alias, ~FCv.get_alias, m, FCv.get_alias(s)) == Wr.get_list.go(~Cv.Alias, ~CvarEntry.cvs_read_alias, m, _) : Wr.Dec<List<&2, Cv.Alias>>}
          cve.aliases_lgo(m, FCv.get_alias(s))
    case Wr.Bad{}:
      {==}

def cve.aliases_get(s: String) -> {Wr.get_list(~Cv.Alias, ~FCv.get_alias, s) == Wr.get_list(~Cv.Alias, ~CvarEntry.cvs_read_alias, s) : Wr.Dec<List<&2, Cv.Alias>>}:
  cve.aliases_start(Wr.get_nat(s))

def cve.binds_step(+x: Cv.KeyBind, r: Nat & String) -> {Wr.put_list.step(~Cv.KeyBind, ~FCv.put_bind, x, r) == Wr.put_list.step(~Cv.KeyBind, ~CvarEntry.cvs_spell_bind, x, r) : Nat & String}:
  match r:
    case (n, +s):
      %cve.bind(x, s) : {(1n+n, FCv.put_bind(x, s)) == (1n+n, _) : Nat & String}
      {==}

def cve.binds_go(xs: List<&2, Cv.KeyBind>, +rest: String) -> {Wr.put_list.go(~Cv.KeyBind, ~FCv.put_bind, xs, rest) == Wr.put_list.go(~Cv.KeyBind, ~CvarEntry.cvs_spell_bind, xs, rest) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %cve.binds_go(t, rest) : {Wr.put_list.step(~Cv.KeyBind, ~FCv.put_bind, x, Wr.put_list.go(~Cv.KeyBind, ~FCv.put_bind, t, rest)) == Wr.put_list.step(~Cv.KeyBind, ~CvarEntry.cvs_spell_bind, x, _) : Nat & String}
      cve.binds_step(x, Wr.put_list.go(~Cv.KeyBind, ~FCv.put_bind, t, rest))

def cve.binds_put(xs: List<&2, Cv.KeyBind>, +rest: String) -> {Wr.put_list(~Cv.KeyBind, ~FCv.put_bind, xs, rest) == Wr.put_list(~Cv.KeyBind, ~CvarEntry.cvs_spell_bind, xs, rest) : String}:
  %cve.binds_go(xs, rest) : {Wr.put_list.fin(Wr.put_list.go(~Cv.KeyBind, ~FCv.put_bind, xs, rest)) == Wr.put_list.fin(_) : String}
  {==}

def cve.binds_lgo(n: Nat, cur: Wr.Dec<Cv.KeyBind>) -> {Wr.get_list.go(~Cv.KeyBind, ~FCv.get_bind, n, cur) == Wr.get_list.go(~Cv.KeyBind, ~CvarEntry.cvs_read_bind, n, cur) : Wr.Dec<List<&2, Cv.KeyBind>>}:
  match n cur:
    case 0n Wr.Got{x, s}:
      {==}
    case 0n Wr.Bad{}:
      {==}
    case 1n+m Wr.Got{+x, +s}:
      %cve.get_bind(s) : {Wr.get_list.cons(Cv.KeyBind, x, Wr.get_list.go(~Cv.KeyBind, ~FCv.get_bind, m, FCv.get_bind(s))) == Wr.get_list.cons(Cv.KeyBind, x, Wr.get_list.go(~Cv.KeyBind, ~CvarEntry.cvs_read_bind, m, _)) : Wr.Dec<List<&2, Cv.KeyBind>>}
      %cve.binds_lgo(m, FCv.get_bind(s)) : {Wr.get_list.cons(Cv.KeyBind, x, Wr.get_list.go(~Cv.KeyBind, ~FCv.get_bind, m, FCv.get_bind(s))) == Wr.get_list.cons(Cv.KeyBind, x, _) : Wr.Dec<List<&2, Cv.KeyBind>>}
      {==}
    case 1n+m Wr.Bad{}:
      {==}

def cve.binds_start(r: Wr.Dec<Nat>) -> {Wr.get_list.start(~Cv.KeyBind, ~FCv.get_bind, r) == Wr.get_list.start(~Cv.KeyBind, ~CvarEntry.cvs_read_bind, r) : Wr.Dec<List<&2, Cv.KeyBind>>}:
  match r:
    case Wr.Got{n, +s}:
      match n:
        case 0n:
          {==}
        case 1n+m:
          %cve.get_bind(s) : {Wr.get_list.go(~Cv.KeyBind, ~FCv.get_bind, m, FCv.get_bind(s)) == Wr.get_list.go(~Cv.KeyBind, ~CvarEntry.cvs_read_bind, m, _) : Wr.Dec<List<&2, Cv.KeyBind>>}
          cve.binds_lgo(m, FCv.get_bind(s))
    case Wr.Bad{}:
      {==}

def cve.binds_get(s: String) -> {Wr.get_list(~Cv.KeyBind, ~FCv.get_bind, s) == Wr.get_list(~Cv.KeyBind, ~CvarEntry.cvs_read_bind, s) : Wr.Dec<List<&2, Cv.KeyBind>>}:
  cve.binds_start(Wr.get_nat(s))

def cve.put_xreq(+as: List<&2, Cv.Alias>, +cs: List<&2, Cv.Cmd>, +rest: String) -> {FCv.put_xreq(FCv.Xreq{as, cs}, rest) == CvarEntry.cvs_spell_xreq(as, cs, rest) : String}:
  %cve.cmds_put(cs, rest) : {Wr.put_list(~Cv.Alias, ~FCv.put_alias, as, Wr.put_list(~Cv.Cmd, ~FCv.put_cmd, cs, rest)) == Wr.put_list(~Cv.Alias, ~CvarEntry.cvs_spell_alias, as, _) : String}
  cve.aliases_put(as, Wr.put_list(~Cv.Cmd, ~FCv.put_cmd, cs, rest))

def cve.put_table(+bs: List<&2, Cv.KeyBind>, +as: List<&2, Cv.Alias>, +rest: String) -> {FCv.put_table(bs, as, rest) == CvarEntry.cvs_spell_table(bs, as, rest) : String}:
  %cve.aliases_put(as, rest) : {Wr.put_list(~Cv.KeyBind, ~FCv.put_bind, bs, Wr.put_list(~Cv.Alias, ~FCv.put_alias, as, rest)) == Wr.put_list(~Cv.KeyBind, ~CvarEntry.cvs_spell_bind, bs, _) : String}
  cve.binds_put(bs, Wr.put_list(~Cv.Alias, ~FCv.put_alias, as, rest))

def cve.x_cmds(as: List<&2, Cv.Alias>, d: Wr.Dec<List<&2, Cv.Cmd>>) -> {FCv.get_xreq.cmds(as, d) == CvarEntry.cvs_read_xreq.cmds(as, d) : Wr.Dec<FCv.Xreq>}:
  match d:
    case Wr.Got{cs, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cve.x_aliases(d: Wr.Dec<List<&2, Cv.Alias>>) -> {FCv.get_xreq.aliases(d) == CvarEntry.cvs_read_xreq.aliases(d) : Wr.Dec<FCv.Xreq>}:
  match d:
    case Wr.Got{+as, +s}:
      %cve.cmds_get(s) : {FCv.get_xreq.cmds(as, Wr.get_list(~Cv.Cmd, ~FCv.get_cmd, s)) == CvarEntry.cvs_read_xreq.cmds(as, _) : Wr.Dec<FCv.Xreq>}
      cve.x_cmds(as, Wr.get_list(~Cv.Cmd, ~FCv.get_cmd, s))
    case Wr.Bad{}:
      {==}

def cve.xreq(+s: String) -> {FCv.get_xreq(s) == CvarEntry.cvs_read_xreq(s) : Wr.Dec<FCv.Xreq>}:
  %cve.aliases_get(s) : {FCv.get_xreq.aliases(Wr.get_list(~Cv.Alias, ~FCv.get_alias, s)) == CvarEntry.cvs_read_xreq.aliases(_) : Wr.Dec<FCv.Xreq>}
  cve.x_aliases(Wr.get_list(~Cv.Alias, ~FCv.get_alias, s))

def cve.t_aliases(bs: List<&2, Cv.KeyBind>, d: Wr.Dec<List<&2, Cv.Alias>>) -> {FCv.get_table.aliases(bs, d) == CvarEntry.cvs_read_table.aliases(bs, d) : Wr.Dec<FCv.St>}:
  match d:
    case Wr.Got{as, s}:
      {==}
    case Wr.Bad{}:
      {==}

def cve.t_binds(d: Wr.Dec<List<&2, Cv.KeyBind>>) -> {FCv.get_table.binds(d) == CvarEntry.cvs_read_table.binds(d) : Wr.Dec<FCv.St>}:
  match d:
    case Wr.Got{+bs, +s}:
      %cve.aliases_get(s) : {FCv.get_table.aliases(bs, Wr.get_list(~Cv.Alias, ~FCv.get_alias, s)) == CvarEntry.cvs_read_table.aliases(bs, _) : Wr.Dec<FCv.St>}
      cve.t_aliases(bs, Wr.get_list(~Cv.Alias, ~FCv.get_alias, s))
    case Wr.Bad{}:
      {==}

def cve.table(+s: String) -> {FCv.get_table(s) == CvarEntry.cvs_read_table(s) : Wr.Dec<FCv.St>}:
  %cve.binds_get(s) : {FCv.get_table.binds(Wr.get_list(~Cv.KeyBind, ~FCv.get_bind, s)) == CvarEntry.cvs_read_table.binds(_) : Wr.Dec<FCv.St>}
  cve.t_binds(Wr.get_list(~Cv.KeyBind, ~FCv.get_bind, s))

# The entries
# -----------

def cve.run(q: FCv.Xreq) -> {FCv.ffi.run(q) == CvarEntry.cvs_expand.run(q) : String}:
  match q:
    case FCv.Xreq{+as, +cs}:
      %PAE.pxx.expand(cs, as) : {FCv.put_exp(Cv.expand(cs, as), "") == CvarEntry.cvs_spell_exp(_, "") : String}
      cve.exp(Cv.expand(cs, as), "")

def cve.whole(q: FCv.Xreq, b: Bool) -> {FCv.ffi.whole(q, b) == CvarEntry.cvs_expand.end(b, q) : String}:
  match b:
    case True{}:
      cve.run(q)
    case False{}:
      {==}

def cve.go(d: Wr.Dec<FCv.Xreq>) -> {FCv.ffi.go(d) == CvarEntry.cvs_expand.go(d) : String}:
  match d:
    case Wr.Got{q, s}:
      cve.whole(q, Wr.end(s))
    case Wr.Bad{}:
      {==}

def cve.ffi(+s: String) -> {FCv.ffi(s) == CvarEntry.cvs_expand(s) : String}:
  %cve.xreq(s) : {FCv.ffi.go(FCv.get_xreq(s)) == CvarEntry.cvs_expand.go(_) : String}
  cve.go(FCv.get_xreq(s))

def cve.o_whole(t: FCv.St, b: Bool) -> {FCv.open.whole(t, b) == CvarEntry.cvs_open.end(b, t) : FCv.St & String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cve.o_go(d: Wr.Dec<FCv.St>) -> {FCv.open.go(d) == CvarEntry.cvs_open.go(d) : FCv.St & String}:
  match d:
    case Wr.Got{t, s}:
      cve.o_whole(t, Wr.end(s))
    case Wr.Bad{}:
      {==}

def cve.open(+s: String) -> {FCv.open(s) == CvarEntry.cvs_open(s) : FCv.St & String}:
  %cve.table(s) : {FCv.open.go(FCv.get_table(s)) == CvarEntry.cvs_open.go(_) : FCv.St & String}
  cve.o_go(FCv.get_table(s))

def cve.key(+bs: List<&2, Cv.KeyBind>, +as: List<&2, Cv.Alias>, d: Wr.Dec<Nat>) -> {FCv.step.key(bs, as, d) == CvarEntry.cvs_step.go(bs, as, d) : FCv.St & String}:
  match d:
    case Wr.Got{+k, s}:
      match s:
        case SNil{}:
          %PBP.pxb.press(bs, k, as) : {(FCv.Table{bs, as}, FCv.put_exp(Cv.press(bs, k, as), "")) == (FCv.Table{bs, as}, CvarEntry.cvs_spell_exp(_, "")) : FCv.St & String}
          %cve.exp(Cv.press(bs, k, as), "") : {(FCv.Table{bs, as}, FCv.put_exp(Cv.press(bs, k, as), "")) == (FCv.Table{bs, as}, _) : FCv.St & String}
          {==}
        case SCon{c, t}:
          {==}
    case Wr.Bad{}:
      {==}
