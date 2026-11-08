# eukhe: lemmas of the cvar entry proofs: the entry's encoders write the
# laws' spellings (laws/cvar/entry.bend cvar_spell_*), field by field, so a
# law stated on the spellings follows from one stated on put_*.

import Base
import ../../../bend/cvar.bend as Cv
import ../../../bend/ffi_cvar.bend as FCv
import ../../../bend/wire.bend as Wr
import ../../../laws/cvar/entry.bend as CvarEntry
import ../base.bend as LA
import ../cvar_ffi_open.bend as PCvarFfiOpen

def cvs.val(v: Cv.Val, -rest: String) -> {FCv.put_val(v, rest) == CvarEntry.cvar_spell_val(v, rest) : String}:
  match v:
    case Cv.VNat{n}:
      {==}
    case Cv.VBool{b}:
      {==}

def cvs.cmd(c: Cv.Cmd, -rest: String) -> {FCv.put_cmd(c, rest) == CvarEntry.cvar_spell_cmd(c, rest) : String}:
  match c:
    case Cv.CSet{+i, +v}:
      Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_nat(i, z)), FCv.put_val(v, rest), CvarEntry.cvar_spell_val(v, rest), cvs.val(v, rest))
    case Cv.CToggle{i}:
      {==}
    case Cv.CRun{n}:
      {==}
    case Cv.CGone{n}:
      {==}

def cvs.cs.items(cs: List<&2, Cv.Cmd>, -rest: String) -> {LA.pvf.cs.items(cs, rest) == CvarEntry.cvar_spell_cmds.items(cs, rest) : String}:
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      Equal.trans(String, FCv.put_cmd(c, LA.pvf.cs.items(t, rest)), FCv.put_cmd(c, CvarEntry.cvar_spell_cmds.items(t, rest)), CvarEntry.cvar_spell_cmd(c, CvarEntry.cvar_spell_cmds.items(t, rest)), Equal.cong(String, String, z => FCv.put_cmd(c, z), LA.pvf.cs.items(t, rest), CvarEntry.cvar_spell_cmds.items(t, rest), cvs.cs.items(t, rest)), cvs.cmd(c, CvarEntry.cvar_spell_cmds.items(t, rest)))

# a command list is written as spelled
def cvs.cmds(+cs: List<&2, Cv.Cmd>, -rest: String) -> {FCv.put_cmds(cs, rest) == CvarEntry.cvar_spell_cmds(cs, rest) : String}:
  Equal.trans(String, Wr.put_list(~Cv.Cmd, ~FCv.put_cmd, cs, rest), Wr.put_nat(List.length(&2, Cv.Cmd, cs), LA.pvf.cs.items(cs, rest)), CvarEntry.cvar_spell_cmds(cs, rest), LA.pvf.cs.put(cs, rest), Equal.cong(String, String, z => Wr.put_nat(List.length(&2, Cv.Cmd, cs), z), LA.pvf.cs.items(cs, rest), CvarEntry.cvar_spell_cmds.items(cs, rest), cvs.cs.items(cs, rest)))

def cvs.alias(a: Cv.Alias, -rest: String) -> {FCv.put_alias(a, rest) == CvarEntry.cvar_spell_alias(a, rest) : String}:
  match a:
    case Cv.Alias{+n, +b}:
      Equal.cong(String, String, z => Wr.put_nat(n, z), FCv.put_cmds(b, rest), CvarEntry.cvar_spell_cmds(b, rest), cvs.cmds(b, rest))

def cvs.as.items(xs: List<&2, Cv.Alias>, -rest: String) -> {LA.pvf.as.items(xs, rest) == CvarEntry.cvar_spell_aliases.items(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.trans(String, FCv.put_alias(x, LA.pvf.as.items(t, rest)), FCv.put_alias(x, CvarEntry.cvar_spell_aliases.items(t, rest)), CvarEntry.cvar_spell_alias(x, CvarEntry.cvar_spell_aliases.items(t, rest)), Equal.cong(String, String, z => FCv.put_alias(x, z), LA.pvf.as.items(t, rest), CvarEntry.cvar_spell_aliases.items(t, rest), cvs.as.items(t, rest)), cvs.alias(x, CvarEntry.cvar_spell_aliases.items(t, rest)))

# an alias table is written as spelled
def cvs.aliases(+xs: List<&2, Cv.Alias>, -rest: String) -> {Wr.put_list(~Cv.Alias, ~FCv.put_alias, xs, rest) == CvarEntry.cvar_spell_aliases(xs, rest) : String}:
  Equal.trans(String, Wr.put_list(~Cv.Alias, ~FCv.put_alias, xs, rest), Wr.put_nat(List.length(&2, Cv.Alias, xs), LA.pvf.as.items(xs, rest)), CvarEntry.cvar_spell_aliases(xs, rest), LA.pvf.as.put(xs, rest), Equal.cong(String, String, z => Wr.put_nat(List.length(&2, Cv.Alias, xs), z), LA.pvf.as.items(xs, rest), CvarEntry.cvar_spell_aliases.items(xs, rest), cvs.as.items(xs, rest)))

def cvs.bind(k: Cv.KeyBind, -rest: String) -> {FCv.put_bind(k, rest) == CvarEntry.cvar_spell_bind(k, rest) : String}:
  match k:
    case Cv.KeyBind{+n, +c}:
      Equal.cong(String, String, z => Wr.put_nat(n, z), FCv.put_cmds(c, rest), CvarEntry.cvar_spell_cmds(c, rest), cvs.cmds(c, rest))

def cvs.bs.items(xs: List<&2, Cv.KeyBind>, -rest: String) -> {PCvarFfiOpen.pvf.bs.items(xs, rest) == CvarEntry.cvar_spell_binds.items(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      Equal.trans(String, FCv.put_bind(x, PCvarFfiOpen.pvf.bs.items(t, rest)), FCv.put_bind(x, CvarEntry.cvar_spell_binds.items(t, rest)), CvarEntry.cvar_spell_bind(x, CvarEntry.cvar_spell_binds.items(t, rest)), Equal.cong(String, String, z => FCv.put_bind(x, z), PCvarFfiOpen.pvf.bs.items(t, rest), CvarEntry.cvar_spell_binds.items(t, rest), cvs.bs.items(t, rest)), cvs.bind(x, CvarEntry.cvar_spell_binds.items(t, rest)))

# a bind table is written as spelled
def cvs.binds(+xs: List<&2, Cv.KeyBind>, -rest: String) -> {Wr.put_list(~Cv.KeyBind, ~FCv.put_bind, xs, rest) == CvarEntry.cvar_spell_binds(xs, rest) : String}:
  Equal.trans(String, Wr.put_list(~Cv.KeyBind, ~FCv.put_bind, xs, rest), Wr.put_nat(List.length(&2, Cv.KeyBind, xs), PCvarFfiOpen.pvf.bs.items(xs, rest)), CvarEntry.cvar_spell_binds(xs, rest), PCvarFfiOpen.pvf.bs.put(xs, rest), Equal.cong(String, String, z => Wr.put_nat(List.length(&2, Cv.KeyBind, xs), z), PCvarFfiOpen.pvf.bs.items(xs, rest), CvarEntry.cvar_spell_binds.items(xs, rest), cvs.bs.items(xs, rest)))

# an expansion is written as spelled
def cvs.exp(e: Cv.Exp, -rest: String) -> {FCv.put_exp(e, rest) == CvarEntry.cvar_spell_exp(e, rest) : String}:
  match e:
    case Cv.Flat{+cs}:
      Equal.cong(String, String, z => Wr.put_nat(0n, z), FCv.put_cmds(cs, rest), CvarEntry.cvar_spell_cmds(cs, rest), cvs.cmds(cs, rest))
    case Cv.Cycle{n}:
      {==}
    case Cv.Unknown{n}:
      {==}

# an expand request is written as spelled: the aliases, then the commands
def cvs.xreq(+as: List<&2, Cv.Alias>, +cs: List<&2, Cv.Cmd>, +rest: String) -> {FCv.put_xreq(FCv.Xreq{as, cs}, rest) == CvarEntry.cvar_spell_aliases(as, CvarEntry.cvar_spell_cmds(cs, rest)) : String}:
  Equal.trans(String, Wr.put_list(~Cv.Alias, ~FCv.put_alias, as, FCv.put_cmds(cs, rest)), CvarEntry.cvar_spell_aliases(as, FCv.put_cmds(cs, rest)), CvarEntry.cvar_spell_aliases(as, CvarEntry.cvar_spell_cmds(cs, rest)), cvs.aliases(as, FCv.put_cmds(cs, rest)), Equal.cong(String, String, z => CvarEntry.cvar_spell_aliases(as, z), FCv.put_cmds(cs, rest), CvarEntry.cvar_spell_cmds(cs, rest), cvs.cmds(cs, rest)))

# a press table is written as spelled: the binds, then the aliases
def cvs.table(+bs: List<&2, Cv.KeyBind>, +as: List<&2, Cv.Alias>, +rest: String) -> {FCv.put_table(bs, as, rest) == CvarEntry.cvar_spell_binds(bs, CvarEntry.cvar_spell_aliases(as, rest)) : String}:
  Equal.trans(String, Wr.put_list(~Cv.KeyBind, ~FCv.put_bind, bs, Wr.put_list(~Cv.Alias, ~FCv.put_alias, as, rest)), CvarEntry.cvar_spell_binds(bs, Wr.put_list(~Cv.Alias, ~FCv.put_alias, as, rest)), CvarEntry.cvar_spell_binds(bs, CvarEntry.cvar_spell_aliases(as, rest)), cvs.binds(bs, Wr.put_list(~Cv.Alias, ~FCv.put_alias, as, rest)), Equal.cong(String, String, z => CvarEntry.cvar_spell_binds(bs, z), Wr.put_list(~Cv.Alias, ~FCv.put_alias, as, rest), CvarEntry.cvar_spell_aliases(as, rest), cvs.aliases(as, rest)))
