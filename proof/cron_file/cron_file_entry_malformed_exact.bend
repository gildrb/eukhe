# eukhe: the proof of LAW cron_file_entry_malformed_exact
# The entry reads every input as the laws' reader does (LCfw.cfe.pass);
# where that reader finds no whole request, the entry answers its error
# form.
import Base
import ../../bend/cron_store.bend as CS
import ../../bend/cron_file.bend as CF
import ../../bend/ffi_cron_file.bend as FF
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/cron.bend as Cron
import ../../laws/cron_file/pass.bend as CronFile
import ../../laws/cron_file/entry.bend as CronFileEntry
import ../../laws/cron_file/view.bend as CronFileView
import ./base/wire.bend as LCfw

def cfm.If(m: Maybe<&2, CF.Pass>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def cfm.some_none(-a: CF.Pass, -G: Type, e: {Some{a} == None{} : Maybe<&2, CF.Pass>}) -> G:
  %e : cfm.If(_, G)
  Unit{}

def cfm.end(b: Bool, -a: CF.Pass, no: {CronFileEntry.read_pass.end(b, a) == None{} : Maybe<&2, CF.Pass>}) -> {FF.run.end(b, a) == SCon{'E', SCon{' ', "cron_file: malformed request"}} : String}:
  match b:
    case True{}:
      cfm.some_none(a, {FF.answer(a) == SCon{'E', SCon{' ', "cron_file: malformed request"}} : String}, no)
    case False{}:
      {==}

def cfm.whole(r: Wr.Dec<CF.Pass>, no: {CronFileEntry.read_pass.whole(r) == None{} : Maybe<&2, CF.Pass>}) -> {FF.run(r) == SCon{'E', SCon{' ', "cron_file: malformed request"}} : String}:
  match r:
    case Wr.Got{a, s}:
      cfm.end(Wr.end(s), a, no)
    case Wr.Bad{}:
      {==}

def CronFileEntry.cron_file_entry_malformed_exact(s, no):
  %LCfw.cfe.pass(Wr.get_nat(s)) : {FF.run(_) == SCon{'E', SCon{' ', "cron_file: malformed request"}} : String}
  cfm.whole(CronFileEntry.read_pass.go(Wr.get_nat(s)), no)
