# eukhe: the proof of LAW cron_file_entry_example
# Each string computes.
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

def CronFileEntry.cron_file_entry_example():
  ({==}, ({==}, ({==}, ({==}, {==}))))
