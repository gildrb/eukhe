# eukhe: the proof of LAW theme_load_spec: one case per reading

import Base
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/reader.bend as TReader
import ../../spec/theme_model.bend as Tm
import ../../laws/theme_model.bend as ThemeModel

def ld.of(r: TReader.Read) -> {TReader.load.of(r) == Tm.loaded(r) : Maybe<&2, TFile.Th>}:
  match r:
    case TReader.Loaded{th}:
      {==}
    case TReader.Failed{f}:
      {==}

def ThemeModel.theme_load_spec(f):
  ld.of(TReader.read(f))
