# theme_model (spec): what the theme model's helpers mean (laws in
# laws/theme_model.bend): a token's value in a file, the token list, the
# required tokens, the first of two optional values and a value with a
# default, a value's color, a palette's values, and the colors each shipped
# theme paints. Written without calling the model: the laws pin the model
# to these. A spec: the shipped code never calls it.

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/palette.bend as TPalette
import ../../bend/theme/reader.bend as TReader
import ../../bend/theme/bundled.bend as TBundled
import ./rules.bend as Ts

# a token every file must write: all but refinementHeader (14),
# refinementSummary (15), mdBody (18), background (57), foreground (58)
def required(+t: U32) -> Bool:
  Bool.not(Bool.or(U32.is_eq(t, 14), Bool.or(U32.is_eq(t, 15), Bool.or(U32.is_eq(t, 18), Bool.or(U32.is_eq(t, 57), U32.is_eq(t, 58))))))

def dark() -> List<&2, Co.Rgb>:
  [Co.Rgb{138, 190, 183}, Co.Rgb{95, 135, 255}, Co.Rgb{0, 215, 255}, Co.Rgb{101, 101, 101},
  Co.Rgb{181, 189, 104}, Co.Rgb{204, 102, 102}, Co.Rgb{255, 255, 0}, Co.Rgb{150, 150, 150},
  Co.Rgb{129, 129, 129}, Co.Rgb{229, 229, 231}, Co.Rgb{134, 134, 134}, Co.Rgb{229, 229, 231},
  Co.Rgb{229, 229, 231}, Co.Rgb{212, 175, 93}, Co.Rgb{212, 175, 93}, Co.Rgb{169, 160, 152},
  Co.Rgb{229, 229, 231}, Co.Rgb{150, 150, 150}, Co.Rgb{196, 196, 196}, Co.Rgb{212, 175, 93},
  Co.Rgb{129, 162, 190}, Co.Rgb{129, 129, 129}, Co.Rgb{138, 190, 183}, Co.Rgb{181, 189, 104},
  Co.Rgb{150, 150, 150}, Co.Rgb{150, 150, 150}, Co.Rgb{150, 150, 150}, Co.Rgb{150, 150, 150},
  Co.Rgb{138, 190, 183}, Co.Rgb{63, 185, 80}, Co.Rgb{248, 81, 73}, Co.Rgb{154, 160, 166},
  Co.Rgb{150, 150, 150}, Co.Rgb{106, 153, 85}, Co.Rgb{86, 156, 214}, Co.Rgb{220, 220, 170},
  Co.Rgb{156, 220, 254}, Co.Rgb{206, 145, 120}, Co.Rgb{181, 206, 168}, Co.Rgb{78, 201, 176},
  Co.Rgb{212, 212, 212}, Co.Rgb{212, 212, 212}, Co.Rgb{169, 160, 152}, Co.Rgb{212, 175, 93},
  Co.Rgb{212, 175, 93}, Co.Rgb{255, 255, 255}, Co.Rgb{0, 0, 0}, Co.Rgb{181, 189, 104},
  Co.Rgb{58, 58, 74}, Co.Rgb{52, 53, 65}, Co.Rgb{43, 36, 31}, Co.Rgb{40, 40, 50},
  Co.Rgb{40, 50, 40}, Co.Rgb{60, 40, 40}, Co.Rgb{1, 95, 0}, Co.Rgb{94, 0, 0},
  Co.Rgb{38, 38, 48}, Co.Rgb{24, 24, 30}, Co.Rgb{229, 229, 231}]

# the colors every token of the shipped themes paints (the tables a Rust
# test checks crates/eukhe-theme/themes/*.json paint)
def forge() -> List<&2, Co.Rgb>:
  [Co.Rgb{212, 175, 93}, Co.Rgb{127, 94, 71}, Co.Rgb{212, 175, 93}, Co.Rgb{127, 94, 71},
  Co.Rgb{142, 193, 132}, Co.Rgb{246, 156, 142}, Co.Rgb{235, 164, 116}, Co.Rgb{169, 160, 152},
  Co.Rgb{169, 160, 152}, Co.Rgb{224, 214, 198}, Co.Rgb{169, 160, 152}, Co.Rgb{224, 214, 198},
  Co.Rgb{224, 214, 198}, Co.Rgb{212, 175, 93}, Co.Rgb{212, 175, 93}, Co.Rgb{169, 160, 152},
  Co.Rgb{205, 166, 223}, Co.Rgb{169, 160, 152}, Co.Rgb{224, 214, 198}, Co.Rgb{245, 238, 224},
  Co.Rgb{140, 183, 229}, Co.Rgb{169, 160, 152}, Co.Rgb{142, 193, 132}, Co.Rgb{224, 214, 198},
  Co.Rgb{127, 94, 71}, Co.Rgb{169, 160, 152}, Co.Rgb{127, 94, 71}, Co.Rgb{127, 94, 71},
  Co.Rgb{198, 193, 187}, Co.Rgb{142, 193, 132}, Co.Rgb{246, 156, 142}, Co.Rgb{198, 193, 187},
  Co.Rgb{158, 135, 115}, Co.Rgb{169, 160, 152}, Co.Rgb{212, 175, 93}, Co.Rgb{205, 166, 223},
  Co.Rgb{224, 214, 198}, Co.Rgb{142, 193, 132}, Co.Rgb{235, 164, 116}, Co.Rgb{121, 193, 178},
  Co.Rgb{212, 175, 93}, Co.Rgb{198, 193, 187}, Co.Rgb{169, 160, 152}, Co.Rgb{212, 175, 93},
  Co.Rgb{212, 175, 93}, Co.Rgb{224, 214, 198}, Co.Rgb{17, 11, 7}, Co.Rgb{235, 164, 116},
  Co.Rgb{43, 36, 31}, Co.Rgb{30, 23, 17}, Co.Rgb{30, 23, 17}, Co.Rgb{30, 23, 17},
  Co.Rgb{19, 31, 16}, Co.Rgb{42, 21, 18}, Co.Rgb{19, 31, 16}, Co.Rgb{42, 21, 18},
  Co.Rgb{30, 23, 17}, Co.Rgb{30, 23, 17}, Co.Rgb{224, 214, 198}]

def light() -> List<&2, Co.Rgb>:
  [Co.Rgb{85, 120, 120}, Co.Rgb{79, 117, 157}, Co.Rgb{85, 120, 120}, Co.Rgb{144, 144, 144},
  Co.Rgb{83, 124, 83}, Co.Rgb{170, 85, 85}, Co.Rgb{145, 108, 36}, Co.Rgb{108, 108, 108},
  Co.Rgb{112, 112, 112}, Co.Rgb{0, 0, 0}, Co.Rgb{114, 114, 114}, Co.Rgb{0, 0, 0},
  Co.Rgb{0, 0, 0}, Co.Rgb{122, 90, 30}, Co.Rgb{122, 90, 30}, Co.Rgb{127, 94, 71},
  Co.Rgb{0, 0, 0}, Co.Rgb{108, 108, 108}, Co.Rgb{69, 69, 69}, Co.Rgb{122, 90, 30},
  Co.Rgb{79, 117, 157}, Co.Rgb{112, 112, 112}, Co.Rgb{85, 120, 120}, Co.Rgb{83, 124, 83},
  Co.Rgb{108, 108, 108}, Co.Rgb{108, 108, 108}, Co.Rgb{108, 108, 108}, Co.Rgb{108, 108, 108},
  Co.Rgb{83, 124, 83}, Co.Rgb{83, 124, 83}, Co.Rgb{170, 85, 85}, Co.Rgb{87, 96, 106},
  Co.Rgb{108, 108, 108}, Co.Rgb{0, 128, 0}, Co.Rgb{0, 0, 255}, Co.Rgb{121, 94, 38},
  Co.Rgb{0, 16, 128}, Co.Rgb{163, 21, 21}, Co.Rgb{9, 131, 86}, Co.Rgb{37, 123, 149},
  Co.Rgb{0, 0, 0}, Co.Rgb{0, 0, 0}, Co.Rgb{158, 135, 115}, Co.Rgb{122, 90, 30},
  Co.Rgb{122, 90, 30}, Co.Rgb{255, 255, 255}, Co.Rgb{0, 0, 0}, Co.Rgb{83, 124, 83},
  Co.Rgb{208, 208, 224}, Co.Rgb{232, 232, 232}, Co.Rgb{245, 238, 224}, Co.Rgb{232, 232, 240},
  Co.Rgb{232, 240, 232}, Co.Rgb{240, 232, 232}, Co.Rgb{218, 251, 225}, Co.Rgb{255, 235, 233},
  Co.Rgb{237, 237, 242}, Co.Rgb{248, 248, 248}, Co.Rgb{0, 0, 0}]

# a file's reading as an optional resolved file: none when it failed
def loaded(r: TReader.Read) -> Maybe<&2, TFile.Th>:
  match r:
    case TReader.Loaded{th}:
      Some{th}
    case TReader.Failed{f}:
      None{}
