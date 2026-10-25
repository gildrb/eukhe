# theme_model (spec): what the theme model's helpers mean (laws in
# laws/theme_model.bend): a token's value in a file, the token list, the
# required tokens, the first of two optional values and a value with a
# default, a value's color, a palette's values, and the colors each shipped
# theme paints. Written without calling the model: the laws pin the model
# to these. A spec: the shipped code never calls it.

import Base
import ../bend/color.bend as Co
import ../bend/theme/file.bend as TFile
import ../bend/theme/palette.bend as TPalette
import ../bend/theme/reader.bend as TReader
import ../bend/theme/bundled.bend as TBundled
import ./theme_rules.bend as Ts

def pick_val(hit: Bool, v: TFile.Val, other: Maybe<&2, TFile.Val>) -> Maybe<&2, TFile.Val>:
  match hit:
    case True{}:
      Some{v}
    case False{}:
      other

# the value of the first entry for token t
def tok_get(cols: List<&2, TFile.Ent>, +t: U32) -> Maybe<&2, TFile.Val>:
  match cols:
    case Nil{}:
      None{}
    case Con{e, rest}:
      match e:
        case TFile.Ent{k, v}:
          pick_val(U32.is_eq(k, t), v, tok_get(rest, t))

# the tokens, 0 to 58, in order
def toks() -> List<&2, U32>:
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58]

# a token every file must write: all but refinementHeader (14),
# refinementSummary (15), mdBody (18), background (57), foreground (58)
def required(+t: U32) -> Bool:
  Bool.not(Bool.or(U32.is_eq(t, 14), Bool.or(U32.is_eq(t, 15), Bool.or(U32.is_eq(t, 18), Bool.or(U32.is_eq(t, 57), U32.is_eq(t, 58))))))

# the first of two optional values that is set
def first(-A: Data, a: Maybe<&2, A>, b: Maybe<&2, A>) -> Maybe<&2, A>:
  match a:
    case Some{x}:
      Some{x}
    case None{}:
      b

# an optional value, else d
def value(-A: Data, a: Maybe<&2, A>, d: A) -> A:
  match a:
    case Some{x}:
      x
    case None{}:
      d

# the color an optional value paints: none when unset
def concrete_of(m: Maybe<&2, TFile.Val>) -> Maybe<&2, Co.Rgb>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      Ts.concrete(v)

# a palette's values: an unset token is the terminal default
def vals(p: List<&2, Maybe<&2, TFile.Val>>) -> List<&2, TFile.Val>:
  match p:
    case Nil{}:
      Nil{}
    case Con{m, rest}:
      match m:
        case None{}:
          TFile.Dflt{} <> vals(rest)
        case Some{v}:
          v <> vals(rest)

# the value of each token of ts in the palette with colors cols and
# background bg (TPalette.fill, pinned per token by the laws theme_fill_*
# of laws/theme.bend and theme_required_spec)
def fmap(+cols: List<&2, TFile.Ent>, +bg: Co.Rgb, ts: List<&2, U32>) -> List<&2, Maybe<&2, TFile.Val>>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, rest}:
      TPalette.fill(cols, bg, t) <> fmap(cols, bg, rest)

# the colors every token of the shipped themes paints (the tables a Rust
# test checks crates/eukhe-theme/themes/*.json paint)
def eukhe() -> List<&2, Co.Rgb>:
  [Co.Rgb{124, 111, 175}, Co.Rgb{124, 111, 175}, Co.Rgb{124, 111, 175}, Co.Rgb{91, 91, 101},
  Co.Rgb{125, 168, 118}, Co.Rgb{208, 111, 130}, Co.Rgb{245, 158, 11}, Co.Rgb{161, 161, 170},
  Co.Rgb{118, 118, 127}, Co.Rgb{229, 229, 231}, Co.Rgb{139, 139, 148}, Co.Rgb{229, 229, 231},
  Co.Rgb{229, 229, 231}, Co.Rgb{245, 158, 11}, Co.Rgb{149, 117, 205}, Co.Rgb{183, 161, 214},
  Co.Rgb{229, 229, 231}, Co.Rgb{161, 161, 170}, Co.Rgb{216, 216, 220}, Co.Rgb{141, 127, 192},
  Co.Rgb{56, 189, 248}, Co.Rgb{118, 118, 127}, Co.Rgb{200, 200, 205}, Co.Rgb{139, 168, 136},
  Co.Rgb{91, 91, 101}, Co.Rgb{161, 161, 170}, Co.Rgb{91, 91, 101}, Co.Rgb{91, 91, 101},
  Co.Rgb{161, 161, 170}, Co.Rgb{63, 185, 80}, Co.Rgb{248, 81, 73}, Co.Rgb{154, 160, 166},
  Co.Rgb{161, 161, 170}, Co.Rgb{161, 161, 170}, Co.Rgb{56, 189, 248}, Co.Rgb{56, 189, 248},
  Co.Rgb{212, 212, 216}, Co.Rgb{139, 168, 136}, Co.Rgb{245, 158, 11}, Co.Rgb{245, 158, 11},
  Co.Rgb{212, 212, 216}, Co.Rgb{212, 212, 216}, Co.Rgb{124, 111, 175}, Co.Rgb{167, 139, 250},
  Co.Rgb{124, 111, 175}, Co.Rgb{255, 255, 255}, Co.Rgb{0, 0, 0}, Co.Rgb{125, 168, 118},
  Co.Rgb{34, 34, 38}, Co.Rgb{26, 26, 31}, Co.Rgb{21, 21, 24}, Co.Rgb{16, 16, 21},
  Co.Rgb{14, 21, 16}, Co.Rgb{26, 13, 18}, Co.Rgb{1, 95, 0}, Co.Rgb{94, 0, 0},
  Co.Rgb{13, 13, 16}, Co.Rgb{5, 5, 6}, Co.Rgb{229, 229, 231}]

def dark() -> List<&2, Co.Rgb>:
  [Co.Rgb{138, 190, 183}, Co.Rgb{95, 135, 255}, Co.Rgb{0, 215, 255}, Co.Rgb{101, 101, 101},
  Co.Rgb{181, 189, 104}, Co.Rgb{204, 102, 102}, Co.Rgb{255, 255, 0}, Co.Rgb{150, 150, 150},
  Co.Rgb{129, 129, 129}, Co.Rgb{229, 229, 231}, Co.Rgb{134, 134, 134}, Co.Rgb{229, 229, 231},
  Co.Rgb{229, 229, 231}, Co.Rgb{149, 117, 205}, Co.Rgb{149, 117, 205}, Co.Rgb{183, 161, 214},
  Co.Rgb{229, 229, 231}, Co.Rgb{150, 150, 150}, Co.Rgb{196, 196, 196}, Co.Rgb{178, 148, 187},
  Co.Rgb{129, 162, 190}, Co.Rgb{129, 129, 129}, Co.Rgb{138, 190, 183}, Co.Rgb{181, 189, 104},
  Co.Rgb{150, 150, 150}, Co.Rgb{150, 150, 150}, Co.Rgb{150, 150, 150}, Co.Rgb{150, 150, 150},
  Co.Rgb{138, 190, 183}, Co.Rgb{63, 185, 80}, Co.Rgb{248, 81, 73}, Co.Rgb{154, 160, 166},
  Co.Rgb{150, 150, 150}, Co.Rgb{106, 153, 85}, Co.Rgb{86, 156, 214}, Co.Rgb{220, 220, 170},
  Co.Rgb{156, 220, 254}, Co.Rgb{206, 145, 120}, Co.Rgb{181, 206, 168}, Co.Rgb{78, 201, 176},
  Co.Rgb{212, 212, 212}, Co.Rgb{212, 212, 212}, Co.Rgb{178, 148, 187}, Co.Rgb{209, 131, 232},
  Co.Rgb{178, 148, 187}, Co.Rgb{255, 255, 255}, Co.Rgb{0, 0, 0}, Co.Rgb{181, 189, 104},
  Co.Rgb{58, 58, 74}, Co.Rgb{52, 53, 65}, Co.Rgb{45, 40, 56}, Co.Rgb{40, 40, 50},
  Co.Rgb{40, 50, 40}, Co.Rgb{60, 40, 40}, Co.Rgb{1, 95, 0}, Co.Rgb{94, 0, 0},
  Co.Rgb{38, 38, 48}, Co.Rgb{24, 24, 30}, Co.Rgb{229, 229, 231}]

def light() -> List<&2, Co.Rgb>:
  [Co.Rgb{85, 120, 120}, Co.Rgb{79, 117, 157}, Co.Rgb{85, 120, 120}, Co.Rgb{144, 144, 144},
  Co.Rgb{83, 124, 83}, Co.Rgb{170, 85, 85}, Co.Rgb{145, 108, 36}, Co.Rgb{108, 108, 108},
  Co.Rgb{112, 112, 112}, Co.Rgb{0, 0, 0}, Co.Rgb{114, 114, 114}, Co.Rgb{0, 0, 0},
  Co.Rgb{0, 0, 0}, Co.Rgb{126, 87, 194}, Co.Rgb{113, 70, 171}, Co.Rgb{129, 101, 167},
  Co.Rgb{0, 0, 0}, Co.Rgb{108, 108, 108}, Co.Rgb{69, 69, 69}, Co.Rgb{126, 87, 194},
  Co.Rgb{79, 117, 157}, Co.Rgb{112, 112, 112}, Co.Rgb{85, 120, 120}, Co.Rgb{83, 124, 83},
  Co.Rgb{108, 108, 108}, Co.Rgb{108, 108, 108}, Co.Rgb{108, 108, 108}, Co.Rgb{108, 108, 108},
  Co.Rgb{83, 124, 83}, Co.Rgb{83, 124, 83}, Co.Rgb{170, 85, 85}, Co.Rgb{87, 96, 106},
  Co.Rgb{108, 108, 108}, Co.Rgb{0, 128, 0}, Co.Rgb{0, 0, 255}, Co.Rgb{121, 94, 38},
  Co.Rgb{0, 16, 128}, Co.Rgb{163, 21, 21}, Co.Rgb{9, 131, 86}, Co.Rgb{37, 123, 149},
  Co.Rgb{0, 0, 0}, Co.Rgb{0, 0, 0}, Co.Rgb{135, 95, 135}, Co.Rgb{139, 0, 139},
  Co.Rgb{135, 95, 135}, Co.Rgb{255, 255, 255}, Co.Rgb{0, 0, 0}, Co.Rgb{83, 124, 83},
  Co.Rgb{208, 208, 224}, Co.Rgb{232, 232, 232}, Co.Rgb{237, 231, 246}, Co.Rgb{232, 232, 240},
  Co.Rgb{232, 240, 232}, Co.Rgb{240, 232, 232}, Co.Rgb{218, 251, 225}, Co.Rgb{255, 235, 233},
  Co.Rgb{237, 237, 242}, Co.Rgb{248, 248, 248}, Co.Rgb{0, 0, 0}]

# a valid file: every required token written as the terminal default
def blank.keep(keep: Bool, t: U32, rest: List<&2, TFile.REnt>) -> List<&2, TFile.REnt>:
  match keep:
    case True{}:
      TFile.REnt{"k", Some{t}, TFile.JStr{"", None{}}} <> rest
    case False{}:
      rest

def blank.cols(ts: List<&2, U32>) -> List<&2, TFile.REnt>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{+t, rest}:
      blank.keep(required(t), t, blank.cols(rest))

def blank() -> TFile.RFile:
  TFile.RFile{"blank", [], blank.cols(toks()), None{}, None{}, None{}}

# a file's reading as an optional resolved file: none when it failed
def loaded(r: TReader.Read) -> Maybe<&2, TFile.Th>:
  match r:
    case TReader.Loaded{th}:
      Some{th}
    case TReader.Failed{f}:
      None{}

# the file writes token t
def has(+cols: List<&2, TFile.Ent>, +t: U32) -> Bool:
  Maybe.is_some(&2, TFile.Val, tok_get(cols, t))

# what token t needs of a file, by which token it is (refinementHeader
# 14, refinementSummary 15, mdBody 18, background 57, foreground 58,
# else a required one): mdBody needs itself or text (9), a required token
# itself, the other four nothing
def need(t14: Bool, t15: Bool, t18: Bool, t57: Bool, t58: Bool, +cols: List<&2, TFile.Ent>, +t: U32) -> Bool:
  match t14:
    case True{}:
      True{}
    case False{}:
      match t15:
        case True{}:
          True{}
        case False{}:
          match t18:
            case True{}:
              Bool.or(has(cols, t), has(cols, 9))
            case False{}:
              match t57:
                case True{}:
                  True{}
                case False{}:
                  match t58:
                    case True{}:
                      True{}
                    case False{}:
                      has(cols, t)

def ok(+cols: List<&2, TFile.Ent>, +t: U32) -> Bool:
  need(U32.is_eq(t, 14), U32.is_eq(t, 15), U32.is_eq(t, 18), U32.is_eq(t, 57), U32.is_eq(t, 58), cols, t)

def valid.go(+cols: List<&2, TFile.Ent>, ts: List<&2, U32>) -> Bool:
  match ts:
    case Nil{}:
      True{}
    case Con{t, rest}:
      Bool.and(ok(cols, t), valid.go(cols, rest))

# a file is valid when every token gets what it needs
def valid(+cols: List<&2, TFile.Ent>) -> Bool:
  valid.go(cols, toks())

# every token of a palette has a value
def complete(p: List<&2, Maybe<&2, TFile.Val>>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{m, rest}:
      match m:
        case None{}:
          False{}
        case Some{v}:
          complete(rest)
