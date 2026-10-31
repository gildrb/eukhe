# color_model (spec): the linear channel of any U32 channel, read from
# the table of channels 0-255 by its low eight bits (laws/color.bend,
# color_lin_spec). A spec: the shipped code never calls it.

import Base
import ../../bend/color.bend as Co

# the linear channel of any U32 c: the table of channels 0-255 (the sRGB
# transfer function, as color_lin_low/high state it) indexed by c's low
# eight bits, most significant first, in a tree
def lt0() -> Co.LinT:
  Co.Node{Co.Node{Co.Node{Co.Node{Co.Leaf{0}, Co.Leaf{3}}, Co.Node{Co.Leaf{6}, Co.Leaf{9}}}, Co.Node{Co.Node{Co.Leaf{12}, Co.Leaf{15}}, Co.Node{Co.Leaf{18}, Co.Leaf{21}}}}, Co.Node{Co.Node{Co.Node{Co.Leaf{24}, Co.Leaf{27}}, Co.Node{Co.Leaf{30}, Co.Leaf{33}}}, Co.Node{Co.Node{Co.Leaf{37}, Co.Leaf{40}}, Co.Node{Co.Leaf{44}, Co.Leaf{48}}}}}

def lt1() -> Co.LinT:
  Co.Node{Co.Node{Co.Node{Co.Node{Co.Leaf{52}, Co.Leaf{56}}, Co.Node{Co.Leaf{60}, Co.Leaf{65}}}, Co.Node{Co.Node{Co.Leaf{70}, Co.Leaf{75}}, Co.Node{Co.Leaf{80}, Co.Leaf{86}}}}, Co.Node{Co.Node{Co.Node{Co.Leaf{91}, Co.Leaf{97}}, Co.Node{Co.Leaf{103}, Co.Leaf{110}}}, Co.Node{Co.Node{Co.Leaf{116}, Co.Leaf{123}}, Co.Node{Co.Leaf{130}, Co.Leaf{137}}}}}

def lt2() -> Co.LinT:
  Co.Node{Co.Node{Co.Node{Co.Node{Co.Leaf{144}, Co.Leaf{152}}, Co.Node{Co.Leaf{160}, Co.Leaf{168}}}, Co.Node{Co.Node{Co.Leaf{176}, Co.Leaf{185}}, Co.Node{Co.Leaf{194}, Co.Leaf{203}}}}, Co.Node{Co.Node{Co.Node{Co.Leaf{212}, Co.Leaf{222}}, Co.Node{Co.Leaf{232}, Co.Leaf{242}}}, Co.Node{Co.Node{Co.Leaf{252}, Co.Leaf{262}}, Co.Node{Co.Leaf{273}, Co.Leaf{284}}}}}

def lt3() -> Co.LinT:
  Co.Node{Co.Node{Co.Node{Co.Node{Co.Leaf{296}, Co.Leaf{307}}, Co.Node{Co.Leaf{319}, Co.Leaf{331}}}, Co.Node{Co.Node{Co.Leaf{343}, Co.Leaf{356}}, Co.Node{Co.Leaf{369}, Co.Leaf{382}}}}, Co.Node{Co.Node{Co.Node{Co.Leaf{395}, Co.Leaf{409}}, Co.Node{Co.Leaf{423}, Co.Leaf{437}}}, Co.Node{Co.Node{Co.Leaf{452}, Co.Leaf{467}}, Co.Node{Co.Leaf{482}, Co.Leaf{497}}}}}

def lt4() -> Co.LinT:
  Co.Node{Co.Node{Co.Node{Co.Node{Co.Leaf{513}, Co.Leaf{529}}, Co.Node{Co.Leaf{545}, Co.Leaf{561}}}, Co.Node{Co.Node{Co.Leaf{578}, Co.Leaf{595}}, Co.Node{Co.Leaf{612}, Co.Leaf{630}}}}, Co.Node{Co.Node{Co.Node{Co.Leaf{648}, Co.Leaf{666}}, Co.Node{Co.Leaf{685}, Co.Leaf{704}}}, Co.Node{Co.Node{Co.Leaf{723}, Co.Leaf{742}}, Co.Node{Co.Leaf{762}, Co.Leaf{782}}}}}

def lt5() -> Co.LinT:
  Co.Node{Co.Node{Co.Node{Co.Node{Co.Leaf{802}, Co.Leaf{823}}, Co.Node{Co.Leaf{844}, Co.Leaf{865}}}, Co.Node{Co.Node{Co.Leaf{887}, Co.Leaf{908}}, Co.Node{Co.Leaf{931}, Co.Leaf{953}}}}, Co.Node{Co.Node{Co.Node{Co.Leaf{976}, Co.Leaf{999}}, Co.Node{Co.Leaf{1022}, Co.Leaf{1046}}}, Co.Node{Co.Node{Co.Leaf{1070}, Co.Leaf{1095}}, Co.Node{Co.Leaf{1119}, Co.Leaf{1144}}}}}

def lt6() -> Co.LinT:
  Co.Node{Co.Node{Co.Node{Co.Node{Co.Leaf{1170}, Co.Leaf{1195}}, Co.Node{Co.Leaf{1221}, Co.Leaf{1248}}}, Co.Node{Co.Node{Co.Leaf{1274}, Co.Leaf{1301}}, Co.Node{Co.Leaf{1329}, Co.Leaf{1356}}}}, Co.Node{Co.Node{Co.Node{Co.Leaf{1384}, Co.Leaf{1413}}, Co.Node{Co.Leaf{1441}, Co.Leaf{1470}}}, Co.Node{Co.Node{Co.Leaf{1500}, Co.Leaf{1529}}, Co.Node{Co.Leaf{1559}, Co.Leaf{1590}}}}}

def lt7() -> Co.LinT:
  Co.Node{Co.Node{Co.Node{Co.Node{Co.Leaf{1620}, Co.Leaf{1651}}, Co.Node{Co.Leaf{1683}, Co.Leaf{1714}}}, Co.Node{Co.Node{Co.Leaf{1746}, Co.Leaf{1779}}, Co.Node{Co.Leaf{1812}, Co.Leaf{1845}}}}, Co.Node{Co.Node{Co.Node{Co.Leaf{1878}, Co.Leaf{1912}}, Co.Node{Co.Leaf{1946}, Co.Leaf{1981}}}, Co.Node{Co.Node{Co.Leaf{2016}, Co.Leaf{2051}}, Co.Node{Co.Leaf{2086}, Co.Leaf{2122}}}}}

def lt8() -> Co.LinT:
  Co.Node{Co.Node{Co.Node{Co.Node{Co.Leaf{2159}, Co.Leaf{2195}}, Co.Node{Co.Leaf{2232}, Co.Leaf{2270}}}, Co.Node{Co.Node{Co.Leaf{2307}, Co.Leaf{2346}}, Co.Node{Co.Leaf{2384}, Co.Leaf{2423}}}}, Co.Node{Co.Node{Co.Node{Co.Leaf{2462}, Co.Leaf{2502}}, Co.Node{Co.Leaf{2542}, Co.Leaf{2582}}}, Co.Node{Co.Node{Co.Leaf{2623}, Co.Leaf{2664}}, Co.Node{Co.Leaf{2705}, Co.Leaf{2747}}}}}

def lt9() -> Co.LinT:
  Co.Node{Co.Node{Co.Node{Co.Node{Co.Leaf{2789}, Co.Leaf{2831}}, Co.Node{Co.Leaf{2874}, Co.Leaf{2918}}}, Co.Node{Co.Node{Co.Leaf{2961}, Co.Leaf{3005}}, Co.Node{Co.Leaf{3050}, Co.Leaf{3095}}}}, Co.Node{Co.Node{Co.Node{Co.Leaf{3140}, Co.Leaf{3185}}, Co.Node{Co.Leaf{3231}, Co.Leaf{3278}}}, Co.Node{Co.Node{Co.Leaf{3325}, Co.Leaf{3372}}, Co.Node{Co.Leaf{3419}, Co.Leaf{3467}}}}}

def lt10() -> Co.LinT:
  Co.Node{Co.Node{Co.Node{Co.Node{Co.Leaf{3515}, Co.Leaf{3564}}, Co.Node{Co.Leaf{3613}, Co.Leaf{3663}}}, Co.Node{Co.Node{Co.Leaf{3712}, Co.Leaf{3763}}, Co.Node{Co.Leaf{3813}, Co.Leaf{3864}}}}, Co.Node{Co.Node{Co.Node{Co.Leaf{3916}, Co.Leaf{3968}}, Co.Node{Co.Leaf{4020}, Co.Leaf{4072}}}, Co.Node{Co.Node{Co.Leaf{4125}, Co.Leaf{4179}}, Co.Node{Co.Leaf{4233}, Co.Leaf{4287}}}}}

def lt11() -> Co.LinT:
  Co.Node{Co.Node{Co.Node{Co.Node{Co.Leaf{4342}, Co.Leaf{4397}}, Co.Node{Co.Leaf{4452}, Co.Leaf{4508}}}, Co.Node{Co.Node{Co.Leaf{4564}, Co.Leaf{4621}}, Co.Node{Co.Leaf{4678}, Co.Leaf{4735}}}}, Co.Node{Co.Node{Co.Node{Co.Leaf{4793}, Co.Leaf{4851}}, Co.Node{Co.Leaf{4910}, Co.Leaf{4969}}}, Co.Node{Co.Node{Co.Leaf{5029}, Co.Leaf{5089}}, Co.Node{Co.Leaf{5149}, Co.Leaf{5210}}}}}

def lt12() -> Co.LinT:
  Co.Node{Co.Node{Co.Node{Co.Node{Co.Leaf{5271}, Co.Leaf{5333}}, Co.Node{Co.Leaf{5395}, Co.Leaf{5457}}}, Co.Node{Co.Node{Co.Leaf{5520}, Co.Leaf{5583}}, Co.Node{Co.Leaf{5647}, Co.Leaf{5711}}}}, Co.Node{Co.Node{Co.Node{Co.Leaf{5776}, Co.Leaf{5841}}, Co.Node{Co.Leaf{5906}, Co.Leaf{5972}}}, Co.Node{Co.Node{Co.Leaf{6038}, Co.Leaf{6105}}, Co.Node{Co.Leaf{6172}, Co.Leaf{6240}}}}}

def lt13() -> Co.LinT:
  Co.Node{Co.Node{Co.Node{Co.Node{Co.Leaf{6308}, Co.Leaf{6376}}, Co.Node{Co.Leaf{6445}, Co.Leaf{6514}}}, Co.Node{Co.Node{Co.Leaf{6584}, Co.Leaf{6654}}, Co.Node{Co.Leaf{6724}, Co.Leaf{6795}}}}, Co.Node{Co.Node{Co.Node{Co.Leaf{6867}, Co.Leaf{6939}}, Co.Node{Co.Leaf{7011}, Co.Leaf{7084}}}, Co.Node{Co.Node{Co.Leaf{7157}, Co.Leaf{7231}}, Co.Node{Co.Leaf{7305}, Co.Leaf{7379}}}}}

def lt14() -> Co.LinT:
  Co.Node{Co.Node{Co.Node{Co.Node{Co.Leaf{7454}, Co.Leaf{7529}}, Co.Node{Co.Leaf{7605}, Co.Leaf{7682}}}, Co.Node{Co.Node{Co.Leaf{7758}, Co.Leaf{7835}}, Co.Node{Co.Leaf{7913}, Co.Leaf{7991}}}}, Co.Node{Co.Node{Co.Node{Co.Leaf{8070}, Co.Leaf{8148}}, Co.Node{Co.Leaf{8228}, Co.Leaf{8308}}}, Co.Node{Co.Node{Co.Leaf{8388}, Co.Leaf{8469}}, Co.Node{Co.Leaf{8550}, Co.Leaf{8632}}}}}

def lt15() -> Co.LinT:
  Co.Node{Co.Node{Co.Node{Co.Node{Co.Leaf{8714}, Co.Leaf{8796}}, Co.Node{Co.Leaf{8879}, Co.Leaf{8963}}}, Co.Node{Co.Node{Co.Leaf{9047}, Co.Leaf{9131}}, Co.Node{Co.Leaf{9216}, Co.Leaf{9301}}}}, Co.Node{Co.Node{Co.Node{Co.Leaf{9387}, Co.Leaf{9473}}, Co.Node{Co.Leaf{9560}, Co.Leaf{9647}}}, Co.Node{Co.Node{Co.Leaf{9734}, Co.Leaf{9823}}, Co.Node{Co.Leaf{9911}, Co.Leaf{10000}}}}}

def ltable() -> Co.LinT:
  Co.Node{Co.Node{Co.Node{Co.Node{lt0(), lt1()}, Co.Node{lt2(), lt3()}}, Co.Node{Co.Node{lt4(), lt5()}, Co.Node{lt6(), lt7()}}}, Co.Node{Co.Node{Co.Node{lt8(), lt9()}, Co.Node{lt10(), lt11()}}, Co.Node{Co.Node{lt12(), lt13()}, Co.Node{lt14(), lt15()}}}}

def lgo(t: Co.LinT, bs: List<&2, Bool>) -> U32:
  match t:
    case Co.Leaf{v}:
      v
    case Co.Node{lo, hi}:
      match bs:
        case Nil{}:
          0
        case Con{b, rest}:
          match b:
            case True{}:
              lgo(hi, rest)
            case False{}:
              lgo(lo, rest)

def lbit(+c: U32, k: U32) -> Bool:
  Bool.not(U32.is_zero((c .&. k : U32)))

def lin(+c: U32) -> U32:
  lgo(ltable(), [lbit(c, 128), lbit(c, 64), lbit(c, 32), lbit(c, 16), lbit(c, 8), lbit(c, 4), lbit(c, 2), lbit(c, 1)])
