# eukhe: lemmas of area package_source: each function of bend/package_source.bend is
# the spec helper of laws/package_source/model.bend (by the same matches, every
# inner call rewritten by its own lemma)

import Base
import ../../bend/package_source.bend as Ps
import ../../laws/package_source/model.bend as PackageSource
import ../../bend/gateway_answer.bend as Ga

def psb.is_some(+m: Maybe<&2, String>) -> {Ps.is_some(m) == PackageSource.ps_is_some(m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      {==}

def psb.has(+s: String, +x: Char) -> {Ps.has(s, x) == PackageSource.ps_has(s, x) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Ps.has(t, x), PackageSource.ps_has(t, x), psb.has(t, x)) : {Bool.or(Char.is_eq(c, x), _) == Bool.or(Char.is_eq(c, x), PackageSource.ps_has(t, x)) : Bool}
      {==}

def psb.lspace.at(+b: Bool, +c: Char, +t: String, +r: String) -> {Ps.lspace.at(b, c, t, r) == PackageSource.ps_lspace.at(b, c, t, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def psb.lspace(+s: String) -> {Ps.lspace(s) == PackageSource.ps_lspace(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Ps.lspace(t), PackageSource.ps_lspace(t), psb.lspace(t)) : {Ps.lspace.at(Ga.space(c), c, t, _) == PackageSource.ps_lspace.at(Ga.space(c), c, t, PackageSource.ps_lspace(t)) : String}
      psb.lspace.at(Ga.space(c), c, t, PackageSource.ps_lspace(t))

def psb.trim(+s: String) -> {Ps.trim(s) == PackageSource.ps_trim(s) : String}:
  %Equal.sym(String, Ps.lspace(s), PackageSource.ps_lspace(s), psb.lspace(s)) : {String.reverse(Ps.lspace(String.reverse(_))) == String.reverse(PackageSource.ps_lspace(String.reverse(PackageSource.ps_lspace(s)))) : String}
  %Equal.sym(String, Ps.lspace(String.reverse(PackageSource.ps_lspace(s))), PackageSource.ps_lspace(String.reverse(PackageSource.ps_lspace(s))), psb.lspace(String.reverse(PackageSource.ps_lspace(s)))) : {String.reverse(_) == String.reverse(PackageSource.ps_lspace(String.reverse(PackageSource.ps_lspace(s)))) : String}
  {==}

def psb.lslash.at(+b: Bool, +c: Char, +t: String, +r: String) -> {Ps.lslash.at(b, c, t, r) == PackageSource.ps_lslash.at(b, c, t, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def psb.lslash(+s: String) -> {Ps.lslash(s) == PackageSource.ps_lslash(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Ps.lslash(t), PackageSource.ps_lslash(t), psb.lslash(t)) : {Ps.lslash.at(Char.is_eq(c, '/'), c, t, _) == PackageSource.ps_lslash.at(Char.is_eq(c, '/'), c, t, PackageSource.ps_lslash(t)) : String}
      psb.lslash.at(Char.is_eq(c, '/'), c, t, PackageSource.ps_lslash(t))

def psb.nogit.at(+b: Bool, +r: String, +k: String) -> {Ps.nogit.at(b, r, k) == PackageSource.ps_nogit.at(b, r, k) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def psb.nogit(+n: Nat, +r: String) -> {Ps.nogit(n, r) == PackageSource.ps_nogit(n, r) : String}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(String, Ps.nogit(p, String.drop(r, 4n)), PackageSource.ps_nogit(p, String.drop(r, 4n)), psb.nogit(p, String.drop(r, 4n))) : {Ps.nogit.at(String.starts_with(r, "tig."), r, _) == PackageSource.ps_nogit.at(String.starts_with(r, "tig."), r, PackageSource.ps_nogit(p, String.drop(r, 4n))) : String}
      psb.nogit.at(String.starts_with(r, "tig."), r, PackageSource.ps_nogit(p, String.drop(r, 4n)))

def psb.unsuffix(+s: String) -> {Ps.unsuffix(s) == PackageSource.ps_unsuffix(s) : String}:
  %Equal.sym(String, Ps.nogit(String.length(s), String.reverse(s)), PackageSource.ps_nogit(String.length(s), String.reverse(s)), psb.nogit(String.length(s), String.reverse(s))) : {String.reverse(_) == String.reverse(PackageSource.ps_nogit(String.length(s), String.reverse(s))) : String}
  {==}

def psb.cut.at(+b: Bool, +c: Char, +t: String, +r: Maybe<&2, Ps.Cut>) -> {Ps.cut.at(b, c, t, r) == PackageSource.ps_cut.at(b, c, t, r) : Maybe<&2, Ps.Cut>}:
  match b:
    case True{}:
      {==}
    case False{}:
      match r:
        case None{}:
          {==}
        case Some{+x}:
          match x:
            case Ps.Cut{+h, +u}:
              {==}

def psb.cut(+s: String, +sep: Char) -> {Ps.cut(s, sep) == PackageSource.ps_cut(s, sep) : Maybe<&2, Ps.Cut>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(t, sep), PackageSource.ps_cut(t, sep), psb.cut(t, sep)) : {Ps.cut.at(Char.is_eq(c, sep), c, t, _) == PackageSource.ps_cut.at(Char.is_eq(c, sep), c, t, PackageSource.ps_cut(t, sep)) : Maybe<&2, Ps.Cut>}
      psb.cut.at(Char.is_eq(c, sep), c, t, PackageSource.ps_cut(t, sep))

def psb.before.at(+b: Bool, +c: Char, +r: String) -> {Ps.before.at(b, c, r) == PackageSource.ps_before.at(b, c, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def psb.before(+s: String, +sep: Char) -> {Ps.before(s, sep) == PackageSource.ps_before(s, sep) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Ps.before(t, sep), PackageSource.ps_before(t, sep), psb.before(t, sep)) : {Ps.before.at(Char.is_eq(c, sep), c, _) == PackageSource.ps_before.at(Char.is_eq(c, sep), c, PackageSource.ps_before(t, sep)) : String}
      psb.before.at(Char.is_eq(c, sep), c, PackageSource.ps_before(t, sep))

def psb.proto.at(+b: Bool, +c: Char, +t: String, +r: Maybe<&2, Ps.Cut>) -> {Ps.proto.at(b, c, t, r) == PackageSource.ps_proto.at(b, c, t, r) : Maybe<&2, Ps.Cut>}:
  match b:
    case True{}:
      {==}
    case False{}:
      match r:
        case None{}:
          {==}
        case Some{+x}:
          match x:
            case Ps.Cut{+h, +u}:
              {==}

def psb.proto(+s: String) -> {Ps.proto(s) == PackageSource.ps_proto(s) : Maybe<&2, Ps.Cut>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Maybe<&2, Ps.Cut>, Ps.proto(t), PackageSource.ps_proto(t), psb.proto(t)) : {Ps.proto.at(String.starts_with(SCon{c, t}, "://"), c, t, _) == PackageSource.ps_proto.at(String.starts_with(SCon{c, t}, "://"), c, t, PackageSource.ps_proto(t)) : Maybe<&2, Ps.Cut>}
      psb.proto.at(String.starts_with(SCon{c, t}, "://"), c, t, PackageSource.ps_proto(t))

def psb.url.at(+sc: String, +m: Maybe<&2, Ps.Cut>) -> {Ps.url.at(sc, m) == PackageSource.ps_url.at(sc, m) : Maybe<&2, Ps.Url>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+a, +p}:
          {==}

def psb.url.of(+m: Maybe<&2, Ps.Cut>) -> {Ps.url.of(m) == PackageSource.ps_url.of(m) : Maybe<&2, Ps.Url>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+sc, +rest}:
          %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(rest, '/'), PackageSource.ps_cut(rest, '/'), psb.cut(rest, '/')) : {Ps.url.at(sc, _) == PackageSource.ps_url.at(sc, PackageSource.ps_cut(rest, '/')) : Maybe<&2, Ps.Url>}
          psb.url.at(sc, PackageSource.ps_cut(rest, '/'))

def psb.url(+s: String) -> {Ps.url(s) == PackageSource.ps_url(s) : Maybe<&2, Ps.Url>}:
  %Equal.sym(Maybe<&2, Ps.Cut>, Ps.proto(s), PackageSource.ps_proto(s), psb.proto(s)) : {Ps.url.of(_) == PackageSource.ps_url.of(PackageSource.ps_proto(s)) : Maybe<&2, Ps.Url>}
  psb.url.of(PackageSource.ps_proto(s))

def psb.host_of(+a: String) -> {Ps.host_of(a) == PackageSource.ps_host_of(a) : String}:
  %Equal.sym(String, Ps.before(String.reverse(a), '@'), PackageSource.ps_before(String.reverse(a), '@'), psb.before(String.reverse(a), '@')) : {Ps.before(String.reverse(_), ':') == PackageSource.ps_before(String.reverse(PackageSource.ps_before(String.reverse(a), '@')), ':') : String}
  psb.before(String.reverse(PackageSource.ps_before(String.reverse(a), '@')), ':')

def psb.proto_url(+s: String) -> {Ps.proto_url(s) == PackageSource.ps_proto_url(s) : Bool}:
  {==}

def psb.control(+c: Char) -> {Ps.control(c) == PackageSource.ps_control(c) : Bool}:
  match c:
    case Chr{+x}:
      {==}

def psb.any_control(+s: String) -> {Ps.any_control(s) == PackageSource.ps_any_control(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Ps.control(c), PackageSource.ps_control(c), psb.control(c)) : {Bool.or(_, Ps.any_control(t)) == Bool.or(PackageSource.ps_control(c), PackageSource.ps_any_control(t)) : Bool}
      %Equal.sym(Bool, Ps.any_control(t), PackageSource.ps_any_control(t), psb.any_control(t)) : {Bool.or(PackageSource.ps_control(c), _) == Bool.or(PackageSource.ps_control(c), PackageSource.ps_any_control(t)) : Bool}
      {==}

def psb.arg.at(+dash: Bool, +ctl: Bool, +bs: Bool) -> {Ps.arg.at(dash, ctl, bs) == PackageSource.ps_arg.at(dash, ctl, bs) : Maybe<&2, Ps.Defect>}:
  match dash:
    case True{}:
      {==}
    case False{}:
      match ctl:
        case True{}:
          {==}
        case False{}:
          match bs:
            case True{}:
              {==}
            case False{}:
              {==}

def psb.arg(+s: String) -> {Ps.arg(s) == PackageSource.ps_arg(s) : Maybe<&2, Ps.Defect>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Ps.any_control(SCon{c, t}), PackageSource.ps_any_control(SCon{c, t}), psb.any_control(SCon{c, t})) : {Ps.arg.at(Char.is_eq(c, '-'), _, Ps.has(SCon{c, t}, Chr{92})) == PackageSource.ps_arg.at(Char.is_eq(c, '-'), PackageSource.ps_any_control(SCon{c, t}), PackageSource.ps_has(SCon{c, t}, Chr{92})) : Maybe<&2, Ps.Defect>}
      %Equal.sym(Bool, Ps.has(SCon{c, t}, Chr{92}), PackageSource.ps_has(SCon{c, t}, Chr{92}), psb.has(SCon{c, t}, Chr{92})) : {Ps.arg.at(Char.is_eq(c, '-'), PackageSource.ps_any_control(SCon{c, t}), _) == PackageSource.ps_arg.at(Char.is_eq(c, '-'), PackageSource.ps_any_control(SCon{c, t}), PackageSource.ps_has(SCon{c, t}, Chr{92})) : Maybe<&2, Ps.Defect>}
      psb.arg.at(Char.is_eq(c, '-'), PackageSource.ps_any_control(SCon{c, t}), PackageSource.ps_has(SCon{c, t}, Chr{92}))

def psb.seg.at(+dot: Bool, +drive: Bool) -> {Ps.seg.at(dot, drive) == PackageSource.ps_seg.at(dot, drive) : Maybe<&2, Ps.Defect>}:
  match dot:
    case True{}:
      {==}
    case False{}:
      match drive:
        case True{}:
          {==}
        case False{}:
          {==}

def psb.seg(+s: String) -> {Ps.seg(s) == PackageSource.ps_seg(s) : Maybe<&2, Ps.Defect>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      psb.seg.at(Bool.or(String.eq(SCon{c, t}, "."), String.eq(SCon{c, t}, "..")), Bool.and(Char.is_alpha(c), String.starts_with(t, ":")))

def psb.first.at(+m: Maybe<&2, Ps.Defect>, +r: Maybe<&2, Ps.Defect>) -> {Ps.first.at(m, r) == PackageSource.ps_first.at(m, r) : Maybe<&2, Ps.Defect>}:
  match m:
    case None{}:
      {==}
    case Some{+d}:
      {==}

def psb.segs(+xs: List<&2, String>) -> {Ps.segs(xs) == PackageSource.ps_segs(xs) : Maybe<&2, Ps.Defect>}:
  match xs:
    case Nil{}:
      {==}
    case +h <> +t:
      %Equal.sym(Maybe<&2, Ps.Defect>, Ps.seg(h), PackageSource.ps_seg(h), psb.seg(h)) : {Ps.first.at(_, Ps.segs(t)) == PackageSource.ps_first.at(PackageSource.ps_seg(h), PackageSource.ps_segs(t)) : Maybe<&2, Ps.Defect>}
      %Equal.sym(Maybe<&2, Ps.Defect>, Ps.segs(t), PackageSource.ps_segs(t), psb.segs(t)) : {Ps.first.at(PackageSource.ps_seg(h), _) == PackageSource.ps_first.at(PackageSource.ps_seg(h), PackageSource.ps_segs(t)) : Maybe<&2, Ps.Defect>}
      psb.first.at(PackageSource.ps_seg(h), PackageSource.ps_segs(t))

def psb.rel(+s: String) -> {Ps.rel(s) == PackageSource.ps_rel(s) : Maybe<&2, Ps.Defect>}:
  %Equal.sym(Maybe<&2, Ps.Defect>, Ps.arg(s), PackageSource.ps_arg(s), psb.arg(s)) : {Ps.first.at(_, Ps.segs(String.split(s, '/'))) == PackageSource.ps_first.at(PackageSource.ps_arg(s), PackageSource.ps_segs(String.split(s, '/'))) : Maybe<&2, Ps.Defect>}
  %Equal.sym(Maybe<&2, Ps.Defect>, Ps.segs(String.split(s, '/')), PackageSource.ps_segs(String.split(s, '/')), psb.segs(String.split(s, '/'))) : {Ps.first.at(PackageSource.ps_arg(s), _) == PackageSource.ps_first.at(PackageSource.ps_arg(s), PackageSource.ps_segs(String.split(s, '/'))) : Maybe<&2, Ps.Defect>}
  psb.first.at(PackageSource.ps_arg(s), PackageSource.ps_segs(String.split(s, '/')))

def psb.refcut.ok(+e: Bool, +a: String, +b: String) -> {Ps.refcut.ok(e, a, b) == PackageSource.ps_refcut.ok(e, a, b) : Maybe<&2, Ps.Cut>}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def psb.refcut.at(+m: Maybe<&2, Ps.Cut>) -> {Ps.refcut.at(m) == PackageSource.ps_refcut.at(m) : Maybe<&2, Ps.Cut>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+a, +b}:
          psb.refcut.ok(Bool.or(String.is_empty(a), String.is_empty(b)), a, b)

def psb.refcut(+s: String) -> {Ps.refcut(s) == PackageSource.ps_refcut(s) : Maybe<&2, Ps.Cut>}:
  %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(s, '@'), PackageSource.ps_cut(s, '@'), psb.cut(s, '@')) : {Ps.refcut.at(_) == PackageSource.ps_refcut.at(PackageSource.ps_cut(s, '@')) : Maybe<&2, Ps.Cut>}
  psb.refcut.at(PackageSource.ps_cut(s, '@'))

def psb.sref.scp.at(+h: String, +m: Maybe<&2, Ps.Cut>, +u: String) -> {Ps.sref.scp.at(h, m, u) == PackageSource.ps_sref.scp.at(h, m, u) : Ps.Refd}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+p, +r}:
          {==}

def psb.sref.url.at(+sc: String, +a: String, +m: Maybe<&2, Ps.Cut>, +u: String) -> {Ps.sref.url.at(sc, a, m, u) == PackageSource.ps_sref.url.at(sc, a, m, u) : Ps.Refd}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+p, +r}:
          {==}

def psb.sref.short.at(+h: String, +m: Maybe<&2, Ps.Cut>, +u: String) -> {Ps.sref.short.at(h, m, u) == PackageSource.ps_sref.short.at(h, m, u) : Ps.Refd}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+p, +r}:
          {==}

def psb.sref.short(+m: Maybe<&2, Ps.Cut>, +u: String) -> {Ps.sref.short(m, u) == PackageSource.ps_sref.short(m, u) : Ps.Refd}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+h, +p}:
          %Equal.sym(Maybe<&2, Ps.Cut>, Ps.refcut(p), PackageSource.ps_refcut(p), psb.refcut(p)) : {Ps.sref.short.at(h, _, u) == PackageSource.ps_sref.short.at(h, PackageSource.ps_refcut(p), u) : Ps.Refd}
          psb.sref.short.at(h, PackageSource.ps_refcut(p), u)

def psb.sref.url(+m: Maybe<&2, Ps.Url>, +u: String) -> {Ps.sref.url(m, u) == PackageSource.ps_sref.url(m, u) : Ps.Refd}:
  match m:
    case None{}:
      %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(u, '/'), PackageSource.ps_cut(u, '/'), psb.cut(u, '/')) : {Ps.sref.short(_, u) == PackageSource.ps_sref.short(PackageSource.ps_cut(u, '/'), u) : Ps.Refd}
      psb.sref.short(PackageSource.ps_cut(u, '/'), u)
    case Some{+x}:
      match x:
        case Ps.Url{+sc, +a, +p}:
          %Equal.sym(String, Ps.lslash(p), PackageSource.ps_lslash(p), psb.lslash(p)) : {Ps.sref.url.at(sc, a, Ps.refcut(_), u) == PackageSource.ps_sref.url.at(sc, a, PackageSource.ps_refcut(PackageSource.ps_lslash(p)), u) : Ps.Refd}
          %Equal.sym(Maybe<&2, Ps.Cut>, Ps.refcut(PackageSource.ps_lslash(p)), PackageSource.ps_refcut(PackageSource.ps_lslash(p)), psb.refcut(PackageSource.ps_lslash(p))) : {Ps.sref.url.at(sc, a, _, u) == PackageSource.ps_sref.url.at(sc, a, PackageSource.ps_refcut(PackageSource.ps_lslash(p)), u) : Ps.Refd}
          psb.sref.url.at(sc, a, PackageSource.ps_refcut(PackageSource.ps_lslash(p)), u)

def psb.sref.scp(+m: Maybe<&2, Ps.Cut>, +u: String) -> {Ps.sref.scp(m, u) == PackageSource.ps_sref.scp(m, u) : Ps.Refd}:
  match m:
    case None{}:
      %Equal.sym(Maybe<&2, Ps.Url>, Ps.url(u), PackageSource.ps_url(u), psb.url(u)) : {Ps.sref.url(_, u) == PackageSource.ps_sref.url(PackageSource.ps_url(u), u) : Ps.Refd}
      psb.sref.url(PackageSource.ps_url(u), u)
    case Some{+x}:
      match x:
        case Ps.Cut{+h, +p}:
          %Equal.sym(Maybe<&2, Ps.Cut>, Ps.refcut(p), PackageSource.ps_refcut(p), psb.refcut(p)) : {Ps.sref.scp.at(h, _, u) == PackageSource.ps_sref.scp.at(h, PackageSource.ps_refcut(p), u) : Ps.Refd}
          psb.sref.scp.at(h, PackageSource.ps_refcut(p), u)

def psb.sref.at(+b: Bool, +u: String) -> {Ps.sref.at(b, u) == PackageSource.ps_sref.at(b, u) : Ps.Refd}:
  match b:
    case True{}:
      %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(String.drop(u, 4n), ':'), PackageSource.ps_cut(String.drop(u, 4n), ':'), psb.cut(String.drop(u, 4n), ':')) : {Ps.sref.scp(_, u) == PackageSource.ps_sref.scp(PackageSource.ps_cut(String.drop(u, 4n), ':'), u) : Ps.Refd}
      psb.sref.scp(PackageSource.ps_cut(String.drop(u, 4n), ':'), u)
    case False{}:
      %Equal.sym(Maybe<&2, Ps.Url>, Ps.url(u), PackageSource.ps_url(u), psb.url(u)) : {Ps.sref.url(_, u) == PackageSource.ps_sref.url(PackageSource.ps_url(u), u) : Ps.Refd}
      psb.sref.url(PackageSource.ps_url(u), u)

def psb.sref(+u: String) -> {Ps.sref(u) == PackageSource.ps_sref(u) : Ps.Refd}:
  psb.sref.at(String.starts_with(u, "git@"), u)

def psb.short.at(+a: Bool, +b: Bool, +c: Bool, +d: Bool, +u: String) -> {Ps.short.at(a, b, c, d, u) == PackageSource.ps_short.at(a, b, c, d, u) : Maybe<&2, Ps.Cut>}:
  match a:
    case True{}:
      {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          match c:
            case True{}:
              {==}
            case False{}:
              match d:
                case True{}:
                  {==}
                case False{}:
                  {==}

def psb.short(+u: String) -> {Ps.short(u) == PackageSource.ps_short(u) : Maybe<&2, Ps.Cut>}:
  psb.short.at(String.starts_with(u, "github:"), String.starts_with(u, "gitlab:"), String.starts_with(u, "bitbucket:"), String.starts_with(u, "gist:"), u)

def psb.hosted.ok(+e: Bool, +d: String, +u: String, +p: String, +k: Maybe<&2, String>) -> {Ps.hosted.ok(e, d, u, p, k) == PackageSource.ps_hosted.ok(e, d, u, p, k) : Maybe<&2, Ps.Hosted>}:
  match e:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(String, Ps.unsuffix(p), PackageSource.ps_unsuffix(p), psb.unsuffix(p)) : {Some{Ps.Hosted{d, u, _, k}} == Some{Ps.Hosted{d, u, PackageSource.ps_unsuffix(p), k}} : Maybe<&2, Ps.Hosted>}
      {==}

def psb.hosted.parts(+d: String, +m: Maybe<&2, Ps.Cut>, +k: Maybe<&2, String>) -> {Ps.hosted.parts(d, m, k) == PackageSource.ps_hosted.parts(d, m, k) : Maybe<&2, Ps.Hosted>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+u, +p}:
          psb.hosted.ok(Bool.or(String.is_empty(u), String.is_empty(p)), d, u, p, k)

def psb.hosted.short(+m: Maybe<&2, Ps.Cut>, +k: Maybe<&2, String>) -> {Ps.hosted.short(m, k) == PackageSource.ps_hosted.short(m, k) : Maybe<&2, Ps.Hosted>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+d, +rest}:
          %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(rest, '/'), PackageSource.ps_cut(rest, '/'), psb.cut(rest, '/')) : {Ps.hosted.parts(d, _, k) == PackageSource.ps_hosted.parts(d, PackageSource.ps_cut(rest, '/'), k) : Maybe<&2, Ps.Hosted>}
          psb.hosted.parts(d, PackageSource.ps_cut(rest, '/'), k)

def psb.hosted.at(+m: Maybe<&2, Ps.Cut>, +c: String) -> {Ps.hosted.at(m, c) == PackageSource.ps_hosted.at(m, c) : Maybe<&2, Ps.Hosted>}:
  match m:
    case None{}:
      %Equal.sym(Maybe<&2, Ps.Cut>, Ps.short(c), PackageSource.ps_short(c), psb.short(c)) : {Ps.hosted.short(_, None{}) == PackageSource.ps_hosted.short(PackageSource.ps_short(c), None{}) : Maybe<&2, Ps.Hosted>}
      psb.hosted.short(PackageSource.ps_short(c), None{})
    case Some{+x}:
      match x:
        case Ps.Cut{+u, +k}:
          %Equal.sym(Maybe<&2, Ps.Cut>, Ps.short(u), PackageSource.ps_short(u), psb.short(u)) : {Ps.hosted.short(_, Some{k}) == PackageSource.ps_hosted.short(PackageSource.ps_short(u), Some{k}) : Maybe<&2, Ps.Hosted>}
          psb.hosted.short(PackageSource.ps_short(u), Some{k})

def psb.hosted(+c: String) -> {Ps.hosted(c) == PackageSource.ps_hosted(c) : Maybe<&2, Ps.Hosted>}:
  %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(c, '#'), PackageSource.ps_cut(c, '#'), psb.cut(c, '#')) : {Ps.hosted.at(_, c) == PackageSource.ps_hosted.at(PackageSource.ps_cut(c, '#'), c) : Maybe<&2, Ps.Hosted>}
  psb.hosted.at(PackageSource.ps_cut(c, '#'), c)

def psb.keep.at(+drop: Bool, +h: Ps.Hosted) -> {Ps.keep.at(drop, h) == PackageSource.ps_keep.at(drop, h) : Maybe<&2, Ps.Hosted>}:
  match drop:
    case True{}:
      {==}
    case False{}:
      {==}

def psb.keep.of(+h: Ps.Hosted, +r: Bool) -> {Ps.keep.of(h, r) == PackageSource.ps_keep.of(h, r) : Maybe<&2, Ps.Hosted>}:
  match h:
    case Ps.Hosted{+d, +u, +p, +k}:
      %Equal.sym(Bool, Ps.has(p, '@'), PackageSource.ps_has(p, '@'), psb.has(p, '@')) : {Ps.keep.at(Bool.and(r, _), Ps.Hosted{d, u, p, k}) == PackageSource.ps_keep.at(Bool.and(r, PackageSource.ps_has(p, '@')), Ps.Hosted{d, u, p, k}) : Maybe<&2, Ps.Hosted>}
      psb.keep.at(Bool.and(r, PackageSource.ps_has(p, '@')), Ps.Hosted{d, u, p, k})

def psb.keep(+m: Maybe<&2, Ps.Hosted>, +r: Bool) -> {Ps.keep(m, r) == PackageSource.ps_keep(m, r) : Maybe<&2, Ps.Hosted>}:
  match m:
    case None{}:
      {==}
    case Some{+h}:
      psb.keep.of(h, r)

def psb.pick(+a: Maybe<&2, Ps.Hosted>, +b: Maybe<&2, Ps.Hosted>) -> {Ps.pick(a, b) == PackageSource.ps_pick(a, b) : Maybe<&2, Ps.Hosted>}:
  match a:
    case None{}:
      {==}
    case Some{+h}:
      {==}

def psb.cand.at(+repo: String, +m: Maybe<&2, String>) -> {Ps.cand.at(repo, m) == PackageSource.ps_cand.at(repo, m) : Maybe<&2, Ps.Hosted>}:
  match m:
    case None{}:
      {==}
    case Some{+r}:
      %Equal.sym(Maybe<&2, Ps.Hosted>, Ps.hosted(String.concat([repo, "#", r])), PackageSource.ps_hosted(String.concat([repo, "#", r])), psb.hosted(String.concat([repo, "#", r]))) : {Ps.keep(_, True{}) == PackageSource.ps_keep(PackageSource.ps_hosted(String.concat([repo, "#", r])), True{}) : Maybe<&2, Ps.Hosted>}
      psb.keep(PackageSource.ps_hosted(String.concat([repo, "#", r])), True{})

def psb.cand(+rd: Ps.Refd) -> {Ps.cand(rd) == PackageSource.ps_cand(rd) : Maybe<&2, Ps.Hosted>}:
  match rd:
    case Ps.Refd{+repo, +m}:
      psb.cand.at(repo, m)

def psb.or_ref(+a: Maybe<&2, String>, +b: Maybe<&2, String>) -> {Ps.or_ref(a, b) == PackageSource.ps_or_ref(a, b) : Maybe<&2, String>}:
  match a:
    case None{}:
      {==}
    case Some{+x}:
      {==}

def psb.https.at(+b: Bool, +r: String) -> {Ps.https.at(b, r) == PackageSource.ps_https.at(b, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def psb.https(+r: String) -> {Ps.https(r) == PackageSource.ps_https(r) : String}:
  psb.https.at(Bool.or(String.starts_with(r, "http://"), Bool.or(String.starts_with(r, "https://"), Bool.or(String.starts_with(r, "ssh://"), Bool.or(String.starts_with(r, "git://"), String.starts_with(r, "git@"))))), r)

def psb.from_hosted.at(+h: Ps.Hosted, +repo: String, +r: Maybe<&2, String>) -> {Ps.from_hosted.at(h, repo, r) == PackageSource.ps_from_hosted.at(h, repo, r) : Ps.GitSrc}:
  match h:
    case Ps.Hosted{+d, +u, +p, +k}:
      %Equal.sym(String, Ps.https(repo), PackageSource.ps_https(repo), psb.https(repo)) : {Ps.GitSrc{_, d, String.concat([u, "/", p]), Ps.or_ref(k, r), Bool.or(Ps.is_some(k), Ps.is_some(r))} == Ps.GitSrc{PackageSource.ps_https(repo), d, String.concat([u, "/", p]), PackageSource.ps_or_ref(k, r), Bool.or(PackageSource.ps_is_some(k), PackageSource.ps_is_some(r))} : Ps.GitSrc}
      %Equal.sym(Maybe<&2, String>, Ps.or_ref(k, r), PackageSource.ps_or_ref(k, r), psb.or_ref(k, r)) : {Ps.GitSrc{PackageSource.ps_https(repo), d, String.concat([u, "/", p]), _, Bool.or(Ps.is_some(k), Ps.is_some(r))} == Ps.GitSrc{PackageSource.ps_https(repo), d, String.concat([u, "/", p]), PackageSource.ps_or_ref(k, r), Bool.or(PackageSource.ps_is_some(k), PackageSource.ps_is_some(r))} : Ps.GitSrc}
      %Equal.sym(Bool, Ps.is_some(k), PackageSource.ps_is_some(k), psb.is_some(k)) : {Ps.GitSrc{PackageSource.ps_https(repo), d, String.concat([u, "/", p]), PackageSource.ps_or_ref(k, r), Bool.or(_, Ps.is_some(r))} == Ps.GitSrc{PackageSource.ps_https(repo), d, String.concat([u, "/", p]), PackageSource.ps_or_ref(k, r), Bool.or(PackageSource.ps_is_some(k), PackageSource.ps_is_some(r))} : Ps.GitSrc}
      %Equal.sym(Bool, Ps.is_some(r), PackageSource.ps_is_some(r), psb.is_some(r)) : {Ps.GitSrc{PackageSource.ps_https(repo), d, String.concat([u, "/", p]), PackageSource.ps_or_ref(k, r), Bool.or(PackageSource.ps_is_some(k), _)} == Ps.GitSrc{PackageSource.ps_https(repo), d, String.concat([u, "/", p]), PackageSource.ps_or_ref(k, r), Bool.or(PackageSource.ps_is_some(k), PackageSource.ps_is_some(r))} : Ps.GitSrc}
      {==}

def psb.from_hosted(+h: Ps.Hosted, +rd: Ps.Refd) -> {Ps.from_hosted(h, rd) == PackageSource.ps_from_hosted(h, rd) : Ps.GitSrc}:
  match rd:
    case Ps.Refd{+repo, +r}:
      psb.from_hosted.at(h, repo, r)

def psb.shape.at(+bad: Bool, +h: String, +q: String, +clone: String, +r: Maybe<&2, String>) -> {Ps.shape.at(bad, h, q, clone, r) == PackageSource.ps_shape.at(bad, h, q, clone, r) : Maybe<&2, Ps.GitSrc>}:
  match bad:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Bool, Ps.is_some(r), PackageSource.ps_is_some(r), psb.is_some(r)) : {Some{Ps.GitSrc{clone, h, q, r, _}} == Some{Ps.GitSrc{clone, h, q, r, PackageSource.ps_is_some(r)}} : Maybe<&2, Ps.GitSrc>}
      {==}

def psb.shape(+h: String, +p: String, +clone: String, +r: Maybe<&2, String>) -> {Ps.shape(h, p, clone, r) == PackageSource.ps_shape(h, p, clone, r) : Maybe<&2, Ps.GitSrc>}:
  %Equal.sym(String, Ps.unsuffix(p), PackageSource.ps_unsuffix(p), psb.unsuffix(p)) : {Ps.shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(Ps.lslash(_)), Bool.not(Ps.has(Ps.lslash(Ps.unsuffix(p)), '/')))), h, Ps.lslash(Ps.unsuffix(p)), clone, r) == PackageSource.ps_shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(PackageSource.ps_has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/')))), h, PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), clone, r) : Maybe<&2, Ps.GitSrc>}
  %Equal.sym(String, Ps.lslash(PackageSource.ps_unsuffix(p)), PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), psb.lslash(PackageSource.ps_unsuffix(p))) : {Ps.shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(_), Bool.not(Ps.has(Ps.lslash(Ps.unsuffix(p)), '/')))), h, Ps.lslash(Ps.unsuffix(p)), clone, r) == PackageSource.ps_shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(PackageSource.ps_has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/')))), h, PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), clone, r) : Maybe<&2, Ps.GitSrc>}
  %Equal.sym(String, Ps.unsuffix(p), PackageSource.ps_unsuffix(p), psb.unsuffix(p)) : {Ps.shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(Ps.has(Ps.lslash(_), '/')))), h, Ps.lslash(Ps.unsuffix(p)), clone, r) == PackageSource.ps_shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(PackageSource.ps_has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/')))), h, PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), clone, r) : Maybe<&2, Ps.GitSrc>}
  %Equal.sym(String, Ps.lslash(PackageSource.ps_unsuffix(p)), PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), psb.lslash(PackageSource.ps_unsuffix(p))) : {Ps.shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(Ps.has(_, '/')))), h, Ps.lslash(Ps.unsuffix(p)), clone, r) == PackageSource.ps_shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(PackageSource.ps_has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/')))), h, PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), clone, r) : Maybe<&2, Ps.GitSrc>}
  %Equal.sym(Bool, Ps.has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/'), PackageSource.ps_has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/'), psb.has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/')) : {Ps.shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(_))), h, Ps.lslash(Ps.unsuffix(p)), clone, r) == PackageSource.ps_shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(PackageSource.ps_has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/')))), h, PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), clone, r) : Maybe<&2, Ps.GitSrc>}
  %Equal.sym(String, Ps.unsuffix(p), PackageSource.ps_unsuffix(p), psb.unsuffix(p)) : {Ps.shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(PackageSource.ps_has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/')))), h, Ps.lslash(_), clone, r) == PackageSource.ps_shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(PackageSource.ps_has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/')))), h, PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), clone, r) : Maybe<&2, Ps.GitSrc>}
  %Equal.sym(String, Ps.lslash(PackageSource.ps_unsuffix(p)), PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), psb.lslash(PackageSource.ps_unsuffix(p))) : {Ps.shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(PackageSource.ps_has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/')))), h, _, clone, r) == PackageSource.ps_shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(PackageSource.ps_has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/')))), h, PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), clone, r) : Maybe<&2, Ps.GitSrc>}
  psb.shape.at(Bool.or(String.is_empty(h), Bool.or(String.is_empty(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p))), Bool.not(PackageSource.ps_has(PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), '/')))), h, PackageSource.ps_lslash(PackageSource.ps_unsuffix(p)), clone, r)

def psb.generic.scp(+m: Maybe<&2, Ps.Cut>, +repo: String, +r: Maybe<&2, String>) -> {Ps.generic.scp(m, repo, r) == PackageSource.ps_generic.scp(m, repo, r) : Maybe<&2, Ps.GitSrc>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+h, +p}:
          psb.shape(h, p, repo, r)

def psb.generic.url(+m: Maybe<&2, Ps.Url>, +repo: String, +r: Maybe<&2, String>) -> {Ps.generic.url(m, repo, r) == PackageSource.ps_generic.url(m, repo, r) : Maybe<&2, Ps.GitSrc>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Url{+sc, +a, +p}:
          %Equal.sym(String, Ps.host_of(a), PackageSource.ps_host_of(a), psb.host_of(a)) : {Ps.shape(_, Ps.lslash(p), repo, r) == PackageSource.ps_shape(PackageSource.ps_host_of(a), PackageSource.ps_lslash(p), repo, r) : Maybe<&2, Ps.GitSrc>}
          %Equal.sym(String, Ps.lslash(p), PackageSource.ps_lslash(p), psb.lslash(p)) : {Ps.shape(PackageSource.ps_host_of(a), _, repo, r) == PackageSource.ps_shape(PackageSource.ps_host_of(a), PackageSource.ps_lslash(p), repo, r) : Maybe<&2, Ps.GitSrc>}
          psb.shape(PackageSource.ps_host_of(a), PackageSource.ps_lslash(p), repo, r)

def psb.generic.dot(+ok: Bool, +h: String, +p: String, +repo: String, +r: Maybe<&2, String>) -> {Ps.generic.dot(ok, h, p, repo, r) == PackageSource.ps_generic.dot(ok, h, p, repo, r) : Maybe<&2, Ps.GitSrc>}:
  match ok:
    case True{}:
      psb.shape(h, p, String.append("https://", repo), r)
    case False{}:
      {==}

def psb.generic.short(+m: Maybe<&2, Ps.Cut>, +repo: String, +r: Maybe<&2, String>) -> {Ps.generic.short(m, repo, r) == PackageSource.ps_generic.short(m, repo, r) : Maybe<&2, Ps.GitSrc>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+h, +p}:
          %Equal.sym(Bool, Ps.has(h, '.'), PackageSource.ps_has(h, '.'), psb.has(h, '.')) : {Ps.generic.dot(Bool.or(_, String.eq(h, "localhost")), h, p, repo, r) == PackageSource.ps_generic.dot(Bool.or(PackageSource.ps_has(h, '.'), String.eq(h, "localhost")), h, p, repo, r) : Maybe<&2, Ps.GitSrc>}
          psb.generic.dot(Bool.or(PackageSource.ps_has(h, '.'), String.eq(h, "localhost")), h, p, repo, r)

def psb.generic.at(+scp: Bool, +pu: Bool, +repo: String, +r: Maybe<&2, String>) -> {Ps.generic.at(scp, pu, repo, r) == PackageSource.ps_generic.at(scp, pu, repo, r) : Maybe<&2, Ps.GitSrc>}:
  match scp:
    case True{}:
      %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(String.drop(repo, 4n), ':'), PackageSource.ps_cut(String.drop(repo, 4n), ':'), psb.cut(String.drop(repo, 4n), ':')) : {Ps.generic.scp(_, repo, r) == PackageSource.ps_generic.scp(PackageSource.ps_cut(String.drop(repo, 4n), ':'), repo, r) : Maybe<&2, Ps.GitSrc>}
      psb.generic.scp(PackageSource.ps_cut(String.drop(repo, 4n), ':'), repo, r)
    case False{}:
      match pu:
        case True{}:
          %Equal.sym(Maybe<&2, Ps.Url>, Ps.url(repo), PackageSource.ps_url(repo), psb.url(repo)) : {Ps.generic.url(_, repo, r) == PackageSource.ps_generic.url(PackageSource.ps_url(repo), repo, r) : Maybe<&2, Ps.GitSrc>}
          psb.generic.url(PackageSource.ps_url(repo), repo, r)
        case False{}:
          %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(repo, '/'), PackageSource.ps_cut(repo, '/'), psb.cut(repo, '/')) : {Ps.generic.short(_, repo, r) == PackageSource.ps_generic.short(PackageSource.ps_cut(repo, '/'), repo, r) : Maybe<&2, Ps.GitSrc>}
          psb.generic.short(PackageSource.ps_cut(repo, '/'), repo, r)

def psb.generic(+rd: Ps.Refd) -> {Ps.generic(rd) == PackageSource.ps_generic(rd) : Maybe<&2, Ps.GitSrc>}:
  match rd:
    case Ps.Refd{+repo, +r}:
      %Equal.sym(Bool, Ps.proto_url(repo), PackageSource.ps_proto_url(repo), psb.proto_url(repo)) : {Ps.generic.at(String.starts_with(repo, "git@"), _, repo, r) == PackageSource.ps_generic.at(String.starts_with(repo, "git@"), PackageSource.ps_proto_url(repo), repo, r) : Maybe<&2, Ps.GitSrc>}
      psb.generic.at(String.starts_with(repo, "git@"), PackageSource.ps_proto_url(repo), repo, r)

def psb.found.at(+m: Maybe<&2, Ps.Hosted>, +rd: Ps.Refd) -> {Ps.found.at(m, rd) == PackageSource.ps_found.at(m, rd) : Maybe<&2, Ps.GitSrc>}:
  match m:
    case None{}:
      psb.generic(rd)
    case Some{+h}:
      %Equal.sym(Ps.GitSrc, Ps.from_hosted(h, rd), PackageSource.ps_from_hosted(h, rd), psb.from_hosted(h, rd)) : {Some{_} == Some{PackageSource.ps_from_hosted(h, rd)} : Maybe<&2, Ps.GitSrc>}
      {==}

def psb.ref_some(+rd: Ps.Refd) -> {Ps.ref_some(rd) == PackageSource.ps_ref_some(rd) : Bool}:
  match rd:
    case Ps.Refd{+repo, +m}:
      psb.is_some(m)

def psb.found(+u: String, +rd: Ps.Refd) -> {Ps.found(u, rd) == PackageSource.ps_found(u, rd) : Maybe<&2, Ps.GitSrc>}:
  %Equal.sym(Maybe<&2, Ps.Hosted>, Ps.cand(rd), PackageSource.ps_cand(rd), psb.cand(rd)) : {Ps.found.at(Ps.pick(_, Ps.keep(Ps.hosted(u), Ps.ref_some(rd))), rd) == PackageSource.ps_found.at(PackageSource.ps_pick(PackageSource.ps_cand(rd), PackageSource.ps_keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd))), rd) : Maybe<&2, Ps.GitSrc>}
  %Equal.sym(Maybe<&2, Ps.Hosted>, Ps.hosted(u), PackageSource.ps_hosted(u), psb.hosted(u)) : {Ps.found.at(Ps.pick(PackageSource.ps_cand(rd), Ps.keep(_, Ps.ref_some(rd))), rd) == PackageSource.ps_found.at(PackageSource.ps_pick(PackageSource.ps_cand(rd), PackageSource.ps_keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd))), rd) : Maybe<&2, Ps.GitSrc>}
  %Equal.sym(Bool, Ps.ref_some(rd), PackageSource.ps_ref_some(rd), psb.ref_some(rd)) : {Ps.found.at(Ps.pick(PackageSource.ps_cand(rd), Ps.keep(PackageSource.ps_hosted(u), _)), rd) == PackageSource.ps_found.at(PackageSource.ps_pick(PackageSource.ps_cand(rd), PackageSource.ps_keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd))), rd) : Maybe<&2, Ps.GitSrc>}
  %Equal.sym(Maybe<&2, Ps.Hosted>, Ps.keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd)), PackageSource.ps_keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd)), psb.keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd))) : {Ps.found.at(Ps.pick(PackageSource.ps_cand(rd), _), rd) == PackageSource.ps_found.at(PackageSource.ps_pick(PackageSource.ps_cand(rd), PackageSource.ps_keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd))), rd) : Maybe<&2, Ps.GitSrc>}
  %Equal.sym(Maybe<&2, Ps.Hosted>, Ps.pick(PackageSource.ps_cand(rd), PackageSource.ps_keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd))), PackageSource.ps_pick(PackageSource.ps_cand(rd), PackageSource.ps_keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd))), psb.pick(PackageSource.ps_cand(rd), PackageSource.ps_keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd)))) : {Ps.found.at(_, rd) == PackageSource.ps_found.at(PackageSource.ps_pick(PackageSource.ps_cand(rd), PackageSource.ps_keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd))), rd) : Maybe<&2, Ps.GitSrc>}
  psb.found.at(PackageSource.ps_pick(PackageSource.ps_cand(rd), PackageSource.ps_keep(PackageSource.ps_hosted(u), PackageSource.ps_ref_some(rd))), rd)

def psb.on(+p: Ps.Part, +m: Maybe<&2, Ps.Defect>) -> {Ps.on(p, m) == PackageSource.ps_on(p, m) : Maybe<&2, Ps.Flaw>}:
  match m:
    case None{}:
      {==}
    case Some{+d}:
      {==}

def psb.host.at(+b: Bool, +h: String) -> {Ps.host.at(b, h) == PackageSource.ps_host.at(b, h) : Maybe<&2, Ps.Defect>}:
  match b:
    case True{}:
      {==}
    case False{}:
      psb.rel(h)

def psb.gref(+m: Maybe<&2, String>) -> {Ps.gref(m) == PackageSource.ps_gref(m) : Maybe<&2, Ps.Flaw>}:
  match m:
    case None{}:
      {==}
    case Some{+r}:
      %Equal.sym(Maybe<&2, Ps.Defect>, Ps.arg(r), PackageSource.ps_arg(r), psb.arg(r)) : {Ps.on(Ps.PRef{}, _) == PackageSource.ps_on(Ps.PRef{}, PackageSource.ps_arg(r)) : Maybe<&2, Ps.Flaw>}
      psb.on(Ps.PRef{}, PackageSource.ps_arg(r))

def psb.dash.ok(+b: Bool) -> {Ps.dash.ok(b) == PackageSource.ps_dash.ok(b) : Maybe<&2, Ps.Flaw>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def psb.dash.at(+m: Maybe<&2, Ps.Cut>) -> {Ps.dash.at(m) == PackageSource.ps_dash.at(m) : Maybe<&2, Ps.Flaw>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+s, +a}:
          psb.dash.ok(String.starts_with(a, "-"))

def psb.flaw.or(+m: Maybe<&2, Ps.Flaw>, +r: Maybe<&2, Ps.Flaw>) -> {Ps.flaw.or(m, r) == PackageSource.ps_flaw.or(m, r) : Maybe<&2, Ps.Flaw>}:
  match m:
    case None{}:
      {==}
    case Some{+f}:
      {==}

def psb.flaws(+g: Ps.GitSrc) -> {Ps.flaws(g) == PackageSource.ps_flaws(g) : Maybe<&2, Ps.Flaw>}:
  match g:
    case Ps.GitSrc{+repo, +h, +p, +r, +n}:
      %Equal.sym(Bool, Ps.has(h, '/'), PackageSource.ps_has(h, '/'), psb.has(h, '/')) : {Ps.flaw.or(Ps.on(Ps.PHost{}, Ps.host.at(_, h)), Ps.flaw.or(Ps.on(Ps.PPath{}, Ps.rel(p)), Ps.flaw.or(Ps.gref(r), Ps.flaw.or(Ps.on(Ps.PClone{}, Ps.arg(repo)), Ps.dash.at(Ps.proto(repo)))))) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Defect>, Ps.host.at(PackageSource.ps_has(h, '/'), h), PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h), psb.host.at(PackageSource.ps_has(h, '/'), h)) : {Ps.flaw.or(Ps.on(Ps.PHost{}, _), Ps.flaw.or(Ps.on(Ps.PPath{}, Ps.rel(p)), Ps.flaw.or(Ps.gref(r), Ps.flaw.or(Ps.on(Ps.PClone{}, Ps.arg(repo)), Ps.dash.at(Ps.proto(repo)))))) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Flaw>, Ps.on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), psb.on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h))) : {Ps.flaw.or(_, Ps.flaw.or(Ps.on(Ps.PPath{}, Ps.rel(p)), Ps.flaw.or(Ps.gref(r), Ps.flaw.or(Ps.on(Ps.PClone{}, Ps.arg(repo)), Ps.dash.at(Ps.proto(repo)))))) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Defect>, Ps.rel(p), PackageSource.ps_rel(p), psb.rel(p)) : {Ps.flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), Ps.flaw.or(Ps.on(Ps.PPath{}, _), Ps.flaw.or(Ps.gref(r), Ps.flaw.or(Ps.on(Ps.PClone{}, Ps.arg(repo)), Ps.dash.at(Ps.proto(repo)))))) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Flaw>, Ps.on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), psb.on(Ps.PPath{}, PackageSource.ps_rel(p))) : {Ps.flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), Ps.flaw.or(_, Ps.flaw.or(Ps.gref(r), Ps.flaw.or(Ps.on(Ps.PClone{}, Ps.arg(repo)), Ps.dash.at(Ps.proto(repo)))))) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Flaw>, Ps.gref(r), PackageSource.ps_gref(r), psb.gref(r)) : {Ps.flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), Ps.flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), Ps.flaw.or(_, Ps.flaw.or(Ps.on(Ps.PClone{}, Ps.arg(repo)), Ps.dash.at(Ps.proto(repo)))))) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Defect>, Ps.arg(repo), PackageSource.ps_arg(repo), psb.arg(repo)) : {Ps.flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), Ps.flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), Ps.flaw.or(PackageSource.ps_gref(r), Ps.flaw.or(Ps.on(Ps.PClone{}, _), Ps.dash.at(Ps.proto(repo)))))) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Flaw>, Ps.on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), psb.on(Ps.PClone{}, PackageSource.ps_arg(repo))) : {Ps.flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), Ps.flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), Ps.flaw.or(PackageSource.ps_gref(r), Ps.flaw.or(_, Ps.dash.at(Ps.proto(repo)))))) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Cut>, Ps.proto(repo), PackageSource.ps_proto(repo), psb.proto(repo)) : {Ps.flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), Ps.flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), Ps.flaw.or(PackageSource.ps_gref(r), Ps.flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), Ps.dash.at(_))))) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Flaw>, Ps.dash.at(PackageSource.ps_proto(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)), psb.dash.at(PackageSource.ps_proto(repo))) : {Ps.flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), Ps.flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), Ps.flaw.or(PackageSource.ps_gref(r), Ps.flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), _)))) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Flaw>, Ps.flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo))), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo))), psb.flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))) : {Ps.flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), Ps.flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), Ps.flaw.or(PackageSource.ps_gref(r), _))) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Flaw>, Ps.flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))), psb.flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo))))) : {Ps.flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), Ps.flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), _)) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      %Equal.sym(Maybe<&2, Ps.Flaw>, Ps.flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo))))), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo))))), psb.flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : {Ps.flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), _) == PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo)))))) : Maybe<&2, Ps.Flaw>}
      psb.flaw.or(PackageSource.ps_on(Ps.PHost{}, PackageSource.ps_host.at(PackageSource.ps_has(h, '/'), h)), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PPath{}, PackageSource.ps_rel(p)), PackageSource.ps_flaw.or(PackageSource.ps_gref(r), PackageSource.ps_flaw.or(PackageSource.ps_on(Ps.PClone{}, PackageSource.ps_arg(repo)), PackageSource.ps_dash.at(PackageSource.ps_proto(repo))))))

def psb.checked.at(+m: Maybe<&2, Ps.Flaw>, +g: Ps.GitSrc) -> {Ps.checked.at(m, g) == PackageSource.ps_checked.at(m, g) : Ps.GitAns}:
  match m:
    case None{}:
      {==}
    case Some{+f}:
      {==}

def psb.checked(+m: Maybe<&2, Ps.GitSrc>) -> {Ps.checked(m) == PackageSource.ps_checked(m) : Ps.GitAns}:
  match m:
    case None{}:
      {==}
    case Some{+g}:
      %Equal.sym(Maybe<&2, Ps.Flaw>, Ps.flaws(g), PackageSource.ps_flaws(g), psb.flaws(g)) : {Ps.checked.at(_, g) == PackageSource.ps_checked.at(PackageSource.ps_flaws(g), g) : Ps.GitAns}
      psb.checked.at(PackageSource.ps_flaws(g), g)

def psb.git.gate(+go: Bool, +u: String) -> {Ps.git.gate(go, u) == PackageSource.ps_git.gate(go, u) : Ps.GitAns}:
  match go:
    case True{}:
      %Equal.sym(Ps.Refd, Ps.sref(u), PackageSource.ps_sref(u), psb.sref(u)) : {Ps.checked(Ps.found(u, _)) == PackageSource.ps_checked(PackageSource.ps_found(u, PackageSource.ps_sref(u))) : Ps.GitAns}
      %Equal.sym(Maybe<&2, Ps.GitSrc>, Ps.found(u, PackageSource.ps_sref(u)), PackageSource.ps_found(u, PackageSource.ps_sref(u)), psb.found(u, PackageSource.ps_sref(u))) : {Ps.checked(_) == PackageSource.ps_checked(PackageSource.ps_found(u, PackageSource.ps_sref(u))) : Ps.GitAns}
      psb.checked(PackageSource.ps_found(u, PackageSource.ps_sref(u)))
    case False{}:
      {==}

def psb.git.at(+b: Bool, +t: String) -> {Ps.git.at(b, t) == PackageSource.ps_git.at(b, t) : Ps.GitAns}:
  match b:
    case True{}:
      %Equal.sym(String, Ps.trim(String.drop(t, 4n)), PackageSource.ps_trim(String.drop(t, 4n)), psb.trim(String.drop(t, 4n))) : {Ps.git.gate(True{}, _) == PackageSource.ps_git.gate(True{}, PackageSource.ps_trim(String.drop(t, 4n))) : Ps.GitAns}
      psb.git.gate(True{}, PackageSource.ps_trim(String.drop(t, 4n)))
    case False{}:
      %Equal.sym(Bool, Ps.proto_url(t), PackageSource.ps_proto_url(t), psb.proto_url(t)) : {Ps.git.gate(_, t) == PackageSource.ps_git.gate(PackageSource.ps_proto_url(t), t) : Ps.GitAns}
      psb.git.gate(PackageSource.ps_proto_url(t), t)

def psb.git(+s: String) -> {Ps.git(s) == PackageSource.ps_git(s) : Ps.GitAns}:
  %Equal.sym(String, Ps.trim(s), PackageSource.ps_trim(s), psb.trim(s)) : {Ps.git.at(String.starts_with(_, "git:"), Ps.trim(s)) == PackageSource.ps_git.at(String.starts_with(PackageSource.ps_trim(s), "git:"), PackageSource.ps_trim(s)) : Ps.GitAns}
  %Equal.sym(String, Ps.trim(s), PackageSource.ps_trim(s), psb.trim(s)) : {Ps.git.at(String.starts_with(PackageSource.ps_trim(s), "git:"), _) == PackageSource.ps_git.at(String.starts_with(PackageSource.ps_trim(s), "git:"), PackageSource.ps_trim(s)) : Ps.GitAns}
  psb.git.at(String.starts_with(PackageSource.ps_trim(s), "git:"), PackageSource.ps_trim(s))

def psb.local(+s: String) -> {Ps.local(s) == PackageSource.ps_local(s) : Bool}:
  %Equal.sym(String, Ps.trim(s), PackageSource.ps_trim(s), psb.trim(s)) : {Bool.not(Bool.or(String.starts_with(_, "npm:"), Bool.or(String.starts_with(Ps.trim(s), "git:"), Bool.or(String.starts_with(Ps.trim(s), "github:"), Bool.or(String.starts_with(Ps.trim(s), "http:"), Bool.or(String.starts_with(Ps.trim(s), "https:"), String.starts_with(Ps.trim(s), "ssh:"))))))) == Bool.not(Bool.or(String.starts_with(PackageSource.ps_trim(s), "npm:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "git:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "github:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "http:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "https:"), String.starts_with(PackageSource.ps_trim(s), "ssh:"))))))) : Bool}
  %Equal.sym(String, Ps.trim(s), PackageSource.ps_trim(s), psb.trim(s)) : {Bool.not(Bool.or(String.starts_with(PackageSource.ps_trim(s), "npm:"), Bool.or(String.starts_with(_, "git:"), Bool.or(String.starts_with(Ps.trim(s), "github:"), Bool.or(String.starts_with(Ps.trim(s), "http:"), Bool.or(String.starts_with(Ps.trim(s), "https:"), String.starts_with(Ps.trim(s), "ssh:"))))))) == Bool.not(Bool.or(String.starts_with(PackageSource.ps_trim(s), "npm:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "git:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "github:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "http:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "https:"), String.starts_with(PackageSource.ps_trim(s), "ssh:"))))))) : Bool}
  %Equal.sym(String, Ps.trim(s), PackageSource.ps_trim(s), psb.trim(s)) : {Bool.not(Bool.or(String.starts_with(PackageSource.ps_trim(s), "npm:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "git:"), Bool.or(String.starts_with(_, "github:"), Bool.or(String.starts_with(Ps.trim(s), "http:"), Bool.or(String.starts_with(Ps.trim(s), "https:"), String.starts_with(Ps.trim(s), "ssh:"))))))) == Bool.not(Bool.or(String.starts_with(PackageSource.ps_trim(s), "npm:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "git:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "github:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "http:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "https:"), String.starts_with(PackageSource.ps_trim(s), "ssh:"))))))) : Bool}
  %Equal.sym(String, Ps.trim(s), PackageSource.ps_trim(s), psb.trim(s)) : {Bool.not(Bool.or(String.starts_with(PackageSource.ps_trim(s), "npm:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "git:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "github:"), Bool.or(String.starts_with(_, "http:"), Bool.or(String.starts_with(Ps.trim(s), "https:"), String.starts_with(Ps.trim(s), "ssh:"))))))) == Bool.not(Bool.or(String.starts_with(PackageSource.ps_trim(s), "npm:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "git:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "github:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "http:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "https:"), String.starts_with(PackageSource.ps_trim(s), "ssh:"))))))) : Bool}
  %Equal.sym(String, Ps.trim(s), PackageSource.ps_trim(s), psb.trim(s)) : {Bool.not(Bool.or(String.starts_with(PackageSource.ps_trim(s), "npm:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "git:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "github:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "http:"), Bool.or(String.starts_with(_, "https:"), String.starts_with(Ps.trim(s), "ssh:"))))))) == Bool.not(Bool.or(String.starts_with(PackageSource.ps_trim(s), "npm:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "git:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "github:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "http:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "https:"), String.starts_with(PackageSource.ps_trim(s), "ssh:"))))))) : Bool}
  %Equal.sym(String, Ps.trim(s), PackageSource.ps_trim(s), psb.trim(s)) : {Bool.not(Bool.or(String.starts_with(PackageSource.ps_trim(s), "npm:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "git:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "github:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "http:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "https:"), String.starts_with(_, "ssh:"))))))) == Bool.not(Bool.or(String.starts_with(PackageSource.ps_trim(s), "npm:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "git:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "github:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "http:"), Bool.or(String.starts_with(PackageSource.ps_trim(s), "https:"), String.starts_with(PackageSource.ps_trim(s), "ssh:"))))))) : Bool}
  {==}

def psb.npm_spec.ok(+e: Bool, +c: Char, +h: String, +v: String, +t: String) -> {Ps.npm_spec.ok(e, c, h, v, t) == PackageSource.ps_npm_spec.ok(e, c, h, v, t) : Ps.NpmSpec}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def psb.npm_spec.at(+m: Maybe<&2, Ps.Cut>, +c: Char, +t: String) -> {Ps.npm_spec.at(m, c, t) == PackageSource.ps_npm_spec.at(m, c, t) : Ps.NpmSpec}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ps.Cut{+h, +v}:
          psb.npm_spec.ok(String.is_empty(v), c, h, v, t)

def psb.npm_spec(+s: String) -> {Ps.npm_spec(s) == PackageSource.ps_npm_spec(s) : Ps.NpmSpec}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Maybe<&2, Ps.Cut>, Ps.cut(t, '@'), PackageSource.ps_cut(t, '@'), psb.cut(t, '@')) : {Ps.npm_spec.at(_, c, t) == PackageSource.ps_npm_spec.at(PackageSource.ps_cut(t, '@'), c, t) : Ps.NpmSpec}
      psb.npm_spec.at(PackageSource.ps_cut(t, '@'), c, t)

def psb.npm.ok(+m: Maybe<&2, Ps.Defect>, +name: String, +pinned: Bool, +spec: String) -> {Ps.npm.ok(m, name, pinned, spec) == PackageSource.ps_npm.ok(m, name, pinned, spec) : Ps.Parsed}:
  match m:
    case None{}:
      {==}
    case Some{+d}:
      {==}

def psb.npm.name(+ns: Ps.NpmSpec, +spec: String) -> {Ps.npm.name(ns, spec) == PackageSource.ps_npm.name(ns, spec) : Ps.Parsed}:
  match ns:
    case Ps.NpmSpec{+name, +v}:
      %Equal.sym(Maybe<&2, Ps.Defect>, Ps.rel(name), PackageSource.ps_rel(name), psb.rel(name)) : {Ps.npm.ok(_, name, Ps.is_some(v), spec) == PackageSource.ps_npm.ok(PackageSource.ps_rel(name), name, PackageSource.ps_is_some(v), spec) : Ps.Parsed}
      %Equal.sym(Bool, Ps.is_some(v), PackageSource.ps_is_some(v), psb.is_some(v)) : {Ps.npm.ok(PackageSource.ps_rel(name), name, _, spec) == PackageSource.ps_npm.ok(PackageSource.ps_rel(name), name, PackageSource.ps_is_some(v), spec) : Ps.Parsed}
      psb.npm.ok(PackageSource.ps_rel(name), name, PackageSource.ps_is_some(v), spec)

def psb.npm.at(+m: Maybe<&2, Ps.Defect>, +spec: String) -> {Ps.npm.at(m, spec) == PackageSource.ps_npm.at(m, spec) : Ps.Parsed}:
  match m:
    case None{}:
      %Equal.sym(Ps.NpmSpec, Ps.npm_spec(spec), PackageSource.ps_npm_spec(spec), psb.npm_spec(spec)) : {Ps.npm.name(_, spec) == PackageSource.ps_npm.name(PackageSource.ps_npm_spec(spec), spec) : Ps.Parsed}
      psb.npm.name(PackageSource.ps_npm_spec(spec), spec)
    case Some{+d}:
      {==}

def psb.npm(+spec: String) -> {Ps.npm(spec) == PackageSource.ps_npm(spec) : Ps.Parsed}:
  %Equal.sym(Maybe<&2, Ps.Defect>, Ps.arg(spec), PackageSource.ps_arg(spec), psb.arg(spec)) : {Ps.npm.at(_, spec) == PackageSource.ps_npm.at(PackageSource.ps_arg(spec), spec) : Ps.Parsed}
  psb.npm.at(PackageSource.ps_arg(spec), spec)

def psb.source.git(+a: Ps.GitAns, +s: String) -> {Ps.source.git(a, s) == PackageSource.ps_source.git(a, s) : Ps.Parsed}:
  match a:
    case Ps.NoGit{}:
      {==}
    case Ps.IsGit{+g}:
      {==}
    case Ps.BadGit{+f}:
      {==}

def psb.source.local(+b: Bool, +s: String) -> {Ps.source.local(b, s) == PackageSource.ps_source.local(b, s) : Ps.Parsed}:
  match b:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Ps.GitAns, Ps.git(s), PackageSource.ps_git(s), psb.git(s)) : {Ps.source.git(_, s) == PackageSource.ps_source.git(PackageSource.ps_git(s), s) : Ps.Parsed}
      psb.source.git(PackageSource.ps_git(s), s)

def psb.source.at(+b: Bool, +s: String) -> {Ps.source.at(b, s) == PackageSource.ps_source.at(b, s) : Ps.Parsed}:
  match b:
    case True{}:
      %Equal.sym(String, Ps.trim(String.drop(s, 4n)), PackageSource.ps_trim(String.drop(s, 4n)), psb.trim(String.drop(s, 4n))) : {Ps.npm(_) == PackageSource.ps_npm(PackageSource.ps_trim(String.drop(s, 4n))) : Ps.Parsed}
      psb.npm(PackageSource.ps_trim(String.drop(s, 4n)))
    case False{}:
      %Equal.sym(Bool, Ps.local(s), PackageSource.ps_local(s), psb.local(s)) : {Ps.source.local(_, s) == PackageSource.ps_source.local(PackageSource.ps_local(s), s) : Ps.Parsed}
      psb.source.local(PackageSource.ps_local(s), s)

def psb.source(+s: String) -> {Ps.source(s) == PackageSource.ps_source(s) : Ps.Parsed}:
  psb.source.at(String.starts_with(s, "npm:"), s)

def psb.part_text(+p: Ps.Part) -> {Ps.part_text(p) == PackageSource.ps_part_text(p) : String}:
  match p:
    case Ps.PHost{}:
      {==}
    case Ps.PPath{}:
      {==}
    case Ps.PRef{}:
      {==}
    case Ps.PClone{}:
      {==}
    case Ps.PSpec{}:
      {==}
    case Ps.PName{}:
      {==}

def psb.defect_text(+d: Ps.Defect) -> {Ps.defect_text(d) == PackageSource.ps_defect_text(d) : String}:
  match d:
    case Ps.DEmpty{}:
      {==}
    case Ps.DEmptySeg{}:
      {==}
    case Ps.DDot{}:
      {==}
    case Ps.DDrive{}:
      {==}
    case Ps.DBackslash{}:
      {==}
    case Ps.DControl{}:
      {==}
    case Ps.DDash{}:
      {==}
    case Ps.DSlash{}:
      {==}

def psb.error_text(+s: String, +f: Ps.Flaw) -> {Ps.error_text(s, f) == PackageSource.ps_error_text(s, f) : String}:
  match f:
    case Ps.Flaw{+p, +d}:
      %Equal.sym(String, Ps.part_text(p), PackageSource.ps_part_text(p), psb.part_text(p)) : {String.concat(["Invalid package source ", s, ": ", _, " ", Ps.defect_text(d)]) == String.concat(["Invalid package source ", s, ": ", PackageSource.ps_part_text(p), " ", PackageSource.ps_defect_text(d)]) : String}
      %Equal.sym(String, Ps.defect_text(d), PackageSource.ps_defect_text(d), psb.defect_text(d)) : {String.concat(["Invalid package source ", s, ": ", PackageSource.ps_part_text(p), " ", _]) == String.concat(["Invalid package source ", s, ": ", PackageSource.ps_part_text(p), " ", PackageSource.ps_defect_text(d)]) : String}
      {==}
