# eukhe: the proof of LAW refine_plan_check_rules
#
# PROOF: per action and kind, the code's nested checks (skill, factory,
# when) give the message of the first broken rule of R3's list, rule by
# rule (rpc.rules).

import Base
import ../../bend/refine_plan.bend as Rp
import ../../laws/refine_plan/model.bend as RefinePlan

def rpc.first.same(b: Bool, +m: String, r1: Maybe<&2, String>, -r2: Maybe<&2, String>, er: {r1 == r2 : Maybe<&2, String>}) -> {Rp.first(b, m, r1) == RefinePlan.rs_first.at(RefinePlan.RsRule{b, m}, r2) : Maybe<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      er

def rpc.first(+b1: Bool, -b2: Bool, eb: {b1 == b2 : Bool}, +m: String, +r1: Maybe<&2, String>, +r2: Maybe<&2, String>, +er: {r1 == r2 : Maybe<&2, String>}) -> {Rp.first(b1, m, r1) == RefinePlan.rs_first.at(RefinePlan.RsRule{b2, m}, r2) : Maybe<&2, String>}:
  %eb : {Rp.first(b1, m, r1) == RefinePlan.rs_first.at(RefinePlan.RsRule{_, m}, r2) : Maybe<&2, String>}
  rpc.first.same(b1, m, r1, r2, er)

def rpc.bsp(id: Maybe<&2, String>, cid: Maybe<&2, String>) -> {Bool.or(Rp.is_text(id, "base_system_prompt"), Rp.is_text(cid, "base_system_prompt")) == Bool.or(RefinePlan.rs_named(id, "base_system_prompt"), RefinePlan.rs_named(cid, "base_system_prompt")) : Bool}:
  match id:
    case None{}:
      match cid:
        case None{}:
          {==}
        case Some{z}:
          {==}
    case Some{y}:
      match cid:
        case None{}:
          {==}
        case Some{z}:
          {==}

def rpc.python(ty: Maybe<&2, String>) -> {Bool.not(Rp.is_text(ty, "python")) == Bool.not(RefinePlan.rs_named(ty, "python")) : Bool}:
  match ty:
    case None{}:
      {==}
    case Some{y}:
      {==}

def rpc.filled(a: Maybe<&2, String>, b: Maybe<&2, String>) -> {Bool.not(Bool.or(Rp.filled(a), Rp.filled(b))) == Bool.not(Bool.or(RefinePlan.rs_filled(a), RefinePlan.rs_filled(b))) : Bool}:
  match a:
    case None{}:
      match b:
        case None{}:
          {==}
        case Some{z}:
          {==}
    case Some{y}:
      match b:
        case None{}:
          {==}
        case Some{z}:
          {==}

# the spec's skill rules of an edit that is a skill create or update
def rpc.skill.S(+vn: String, args: Maybe<&2, Rp.Args>, +p: Maybe<&2, Rp.Pyref>) -> Maybe<&2, String>:
  RefinePlan.rs_first.at(RefinePlan.RsRule{Maybe.is_none(&2, Rp.Args, args), String.concat([vn, " skill requires arguments"])}, RefinePlan.rs_first.at(RefinePlan.RsRule{Maybe.is_none(&2, Rp.Pyref, p), String.concat([vn, " skill requires python reference"])}, RefinePlan.rs_first.at(RefinePlan.RsRule{Bool.not(RefinePlan.rs_ref_python(p)), String.concat([vn, " skill reference.type must be python"])}, RefinePlan.rs_first.at(RefinePlan.RsRule{Bool.not(RefinePlan.rs_ref_import(p)), String.concat([vn, " skill requires python import"])}, RefinePlan.rs_first.at(RefinePlan.RsRule{Bool.not(RefinePlan.rs_ref_callable(p)), String.concat([vn, " skill requires callable or call_pattern"])}, None{})))))

def rpc.skill.ref(+vn: String, p: Maybe<&2, Rp.Pyref>) -> {Rp.skill.ref(vn, p) == RefinePlan.rs_first.at(RefinePlan.RsRule{Maybe.is_none(&2, Rp.Pyref, p), String.concat([vn, " skill requires python reference"])}, RefinePlan.rs_first.at(RefinePlan.RsRule{Bool.not(RefinePlan.rs_ref_python(p)), String.concat([vn, " skill reference.type must be python"])}, RefinePlan.rs_first.at(RefinePlan.RsRule{Bool.not(RefinePlan.rs_ref_import(p)), String.concat([vn, " skill requires python import"])}, RefinePlan.rs_first.at(RefinePlan.RsRule{Bool.not(RefinePlan.rs_ref_callable(p)), String.concat([vn, " skill requires callable or call_pattern"])}, None{})))) : Maybe<&2, String>}:
  match p:
    case None{}:
      {==}
    case Some{r}:
      match r:
        case Rp.Pyref{+ty, +imp, +pyimp, +call, +pat}:
          +m8 = String.concat([vn, " skill requires callable or call_pattern"])
          +m7 = String.concat([vn, " skill requires python import"])
          +m6 = String.concat([vn, " skill reference.type must be python"])
          +c8 = Rp.first(Bool.not(Bool.or(Rp.filled(call), Rp.filled(pat))), m8, None{})
          +s8 = RefinePlan.rs_first.at(RefinePlan.RsRule{Bool.not(Bool.or(RefinePlan.rs_filled(call), RefinePlan.rs_filled(pat))), m8}, None{})
          +p8 = rpc.first(Bool.not(Bool.or(Rp.filled(call), Rp.filled(pat))), Bool.not(Bool.or(RefinePlan.rs_filled(call), RefinePlan.rs_filled(pat))), rpc.filled(call, pat), m8, None{}, None{}, {==})
          +c7 = Rp.first(Bool.not(Bool.or(Rp.filled(imp), Rp.filled(pyimp))), m7, c8)
          +s7 = RefinePlan.rs_first.at(RefinePlan.RsRule{Bool.not(Bool.or(RefinePlan.rs_filled(imp), RefinePlan.rs_filled(pyimp))), m7}, s8)
          +p7 = rpc.first(Bool.not(Bool.or(Rp.filled(imp), Rp.filled(pyimp))), Bool.not(Bool.or(RefinePlan.rs_filled(imp), RefinePlan.rs_filled(pyimp))), rpc.filled(imp, pyimp), m7, c8, s8, p8)
          rpc.first(Bool.not(Rp.is_text(ty, "python")), Bool.not(RefinePlan.rs_named(ty, "python")), rpc.python(ty), m6, c7, s7, p7)

def rpc.skill(+vn: String, +args: Maybe<&2, Rp.Args>, +p: Maybe<&2, Rp.Pyref>) -> {Rp.skill(vn, args, p) == rpc.skill.S(vn, args, p) : Maybe<&2, String>}:
  rpc.first.same(Maybe.is_none(&2, Rp.Args, args), String.concat([vn, " skill requires arguments"]), Rp.skill.ref(vn, p), RefinePlan.rs_first.at(RefinePlan.RsRule{Maybe.is_none(&2, Rp.Pyref, p), String.concat([vn, " skill requires python reference"])}, RefinePlan.rs_first.at(RefinePlan.RsRule{Bool.not(RefinePlan.rs_ref_python(p)), String.concat([vn, " skill reference.type must be python"])}, RefinePlan.rs_first.at(RefinePlan.RsRule{Bool.not(RefinePlan.rs_ref_import(p)), String.concat([vn, " skill requires python import"])}, RefinePlan.rs_first.at(RefinePlan.RsRule{Bool.not(RefinePlan.rs_ref_callable(p)), String.concat([vn, " skill requires callable or call_pattern"])}, None{})))), rpc.skill.ref(vn, p))

def rpc.factory.S(+a: Maybe<&2, Rp.Args>) -> Maybe<&2, String>:
  RefinePlan.rs_first.at(RefinePlan.RsRule{RefinePlan.rs_both(a), "pass either dag or machine form, not both"}, RefinePlan.rs_first.at(RefinePlan.RsRule{Bool.not(RefinePlan.rs_spec_object(a)), "factory entry requires a dag or machine object in arguments"}, None{}))

def rpc.factory.U(+a: Maybe<&2, Rp.Args>) -> Maybe<&2, String>:
  RefinePlan.rs_first.at(RefinePlan.RsRule{Bool.and(Maybe.is_some(&2, Rp.Args, a), RefinePlan.rs_both(a)), "pass either dag or machine form, not both"}, RefinePlan.rs_first.at(RefinePlan.RsRule{Bool.and(Maybe.is_some(&2, Rp.Args, a), Bool.not(RefinePlan.rs_spec_object(a))), "factory entry requires a dag or machine object in arguments"}, None{}))

def rpc.factory(a: Maybe<&2, Rp.Args>) -> {Rp.factory(a) == rpc.factory.S(a) : Maybe<&2, String>}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case Rp.Args{dag, machine}:
          match dag:
            case Rp.VMissing{}:
              match machine:
                case Rp.VMissing{}:
                  {==}
                case Rp.VNull{}:
                  {==}
                case Rp.VObject{}:
                  {==}
                case Rp.VOther{}:
                  {==}
            case Rp.VNull{}:
              match machine:
                case Rp.VMissing{}:
                  {==}
                case Rp.VNull{}:
                  {==}
                case Rp.VObject{}:
                  {==}
                case Rp.VOther{}:
                  {==}
            case Rp.VObject{}:
              match machine:
                case Rp.VMissing{}:
                  {==}
                case Rp.VNull{}:
                  {==}
                case Rp.VObject{}:
                  {==}
                case Rp.VOther{}:
                  {==}
            case Rp.VOther{}:
              match machine:
                case Rp.VMissing{}:
                  {==}
                case Rp.VNull{}:
                  {==}
                case Rp.VObject{}:
                  {==}
                case Rp.VOther{}:
                  {==}

def rpc.factory_u(a: Maybe<&2, Rp.Args>) -> {Rp.when(Maybe.is_some(&2, Rp.Args, a), Rp.factory(a), None{}) == rpc.factory.U(a) : Maybe<&2, String>}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      rpc.factory(Some{x})

def rpc.rules(+v: Rp.Verb, +c: Rp.Comp, +id: Maybe<&2, String>, +cid: Maybe<&2, String>, +title: Maybe<&2, String>, +content: Bool, +p: Maybe<&2, Rp.Pyref>, +args: Maybe<&2, Rp.Args>) -> {Rp.rules(v, c, id, cid, Maybe.is_some(&2, String, title), content, p, args) == RefinePlan.rs_first(RefinePlan.rs_rules(v, c, id, cid, title, content, p, args)) : Maybe<&2, String>}:
  match v:
    case Rp.ACreate{}:
      match c:
        case Rp.KPrompt{}:
          rpc.first(Bool.or(Rp.is_text(id, "base_system_prompt"), Rp.is_text(cid, "base_system_prompt")), Bool.or(RefinePlan.rs_named(id, "base_system_prompt"), RefinePlan.rs_named(cid, "base_system_prompt")), rpc.bsp(id, cid), "base system prompt is not editable", Rp.first(Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "create requires title and content", None{}), RefinePlan.rs_first.at(RefinePlan.RsRule{Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "create requires title and content"}, None{}), rpc.first.same(Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "create requires title and content", None{}, None{}, {==}))
        case Rp.KMemory{}:
          rpc.first.same(Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "create requires title and content", None{}, None{}, {==})
        case Rp.KSkill{}:
          rpc.first.same(Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "create requires title and content", Rp.skill("create", args, p), rpc.skill.S("create", args, p), rpc.skill("create", args, p))
        case Rp.KSubagent{}:
          rpc.first.same(Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "create requires title and content", None{}, None{}, {==})
        case Rp.KFactory{}:
          rpc.first.same(Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "create requires title and content", Rp.factory(args), rpc.factory.S(args), rpc.factory(args))
    case Rp.AUpdate{}:
      match c:
        case Rp.KPrompt{}:
          rpc.first(Bool.or(Rp.is_text(id, "base_system_prompt"), Rp.is_text(cid, "base_system_prompt")), Bool.or(RefinePlan.rs_named(id, "base_system_prompt"), RefinePlan.rs_named(cid, "base_system_prompt")), rpc.bsp(id, cid), "base system prompt is not editable", Rp.first(Maybe.is_none(&2, String, id), "update requires id", Rp.first(Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "update requires title and content", None{})), RefinePlan.rs_first.at(RefinePlan.RsRule{Maybe.is_none(&2, String, id), "update requires id"}, RefinePlan.rs_first.at(RefinePlan.RsRule{Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "update requires title and content"}, None{})), rpc.first.same(Maybe.is_none(&2, String, id), "update requires id", Rp.first(Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "update requires title and content", None{}), RefinePlan.rs_first.at(RefinePlan.RsRule{Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "update requires title and content"}, None{}), rpc.first.same(Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "update requires title and content", None{}, None{}, {==})))
        case Rp.KMemory{}:
          rpc.first.same(Maybe.is_none(&2, String, id), "update requires id", Rp.first(Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "update requires title and content", None{}), RefinePlan.rs_first.at(RefinePlan.RsRule{Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "update requires title and content"}, None{}), rpc.first.same(Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "update requires title and content", None{}, None{}, {==}))
        case Rp.KSkill{}:
          rpc.first.same(Maybe.is_none(&2, String, id), "update requires id", Rp.first(Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "update requires title and content", Rp.skill("update", args, p)), RefinePlan.rs_first.at(RefinePlan.RsRule{Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "update requires title and content"}, rpc.skill.S("update", args, p)), rpc.first.same(Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "update requires title and content", Rp.skill("update", args, p), rpc.skill.S("update", args, p), rpc.skill("update", args, p)))
        case Rp.KSubagent{}:
          rpc.first.same(Maybe.is_none(&2, String, id), "update requires id", Rp.first(Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "update requires title and content", None{}), RefinePlan.rs_first.at(RefinePlan.RsRule{Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "update requires title and content"}, None{}), rpc.first.same(Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "update requires title and content", None{}, None{}, {==}))
        case Rp.KFactory{}:
          rpc.first.same(Maybe.is_none(&2, String, id), "update requires id", Rp.first(Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "update requires title and content", Rp.when(Maybe.is_some(&2, Rp.Args, args), Rp.factory(args), None{})), RefinePlan.rs_first.at(RefinePlan.RsRule{Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "update requires title and content"}, rpc.factory.U(args)), rpc.first.same(Bool.not(Bool.and(Maybe.is_some(&2, String, title), content)), "update requires title and content", Rp.when(Maybe.is_some(&2, Rp.Args, args), Rp.factory(args), None{}), rpc.factory.U(args), rpc.factory_u(args)))
    case Rp.ADelete{}:
      match c:
        case Rp.KPrompt{}:
          rpc.first(Bool.or(Rp.is_text(id, "base_system_prompt"), Rp.is_text(cid, "base_system_prompt")), Bool.or(RefinePlan.rs_named(id, "base_system_prompt"), RefinePlan.rs_named(cid, "base_system_prompt")), rpc.bsp(id, cid), "base system prompt is not editable", Rp.first(Maybe.is_none(&2, String, id), "delete requires id", None{}), RefinePlan.rs_first.at(RefinePlan.RsRule{Maybe.is_none(&2, String, id), "delete requires id"}, None{}), rpc.first.same(Maybe.is_none(&2, String, id), "delete requires id", None{}, None{}, {==}))
        case Rp.KMemory{}:
          rpc.first.same(Maybe.is_none(&2, String, id), "delete requires id", None{}, None{}, {==})
        case Rp.KSkill{}:
          rpc.first.same(Maybe.is_none(&2, String, id), "delete requires id", None{}, None{}, {==})
        case Rp.KSubagent{}:
          rpc.first.same(Maybe.is_none(&2, String, id), "delete requires id", None{}, None{}, {==})
        case Rp.KFactory{}:
          rpc.first.same(Maybe.is_none(&2, String, id), "delete requires id", None{}, None{}, {==})

def rpc.at(+v: Rp.Verb, +c: Rp.Comp, m: Maybe<&2, String>) -> {Rp.check.at(v, c, m) == RefinePlan.rs_check.at(v, c, m) : Rp.Check}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def rpc.check(e: Rp.Ed, +cid: Maybe<&2, String>) -> {Rp.check(e, cid) == RefinePlan.rs_check(e, cid) : Rp.Check}:
  match e:
    case Rp.Ed{verb, comp, +id, +title, +content, +pyref, +args, exists, differs, held}:
      match verb:
        case None{}:
          {==}
        case Some{+v}:
          match comp:
            case None{}:
              {==}
            case Some{+c}:
              %rpc.rules(v, c, id, cid, title, content, pyref, args) : {Rp.check.at(v, c, Rp.rules(v, c, id, cid, Maybe.is_some(&2, String, title), content, pyref, args)) == RefinePlan.rs_check.at(v, c, _) : Rp.Check}
              rpc.at(v, c, Rp.rules(v, c, id, cid, Maybe.is_some(&2, String, title), content, pyref, args))

def RefinePlan.refine_plan_check_rules(e, cid):
  rpc.check(e, cid)
