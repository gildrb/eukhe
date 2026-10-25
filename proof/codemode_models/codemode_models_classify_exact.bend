# eukhe: the proof of LAW codemode_models_classify_exact

import Base
import ../../bend/codemode_models.bend as Mod
import ../../laws/codemode_models/checks.bend as CodemodeModels
import ./base.bend as LACm

# PROOF of LAW codemode_models_classify_exact: each check of the model's chain is the spec's (cm.fu, cm.ft), the images part (cm.images_check) and the questions (cm.questions), wrapped alike (cm.wrap).

def CodemodeModels.codemode_models_classify_exact(x):
  match x:
    case Mod.Ctx{+ctx, +state, +images, +bs, +questions, +qs}:
      +a : String = "expects a context object as its second argument"
      +b : String = "context.state must be an object"
      +c : String = "context.questions must map question IDs to questions"
      +m4 = Mod.first(Mod.unless(Mod.is_map(questions), Mod.got(c, questions)), Mod.questions_check(qs))
      +s4 = CodemodeModels.or_else(CodemodeModels.map_spec(questions), CodemodeModels.got_spec(c, questions), CodemodeModels.questions_spec(qs))
      +m3 = Mod.first(Mod.images_check(images, bs), m4)
      +s3 = CodemodeModels.then_spec(CodemodeModels.images_part(images, bs), s4)
      +m2 = Mod.first(Mod.unless(Mod.is_obj(state), Mod.got(b, state)), m3)
      +s2 = CodemodeModels.or_else(CodemodeModels.kind_obj(state), CodemodeModels.got_spec(b, state), s3)
      LACm.cm.wrap("models.classify() ", String.concat([". Expected context: ", Mod.classify_shape(), "."]), Mod.first(Mod.unless(Mod.is_obj(ctx), Mod.got(a, ctx)), m2), CodemodeModels.or_else(CodemodeModels.kind_obj(ctx), CodemodeModels.got_spec(a, ctx), s2), LACm.cm.fu(Mod.is_obj(ctx), CodemodeModels.kind_obj(ctx), Mod.got(a, ctx), CodemodeModels.got_spec(a, ctx), m2, s2, LACm.cm.obj(ctx), LACm.cm.got(a, ctx), LACm.cm.fu(Mod.is_obj(state), CodemodeModels.kind_obj(state), Mod.got(b, state), CodemodeModels.got_spec(b, state), m3, s3, LACm.cm.obj(state), LACm.cm.got(b, state), LACm.cm.ft(Mod.images_check(images, bs), CodemodeModels.images_part(images, bs), m4, s4, LACm.cm.images_check(images, bs), LACm.cm.fu(Mod.is_map(questions), CodemodeModels.map_spec(questions), Mod.got(c, questions), CodemodeModels.got_spec(c, questions), Mod.questions_check(qs), CodemodeModels.questions_spec(qs), LACm.cm.map(questions), LACm.cm.got(c, questions), LACm.cm.questions(qs))))))
