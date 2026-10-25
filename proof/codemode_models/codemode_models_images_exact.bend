# eukhe: the proof of LAW codemode_models_images_exact

import Base
import ../../bend/codemode_models.bend as Mod
import ../../laws/codemode_models/checks.bend as CodemodeModels
import ./base.bend as LACm

# PROOF of LAW codemode_models_images_exact: each check of the model's chain is the spec's (cm.fu), the blocks too (cm.bad_block), wrapped alike (cm.wrap).

def CodemodeModels.codemode_models_images_exact(x):
  match x:
    case Mod.ICtx{+ctx, +input, +bs}:
      +a : String = "expects a context object as its second argument"
      +b : String = "context.input must be a non-empty array of blocks"
      +m2 = Mod.first(Mod.unless(Mod.is_full(input), Mod.got(b, input)), Mod.bad_block(bs, 0n))
      +s2 = CodemodeModels.or_else(CodemodeModels.full_spec(input), CodemodeModels.got_spec(b, input), CodemodeModels.blocks_spec(bs, 0n))
      LACm.cm.wrap("models.generateImages() ", ". Expected context: { input: [{ type: \"text\", text: <prompt> }, ...optional { type: \"image\", data: <base64>, mimeType } references] }.", Mod.first(Mod.unless(Mod.is_obj(ctx), Mod.got(a, ctx)), m2), CodemodeModels.or_else(CodemodeModels.kind_obj(ctx), CodemodeModels.got_spec(a, ctx), s2), LACm.cm.fu(Mod.is_obj(ctx), CodemodeModels.kind_obj(ctx), Mod.got(a, ctx), CodemodeModels.got_spec(a, ctx), m2, s2, LACm.cm.obj(ctx), LACm.cm.got(a, ctx), LACm.cm.fu(Mod.is_full(input), CodemodeModels.full_spec(input), Mod.got(b, input), CodemodeModels.got_spec(b, input), Mod.bad_block(bs, 0n), CodemodeModels.blocks_spec(bs, 0n), LACm.cm.full(input), LACm.cm.got(b, input), LACm.cm.bad_block(bs, 0n))))
