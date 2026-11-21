import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

/-! Every module embeds in an injective module.

Mathlib's enough-injectives construction uses characters into Q/Z, whose
separation of nonzero elements is proved in
`CharacterModule.exists_character_apply_ne_zero_of_ne_zero`. The character
product is injective by divisibility and Baer's criterion. Restriction and
coextension of scalars then give enough injectives over any unital ring.
Here categorical monomorphisms and injectivity are converted to their
ordinary module counterparts; no injectivity certificate is assumed.
-/

namespace P103.Ch02.EnoughInjectives

open P103.Specs.Ch02.EnoughInjectives
open CategoryTheory

universe u v

theorem leftEmbedding : leftEmbeddingType.{u, v} := by
  intro R M _ _ _
  let M' := ULift.{u} M
  let P := (EnoughInjectives.presentation (ModuleCat.of R M')).some
  refine ⟨P.J, inferInstance, inferInstance,
    P.f.hom.comp (ULift.moduleEquiv.symm.toLinearMap : M →ₗ[R] M'), ?_, ?_⟩
  · exact ((ModuleCat.mono_iff_injective P.f).mp P.mono).comp
      ULift.moduleEquiv.symm.injective
  · exact Module.injective_module_of_injective_object (inj := P.injective) R P.J

theorem rightEmbedding : rightEmbeddingType.{u, v} := by
  intro R M _ _ _
  exact leftEmbedding Rᵐᵒᵖ M

end P103.Ch02.EnoughInjectives
