import MathGenome.Internal.Specs.D07.Ch14.NormalQuotientRestrictionSurjectivity

/-!
Restriction in a finite Galois extension (K07.14.normal_quotient).

Mathlib's normal-extension lifting theorem extends a prescribed base-fixing
map, and normality makes the resulting self-embedding an automorphism.
Its commutation law retains the prescribed values on E. This theorem in
fact only needs normality of L/K; we apply it under the source's finite
Galois hypotheses. The restriction formula and injectivity of E → L
identify its kernel with pointwise fixation of the image of E.
-/

universe u v w

namespace D07.Ch14.NormalQuotientRestrictionSurjectivity

open Specs.D07.Ch14.NormalQuotientRestrictionSurjectivity

/-- Restriction to the specified normal intermediate extension. -/
noncomputable def restrictionHom (K : Type u) (E : Type v) (L : Type w)
    [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L]
    [Normal K E] : (L ≃ₐ[K] L) →* (E ≃ₐ[K] E) :=
  AlgEquiv.restrictNormalHom E

theorem restriction_agrees : RestrictionAgrees.{u, v, w} := by
  intro K E L _ _ _ _ _ _ _ _ σ x
  exact σ.restrictNormal_commutes E x

theorem restriction_group_laws : RestrictionGroupLaws.{u, v, w} := by
  intro K E L _ _ _ _ _ _ _ _
  exact ⟨(restrictionHom K E L).map_one, (restrictionHom K E L).map_mul⟩

theorem automorphism_extension : AutomorphismExtension.{u, v, w} := by
  intro K E L _ _ _ _ _ _ _ _ _ _ τ
  exact ⟨τ.liftNormal L, fun x => τ.liftNormal_commutes L x⟩

theorem restriction_surjective : RestrictionSurjective.{u, v, w} := by
  intro K E L _ _ _ _ _ _ _ _ _ _
  exact AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) (E := L)

theorem restriction_kernel : RestrictionKernel.{u, v, w} := by
  intro K E L _ _ _ _ _ _ _ _
  exact AlgEquiv.ker_restrictNormalHom E

theorem intermediate_restriction_kernel : IntermediateRestrictionKernel.{u, v} := by
  intro K L _ _ _ E _
  exact E.restrictNormalHom_ker

end D07.Ch14.NormalQuotientRestrictionSurjectivity
