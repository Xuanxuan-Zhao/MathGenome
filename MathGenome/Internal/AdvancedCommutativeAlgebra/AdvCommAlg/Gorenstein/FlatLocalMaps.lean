import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.TypeOneCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.FlatLocalCohenMacaulay
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.TypeMultiplication
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.FlatLocalMaps

/-! Gorensteinness under flat local maps (GC-08).
First specialize the module type formula to the regular modules. The CM
criterion then supplies CM for both factors in the descent direction;
the natural-number type product is one exactly when both factors are one.
-/

noncomputable section
universe u
open scoped TensorProduct
open TensorProduct
namespace AdvCommAlg.Gorenstein

section Local
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
  [IsLocalHom (algebraMap R S)] [Module.Flat R S]

/-- The type formula for rings uses the quotient ring as the closed fiber. -/
lemma flatLocal_ringType :
    let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
    letI := CohenMacaulay.Specs.closedFiberLocalRing R S
    ringType S = ringType R * ringType (S ⧸ J) := by
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  letI := CohenMacaulay.Specs.closedFiberLocalRing R S
  let F := S ⧸ (J • (⊤ : Submodule S S))
  letI : Module.Finite (S ⧸ J) F := Module.Finite.of_restrictScalars_finite S (S ⧸ J) F
  letI := CohenMacaulay.closedFiber_nontrivial R S S
  letI : Module.FaithfullyFlat R S := CohenMacaulay.faithfullyFlat_of_flatLocal R S S
  let e : (S ⊗[R] R) ≃ₗ[S] S := AlgebraTensorModule.rid R S S
  have ht := CohenMacaulay.TypeMultiplication.tensor_type_left R S R S
  rw [CohenMacaulay.TypeMultiplication.moduleType_eq_of_linearEquiv e,
    ← CohenMacaulay.TypeMultiplication.moduleType_of_surjective S (S ⧸ J)
      Ideal.Quotient.mk_surjective F,
    CohenMacaulay.TypeMultiplication.moduleType_eq_of_linearEquiv
      (CohenMacaulay.quotientSelfEquiv S J)] at ht
  exact ht

end Local

/-- A flat local map has Gorenstein target exactly when its source and
closed fiber are Gorenstein, without any initial CM assumption. -/
theorem flatLocal_gorenstein : FlatLocalMapsSpecs.flatLocal_gorensteinType.{u} := by
  intro R S _ _ _ _ _ _ _ _ _
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  letI := CohenMacaulay.Specs.closedFiberLocalRing R S
  change LocalGorenstein S ↔ LocalGorenstein R ∧ LocalGorenstein (S ⧸ J)
  rw [localGorenstein_iff_cohenMacaulay_type_one S,
    localGorenstein_iff_cohenMacaulay_type_one R,
    localGorenstein_iff_cohenMacaulay_type_one (S ⧸ J)]
  have hCM := CohenMacaulay.flatLocal_ring_cohenMacaulay R S
  change CohenMacaulay.LocalCohenMacaulay S S ↔
    CohenMacaulay.LocalCohenMacaulay R R ∧
      CohenMacaulay.LocalCohenMacaulay (S ⧸ J) (S ⧸ J) at hCM
  rw [hCM, flatLocal_ringType R S, mul_eq_one]
  exact ⟨fun ⟨⟨hR, hF⟩, tR, tF⟩ => ⟨⟨hR, tR⟩, hF, tF⟩,
    fun ⟨⟨hR, tR⟩, hF, tF⟩ => ⟨⟨hR, hF⟩, tR, tF⟩⟩

end AdvCommAlg.Gorenstein
