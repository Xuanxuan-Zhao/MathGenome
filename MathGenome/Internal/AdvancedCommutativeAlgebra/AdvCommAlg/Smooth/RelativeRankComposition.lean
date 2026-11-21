import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.RelativeRank
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.Permanence
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.SplitTransitivity
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.RelativeRankComposition
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! Additivity of the relative rank of smooth algebras (SM-09). -/
namespace AdvCommAlg.Smooth

universe u v w
noncomputable section
open scoped TensorProduct
open Specs.AdvCommAlg.Smooth
open Specs.AdvCommAlg.Smooth.RelativeRankComposition

/-- The left term of transitivity over κ(r) is the cotangent fiber at the
contracted prime, extended along the canonical map κ(q) → κ(r). -/
theorem residue_fiber_identification : residueFiberIdentification.{u,v,w} := by
  intro A B C _ _ _ _ _ r
  let q := r.comap (algebraMap B C)
  letI := residueExtension B C r
  let := residueExtensionTower B C r
  let K := r.asIdeal.ResidueField
  let k := q.asIdeal.ResidueField
  refine ⟨(TensorProduct.AlgebraTensorModule.cancelBaseChange B C K K
      (KaehlerDifferential A B)).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange B k K K
      (KaehlerDifferential A B)).symm, ?_⟩
  intro t c ω
  simp only [LinearEquiv.trans_apply,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
  rw [Algebra.smul_def]

/-- Tensor the split transitivity sequence with κ(r), identify the first
fiber by residue-field scalar extension, and add the two finite dimensions. -/
theorem relativeRank_composition : compositionRank.{u,v,w} := by
  intro A B C _ _ _ _ _ _ _ hAB hBC r
  let : Algebra.Smooth A B := hAB
  let : Algebra.Smooth B C := hBC
  let : Algebra.Smooth A C := smooth_composition A B C hAB hBC
  let K := r.asIdeal.ResidueField
  let q := r.comap (algebraMap B C)
  letI := residueExtension B C r
  let := residueExtensionTower B C r
  obtain ⟨_, hex, hsurj, s, hs⟩ := FormalLifting.split_transitivity A B C
    ((smooth_iff B C).mp hBC).2
  let e := (hex.splitInjectiveEquiv hsurj) ⟨s, hs⟩
  let eK := (e.1.baseChange C K _ _).trans
    (TensorProduct.prodRight C K K (C ⊗[B] KaehlerDifferential A B)
      (KaehlerDifferential B C))
  obtain ⟨i, _⟩ := residue_fiber_identification A B C r
  have hleft : Module.finrank K (K ⊗[C] (C ⊗[B] KaehlerDifferential A B)) =
      RelativeRank.relativeRankValue A B q := by
    rw [i.finrank_eq, Module.finrank_baseChange]
    rfl
  change Module.finrank K (K ⊗[C] KaehlerDifferential A C) =
    RelativeRank.relativeRankValue A B q +
      Module.finrank K (K ⊗[C] KaehlerDifferential B C)
  rw [eK.finrank_eq, Module.finrank_prod, hleft]

end
end AdvCommAlg.Smooth
