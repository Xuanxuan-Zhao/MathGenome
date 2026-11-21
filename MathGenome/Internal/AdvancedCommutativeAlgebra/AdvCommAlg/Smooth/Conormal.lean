import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Smooth.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.SplittingCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Polynomial
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.Conormal
import Mathlib.RingTheory.TensorProduct.Free

/-! The conormal criterion for every finite polynomial presentation (SM-02). -/
namespace AdvCommAlg.Smooth

universe u v
noncomputable section
open Specs.AdvCommAlg.Differentials
open Specs.AdvCommAlg.FormalLifting.SplittingCriterion
open TensorProduct

/-- Smoothness is equivalent to a left inverse of the actual conormal arrow. -/
theorem conormal_criterion : Specs.AdvCommAlg.Smooth.Conormal.criterion.{u,v} := by
  intro A B _ _ _ _ n _ _ h
  let P := MvPolynomial (Fin n) A
  have hP : Specs.AdvCommAlg.FormalLifting.formallySmoothValue A P :=
    (FormalLifting.formallySmooth_iff A P).mpr inferInstance
  rw [smooth_iff A B, and_iff_right (inferInstance : Algebra.FinitePresentation A B)]
  exact ((FormalLifting.SplittingCriterion.splitting_criterion A P B h hP).2).trans
    (FormalLifting.SplittingCriterion.splitConormal_iff_retraction h)

/-- A retraction exhibits the two outside terms as finite projective summands
of the finite free middle term. -/
theorem conormal_split_finite_projective :
    Specs.AdvCommAlg.Smooth.Conormal.splitFiniteProjective.{u,v} := by
  intro A B _ _ _ _ n _ _ h hs
  let P := MvPolynomial (Fin n) A
  let F := B ⊗[P] KaehlerDifferential A P
  let δ := conormalMapValue A P B h
  let q := conormalProjectionValue A P B
  let b := Algebra.TensorProduct.basis B (Differentials.polynomialBasis A (Fin n))
  let : Module.Free B F := Module.Free.of_basis b
  let : Module.Finite B F := Module.Finite.of_basis b
  obtain ⟨ρ, hρ⟩ := (conormal_criterion A B n h).mp hs
  have hsplit := (FormalLifting.SplittingCriterion.splitConormal_iff_retraction h).mpr ⟨ρ, hρ⟩
  have hsurj : Function.Surjective ρ :=
    Function.LeftInverse.surjective (LinearMap.congr_fun hρ)
  obtain ⟨s, hs'⟩ := ((hsplit.2.1.split_tfae').out 2 1 rfl rfl).mp
    ⟨hsplit.2.2.1, ρ, hρ⟩ |>.2
  exact ⟨hsplit, Module.Finite.of_surjective ρ hsurj,
    Module.Projective.of_split δ ρ hρ,
    Module.Finite.of_surjective q hsplit.2.2.1,
    Module.Projective.of_split s q hs'⟩

/-- Injectivity and projectivity of the quotient are equivalent to splitting. -/
theorem conormal_two_term_criterion :
    Specs.AdvCommAlg.Smooth.Conormal.twoTermCriterion.{u,v} := by
  intro A B _ _ _ _ n _ _ h
  constructor
  · intro hs
    have H := conormal_split_finite_projective A B n h hs
    exact ⟨H.1.1, H.2.2.2.2⟩
  · rintro ⟨hi, hp⟩
    let := hp
    obtain ⟨he, hq⟩ := Differentials.conormal_exact A (MvPolynomial (Fin n) A) B h
    obtain ⟨s, hs⟩ :=
      (conormalProjectionValue A (MvPolynomial (Fin n) A) B).exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
    apply (conormal_criterion A B n h).mpr
    exact (((he.split_tfae').out 1 2 rfl rfl).mp ⟨hi, s, hs⟩).2

end
end AdvCommAlg.Smooth
