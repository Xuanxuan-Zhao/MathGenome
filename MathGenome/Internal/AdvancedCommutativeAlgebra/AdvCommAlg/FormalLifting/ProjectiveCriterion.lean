import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.ProjectiveCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.SplittingCriterion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.PolynomialLifts
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Differentials.Polynomial

namespace AdvCommAlg.FormalLifting.ProjectiveCriterion

universe u v w
noncomputable section
open TensorProduct
open Specs.AdvCommAlg.Differentials
open Specs.AdvCommAlg.FormalLifting.SplittingCriterion
open AdvCommAlg.FormalLifting.SplittingCriterion

section General

variable (A : Type u) (P : Type v) (B : Type w)
  [CommRing A] [CommRing P] [CommRing B]
  [Algebra A P] [Algebra A B] [Algebra P B] [IsScalarTower A P B]
  (h : Function.Surjective (algebraMap P B))

/-- In a right exact sequence with projective middle module, splitting is
equivalent to injectivity of the first arrow and projectivity of the cokernel. -/
lemma splitConormal_iff_injective_projective
    [Module.Projective B (B ⊗[P] KaehlerDifferential A P)] :
    SplitConormal A P B h ↔
      Function.Injective (conormalMapValue A P B h) ∧
        Module.Projective B (KaehlerDifferential A B) := by
  obtain ⟨he, hs⟩ := AdvCommAlg.Differentials.conormal_exact A P B h
  constructor
  · intro H
    obtain ⟨_, s, hsp⟩ := (he.split_tfae'.out 2 1 rfl rfl).mp ⟨hs, H.2.2.2⟩
    exact ⟨H.1, Module.Projective.of_split s _ hsp⟩
  · rintro ⟨hi, hp⟩
    let := hp
    obtain ⟨s, hsp⟩ := (conormalProjectionValue A P B).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr hs)
    obtain ⟨_, ρ, hρ⟩ := (he.split_tfae'.out 1 2 rfl rfl).mp ⟨hi, s, hsp⟩
    exact (splitConormal_iff_retraction h).mpr ⟨ρ, hρ⟩

end General

section Polynomial

variable (A : Type u) (ι : Type v) (B : Type w)
  [CommRing A] [CommRing B] [Algebra A B]
  [Algebra (MvPolynomial ι A) B] [IsScalarTower A (MvPolynomial ι A) B]

/-- Scalar extension of the polynomial differential basis. -/
def middleBasis : Module.Basis ι B
    (B ⊗[MvPolynomial ι A] KaehlerDifferential A (MvPolynomial ι A)) :=
  (AdvCommAlg.Differentials.polynomialBasis A ι).baseChange B

theorem polynomial_criterion :
    Specs.AdvCommAlg.FormalLifting.ProjectiveCriterion.polynomialCriterion.{u,v,w} := by
  intro A ι B _ _ _ _ _ h
  let := Module.Free.of_basis (middleBasis A ι B)
  exact ((splitting_criterion A (MvPolynomial ι A) B h
    (polynomial_formallySmooth A ι)).2).trans
      (splitConormal_iff_injective_projective A (MvPolynomial ι A) B h)

theorem polynomial_summands :
    Specs.AdvCommAlg.FormalLifting.ProjectiveCriterion.polynomialSummands.{u,v,w} := by
  intro A ι B _ _ _ _ _ h hB
  let := Module.Free.of_basis (middleBasis A ι B)
  have H := ((splitting_criterion A (MvPolynomial ι A) B h
    (polynomial_formallySmooth A ι)).2).mp hB
  obtain ⟨ρ, hρ⟩ := H.2.2.2
  have hpL := Module.Projective.of_split (conormalMapValue A (MvPolynomial ι A) B h) ρ hρ
  have hpΩ := ((polynomial_criterion A ι B h).mp hB).2
  refine ⟨inferInstance, hpL, hpΩ, ?_⟩
  exact (H.2.1.split_tfae'.out 2 3 rfl rfl).mp ⟨H.2.2.1, ρ, hρ⟩

theorem finite_projective :
    Specs.AdvCommAlg.FormalLifting.ProjectiveCriterion.finiteProjective.{u,v,w} := by
  intro A ι B _ _ _ _ _ _ h hB
  let := Module.Finite.of_basis (middleBasis A ι B)
  obtain ⟨_, hpL, hpΩ, e, _, _⟩ := polynomial_summands A ι B h hB
  have hL : Module.Finite B (Conormal A (MvPolynomial ι A) B h) :=
    Module.Finite.of_surjective ((LinearMap.fst B _ _).comp e.toLinearMap)
      (Prod.fst_surjective.comp e.surjective)
  have hΩ : Module.Finite B (KaehlerDifferential A B) :=
    Module.Finite.of_surjective ((LinearMap.snd B _ _).comp e.toLinearMap)
      (Prod.snd_surjective.comp e.surjective)
  exact ⟨inferInstance, hL, hpL, hΩ, hpΩ⟩

end Polynomial
end
end AdvCommAlg.FormalLifting.ProjectiveCriterion
