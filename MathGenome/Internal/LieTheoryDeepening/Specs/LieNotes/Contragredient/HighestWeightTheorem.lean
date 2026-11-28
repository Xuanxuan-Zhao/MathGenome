import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Contragredient.SimpleHighestWeight
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! The assembled highest-weight theorem for the canonical contragredient algebra. -/

namespace Specs.LieNotes.Contragredient.HighestWeightTheorem

open CartanData CartanQuotient
open SimpleHighestWeight (L quotientMap)
open VermaModules (Verma IsWeightCharacter)
open _root_.RepTheorySurvey.CategoryO.BorelInduction (U)
open UniversalEnvelopingAlgebra (ι)

universe u v w

/-- For every realization and weight, the induced Verma module has finite-dimensional
weight spaces, a one-dimensional top, and a unique simple quotient. The simple quotient
is integrable exactly at dominant integral weights, where all its weight multiplicities
are invariant under simple reflections. -/
def HighestWeightResult : Prop :=
  ∀ {I : Type u} {A : Matrix I I ℤ} {H : Type v}
    [AddCommGroup H] [Module ℂ H] [Finite I],
    IsGeneralizedCartanMatrix A → ∀ (R : Realization A H) (Λ : Module.Dual ℂ H),
    ∃ hχ : ∃! χ, IsWeightCharacter R Λ χ,
      (∀ μ : Module.Dual ℂ H, FiniteDimensional ℂ (VermaModules.weightSpaceAt R Λ hχ μ)) ∧
      Module.finrank ℂ (VermaModules.weightSpaceAt R Λ hχ Λ) = 1 ∧
      IsSimpleModule (U (Algebra R)) (L R Λ hχ) ∧
      (∀ (V : Type w) [AddCommGroup V] [Module (U (Algebra R)) V]
          [IsSimpleModule (U (Algebra R)) V]
          (q : Verma R Λ hχ →ₗ[U (Algebra R)] V), Function.Surjective q →
        ∃! e : L R Λ hχ ≃ₗ[U (Algebra R)] V, e.toLinearMap.comp (quotientMap R Λ hχ) = q) ∧
      (((∀ (i : I) (z : L R Λ hχ), ∃ n : ℕ, (ι ℂ (e R i) : U (Algebra R)) ^ n • z = 0) ∧
        (∀ (i : I) (z : L R Λ hχ), ∃ n : ℕ, (ι ℂ (f R i) : U (Algebra R)) ^ n • z = 0)) ↔
        ∀ i : I, ∃ m : ℕ, Λ (R.h i) = (m : ℂ)) ∧
      (∀ μ : Module.Dual ℂ H, FiniteDimensional ℂ (SimpleHighestWeight.weightSpaceAt R Λ hχ μ)) ∧
      ((∀ i : I, ∃ m : ℕ, Λ (R.h i) = (m : ℂ)) → ∀ (i : I) (μ : Module.Dual ℂ H),
        Module.finrank ℂ (SimpleHighestWeight.weightSpaceAt R Λ hχ μ) =
          Module.finrank ℂ (SimpleHighestWeight.weightSpaceAt R Λ hχ (R.weightReflection i μ)))

end Specs.LieNotes.Contragredient.HighestWeightTheorem
