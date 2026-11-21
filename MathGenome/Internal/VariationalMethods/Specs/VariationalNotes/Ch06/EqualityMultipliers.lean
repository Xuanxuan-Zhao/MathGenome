import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.EqualityChart
import Mathlib.Analysis.Calculus.LocalExtr.Basic

open Set
open scoped Topology ContDiff

namespace VariationalNotes.Ch06.EqualityMultipliers.Specs

/-- The dual is the continuous real dual. Precomposition `ν.comp B` is
`B* ν`, so the equation has the source's Lagrangian sign convention. -/
def EqualityMultipliersType : Prop :=
  ∀ (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (r : ℕ∞ω), 1 ≤ r → ∀ (U : Set X), IsOpen U →
    ∀ (h : X → Y), ContDiffOn ℝ r h U → ∀ a ∈ U, h a = 0 →
    ∀ (B : X →L[ℝ] Y), HasFDerivAt h B a →
    ∀ (R : Y →L[ℝ] X), B.comp R = ContinuousLinearMap.id ℝ Y →
    ∀ (f : X → ℝ), DifferentiableAt ℝ f a →
    IsLocalMinOn f (U ∩ h ⁻¹' {0}) a →
    ∃! ν : Y →L[ℝ] ℝ, fderiv ℝ f a + ν.comp B = 0

/-- Finitely many equality constraints on a Banach domain: the target alone
is finite-dimensional, and surjectivity suffices. This includes the case
where both spaces are finite-dimensional. -/
def FiniteTargetEqualityMultipliersType : Prop :=
  ∀ (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (r : ℕ∞ω), 1 ≤ r → ∀ (U : Set X), IsOpen U →
    ∀ (h : X → Y), ContDiffOn ℝ r h U → ∀ a ∈ U, h a = 0 →
    ∀ (B : X →L[ℝ] Y), HasFDerivAt h B a → Function.Surjective B →
    ∀ (f : X → ℝ), DifferentiableAt ℝ f a →
    IsLocalMinOn f (U ∩ h ⁻¹' {0}) a →
    ∃! ν : Y →L[ℝ] ℝ, fderiv ℝ f a + ν.comp B = 0

end VariationalNotes.Ch06.EqualityMultipliers.Specs
