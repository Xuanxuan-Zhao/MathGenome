import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.EventuallyCompactSpectralMapping
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Independent obligations for the last two assertions of
`fa2:p3:semigroup-spectral-mapping` (paper.tex:14566–14570, 14613–14625).
The bounds are extended-real bounds, and the spectrum may be empty.
The expansion retains the exact unbounded generator domain. -/
noncomputable section
open scoped NNReal

namespace ExpandedFA.Semigroups.EventuallyCompactAsymptoticsSpec
open EventuallyCompactSpectralMappingSpec

/-- Equality includes the value −∞ and the zero Banach space. -/
def GrowthSpectralBoundEquality : Prop :=
  ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : C0Semigroup ℂ X), EventuallyCompact T →
    C0SemigroupSpec.growthBoundValue T =
      C0SemigroupSpec.spectralBoundValue (C0SemigroupSpec.generatorValue T)

/-- A finite Jordan expansion on precisely the generalized eigenspaces to the
right of the cut. The bounded ambient nilpotent maps vanish off their spectral
summands. Their action agrees with A−λ on those summands, including its domain.
The residual estimate holds at every nonnegative time, including zero. -/
def HasFiniteExpansion {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] [CompleteSpace X] (T : C0Semigroup ℂ X) (a : ℝ) : Prop :=
  let A := C0SemigroupSpec.generatorValue T
  ∃ (s : Finset ℂ) (P N : ℂ → X →L[ℂ] X) (m : ℂ → ℕ)
    (R : ℝ≥0 → X →L[ℂ] X) (C : ℝ),
    (∀ ζ : ℂ, ζ ∈ s ↔ ζ ∈ C0SemigroupSpec.spectrumValue A ∧ a < ζ.re) ∧
    (∀ ζ ∈ s,
      0 < m ζ ∧
      FiniteDimensional ℂ (generatorGeneralizedEigenspace A ζ) ∧
      LinearMap.range (P ζ).toLinearMap = generatorGeneralizedEigenspace A ζ ∧
      P ζ * P ζ = P ζ ∧
      N ζ * P ζ = N ζ ∧ P ζ * N ζ = N ζ ∧ N ζ ^ m ζ = 0 ∧
      (∀ x : X, P ζ x ∈ A.domain) ∧
      (∀ (x : X) (hx : P ζ x ∈ A.domain),
        A ⟨P ζ x, hx⟩ = ζ • P ζ x + N ζ (P ζ x)) ∧
      (∀ t : ℝ≥0, Commute (P ζ) (T.operators t))) ∧
    (∀ ζ ∈ s, ∀ η ∈ s, ζ ≠ η → P ζ * P η = 0) ∧
    0 ≤ C ∧
    (∀ t : ℝ≥0,
      T.operators t =
        (∑ ζ ∈ s, Complex.exp ((t : ℂ) * ζ) •
          (∑ j ∈ Finset.range (m ζ),
            ((t : ℂ) ^ j / (Nat.factorial j : ℂ)) • (N ζ ^ j * P ζ))) + R t) ∧
    ∀ t : ℝ≥0, ‖R t‖ ≤ C * Real.exp (a * (t : ℝ))

/-- Every spectral cut avoiding the spectrum has the asserted finite
exponential-polynomial expansion. No compact-resolvent premise is added. -/
def FiniteExponentialPolynomialExpansion : Prop :=
  ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : C0Semigroup ℂ X), EventuallyCompact T →
    ∀ a : ℝ, (∀ ζ ∈ C0SemigroupSpec.spectrumValue
      (C0SemigroupSpec.generatorValue T), ζ.re ≠ a) → HasFiniteExpansion T a

end ExpandedFA.Semigroups.EventuallyCompactAsymptoticsSpec
