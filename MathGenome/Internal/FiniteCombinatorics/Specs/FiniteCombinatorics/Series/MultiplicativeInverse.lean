import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.GeneratingSeries
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Independent statements for the multiplicative assertion of p204:W12.
The inverse is Mathlib's recursive unit-based construction, in the same
`PowerSeries R` representation as the upstream generating series. -/

noncomputable section
universe u

namespace Specs.FiniteCombinatorics.Series

def multiplicative_inverse_criterion : Prop :=
  ∀ {R : Type u} [CommRing R] (A : PowerSeries R),
    (∃ C : PowerSeries R, A * C = 1 ∧ C * A = 1) ↔
      IsUnit (PowerSeries.constantCoeff A)

def unit_inverse_identities : Prop :=
  ∀ {R : Type u} [CommRing R] (A : PowerSeries R) (a₀ : Rˣ),
    PowerSeries.constantCoeff A = (a₀ : R) →
      A * PowerSeries.invOfUnit A a₀ = 1 ∧
        PowerSeries.invOfUnit A a₀ * A = 1

def unit_inverse_constant : Prop :=
  ∀ {R : Type u} [CommRing R] (A : PowerSeries R) (a₀ : Rˣ),
    PowerSeries.constantCoeff A = (a₀ : R) →
      PowerSeries.coeff 0 (PowerSeries.invOfUnit A a₀) = (↑a₀⁻¹ : R)

def unit_inverse_recurrence : Prop :=
  ∀ {R : Type u} [CommRing R] (A : PowerSeries R) (a₀ : Rˣ),
    PowerSeries.constantCoeff A = (a₀ : R) →
      ∀ n : ℕ, 1 ≤ n →
        PowerSeries.coeff n (PowerSeries.invOfUnit A a₀) =
          -(↑a₀⁻¹ : R) * ∑ i ∈ Finset.Icc 1 n,
            PowerSeries.coeff i A *
              PowerSeries.coeff (n - i) (PowerSeries.invOfUnit A a₀)

end Specs.FiniteCombinatorics.Series
