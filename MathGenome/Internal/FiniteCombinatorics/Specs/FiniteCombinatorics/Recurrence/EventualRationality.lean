import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.GeneratingSeries
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Independent specification of the first assertion of paper.tex, p204:W16.
The quotient is multiplication by the formal inverse of the normalized
polynomial denominator. No splitting or characteristic restriction is imposed.
The threshold applies to the starting index n of the recurrence window.
-/
noncomputable section
open scoped BigOperators
universe u
namespace Specs.FiniteCombinatorics.Recurrence

/-- Rational OGF iff a homogeneous recurrence holds from some index onward.
Positive order is required, but a zero coefficient is allowed, including for
order one and for polynomial generating series. -/
def eventual_rationality : Prop :=
  ∀ {K : Type u} [Field K] (a : ℕ → K),
    (∃ P Q : Polynomial K, Q.coeff 0 = 1 ∧
      Series.ogfValue a = (P : PowerSeries K) *
        PowerSeries.invOfUnit (Q : PowerSeries K) (1 : Kˣ)) ↔
    ∃ (r : ℕ) (_hr : 1 ≤ r) (c : Fin r → K) (N : ℕ),
      ∀ n : ℕ, N ≤ n → a (n + r) = ∑ j : Fin r, c j * a (n + (j : ℕ))

end Specs.FiniteCombinatorics.Recurrence
