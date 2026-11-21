import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C06.NullCovers
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! Independent statements for `d04:06:riemann-criterion`. Continuity is
within the closed box, including its faces and degenerate coordinate intervals.
Nullity is the countable box-cover predicate from the upstream specification. -/
noncomputable section
open Set
namespace Specs.D04.C06.DiscontinuityCriterion.Model
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.NullCovers.Model

def discontinuitySet {n : ℕ} (f : E n → ℝ) (Q : Box n) : Set (E n) :=
  {x | x ∈ carrier Q ∧ ¬ ContinuousWithinAt f (carrier Q) x}

def badOscillationSet {n : ℕ} (f : E n → ℝ) (Q : Box n) (η : ℝ) : Set (E n) :=
  {x | x ∈ carrier Q ∧ η ≤ oscillation f Q x}
end Specs.D04.C06.DiscontinuityCriterion.Model

namespace Specs.D04.C06.DiscontinuityCriterion
open Specs.D04.C06.DarbouxIntegral.Model
open Specs.D04.C06.NullCovers.Model Model

abbrev discontinuitySetType := {n : ℕ} → (E n → ℝ) → Box n → Set (E n)
def discontinuitySetValue : discontinuitySetType := @Model.discontinuitySet
abbrev badOscillationSetType := {n : ℕ} → (E n → ℝ) → Box n → ℝ → Set (E n)
def badOscillationSetValue : badOscillationSetType := @Model.badOscillationSet

def oscillation_eq_zero_iffType : Prop := ∀ {n} (f : E n → ℝ) (Q : Box n),
  Bounded f Q → ∀ x ∈ carrier Q,
    (oscillation f Q x = 0 ↔ ContinuousWithinAt f (carrier Q) x)

def badOscillationSet_compactType : Prop := ∀ {n} (f : E n → ℝ) (Q : Box n),
  Bounded f Q → ∀ η > 0, IsCompact (badOscillationSet f Q η)

/-- Index `k` represents the positive integer `k+1`. -/
def discontinuitySet_eq_iUnionType : Prop := ∀ {n} (f : E n → ℝ) (Q : Box n),
  Bounded f Q → discontinuitySet f Q =
    ⋃ k : ℕ, badOscillationSet f Q (1 / (k + 1 : ℝ))

def integrable_iff_null_discontinuitySetType : Prop :=
  ∀ {n : ℕ}, 0 < n → ∀ (f : E n → ℝ) (Q : Box n), Bounded f Q →
    (Integrable f Q ↔ Null (discontinuitySet f Q))

end Specs.D04.C06.DiscontinuityCriterion
