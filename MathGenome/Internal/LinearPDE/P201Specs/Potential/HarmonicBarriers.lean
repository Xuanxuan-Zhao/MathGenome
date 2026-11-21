import MathGenome.Internal.LinearPDE.P201Specs.Potential.MeanValues

/-! Barriers for the continuous-data part of paper.tex:1024–1094.
The C² boundary hypothesis is exactly the shared local one-sided graph condition.
-/
noncomputable section
open Set
namespace P201Specs.HarmonicBarriers

/-- A real harmonic barrier with a unique zero on the entire closed domain. -/
def HasHarmonicBarrierAt {n : ℕ} (Ω : Domain n) (z : Space n) : Prop :=
  ∃ b : Space n → ℝ, MeanValues.IsHarmonic Ω b ∧
    ContinuousOn b (closure (Ω : Set (Space n))) ∧ b z = 0 ∧
    ∀ x ∈ closure (Ω : Set (Space n)), x ≠ z → 0 < b x

abbrev HasHarmonicBarrierAtType := {n : ℕ} → Domain n → Space n → Prop

/-- Every boundary point of a bounded C² open set in dimension at least two
admits a barrier. No connectedness or exterior-ball certificate is assumed. -/
def C2HarmonicBarriersStatement : Prop :=
  ∀ {m : ℕ}, 1 ≤ m → ∀ (Ω : Domain (m + 1)),
    Bornology.IsBounded (Ω : Set (Space (m + 1))) → HasCkBoundary Ω 2 →
    ∀ z ∈ frontier (Ω : Set (Space (m + 1))), HasHarmonicBarrierAt Ω z

end P201Specs.HarmonicBarriers
