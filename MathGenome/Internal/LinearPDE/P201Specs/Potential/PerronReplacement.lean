import MathGenome.Internal.LinearPDE.P201Specs.Potential.SubharmonicMaximum

/-! The concrete Perron family and its two closure properties from the
continuous-data proof of `lem:pde-harmonic-lift` (paper.tex:1055–1071).
No boundedness, connectedness, or boundary regularity is required here. -/

noncomputable section
open Set Metric

namespace P201Specs.PerronReplacement

/-- Continuous real subsolutions with the prescribed upper boundary bound. -/
def perronClass {n : ℕ} (Ω : Domain n)
    (g : C(frontier (Ω : Set (Space n)), ℝ)) : Set (Space n → ℝ) :=
  {u | ContinuousOn u (closure (Ω : Set (Space n))) ∧
    SubharmonicMaximum.IsSubharmonic Ω (fun x => (u x : EReal)) ∧
    ∀ z : frontier (Ω : Set (Space n)), u z ≤ g z}

abbrev PerronClassType := {n : ℕ} → (Ω : Domain n) →
  C(frontier (Ω : Set (Space n)), ℝ) → Set (Space n → ℝ)

def MaxClosureStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (Ω : Domain n)
    (g : C(frontier (Ω : Set (Space n)), ℝ)) (u v : Space n → ℝ),
    u ∈ perronClass Ω g → v ∈ perronClass Ω g →
    (fun x => max (u x) (v x)) ∈ perronClass Ω g

def HarmonicRaisingStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (Ω : Domain n)
    (g : C(frontier (Ω : Set (Space n)), ℝ))
    (a : Space n) (r : ℝ), 0 < r → closedBall a r ⊆ (Ω : Set (Space n)) →
    ∀ u ∈ perronClass Ω g, ∃ v ∈ perronClass Ω g,
      u ≤ v ∧ MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ v

end P201Specs.PerronReplacement
