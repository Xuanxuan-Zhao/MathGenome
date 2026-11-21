import MathGenome.Internal.LinearPDE.P201Specs.Potential.SubharmonicMaximum

/-! The full comparison theorem of paper.tex:784–851. The extended-valued
submean predicates, admissibility, measures and Laplacian are the canonical
upstream definitions. Only real harmonic comparison functions are used.
Boundary control is an interior limsup, with no boundary trace assumption. -/
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology ContDiff

namespace P201Specs.SubharmonicComparison
open SubharmonicMaximum

abbrev ComparisonType := {n : ℕ} → Domain n → (Space n → EReal) → Prop

def HasHarmonicComparison : ComparisonType := fun Ω u =>
  ∀ (a : Space _) (r : ℝ), 0 < r → closedBall a r ⊆ (Ω : Set _) →
    ∀ h : Space _ → ℝ,
      MeanValues.IsHarmonic ⟨ball a r, isOpen_ball⟩ h →
      ContinuousOn h (closedBall a r) →
      (∀ ζ ∈ sphere a r, limsup u (𝓝[ball a r] ζ) ≤ (h ζ : EReal)) →
      ∀ x ∈ ball a r, u x ≤ (h x : EReal)

def BallImpliesComparisonStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (Ω : Domain n) (u : Space n → EReal),
    UpperSemicontinuousOn u (Ω : Set _) → (∀ x ∈ Ω, u x ≠ ⊤) →
    HasBallSubmean Ω u → HasHarmonicComparison Ω u

def ComparisonImpliesSphereStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (Ω : Domain n) (u : Space n → EReal),
    UpperSemicontinuousOn u (Ω : Set _) → (∀ x ∈ Ω, u x ≠ ⊤) →
    HasHarmonicComparison Ω u → HasSphereSubmean Ω u

/-- All three conditions are equivalent under the original admissibility
hypotheses, allowing negative infinite values. -/
def EquivalenceStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (Ω : Domain n) (u : Space n → EReal),
    IsAdmissible Ω u →
      (HasSphereSubmean Ω u ↔ HasBallSubmean Ω u) ∧
      (HasSphereSubmean Ω u ↔ HasHarmonicComparison Ω u)

/-- A maximum is taken over the entire component, not just a neighborhood. -/
def StrongMaximumStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (Ω : Domain n) (u : Space n → EReal),
    IsSubharmonic Ω u → ∀ a ∈ Ω, ∀ m : ℝ, u a = (m : EReal) →
      (∀ x ∈ connectedComponentIn (Ω : Set _) a, u x ≤ (m : EReal)) →
      ∀ x ∈ connectedComponentIn (Ω : Set _) a, u x = (m : EReal)

def BoundaryMaximumStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (Ω : Domain n) (u : Space n → EReal) (M : ℝ),
    Bornology.IsBounded (Ω : Set (Space n)) → IsSubharmonic Ω u →
    (∀ ζ ∈ frontier (Ω : Set _), limsup u (𝓝[Ω] ζ) ≤ (M : EReal)) →
      ∀ x ∈ Ω, u x ≤ (M : EReal)

/-- Each of the three conditions, and the original subharmonicity definition,
specializes to the nonnegative coordinate Laplacian for real C² functions. -/
def SmoothCriterionStatement : Prop :=
  ∀ {n : ℕ}, 2 ≤ n → ∀ (Ω : Domain n) (u : Space n → ℝ),
    ContDiffOn ℝ 2 u Ω →
      (HasSphereSubmean Ω (fun x => (u x : EReal)) ↔
        ∀ x ∈ Ω, 0 ≤ laplacian u x) ∧
      (HasBallSubmean Ω (fun x => (u x : EReal)) ↔
        ∀ x ∈ Ω, 0 ≤ laplacian u x) ∧
      (HasHarmonicComparison Ω (fun x => (u x : EReal)) ↔
        ∀ x ∈ Ω, 0 ≤ laplacian u x) ∧
      (IsSubharmonic Ω (fun x => (u x : EReal)) ↔
        ∀ x ∈ Ω, 0 ≤ laplacian u x)

end P201Specs.SubharmonicComparison
