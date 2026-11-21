import MathGenome.Internal.LinearPDE.P201Specs.Potential.GreenConstruction

/-! The C² testing and volume-integrability ingredients of the Green
representation theorem, paper.tex:1117–1133 and 1159–1176. All derivatives
are the canonical ambient coordinate derivatives on the open domain. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff
namespace P201Specs.GreenCompactC2

/-- Extend the distributional Green identity to genuine compact C² tests.
No regularity or boundedness of the boundary is required here. -/
def CompactC2Statement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ (Ω : Domain n) (x : Space n), x ∈ Ω →
    ∀ g : Space n → ℝ, GreenConstruction.IsGreenFunction Ω x g →
    ∀ φ : Space n → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ →
      tsupport φ ⊆ (Ω : Set _) →
      IntegrableOn (fun y => g y * (-laplacian φ y)) (Ω : Set _) volume ∧
      (∫ y in (Ω : Set _), g y * (-laplacian φ y)) = φ x

/-- C² on the closure suffices; arbitrary ambient behavior outside the
closure is allowed. Empty and disconnected bounded C² domains are included. -/
def VolumeIntegrabilityStatement : Prop :=
  ∀ {m : ℕ} (Ω : Domain (m + 1)),
    Bornology.IsBounded (Ω : Set (Space (m + 1))) → HasCkBoundary Ω 2 →
    ∀ (x : Space (m + 1)), x ∈ Ω → ∀ g : Space (m + 1) → ℝ,
      GreenConstruction.IsGreenFunction Ω x g →
      ∀ u : Space (m + 1) → ℝ,
        ContDiffOn ℝ 2 u (closure (Ω : Set _)) →
        IntegrableOn (fun y => g y * (-laplacian u y)) (Ω : Set _) volume

end P201Specs.GreenCompactC2
