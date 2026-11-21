import MathGenome.Internal.LinearPDE.P201Specs.Potential.ContinuousHarmonicLift

/-! Real weak/continuous boundary identification in the smooth-data clause of
paper.tex:1032–1037, 1102–1115. No boundary continuity of the weak solution
and no dimensional Sobolev embedding are hypotheses. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace P201Specs.WeakHarmonicBoundary

/-- Every real affine weak harmonic solution agrees almost everywhere with
any continuous harmonic extension of the same boundary datum. -/
def BoundaryIdentificationStatement : Prop :=
  ∀ {m : ℕ}, 1 ≤ m → ∀ (Ω : Domain (m + 1)),
    Bornology.IsBounded (Ω : Set (Space (m + 1))) → HasCkBoundary Ω 2 →
    ∀ (g : C(frontier (Ω : Set (Space (m + 1))), ℝ))
      (G₀ : Space (m + 1) → ℝ),
      (∃ U : Set (Space (m + 1)), IsOpen U ∧ closure (Ω : Set _) ⊆ U ∧
        ContDiffOn ℝ (⊤ : ℕ∞) G₀ U) →
      (∀ z : frontier (Ω : Set (Space (m + 1))), G₀ z = g z) →
      ∀ u : H ℝ Ω 1,
        (∃ z : H10 ℝ Ω, (hUnderlying Ω 1 u : Space (m + 1) → ℝ)
          =ᵐ[domainMeasure Ω] fun x => G₀ x + hZeroUnderlying Ω z x) →
        (∀ v : H10 ℝ Ω, ellipticEnergyForm Ω
          (fun _ => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)) u v.val = 0) →
        ∀ h : Space (m + 1) → ℝ, ContinuousHarmonicLift.IsExtension Ω g h →
          (hUnderlying Ω 1 u : Space (m + 1) → ℝ) =ᵐ[domainMeasure Ω] h

end P201Specs.WeakHarmonicBoundary
