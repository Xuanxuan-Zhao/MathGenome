import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.MoserProfiles

/-! Sobolev realization of the explicit profiles in paper.tex:2229–2244.
The space is the closure of tests in the distribution derivative tuple norm.
The domain is any open set containing the entire closed supporting ball. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal
namespace P102.Sobolev.MoserMembershipExpected
open P102.U4 TrudingerMoser

/-- The source profile, at every positive real logarithmic time, represents a
zero-boundary Sobolev function whose Euclidean gradient has norm exactly one. -/
def ProfileMembership : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d),
    letI : Fact (1 ≤ (d : ℝ≥0∞)) :=
      ⟨by exact_mod_cast (by omega : 1 ≤ d)⟩
    ∀ (Ω : Opens (Space d)) (c : Space d) (R : ℝ),
      0 < R → Metric.closedBall c R ⊆ (Ω : Set (Space d)) →
      ∀ L : ℝ, 0 < L → ∃ u : SobolevZero ℝ Ω 1 (d : ℝ≥0∞),
        (sobolevUnderlying u.val : Space d → ℝ) =ᵐ[volume.restrict (Ω : Set (Space d))]
          moserFunction c R L ∧
        eLpNorm (weakGradient u.val) (d : ℝ≥0∞)
          (volume.restrict (Ω : Set (Space d))) = 1

end P102.Sobolev.MoserMembershipExpected
