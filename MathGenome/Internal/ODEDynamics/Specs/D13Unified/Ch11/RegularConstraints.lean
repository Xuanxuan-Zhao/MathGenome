import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch11.Invariant

/-! Independent statement of paper.tex, d13:11:first-integral, regular constraints.
Full rank in the finite-dimensional target is expressed as surjectivity of Dh.
The level set is relative to Ω. Neither dimension is required to be positive.
Tangency is required only on that level set, and h is only C¹. -/
noncomputable section
open Set
namespace Specs.D13Unified.Ch11.RegularConstraints
open _root_.D13Unified Ch01.AutonomousParameters
universe u v

def Invariance : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type v} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]
    (F : AutonomousODE E), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ (h : E → H), ContDiffOn ℝ 1 h F.domain → ∀ c : H,
      (∀ p ∈ F.domain, h p = c → Function.Surjective (fderiv ℝ h p)) →
      (∀ p ∈ F.domain, h p = c → (fderiv ℝ h p) (autonomousEvalValue F p) = 0) →
      Invariant.invariantValue F {p | p ∈ F.domain ∧ h p = c}

end Specs.D13Unified.Ch11.RegularConstraints
