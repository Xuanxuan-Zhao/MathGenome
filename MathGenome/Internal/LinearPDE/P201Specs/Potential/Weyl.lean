import MathGenome.Internal.LinearPDE.P201Specs.Potential.MeanValues
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.LocalConvolution

/-! Independent scope of paper.tex:651–708. Distributions are the continuous
scalar-linear dual of the canonical compact smooth test space. In particular,
no local integrability or continuity is assumed of the input distribution.
Representatives are ambient functions, and uniqueness is asserted on Ω only. -/
noncomputable section
open Set Metric MeasureTheory TopologicalSpace
open scoped ContDiff

namespace P201Specs.Weyl

/-- Pointwise uniqueness already holds among continuous representatives. -/
def ContinuousRepresentativeUniqueStatement : Prop :=
  ∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n) (u v : Space n → 𝕜),
    ContinuousOn u Ω → ContinuousOn v Ω →
    regularDistribution Ω u = regularDistribution Ω v → EqOn u v Ω

/-- Mollification is smooth and harmonic on its full admissible open set. -/
def HarmonicConvolutionStatement : Prop :=
  ∀ {n : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Domain n) (U : Distribution 𝕜 Ω),
    distributionLaplacian U = 0 → ∀ ρ : Test 𝕜 (⊤ : Domain n),
    ContDiffOn ℝ (⊤ : ℕ∞) (P102.U4.localConvolution U ρ)
      (P102.U4.convolutionDomain Ω ρ) ∧
    ∀ x ∈ P102.U4.convolutionDomain Ω ρ,
      laplacian (P102.U4.localConvolution U ρ) x = 0

/-- Weyl's lemma, with uniqueness as actual functions on the original open set. -/
def WeylStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ {𝕜 : Type} [RCLike 𝕜]
    (Ω : Domain n) (U : Distribution 𝕜 Ω), distributionLaplacian U = 0 →
    ∃ u : Space n → 𝕜,
      ContDiffOn ℝ (⊤ : ℕ∞) u Ω ∧ MeanValues.IsHarmonic Ω u ∧
      regularDistribution Ω u = U ∧
      ∀ v : Space n → 𝕜, ContinuousOn v Ω → regularDistribution Ω v = U →
        EqOn v u Ω

/-- The full source theorem retains both forward means and each converse. -/
def MeanValuesAndWeylStatement : Prop :=
  MeanValues.MeanValuesStatement ∧ MeanValues.BallConverseStatement ∧
    MeanValues.SphereConverseStatement ∧ WeylStatement

end P201Specs.Weyl
