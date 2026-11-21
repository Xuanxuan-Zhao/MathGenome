import MathGenome.RealAnalysis

/-! Independent downstream expectations. The formulas below spell out the
mathematical conclusions rather than referring to the D11 statement aliases. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace Examples.GenomeAnalysisProbeSpecs

def complexPrimitiveStieltjes : Prop :=
  ∀ (f : ℝ → ℂ) (c : ℂ) {a b : ℝ}, a < b →
    IntegrableOn f (Icc a b) →
    let F : ℝ → ℂ := fun x => c + ∫ t in a..x, f t
    let G : ℝ → ℂ := fun x => F (max a (min b x)) - F a
    D11.Ch12.GloballyBV G ∧
      (∀ x, ContinuousWithinAt G (Ici x) x) ∧
      Tendsto G atBot (𝓝 0) ∧ Continuous G ∧
      (D11.Ch12.ScalarStieltjesCorrespondence.stieltjesMeasure G).variation ≪ volume

def complexPrimitiveVariationAndRepresentative : Prop :=
  ∀ (f : ℝ → ℂ) (c : ℂ) {a b : ℝ}, a < b →
    IntegrableOn f (Icc a b) →
    let F : ℝ → ℂ := fun x => c + ∫ t in a..x, f t
    D11.Ch12.variation F a b = ENNReal.ofReal (∫ t in a..b, ‖f t‖) ∧
      (∀ᵐ x ∂volume, x ∈ Ioo a b → HasDerivAt F (f x) x) ∧
      ∀ g : ℝ → ℂ, IntegrableOn g (Icc a b) →
        f =ᵐ[volume.restrict (Icc a b)] g →
        ∀ x ∈ Icc a b, F x = c + ∫ t in a..x, g t

def squareRootProductFtc : Prop :=
  let F : ℝ → ℝ := fun x => Real.sqrt x * Real.sqrt x
  IntegrableOn (deriv F) (Icc 0 1) ∧
    (∀ᵐ x ∂volume, x ∈ Ioo 0 1 → HasDerivAt F (deriv F x) x) ∧
    ∀ x ∈ Icc 0 1, F x = F 0 + ∫ t in 0..x, deriv F t

end Examples.GenomeAnalysisProbeSpecs
