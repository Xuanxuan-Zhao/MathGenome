import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch17.LaplaceLocalization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! K03.17.laplace_local, paper.tex:4540–4581: the leading normalized
Laplace limit. The integral is the proper Darboux value, whose existence is
part of the conclusion. Scalars are exactly ℝ and ℂ. C² and continuity are
relative to the closed interval; no extension hypothesis is imposed. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch17.LaplaceLocal
open Set Filter
open scoped Topology
open _root_.SingleVariableAnalysis

def normalizedLimit : Prop :=
  ∀ (k : ScalarKind), letI := LaplaceLocalization.scalarRCLike k;
  ∀ (φ : ℝ → ℝ) (g : ℝ → Ch01.Scalar.scalarValue k) (a b x₀ : ℝ),
    a < b → ContDiffOn ℝ 2 φ (Icc a b) → ContinuousOn g (Icc a b) →
    x₀ ∈ Ioo a b →
    (∀ x ∈ Icc a b, x ≠ x₀ → φ x₀ < φ x) →
    0 < deriv (deriv φ) x₀ →
    ∃ h : ∀ t : ℝ, Ch08.Integral.scalarIntegrableValue k
        (fun x => Real.exp (-t * φ x) • g x) a b,
      Tendsto (fun t : ℝ => (Real.sqrt t * Real.exp (t * φ x₀)) •
        Ch08.Integral.scalarIntegralValue k _ (h t)) atTop
        (𝓝 (Real.sqrt (2 * Real.pi / deriv (deriv φ) x₀) • g x₀))

end Specs.SingleVariableAnalysis.Ch17.LaplaceLocal
