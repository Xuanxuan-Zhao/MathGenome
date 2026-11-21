import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Real.Sqrt

/-! Localization part of K03.17.laplace_local (paper.tex:4553–4560).
The strict inequality off x₀ expresses uniqueness of the global minimum.
C² is relative to the closed interval, with no extension hypothesis.
The exterior is the sum of the two proper Darboux integrals. -/
noncomputable section
namespace Specs.SingleVariableAnalysis.Ch17.LaplaceLocalization
open Set Filter
open scoped Topology
open _root_.SingleVariableAnalysis

/-- The canonical real/complex structures, selected by the existing scalar tag. -/
@[instance_reducible] def scalarRCLike : (k : ScalarKind) → RCLike (Ch01.Scalar.scalarValue k)
  | .real => inferInstanceAs (RCLike ℝ)
  | .complex => inferInstanceAs (RCLike ℂ)

/-- Fermat at the interior minimum. -/
def stationary : Prop :=
  ∀ (φ : ℝ → ℝ) (a b x₀ : ℝ),
    ContDiffOn ℝ 2 φ (Icc a b) → x₀ ∈ Ioo a b →
    (∀ x ∈ Icc a b, x ≠ x₀ → φ x₀ < φ x) → deriv φ x₀ = 0

/-- Second order Taylor expansion, with the actual second real derivative. -/
def quadraticPeano : Prop :=
  ∀ (φ : ℝ → ℝ) (a b x₀ : ℝ),
    ContDiffOn ℝ 2 φ (Icc a b) → x₀ ∈ Ioo a b →
    (∀ x ∈ Icc a b, x ≠ x₀ → φ x₀ < φ x) →
    Asymptotics.IsLittleO (𝓝[≠] (0 : ℝ))
      (fun h => φ (x₀+h) - φ x₀ - deriv (deriv φ) x₀ * h^2 / 2)
      (fun h : ℝ => h^2)

/-- A closed symmetric neighborhood inside the interval and the bound d h²/4. -/
def localLower : Prop :=
  ∀ (φ : ℝ → ℝ) (a b x₀ : ℝ),
    ContDiffOn ℝ 2 φ (Icc a b) → x₀ ∈ Ioo a b →
    (∀ x ∈ Icc a b, x ≠ x₀ → φ x₀ < φ x) →
    0 < deriv (deriv φ) x₀ →
    ∃ r : ℝ, 0 < r ∧ a < x₀-r ∧ x₀+r < b ∧
      ∀ h : ℝ, |h| ≤ r →
        deriv (deriv φ) x₀ / 4 * h^2 ≤ φ (x₀+h) - φ x₀

/-- Compactness and uniqueness give a gap outside every positive radius. -/
def exteriorGap : Prop :=
  ∀ (φ : ℝ → ℝ) (a b x₀ : ℝ),
    ContinuousOn φ (Icc a b) → x₀ ∈ Ioo a b →
    (∀ x ∈ Icc a b, x ≠ x₀ → φ x₀ < φ x) →
    ∀ r : ℝ, 0 < r → ∃ η : ℝ, 0 < η ∧
      ∀ x ∈ Icc a b, r ≤ |x-x₀| → φ x₀ + η ≤ φ x

/-- Explicit exponential bound and zero limit for the normalized exterior
contribution, for each of the two scalar fields. Integrability is asserted,
not assumed as an additional certificate. -/
def exteriorDecay : Prop :=
  ∀ (k : ScalarKind), letI := scalarRCLike k; ∀ (φ : ℝ → ℝ)
    (g : ℝ → Ch01.Scalar.scalarValue k) (a b x₀ : ℝ),
    ContinuousOn φ (Icc a b) → ContinuousOn g (Icc a b) →
    x₀ ∈ Ioo a b →
    (∀ x ∈ Icc a b, x ≠ x₀ → φ x₀ < φ x) →
    ∀ r : ℝ, 0 < r → a < x₀-r → x₀+r < b →
    ∃ η M : ℝ, 0 < η ∧ 0 ≤ M ∧
      (∀ x ∈ Icc a b, ‖g x‖ ≤ M) ∧
      ∃ (hL : ∀ t : ℝ, Ch08.Integral.scalarIntegrableValue k
            (fun x => Real.exp (-t * φ x) • g x) a (x₀-r))
        (hR : ∀ t : ℝ, Ch08.Integral.scalarIntegrableValue k
            (fun x => Real.exp (-t * φ x) • g x) (x₀+r) b),
      (∀ t : ℝ, 0 ≤ t →
        ‖(Real.sqrt t * Real.exp (t * φ x₀)) •
          (Ch08.Integral.scalarIntegralValue k _ (hL t) +
           Ch08.Integral.scalarIntegralValue k _ (hR t))‖ ≤
          Real.sqrt t * M * (b-a) * Real.exp (-t * η)) ∧
      Tendsto (fun t : ℝ => (Real.sqrt t * Real.exp (t * φ x₀)) •
          (Ch08.Integral.scalarIntegralValue k _ (hL t) +
           Ch08.Integral.scalarIntegralValue k _ (hR t))) atTop (𝓝 0)

end Specs.SingleVariableAnalysis.Ch17.LaplaceLocalization
