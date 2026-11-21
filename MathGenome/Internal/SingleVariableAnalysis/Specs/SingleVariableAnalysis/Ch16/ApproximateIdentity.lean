import Mathlib.Analysis.Complex.Basic
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.Algebra.Support

/-! K03.16.approximate_identity, paper.tex:3946–3960.
The values below are the existing proper Darboux integrals, componentwise for ℂ.
Kernel normalization is over its support interval. Both scalar cases retain
boundedness, global uniform continuity, and positive decreasing radii tending to zero.
-/
namespace Specs.SingleVariableAnalysis.Ch16.ApproximateIdentity
open Filter
open scoped Topology
namespace I
export Specs.SingleVariableAnalysis.Ch08.Integral
  (realIntegrableValue realIntegralValue complexIntegrableValue complexIntegralValue)
end I

abbrev modulusType := {E : Type} → [NormedAddCommGroup E] → (ℝ → E) → ℝ → ℝ
noncomputable def modulusValue : modulusType := fun f δ =>
  sSup {r : ℝ | ∃ x y : ℝ, |x - y| ≤ δ ∧ r = ‖f x - f y‖}

abbrev triangleType := ℝ → ℝ → ℝ
noncomputable def triangleValue : triangleType := fun δ t => δ⁻¹ * max (1 - |t| / δ) 0

/-- All integrability and all uniform conclusions, with no restriction of x
 to a compact set. The displayed supremum is of the full real error image. -/
def realApproximation : Prop :=
  ∀ (f : ℝ → ℝ), (∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) → UniformContinuous f →
  ∀ (δ : ℕ → ℝ), (∀ j, 0 < δ j) → Antitone δ → Tendsto δ atTop (𝓝 0) →
  ∀ (k : ℕ → ℝ → ℝ), (∀ j, Continuous (k j)) → (∀ j t, 0 ≤ k j t) →
  (∀ j, Function.support (k j) ⊆ Set.Icc (-δ j) (δ j)) →
  ∀ hk : ∀ j, I.realIntegrableValue (k j) (-δ j) (δ j),
  (∀ j, I.realIntegralValue (k j) (hk j) = 1) →
  ∃ h : ∀ j x, I.realIntegrableValue (fun t => k j t • f (x - t)) (-δ j) (δ j),
    (∀ j x, ‖I.realIntegralValue _ (h j x) - f x‖ ≤ modulusValue f (δ j)) ∧
    (∀ j, sSup (Set.range (fun x => ‖I.realIntegralValue _ (h j x) - f x‖)) ≤
      modulusValue f (δ j)) ∧
    TendstoUniformly (fun j x => I.realIntegralValue _ (h j x)) f atTop

def complexApproximation : Prop :=
  ∀ (f : ℝ → ℂ), (∃ M : ℝ, ∀ x, ‖f x‖ ≤ M) → UniformContinuous f →
  ∀ (δ : ℕ → ℝ), (∀ j, 0 < δ j) → Antitone δ → Tendsto δ atTop (𝓝 0) →
  ∀ (k : ℕ → ℝ → ℝ), (∀ j, Continuous (k j)) → (∀ j t, 0 ≤ k j t) →
  (∀ j, Function.support (k j) ⊆ Set.Icc (-δ j) (δ j)) →
  ∀ hk : ∀ j, I.realIntegrableValue (k j) (-δ j) (δ j),
  (∀ j, I.realIntegralValue (k j) (hk j) = 1) →
  ∃ h : ∀ j x, I.complexIntegrableValue (fun t => k j t • f (x - t)) (-δ j) (δ j),
    (∀ j x, ‖I.complexIntegralValue _ (h j x) - f x‖ ≤ modulusValue f (δ j)) ∧
    (∀ j, sSup (Set.range (fun x => ‖I.complexIntegralValue _ (h j x) - f x‖)) ≤
      modulusValue f (δ j)) ∧
    TendstoUniformly (fun j x => I.complexIntegralValue _ (h j x)) f atTop

/-- The explicit triangular construction, including its proper normalization.
Function support containment also gives topological support containment since
 the containing interval is closed. -/
def triangularKernel : Prop := ∀ δ : ℝ, 0 < δ →
  Continuous (triangleValue δ) ∧ (∀ t, 0 ≤ triangleValue δ t) ∧
  Function.support (triangleValue δ) ⊆ Set.Icc (-δ) δ ∧
  tsupport (triangleValue δ) ⊆ Set.Icc (-δ) δ ∧
  ∃ h : I.realIntegrableValue (triangleValue δ) (-δ) δ,
    I.realIntegralValue _ h = 1

end Specs.SingleVariableAnalysis.Ch16.ApproximateIdentity
