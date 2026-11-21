import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.MetricCompactness
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.UniformContinuity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.HeineCantor
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Heine–Cantor

K03.03.heine_cantor, paper.tex:592–598. We use Mathlib's Heine–Cantor
theorem on compact subsets of uniform spaces, after converting the upstream
relative epsilon–delta continuity hypothesis to ContinuousOn. The upstream
uniform-continuity bridge converts its conclusion back to a single positive
radius valid for every pair in E. Metric spaces carry their canonical uniform
structures, so this applies to arbitrary metric domains and to both scalar
targets, including empty domains. This proof uses the library's uniform-space
argument rather than the manuscript's sequential contradiction argument.
-/
namespace SingleVariableAnalysis

universe u v

/-- A continuous map on a compact metric subset is uniformly continuous there. -/
theorem heine_cantor
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (hE : IsCompact E)
    (hf : RelativeContinuous f E) : RelativeUniformContinuous f E := by
  apply (relativeUniformContinuous_on_iff f E).mpr
  apply hE.uniformContinuousOn_of_continuous
  intro a ha
  exact (relativeContinuousAt_within_iff f E a).mp (hf a ha)

/-- The real scalar statement, with absolute values and a uniform radius. -/
theorem heine_cantor_real
    {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X)
    (hE : IsCompact E)
    (hf : ∀ a ∈ E, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ E, dist x a < δ → |f x - f a| < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ E, ∀ y ∈ E, dist x y < δ → |f x - f y| < ε := by
  have hc : RelativeContinuous f E := by
    simpa only [RelativeContinuous, RelativeContinuousAt, Real.dist_eq] using hf
  exact (real_relativeUniformContinuous_iff f E).mp (heine_cantor f E hE hc)

/-- The complex scalar statement uses the usual complex modulus. -/
theorem heine_cantor_complex
    {X : Type u} [MetricSpace X] (f : X → ℂ) (E : Set X)
    (hE : IsCompact E)
    (hf : ∀ a ∈ E, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ E, dist x a < δ → ‖f x - f a‖ < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ E, ∀ y ∈ E, dist x y < δ → ‖f x - f y‖ < ε := by
  have hc : RelativeContinuous f E := by
    simpa only [RelativeContinuous, RelativeContinuousAt, dist_eq_norm] using hf
  exact (complex_relativeUniformContinuous_iff f E).mp (heine_cantor f E hE hc)

end SingleVariableAnalysis
