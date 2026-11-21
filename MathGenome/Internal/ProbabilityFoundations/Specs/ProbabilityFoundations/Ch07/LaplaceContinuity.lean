import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.TransformObjects
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakFramework

/-! The full Laplace continuity theorem, paper.tex:2563–2587.
The subtype topology makes continuity at zero relative to the closed orthant.
No target probability, tightness, or moment condition is assumed. -/

open MeasureTheory Filter Topology

namespace Specs.ProbabilityFoundations.Ch07.LaplaceContinuity

open _root_.ProbabilityFoundations.Ch07

/-- Existence and uniqueness of the law with the stipulated transform, and
weak convergence of the entire original sequence to this law. -/
def laplaceContinuityType : Prop :=
  ∀ {d : ℕ} (μ : ℕ → ProbabilityMeasure (PositiveOrthant d))
    (L : PositiveOrthant d → ℝ),
    (∀ t : PositiveOrthant d, Tendsto
      (fun n => TransformObjects.laplaceTransformValue (μ n : Measure (PositiveOrthant d)) t)
      atTop (𝓝 (L t))) →
    ContinuousAt L 0 →
    ∃ ν : ProbabilityMeasure (PositiveOrthant d),
      (∀ t : PositiveOrthant d,
        TransformObjects.laplaceTransformValue (ν : Measure (PositiveOrthant d)) t = L t) ∧
      Ch06.WeakFramework.weaklyConvergesValue atTop μ ν ∧
      ∀ ρ : ProbabilityMeasure (PositiveOrthant d),
        (∀ t : PositiveOrthant d,
          TransformObjects.laplaceTransformValue (ρ : Measure (PositiveOrthant d)) t = L t) → ρ = ν

/-- The converse, tested against bounded continuous Laplace kernels. -/
def weaklyConvergesLaplaceType : Prop :=
  ∀ {d : ℕ} (μ : ℕ → ProbabilityMeasure (PositiveOrthant d))
    (ν : ProbabilityMeasure (PositiveOrthant d)),
    Ch06.WeakFramework.weaklyConvergesValue atTop μ ν →
    ∀ t : PositiveOrthant d, Tendsto
      (fun n => TransformObjects.laplaceTransformValue (μ n : Measure (PositiveOrthant d)) t)
      atTop (𝓝 (TransformObjects.laplaceTransformValue (ν : Measure (PositiveOrthant d)) t))

end Specs.ProbabilityFoundations.Ch07.LaplaceContinuity
