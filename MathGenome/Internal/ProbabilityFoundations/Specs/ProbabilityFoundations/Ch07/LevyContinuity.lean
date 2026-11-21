import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.TransformObjects
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.WeakFramework

/-!
Independent statements of the Lévy continuity theorem, paper.tex:2533–2560.
Euclidean spaces have their Borel sigma algebra. All dimensions, including
zero, are allowed. The forward hypothesis requires continuity only at the
origin and supplies neither a limiting law nor tightness.
-/

open MeasureTheory Filter Topology

namespace Specs.ProbabilityFoundations.Ch07.LevyContinuity

open _root_.ProbabilityFoundations.Ch07
open Specs.ProbabilityFoundations.Ch07.TransformObjects

/-- Existence and uniqueness of the law with the prescribed limiting transform,
together with weak convergence of the entire original sequence. Uniqueness is
among all probability laws with that transform, irrespective of convergence. -/
def forward : Prop :=
  ∀ {d : ℕ} (μs : ℕ → ProbabilityMeasure (Euclidean d)) (φ : Euclidean d → ℂ),
    (∀ t : Euclidean d, Tendsto (fun n => characteristicFunctionValue (μs n : Measure (Euclidean d)) t) atTop (𝓝 (φ t))) →
    ContinuousAt φ 0 →
    ∃ μ : ProbabilityMeasure (Euclidean d),
      (∀ t : Euclidean d, characteristicFunctionValue (μ : Measure (Euclidean d)) t = φ t) ∧
      Specs.ProbabilityFoundations.Ch06.WeakFramework.weaklyConvergesValue atTop μs μ ∧
      ∀ ν : ProbabilityMeasure (Euclidean d),
        (∀ t : Euclidean d, characteristicFunctionValue (ν : Measure (Euclidean d)) t = φ t) → ν = μ

/-- Every weakly convergent sequence has pointwise convergent characteristic
functions, with limit the characteristic function of its weak limit. -/
def converse : Prop :=
  ∀ {d : ℕ} (μs : ℕ → ProbabilityMeasure (Euclidean d))
    (μ : ProbabilityMeasure (Euclidean d)),
    Specs.ProbabilityFoundations.Ch06.WeakFramework.weaklyConvergesValue atTop μs μ →
    ∀ t : Euclidean d, Tendsto (fun n => characteristicFunctionValue (μs n : Measure (Euclidean d)) t) atTop
      (𝓝 (characteristicFunctionValue (μ : Measure (Euclidean d)) t))

end Specs.ProbabilityFoundations.Ch07.LevyContinuity
