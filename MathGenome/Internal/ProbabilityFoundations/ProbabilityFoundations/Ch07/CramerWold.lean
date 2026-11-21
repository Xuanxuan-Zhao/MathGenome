import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.CharacteristicUniqueness
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.LevyContinuity
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.ContinuousMapping
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.CramerWold

/-!
Cramér–Wold (paper.tex:2591–2602). The transform at t is the transform
of the real t-projection at 1. Uniqueness gives equality of laws; Lévy's
convergence criterion and continuous mapping give the convergence equivalence.
No moments, nondegeneracy, or positive dimension are assumed.
-/

open MeasureTheory Filter Topology

namespace ProbabilityFoundations.Ch07

/-- The characteristic function at t is read from its real projection at 1. -/
theorem characteristicFunction_eq_projection {d : ℕ}
    (μ : Measure (Euclidean d)) (t : Euclidean d) :
    characteristicFunction μ t =
      charFun (Measure.map (fun x => inner ℝ t x) μ) (1 : ℝ) := by
  simpa only [characteristicFunction, Measure.map_id, id_eq, real_inner_comm t] using
    (charFun_map_eq_charFun_map_inner_one (μ := μ) (Y := id)
      measurable_id.aemeasurable t)

/-- Borel probability laws agree if every real linear image law agrees. -/
theorem measure_eq_of_linear_projections_eq {d : ℕ}
    (μ ν : Measure (Euclidean d))
    (hμ : IsProbabilityMeasure μ) (hν : IsProbabilityMeasure ν)
    (h : ∀ t : Euclidean d,
      Measure.map (fun x => inner ℝ t x) μ =
        Measure.map (fun x => inner ℝ t x) ν) :
    μ = ν := by
  apply measure_eq_of_characteristicFunction_eq μ ν hμ hν
  intro t
  rw [characteristicFunction_eq_projection, characteristicFunction_eq_projection, h t]

/-- Cramér–Wold for sequences and a specified target probability law. -/
theorem weaklyConverges_iff_linear_projections {d : ℕ}
    (μs : ℕ → ProbabilityMeasure (Euclidean d))
    (μ : ProbabilityMeasure (Euclidean d)) :
    Ch06.WeaklyConverges atTop μs μ ↔
      ∀ t : Euclidean d,
        Ch06.WeaklyConverges atTop
          (fun n => (μs n).map (fun x => inner ℝ t x))
          (μ.map (fun x => inner ℝ t x)) := by
  constructor
  · intro h t
    exact Ch06.weaklyConverges_map atTop μs μ
      (fun x => inner ℝ t x) (by fun_prop) h
  · intro h
    apply ProbabilityMeasure.tendsto_of_tendsto_charFun
    intro t
    have ht := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp (h t) (1 : ℝ)
    simpa only [ProbabilityMeasure.toMeasure_map, ← characteristicFunction_eq_projection,
      characteristicFunction] using ht

end ProbabilityFoundations.Ch07
