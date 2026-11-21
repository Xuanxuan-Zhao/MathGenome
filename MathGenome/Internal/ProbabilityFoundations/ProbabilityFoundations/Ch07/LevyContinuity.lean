import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch07.CharacteristicUniqueness
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.WeakFramework
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.LevyConvergence
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.LevyContinuity

/-!
Lévy's continuity theorem (paper.tex:2533–2560). Tightness is deduced from
continuity at zero of the pointwise limit. A weak subsequential limit provides
the previously unspecified law, so no existence assertion is assumed.
-/

open MeasureTheory Filter Topology

namespace ProbabilityFoundations.Ch07

/-- Weak convergence implies pointwise convergence of characteristic functions. -/
theorem characteristicFunction_tendsto_of_weaklyConverges {d : ℕ}
    (μs : ℕ → ProbabilityMeasure (Euclidean d)) (μ : ProbabilityMeasure (Euclidean d))
    (h : Ch06.WeaklyConverges atTop μs μ) (t : Euclidean d) :
    Tendsto (fun n => characteristicFunction (μs n) t) atTop
      (𝓝 (characteristicFunction μ t)) := by
  exact ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp h t

/-- A pointwise limiting transform continuous at zero determines a unique
probability law, and the original sequence converges weakly to that law. -/
theorem levy_continuity {d : ℕ} (μs : ℕ → ProbabilityMeasure (Euclidean d))
    (φ : Euclidean d → ℂ)
    (hlim : ∀ t, Tendsto (fun n => characteristicFunction (μs n) t) atTop (𝓝 (φ t)))
    (hcont : ContinuousAt φ 0) :
    ∃ μ : ProbabilityMeasure (Euclidean d),
      (∀ t, characteristicFunction μ t = φ t) ∧
      Ch06.WeaklyConverges atTop μs μ ∧
      ∀ ν : ProbabilityMeasure (Euclidean d),
        (∀ t, characteristicFunction ν t = φ t) → ν = μ := by
  have htight : IsTightMeasureSet (Set.range (fun n => (μs n : Measure (Euclidean d)))) :=
    isTightMeasureSet_of_tendsto_charFun hcont hlim
  have hc : IsCompact (closure (Set.range μs)) :=
    isCompact_closure_of_isTightMeasureSet (by
      convert htight using 1
      ext m
      constructor
      · rintro ⟨ν, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, rfl⟩
      · rintro ⟨n, rfl⟩
        exact ⟨μs n, ⟨n, rfl⟩, rfl⟩)
  obtain ⟨μ, _, ψ, hψ, hsub⟩ := hc.isSeqCompact
    (fun n => subset_closure (Set.mem_range_self n))
  have hφ : ∀ t, characteristicFunction μ t = φ t := by
    intro t
    exact tendsto_nhds_unique
      (characteristicFunction_tendsto_of_weaklyConverges (μs ∘ ψ) μ hsub t)
      ((hlim t).comp hψ.tendsto_atTop)
  refine ⟨μ, hφ, ?_, ?_⟩
  · exact ProbabilityMeasure.tendsto_of_tendsto_charFun (by
      intro t
      simpa only [← hφ t, characteristicFunction] using hlim t)
  · intro ν hν
    apply ProbabilityMeasure.toMeasure_injective
    exact measure_eq_of_characteristicFunction_eq ν μ inferInstance inferInstance
      (fun t => (hν t).trans (hφ t).symm)

end ProbabilityFoundations.Ch07
