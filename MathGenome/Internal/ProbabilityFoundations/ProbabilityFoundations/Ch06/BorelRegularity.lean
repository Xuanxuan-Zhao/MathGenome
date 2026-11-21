import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.WeakFramework
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.BorelRegularity

/-!
# Finite Borel regularity and determination by continuous tests

Proposition 6.1, paper.tex lines 1437–1462. Mathlib's weak regularity of
finite Borel measures on metrizable spaces supplies closed and open
approximations. Its determination theorem uses bounded continuous
approximations to closed-set indicators and finite-measure convergence.
These results require neither separability nor completeness.
-/

open Set MeasureTheory BoundedContinuousFunction

namespace ProbabilityFoundations.Ch06

universe u

/-- A finite Borel measure on any metric space admits simultaneous closed/open
approximation with arbitrarily small measure of the gap. -/
theorem closed_open_approximation {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ : Measure S) [IsFiniteMeasure μ]
    (A : Set S) (hA : MeasurableSet A) (ε : ℝ) (hε : 0 < ε) :
    ∃ F G : Set S, IsClosed F ∧ IsOpen G ∧ F ⊆ A ∧ A ⊆ G ∧
      μ (G \ F) < ENNReal.ofReal ε := by
  have hhalf : 0 < ε / 2 := half_pos hε
  have hδ : ENNReal.ofReal (ε / 2) ≠ 0 := (ENNReal.ofReal_pos.mpr hhalf).ne'
  obtain ⟨F, hFA, hF, hμF⟩ :=
    hA.exists_isClosed_sdiff_lt (measure_ne_top μ A) hδ
  obtain ⟨G, hAG, hG, _, hμG⟩ :=
    hA.exists_isOpen_sdiff_lt (measure_ne_top μ A) hδ
  refine ⟨F, G, hF, hG, hFA, hAG, ?_⟩
  calc
    μ (G \ F) ≤ μ ((G \ A) ∪ (A \ F)) := by
      apply measure_mono
      intro x hx
      by_cases hxA : x ∈ A
      · exact Or.inr ⟨hxA, hx.2⟩
      · exact Or.inl ⟨hx.1, hxA⟩
    _ ≤ μ (G \ A) + μ (A \ F) := measure_union_le _ _
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hμG hμF
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add hhalf.le hhalf.le, add_halves]

/-- Bounded continuous real functions determine Borel probability measures on
an arbitrary metric space. -/
theorem probabilityMeasure_eq_of_integrals {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] (μ ν : ProbabilityMeasure S)
    (h : ∀ f : S →ᵇ ℝ,
      (∫ x, f x ∂(μ : Measure S)) = ∫ x, f x ∂(ν : Measure S)) : μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure h

/-- The weak topology, defined by all bounded continuous real tests, is Hausdorff. -/
theorem weakTopology_hausdorff {S : Type u} [MetricSpace S]
    [MeasurableSpace S] [BorelSpace S] :
    @T2Space (ProbabilityMeasure S) (weakTopology (S := S)) := by
  rw [weakTopology_eq]
  infer_instance

end ProbabilityFoundations.Ch06
