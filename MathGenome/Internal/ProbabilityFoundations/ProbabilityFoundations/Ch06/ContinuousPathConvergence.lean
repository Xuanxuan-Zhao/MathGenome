import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.ProkhorovReverse
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch05.ContinuousProcessLaw
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.ContinuousPathConvergence

/-! Finite-dimensional convergence and tightness on continuous path space.
The proof first works for an arbitrary separable metric state space,
then specializes to the manuscript's Euclidean spaces in all finite dimensions. -/

open MeasureTheory Filter Topology Set TopologicalSpace

namespace ProbabilityFoundations.Ch06

noncomputable section

section GeneralState

variable {S : Type*} [MetricSpace S] [Nonempty S] [SeparableSpace S]
  [MeasurableSpace S] [BorelSpace S]
  {T : ℝ} {D : Set (Ch05.Time T)}

omit [Nonempty S] [SeparableSpace S] [MeasurableSpace S] [BorelSpace S] in
private theorem finite_evaluation_continuous (I : Finset D) :
    Continuous (fun f : C(Ch05.Time T, S) => fun i : I => f i.1.1) :=
  continuous_pi fun i => continuous_eval_const i.1.1

/-- Dense finite-dimensional marginals determine a probability law. -/
theorem path_probability_eq_of_marginals (hT : 0 < T) (hDc : D.Countable) (hDd : Dense D)
    (μ ν : ProbabilityMeasure C(Ch05.Time T, S))
    (h : ∀ I : Finset D,
      μ.map (fun f => fun i : I => f i.1.1) = ν.map (fun f => fun i : I => f i.1.1)) :
    μ = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Ch05.continuousPathMeasure_unique T hT D hDc hDd
  intro I
  exact congrArg ProbabilityMeasure.toMeasure (h I)

omit [Nonempty S] in
/-- Any subsequential weak limit realizes all the specified limiting marginals. -/
private theorem path_limit_marginals
    (μ : ℕ → ProbabilityMeasure C(Ch05.Time T, S))
    (ν : (I : Finset D) → ProbabilityMeasure (I → S))
    (hν : ∀ I : Finset D, Tendsto (fun n => (μ n).map (fun f => fun i : I => f i.1.1))
      atTop (𝓝 (ν I)))
    {η : ProbabilityMeasure C(Ch05.Time T, S)} {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) (hη : Tendsto (μ ∘ φ) atTop (𝓝 η)) :
    ∀ I : Finset D, η.map (fun f => fun i : I => f i.1.1) = ν I := by
  intro I
  exact tendsto_nhds_unique
    (weaklyConverges_map atTop (μ ∘ φ) η _ (finite_evaluation_continuous I) hη)
    ((hν I).comp hφ)

/-- Tightness plus convergent dense finite marginals constructs the path law. -/
theorem path_limit_exists_of_tight_marginals
    (hT : 0 < T) (hDc : D.Countable) (hDd : Dense D)
    (μ : ℕ → ProbabilityMeasure C(Ch05.Time T, S))
    (ht : UniformlyTight (range μ))
    (ν : (I : Finset D) → ProbabilityMeasure (I → S))
    (hν : ∀ I : Finset D, Tendsto (fun n => (μ n).map (fun f => fun i : I => f i.1.1))
      atTop (𝓝 (ν I))) :
    ∃ η : ProbabilityMeasure C(Ch05.Time T, S),
      (∀ I : Finset D, η.map (fun f => fun i : I => f i.1.1) = ν I) ∧
      Tendsto μ atTop (𝓝 η) ∧
      ∀ ρ : ProbabilityMeasure C(Ch05.Time T, S),
        (∀ I : Finset D, ρ.map (fun f => fun i : I => f i.1.1) = ν I) → ρ = η := by
  obtain ⟨η, φ, hφ, hη⟩ := prokhorov_subsequence (range μ) ht μ (mem_range_self)
  have hm := path_limit_marginals μ ν hν hφ.tendsto_atTop hη
  have huniq (ρ : ProbabilityMeasure C(Ch05.Time T, S))
      (hρ : ∀ I : Finset D, ρ.map (fun f => fun i : I => f i.1.1) = ν I) : ρ = η :=
    path_probability_eq_of_marginals hT hDc hDd ρ η (fun I => (hρ I).trans (hm I).symm)
  refine ⟨η, hm, ?_, huniq⟩
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ρ, ms, hms, hρ⟩ := prokhorov_subsequence (range μ) ht (μ ∘ ns)
    (fun n => mem_range_self (ns n))
  have hρm := path_limit_marginals μ ν hν (hns.comp hms.tendsto_atTop) hρ
  rw [huniq ρ hρm] at hρ
  exact ⟨ms, hρ⟩

omit [Nonempty S] in
/-- Weak convergence gives uniform tightness of the entire sequence of laws. -/
theorem uniformlyTight_range_of_converges [CompleteSpace S]
    (μ : ℕ → ProbabilityMeasure S) (η : ProbabilityMeasure S)
    (h : Tendsto μ atTop (𝓝 η)) : UniformlyTight (range μ) := by
  apply prokhorov_reverse_compact_closure
  exact h.isCompact_insert_range.of_isClosed_subset isClosed_closure
    (closure_minimal (subset_insert η (range μ)) h.isCompact_insert_range.isClosed)

end GeneralState

/-- The first assertion of paper.tex, Theorem `thm:p06-path-weak`. -/
theorem continuousPath_limit_exists : PathWeakSpec.existenceType := by
  intro T hT d D hDc hDd μ ht ν hν
  exact path_limit_exists_of_tight_marginals hT hDc hDd μ ht ν hν

/-- The criterion for a given limiting path law. -/
theorem continuousPath_weak_iff : PathWeakSpec.convergenceIffType := by
  intro T hT d D hDc hDd μ η
  constructor
  · intro h
    refine ⟨uniformlyTight_range_of_converges μ η h, fun I => ?_⟩
    exact weaklyConverges_map atTop μ η _ (finite_evaluation_continuous I) h
  · rintro ⟨ht, hm⟩
    obtain ⟨ρ, hρ, hconv, huniq⟩ :=
      path_limit_exists_of_tight_marginals hT hDc hDd μ ht
        (fun I => η.map (PathWeakSpec.finiteEval I)) hm
    rw [← huniq η (fun _ => rfl)] at hconv
    exact hconv

end
end ProbabilityFoundations.Ch06
