import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.Portmanteau
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.ContinuousMapping
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.FiniteProductConvergence

/-! Finite products, paper.tex 1970–2000. All finite index types are allowed,
including the empty index type; there is no completeness assumption. -/

open MeasureTheory Filter Topology TopologicalSpace Set Metric

namespace ProbabilityFoundations.Ch06

universe u v w
noncomputable section

/-- A continuous inverse image preserves the continuity-set property relative
to the pushforward law. -/
theorem IsContinuitySet.preimage_map
    {E : Type u} {F : Type v} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [MetricSpace F] [MeasurableSpace F] [BorelSpace F]
    (μ : ProbabilityMeasure E) {g : E → F} (hg : Continuous g) {A : Set F}
    (hA : IsContinuitySet (μ.map g : Measure F) A) :
    IsContinuitySet (μ : Measure E) (g ⁻¹' A) := by
  refine ⟨hg.measurable hA.1, measure_mono_null (hg.frontier_preimage_subset A) ?_⟩
  rw [← μ.map_apply' hg.measurable.aemeasurable isClosed_frontier.measurableSet]
  exact hA.2

variable {I : Type u} [Fintype I] {S : I → Type v}
  [∀ i, MetricSpace (S i)] [∀ i, MeasurableSpace (S i)]
  [∀ i, BorelSpace (S i)] [∀ i, SeparableSpace (S i)]

/-- A rectangle of marginal continuity sets is a joint continuity set. -/
theorem IsContinuitySet.pi_marginals
    (ν : ProbabilityMeasure (∀ i, S i)) (A : ∀ i, Set (S i))
    (hA : ∀ i, IsContinuitySet (ν.map (Function.eval i) : Measure (S i)) (A i)) :
    IsContinuitySet (ν : Measure (∀ i, S i)) (univ.pi A) := by
  classical
  have hpre (i : I) := IsContinuitySet.preimage_map ν (continuous_apply i) (hA i)
  have hfin (F : Finset I) :
      IsContinuitySet (ν : Measure (∀ i, S i)) (⋂ i ∈ F, Function.eval i ⁻¹' A i) := by
    induction F using Finset.induction with
    | empty => simp [IsContinuitySet]
    | insert i F hi ih =>
      simpa only [Finset.set_biInter_insert] using (hpre i).inter ih
  simpa [Set.pi_def] using hfin Finset.univ

/-- The continuity rectangles of the limiting marginals determine joint weak
convergence on a finite product of separable metric spaces. -/
theorem weaklyConverges_iff_rectangles
    (νs : ℕ → ProbabilityMeasure (∀ i, S i)) (ν : ProbabilityMeasure (∀ i, S i)) :
    WeaklyConverges atTop νs ν ↔
      ∀ A : ∀ i, Set (S i),
        (∀ i, IsContinuitySet (ν.map (Function.eval i) : Measure (S i)) (A i)) →
        Tendsto (fun n => (νs n : Measure (∀ i, S i)) (univ.pi A)) atTop
          (𝓝 ((ν : Measure (∀ i, S i)) (univ.pi A))) := by
  constructor
  · intro h A hA
    exact ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' h
      (IsContinuitySet.pi_marginals ν A hA).2
  · intro h
    let C : Set (Set (∀ i, S i)) := {B | ∃ A : ∀ i, Set (S i),
      B = univ.pi A ∧ ∀ i,
        IsContinuitySet (ν.map (Function.eval i) : Measure (S i)) (A i)}
    have hC : IsPiSystem C := by
      rintro B ⟨A, rfl, hA⟩ B' ⟨A', rfl, hA'⟩ _
      exact ⟨fun i => A i ∩ A' i, pi_inter_distrib.symm, fun i => (hA i).inter (hA' i)⟩
    apply hC.tendsto_probabilityMeasure_of_tendsto_of_mem
    · rintro B ⟨A, rfl, hA⟩
      exact MeasurableSet.univ_pi (fun i => (hA i).1)
    · intro U hU x hx
      obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hU x hx
      have hex (i : I) : ∃ r ∈ Ioo 0 ε,
          IsContinuitySet (ν.map (Function.eval i) : Measure (S i)) (ball (x i) r) :=
        exists_continuity_ball_radius _ (x i) hε
      choose r hr hnull using hex
      refine ⟨univ.pi (fun i => ball (x i) (r i)),
        ⟨fun i => ball (x i) (r i), rfl, hnull⟩, ?_, ?_⟩
      · exact (isOpen_set_pi finite_univ (fun _ _ => isOpen_ball)).mem_nhds
          (by simpa using fun i => (hr i).1)
      · calc
          univ.pi (fun i => ball (x i) (r i)) ⊆ univ.pi (fun i => ball (x i) ε) := by
            intro y hy i hi
            exact ball_subset_ball (hr i).2.le (hy i hi)
          _ ⊆ U := by rwa [← ball_pi _ hε]
    · rintro B ⟨A, rfl, hA⟩
      exact (ENNReal.tendsto_toNNReal (measure_ne_top _ _)).comp (h A hA)

/-- Each marginal of a finite product probability law is its corresponding
factor, also for arbitrary finite dependent families. -/
theorem probabilityMeasure_pi_map_eval (μ : ∀ i, ProbabilityMeasure (S i)) (i : I) :
    (ProbabilityMeasure.pi μ).map (Function.eval i) = μ i := by
  apply Subtype.ext
  exact (measurePreserving_eval (fun i => (μ i : Measure (S i))) i).map_eq

/-- Finite products converge weakly exactly when all their factors do. The
empty product is included, and the coordinate condition is then vacuous. -/
theorem weaklyConverges_pi_iff
    (μs : ℕ → ∀ i, ProbabilityMeasure (S i)) (μ : ∀ i, ProbabilityMeasure (S i)) :
    WeaklyConverges atTop (fun n => ProbabilityMeasure.pi (μs n))
      (ProbabilityMeasure.pi μ) ↔
        ∀ i, WeaklyConverges atTop (fun n => μs n i) (μ i) := by
  constructor
  · intro h i
    simpa only [probabilityMeasure_pi_map_eval] using
      weaklyConverges_map atTop _ _ (Function.eval i) (continuous_apply i) h
  · intro h
    exact ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr h)

end
end ProbabilityFoundations.Ch06
