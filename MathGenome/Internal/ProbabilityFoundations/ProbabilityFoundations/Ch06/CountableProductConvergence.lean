import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch06.FiniteProductConvergence
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch05.IndependentProduct
import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch06.CountableProductConvergence

/-! Countable products, paper.tex 2002–2032. We use continuity cylinders and
Portmanteau. This proves the result directly in the product topology, without
requiring a choice of product metric or complete factor spaces. -/

open MeasureTheory Filter Topology TopologicalSpace Set Metric

namespace ProbabilityFoundations.Ch06

universe u v
noncomputable section

def countableProductLaw {I : Type u} {S : I → Type v}
    [∀ i, MeasurableSpace (S i)] (μ : ∀ i, ProbabilityMeasure (S i)) :
    ProbabilityMeasure (∀ i, S i) :=
  ⟨Measure.infinitePi (fun i => (μ i : Measure (S i))), inferInstance⟩

variable {I : Type u} [Countable I] {S : I → Type v}
  [∀ i, MetricSpace (S i)] [∀ i, MeasurableSpace (S i)]
  [∀ i, BorelSpace (S i)] [∀ i, SeparableSpace (S i)]

theorem countableProduct_topology_measurability (S : I → Type v)
    [∀ i, MetricSpace (S i)] [∀ i, MeasurableSpace (S i)]
    [∀ i, BorelSpace (S i)] [∀ i, SeparableSpace (S i)] :
    MetrizableSpace (∀ i, S i) ∧ SeparableSpace (∀ i, S i) ∧
      borel (∀ i, S i) = Ch05.CylinderFramework.cylinderSigma S := by
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [Ch05.CylinderFramework.cylinderSigma_eq_pi]
  exact BorelSpace.measurable_eq.symm

private theorem map_restrict_eval (ν : ProbabilityMeasure (∀ i, S i))
    (F : Finset I) (i : F) :
    (ν.map F.restrict).map (Function.eval i) = ν.map (Function.eval i.val) := by
  apply Subtype.ext
  exact Measure.map_map (measurable_pi_apply i) F.measurable_restrict

/-- General joint laws need no independence assumption. -/
theorem weaklyConverges_iff_finite_marginals
    (νs : ℕ → ProbabilityMeasure (∀ i, S i)) (ν : ProbabilityMeasure (∀ i, S i)) :
    WeaklyConverges atTop νs ν ↔ ∀ F : Finset I,
      WeaklyConverges atTop (fun n => (νs n).map F.restrict) (ν.map F.restrict) := by
  classical
  constructor
  · intro h F
    exact weaklyConverges_map atTop νs ν F.restrict
      (continuous_pi fun i => continuous_apply i.val) h
  · intro h
    let π : I → Set (Set (∀ i, S i)) := fun i =>
      {B | ∃ A : Set (S i), IsContinuitySet (ν.map (Function.eval i) : Measure _) A ∧
        B = Function.eval i ⁻¹' A}
    have hπ (i : I) : IsPiSystem (π i) := by
      rintro B ⟨A, hA, rfl⟩ B' ⟨A', hA', rfl⟩ _
      exact ⟨A ∩ A', hA.inter hA', rfl⟩
    let C := piiUnionInter π univ
    have hC : IsPiSystem C := isPiSystem_piiUnionInter π hπ univ
    apply hC.tendsto_probabilityMeasure_of_tendsto_of_mem
    · rintro B ⟨F, _, f, hf, rfl⟩
      apply Finset.measurableSet_biInter
      intro i hi
      obtain ⟨A, hA, heq⟩ := hf i hi
      rw [heq]
      exact (measurable_pi_apply i) hA.1
    · intro U hU x hx
      obtain ⟨F, V, hV, hsub⟩ := isOpen_pi_iff.mp hU x hx
      have hex (i : F) : ∃ r > 0,
          IsContinuitySet (ν.map (Function.eval i.val) : Measure _) (ball (x i.val) r) ∧
          ball (x i.val) r ⊆ V i.val := by
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hV i i.prop).1 _ (hV i i.prop).2
        obtain ⟨r, hr, hnull⟩ := exists_continuity_ball_radius
          (ν.map (Function.eval i.val) : Measure _) (x i.val) hε
        exact ⟨r, hr.1, hnull, (ball_subset_ball hr.2.le).trans hball⟩
      choose r hr hnull hrV using hex
      let W : ∀ i, Set (S i) := fun i =>
        if hi : i ∈ F then ball (x i) (r ⟨i, hi⟩) else univ
      refine ⟨(F : Set I).pi W, ?_, ?_, ?_⟩
      · refine ⟨F, subset_univ _, fun i => Function.eval i ⁻¹' W i, ?_, ?_⟩
        · intro i hi
          exact ⟨W i, by simpa only [W, dite_eq_left hi] using hnull ⟨i, hi⟩, rfl⟩
        · exact Set.pi_def _ _
      · apply set_pi_mem_nhds F.finite_toSet
        intro i hi
        simp only [Finset.mem_coe] at hi
        simpa only [W, dite_eq_left hi] using isOpen_ball.mem_nhds (mem_ball_self (hr ⟨i, hi⟩))
      · apply Subset.trans (Set.pi_mono fun i hi => ?_) hsub
        change i ∈ F at hi
        simpa only [W, dite_eq_left hi] using hrV ⟨i, hi⟩
    · rintro B ⟨F, _, f, hf, rfl⟩
      have hex (i : F) : ∃ A : Set (S i.val),
          IsContinuitySet (ν.map (Function.eval i.val) : Measure _) A ∧
          f i.val = Function.eval i.val ⁻¹' A := hf i.val i.prop
      choose A hA heq using hex
      have hAf (i : F) :
          IsContinuitySet ((ν.map F.restrict).map (Function.eval i) : Measure _) (A i) := by
        rw [map_restrict_eval]
        exact hA i
      have hlim := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' (h F)
        (IsContinuitySet.pi_marginals (ν.map F.restrict) A hAf).2
      have hpre : F.restrict ⁻¹' univ.pi A = ⋂ i ∈ F, f i := by
        ext x
        simp only [mem_preimage, Set.mem_pi, mem_univ, forall_const, mem_iInter]
        constructor
        · intro hx i hi
          rw [heq ⟨i, hi⟩]
          exact hx ⟨i, hi⟩
        · intro hx i
          have := hx i.val i.prop
          rwa [heq i] at this
      have hmeas : MeasurableSet (univ.pi A) := MeasurableSet.univ_pi (fun i => (hAf i).1)
      simp only [ProbabilityMeasure.map_apply' _ F.measurable_restrict.aemeasurable hmeas,
        hpre] at hlim
      exact (ENNReal.tendsto_toNNReal (measure_ne_top _ _)).comp hlim

@[simp] theorem countableProductLaw_map_restrict
    (μ : ∀ i, ProbabilityMeasure (S i)) (F : Finset I) :
    (countableProductLaw μ).map F.restrict = ProbabilityMeasure.pi (fun i : F => μ i.val) := by
  apply Subtype.ext
  exact Measure.infinitePi_map_restrict (fun i => (μ i : Measure (S i)))

@[simp] theorem countableProductLaw_map_eval
    (μ : ∀ i, ProbabilityMeasure (S i)) (i : I) :
    (countableProductLaw μ).map (Function.eval i) = μ i := by
  apply Subtype.ext
  exact Measure.infinitePi_map_eval (fun i => (μ i : Measure (S i))) i

theorem weaklyConverges_countableProductLaw_iff
    (μs : ℕ → ∀ i, ProbabilityMeasure (S i)) (μ : ∀ i, ProbabilityMeasure (S i)) :
    WeaklyConverges atTop (fun n => countableProductLaw (μs n)) (countableProductLaw μ) ↔
      ∀ i, WeaklyConverges atTop (fun n => μs n i) (μ i) := by
  constructor
  · intro h i
    simpa only [countableProductLaw_map_eval] using
      weaklyConverges_map atTop _ _ (Function.eval i) (continuous_apply i) h
  · intro h
    apply (weaklyConverges_iff_finite_marginals _ _).mpr
    intro F
    simp only [countableProductLaw_map_restrict]
    exact (weaklyConverges_pi_iff _ _).mpr (fun i => h i.val)

end
end ProbabilityFoundations.Ch06
