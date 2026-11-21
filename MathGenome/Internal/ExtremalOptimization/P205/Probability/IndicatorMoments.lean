import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.IndicatorMoments
import MathGenome.Internal.ExtremalOptimization.P205.Probability.MomentIdentities
import Mathlib.Tactic.Ring

/-!
# Indicator counts

The probabilistic assertions of paper.tex, Proposition p205:W20 (5.1).
The indicator of a measurable event is in L² on a probability space.
Linearity of integration gives the mean, and bilinearity of covariance
gives the double sum. Symmetry pairs the two strict triangles in any
finite enumeration. All sums allow an empty index type.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace P205.Probability.IndicatorMoments

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem indicator_memLp {A : Set Ω} (hA : MeasurableSet A) :
    MemLp (A.indicator (fun _ ↦ (1 : ℝ))) 2 μ :=
  (memLp_const (1 : ℝ)).indicator hA.nullMeasurableSet

theorem count_memLp {ι : Type*} [Fintype ι] {A : ι → Set Ω}
    (hA : ∀ i, MeasurableSet (A i)) :
    MemLp (fun ω ↦ ∑ i, (A i).indicator (fun _ ↦ (1 : ℝ)) ω) 2 μ := by
  exact memLp_finsetSum _ (fun i _ ↦ indicator_memLp (hA i))

theorem expectation_count {ι : Type*} [Fintype ι] {A : ι → Set Ω}
    (hA : ∀ i, MeasurableSet (A i)) :
    (∫ ω, ∑ i, (A i).indicator (fun _ ↦ (1 : ℝ)) ω ∂μ) = ∑ i, μ.real (A i) := by
  rw [integral_finsetSum _ (fun i _ ↦
    MomentIdentities.first_moment_integrable (indicator_memLp (hA i)))]
  exact Finset.sum_congr rfl (fun i _ ↦ integral_indicator_one (hA i))

theorem covariance_indicator {A B : Set Ω} (hA : MeasurableSet A)
    (hB : MeasurableSet B) :
    covariance (A.indicator (fun _ ↦ (1 : ℝ)))
      (B.indicator (fun _ ↦ (1 : ℝ))) μ = μ.real (A ∩ B) - μ.real A * μ.real B := by
  rw [MomentIdentities.covariance_eq_product_moment (indicator_memLp hA) (indicator_memLp hB)]
  have hprod : (fun ω ↦ A.indicator (fun _ ↦ (1 : ℝ)) ω *
      B.indicator (fun _ ↦ (1 : ℝ)) ω) = (A ∩ B).indicator (fun _ ↦ (1 : ℝ)) := by
    ext ω
    by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;> simp [ha, hb]
  rw [hprod]
  simp only [integral_indicator_const _ hA, integral_indicator_const _ hB,
    integral_indicator_const _ (hA.inter hB), smul_eq_mul, mul_one]

theorem variance_indicator {A : Set Ω} (hA : MeasurableSet A) :
    variance (A.indicator (fun _ ↦ (1 : ℝ))) μ = μ.real A * (1 - μ.real A) := by
  rw [← covariance_self (indicator_memLp hA).aemeasurable, covariance_indicator hA hA]
  simp only [Set.inter_self]
  ring

theorem variance_count_covariance {ι : Type*} [Fintype ι] {A : ι → Set Ω}
    (hA : ∀ i, MeasurableSet (A i)) :
    variance (fun ω ↦ ∑ i, (A i).indicator (fun _ ↦ (1 : ℝ)) ω) μ =
      ∑ i, ∑ j, covariance ((A i).indicator (fun _ ↦ (1 : ℝ)))
        ((A j).indicator (fun _ ↦ (1 : ℝ))) μ :=
  variance_fun_sum (fun i ↦ indicator_memLp (hA i))

/-- A symmetric double sum is its diagonal plus twice its upper triangle. -/
theorem sum_sum_symmetric {ι : Type*} [Fintype ι] [LinearOrder ι]
    (f : ι → ι → ℝ) (hf : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, f i j) = (∑ i, f i i) +
      2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j ↦ i < j), f i j := by
  have hsplit (i j : ι) : f i j = (if i = j then f i i else 0) +
      (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j; simp
    · simp [h, ne_of_gt h, not_lt_of_ge h.le]
  have hswap : (∑ i, ∑ j, if j < i then f i j else 0) =
      ∑ i, ∑ j, if i < j then f i j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hf j i]
  calc
    (∑ i, ∑ j, f i j) = ∑ i, ∑ j,
        ((if i = j then f i i else 0) + (if i < j then f i j else 0) +
          (if j < i then f i j else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl (fun j _ ↦ hsplit i j)
    _ = (∑ i, f i i) + (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if j < i then f i j else 0) := by
      simp [Finset.sum_add_distrib]
    _ = _ := by
      rw [hswap]
      simp only [Finset.sum_filter]
      ring

theorem variance_count_ordered {ι : Type*} [Fintype ι] [LinearOrder ι]
    {A : ι → Set Ω} (hA : ∀ i, MeasurableSet (A i)) :
    variance (fun ω ↦ ∑ i, (A i).indicator (fun _ ↦ (1 : ℝ)) ω) μ =
      (∑ i, μ.real (A i) * (1 - μ.real (A i))) +
        2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j ↦ i < j),
          (μ.real (A i ∩ A j) - μ.real (A i) * μ.real (A j)) := by
  rw [variance_count_covariance hA, sum_sum_symmetric _ (fun _ _ ↦ covariance_comm _ _)]
  simp_rw [covariance_self (indicator_memLp (hA _)).aemeasurable, variance_indicator (hA _),
    covariance_indicator (hA _) (hA _)]

theorem variance_count_enumerated {ι : Type*} [Fintype ι] {A : ι → Set Ω}
    (hA : ∀ i, MeasurableSet (A i)) {n : ℕ} (e : Fin n ≃ ι) :
    variance (fun ω ↦ ∑ i, (A i).indicator (fun _ ↦ (1 : ℝ)) ω) μ =
      (∑ i : Fin n, μ.real (A (e i)) * (1 - μ.real (A (e i)))) +
        2 * ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j ↦ i < j),
          (μ.real (A (e i) ∩ A (e j)) - μ.real (A (e i)) * μ.real (A (e j))) := by
  have hcount : (fun ω ↦ ∑ i, (A i).indicator (fun _ ↦ (1 : ℝ)) ω) =
      (fun ω ↦ ∑ i : Fin n, (A (e i)).indicator (fun _ ↦ (1 : ℝ)) ω) := by
    funext ω
    exact (e.sum_comp (fun i ↦ (A i).indicator (fun _ ↦ (1 : ℝ)) ω)).symm
  rw [hcount]
  exact variance_count_ordered (fun i ↦ hA (e i))

theorem independent_covariance {A B : Set Ω} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : IndepSet A B μ) :
    covariance (A.indicator (fun _ ↦ (1 : ℝ)))
      (B.indicator (fun _ ↦ (1 : ℝ))) μ = 0 := by
  rw [covariance_indicator hA hB]
  have hreal : μ.real (A ∩ B) = μ.real A * μ.real B := by
    simpa only [measureReal_def, ENNReal.toReal_mul] using
      congrArg ENNReal.toReal hAB.measure_inter_eq_mul
  rw [hreal, sub_self]

end P205.Probability.IndicatorMoments
