import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.FiniteModels

open MeasureTheory
open scoped BigOperators Classical

namespace P205.Probability.FiniteModel

variable {Ω : Type*} [Fintype Ω]

def fromWeights (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (hs : ∑ ω, p ω = 1) :
    FiniteModel Ω := ⟨p, hp, hs⟩

noncomputable def product {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, Fintype (X i)] (M : ∀ i, FiniteModel (X i)) : FiniteModel (∀ i, X i) := pi M

theorem support_nonempty (M : FiniteModel Ω) : M.positiveSupport.Nonempty := by
  classical
  by_contra h
  have hz : ∀ ω, M.weight ω = 0 := by
    intro ω
    have hn : ¬ 0 < M.weight ω := fun hp => h ⟨ω, hp⟩
    exact le_antisymm (le_of_not_gt hn) (M.weight_nonneg ω)
  have := M.weight_sum
  simp only [hz, Finset.sum_const_zero] at this
  exact zero_ne_one this

theorem eventMass_eq_sum (M : FiniteModel Ω) (A : Set Ω) :
    M.eventMass A = ∑ ω ∈ A.toFinset, M.weight ω := by
  classical
  rw [show A.toFinset = Finset.univ.filter (fun ω => ω ∈ A) by
    ext ω
    simp]
  simp only [eventMass, Finset.sum_filter, Set.indicator]

theorem expectation_indicator (M : FiniteModel Ω) (A : Set Ω) :
    M.expectation (A.indicator (fun _ => (1 : ℝ))) = M.eventMass A := by
  classical
  unfold expectation eventMass
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : ω ∈ A <;> simp [h]

theorem expectation_linear (M : FiniteModel Ω) (a b : ℝ) (Z W : Ω → ℝ) :
    M.expectation (fun ω => a * Z ω + b * W ω) =
      a * M.expectation Z + b * M.expectation W := by
  simp only [expectation, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

theorem expectation_sum {ι : Type*} (s : Finset ι) (M : FiniteModel Ω) (Z : ι → Ω → ℝ) :
    M.expectation (fun ω => ∑ i ∈ s, Z i ω) = ∑ i ∈ s, M.expectation (Z i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem eventMass_nonneg (M : FiniteModel Ω) (A : Set Ω) : 0 ≤ M.eventMass A :=
  Finset.sum_nonneg (fun ω _ => Set.indicator_nonneg (fun ω _ => M.weight_nonneg ω) ω)

instance instIsProbabilityMeasure [MeasurableSpace Ω] (M : FiniteModel Ω) :
    IsProbabilityMeasure M.measure :=
  inferInstanceAs (IsProbabilityMeasure M.pmf.toMeasure)

section Measure
variable [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

theorem all_measurable (A : Set Ω) : MeasurableSet A := A.toFinite.measurableSet

theorem measure_eventMass (M : FiniteModel Ω) (A : Set Ω) :
    M.measure A = ENNReal.ofReal (M.eventMass A) := by
  classical
  rw [measure, PMF.toMeasure_apply_fintype]
  unfold eventMass
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro ω _
    by_cases h : ω ∈ A <;> simp [h, pmf]
  · intro ω _
    exact Set.indicator_nonneg (fun ω _ => M.weight_nonneg ω) ω

theorem measureReal_eventMass (M : FiniteModel Ω) (A : Set Ω) :
    (M.measure A).toReal = M.eventMass A := by
  rw [measure_eventMass, ENNReal.toReal_ofReal (eventMass_nonneg M A)]

theorem integral_expectation (M : FiniteModel Ω) (Z : Ω → ℝ) :
    (∫ ω, Z ω ∂M.measure) = M.expectation Z := by
  rw [measure, PMF.integral_eq_sum]
  simp [pmf, ENNReal.toReal_ofReal (M.weight_nonneg _), smul_eq_mul, expectation]

theorem integrable_all (M : FiniteModel Ω) (Z : Ω → ℝ) : Integrable Z M.measure :=
  Integrable.of_finite

end Measure

/-- A realization requiring no pre-existing measurable structure on the outcome type. -/
theorem discrete_realization (M : FiniteModel Ω) :
    (∀ A : Set Ω, @MeasurableSet Ω ⊤ A) ∧
    @IsProbabilityMeasure Ω ⊤ M.discreteMeasure ∧
    (∀ A : Set Ω, M.discreteMeasure A = ENNReal.ofReal (M.eventMass A)) ∧
    (∀ Z : Ω → ℝ, (∫ ω, Z ω ∂M.discreteMeasure) = M.expectation Z) := by
  let : MeasurableSpace Ω := ⊤
  exact ⟨fun _ => trivial, inferInstanceAs (IsProbabilityMeasure M.measure),
    measure_eventMass M, integral_expectation M⟩

section Product
variable {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, Fintype (X i)]

theorem product_weight (M : ∀ i, FiniteModel (X i)) (ω : ∀ i, X i) :
    (pi M).weight ω = ∏ i, (M i).weight (ω i) := rfl

variable [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]

theorem measure_pi (M : ∀ i, FiniteModel (X i)) :
    (pi M).measure = Measure.pi (fun i => (M i).measure) := by
  classical
  apply Measure.ext_of_singleton
  intro ω
  rw [Measure.pi_singleton]
  simp only [measure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    pmf, PMF.ofFintype_apply, pi]
  exact ENNReal.ofReal_prod_of_nonneg (fun i _ => (M i).weight_nonneg (ω i))

theorem independent_coordinates (M : ∀ i, FiniteModel (X i)) :
    ProbabilityTheory.iIndepFun (fun i (ω : ∀ i, X i) => ω i) (pi M).measure := by
  rw [measure_pi]
  exact ProbabilityTheory.iIndepFun_pi (fun _ => aemeasurable_id)

theorem coordinate_marginal (M : ∀ i, FiniteModel (X i)) (i : ι) :
    (pi M).measure.map (fun ω => ω i) = (M i).measure := by
  rw [measure_pi]
  exact (measurePreserving_eval (fun i => (M i).measure) i).map_eq

omit [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)] in
theorem coordinate_eventMass (M : ∀ i, FiniteModel (X i)) (i : ι) (A : Set (X i)) :
    (pi M).eventMass {ω | ω i ∈ A} = (M i).eventMass A := by
  let : ∀ i, MeasurableSpace (X i) := fun _ => ⊤
  rw [← measureReal_eventMass, ← measureReal_eventMass, ← coordinate_marginal M i]
  rw [Measure.map_apply (measurable_pi_apply i) (all_measurable A)]
  rfl

end Product
end P205.Probability.FiniteModel
