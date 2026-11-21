import MathGenome.Internal.RealAnalysis.D11.Ch19.PositiveContentRadon
import MathGenome.Internal.RealAnalysis.D11.Ch06.ScalarIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.PositiveContentIntegral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Set MeasureTheory
open scoped ENNReal

namespace D11.Ch19.PositiveContentIntegral
universe u
open D11.Ch19.PositiveContentOuterMeasure

abbrev levelSet := @Specs.D11.Ch19.PositiveContentIntegral.levelSet
noncomputable abbrev lowerSum := @Specs.D11.Ch19.PositiveContentIntegral.lowerSum
noncomputable abbrev upperSum := @Specs.D11.Ch19.PositiveContentIntegral.upperSum

variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
variable (I : CompactlySupportedContinuousMap X ℝ →ₗ[ℝ] ℝ)
variable (hI : ∀ f, (∀ x, 0 ≤ f x) → 0 ≤ I f)


/-- The compact-finiteness field proved for the preceding constructed measure. -/
private instance constructed_finiteOnCompacts :
    @IsFiniteMeasureOnCompacts X (borel X) _ (borelMeasure I hI) :=
  ⟨fun K hK => (D11.Ch19.PositiveContentOuterMeasure.radon I hI).1 K hK⟩

/-- Compact support supplies finite absolute integrability on the original Borel domain. -/
theorem scalar_integrable {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (f : CompactlySupportedContinuousMap X 𝕜) :
    letI : MeasurableSpace X := borel X
    D11.Ch06.ScalarIntegral.scalarIntegrable (borelMeasure I hI) f := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  apply (D11.Ch06.ScalarIntegral.scalarIntegrable_iff _ _).mpr
  exact ⟨f.continuous.measurable, f.integrable⟩

/-- The native Riesz integral identity applies to the already identified constructed measure. -/
theorem integral_eq (f : CompactlySupportedContinuousMap X ℝ) :
    letI : MeasurableSpace X := borel X
    ∃ hf : D11.Ch06.ScalarIntegral.scalarIntegrable (borelMeasure I hI) f,
      I f = D11.Ch06.ScalarIntegral.scalarIntegral (borelMeasure I hI) f hf := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  refine ⟨scalar_integrable I hI f, ?_⟩
  exact (RealRMK.integral_rieszMeasure (positiveFunctional I hI) f).symm

/-- Scalar lower rectangular sums never exceed a nonnegative height. -/
private lemma lower_step_le (a : ℝ) (ha : 0 ≤ a) (η : ℝ) (hη : 0 ≤ η) (N : ℕ) :
    η * (∑ j ∈ Finset.range N, if (j + 1 : ℕ) * η ≤ a then (1 : ℝ) else 0) ≤ a := by
  induction N with
  | zero => simpa using ha
  | succ n ih =>
    rw [Finset.sum_range_succ]
    split_ifs with h
    · have hc : (∑ j ∈ Finset.range n,
          if (j + 1 : ℕ) * η ≤ a then (1 : ℝ) else 0) ≤ n := by
        calc
          _ ≤ ∑ _j ∈ Finset.range n, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro j hj
            split_ifs <;> norm_num
          _ = _ := by simp
      have hm := mul_le_mul_of_nonneg_left hc hη
      push_cast at h
      nlinarith
    · simpa using ih

/-- Scalar upper rectangular sums dominate any height below Nη. -/
private lemma le_upper_step (a : ℝ) (η : ℝ) (hη : 0 ≤ η) (N : ℕ)
    (ha : a ≤ (N : ℝ) * η) :
    a ≤ η * (∑ j ∈ Finset.range N, if (j : ℝ) * η ≤ a then (1 : ℝ) else 0) := by
  induction N with
  | zero => simpa using ha
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases h : a ≤ (n : ℝ) * η
    · have hh := ih h
      have hz : (0 : ℝ) ≤ if (n : ℝ) * η ≤ a then (1 : ℝ) else 0 := by positivity
      nlinarith
    · have hn : (n : ℝ) * η ≤ a := le_of_lt (lt_of_not_ge h)
      have hall : (∑ j ∈ Finset.range n,
          if (j : ℝ) * η ≤ a then (1 : ℝ) else 0) = n := by
        have heq : ∀ j ∈ Finset.range n, (j : ℝ) * η ≤ a := by
          intro j hj
          have hjn : (j : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hj).le
          exact (mul_le_mul_of_nonneg_right hjn hη).trans hn
        simp only [Finset.sum_congr rfl (fun j hj => ite_eq_left (heq j hj)), Finset.sum_const,
          Finset.card_range, nsmul_eq_mul, mul_one]
      rw [hall, ite_eq_left hn]
      simpa [Nat.cast_add, Nat.cast_one, add_mul, mul_comm] using ha

/-- Every strictly positive closed level lies in the closed support. -/
lemma levelSet_subset_support (f : CompactlySupportedContinuousMap X ℝ)
    (η : ℝ) (hη : 0 < η) (j : ℕ) : levelSet f η j ⊆ tsupport f := by
  cases j with
  | zero => exact Subset.rfl
  | succ j =>
    intro x hx
    apply subset_closure
    change f x ≠ 0
    have ht : (0 : ℝ) < (j + 1 : ℕ) * η := mul_pos (by positivity) hη
    exact ne_of_gt (ht.trans_le hx)

lemma levelSet_isCompact (f : CompactlySupportedContinuousMap X ℝ)
    (η : ℝ) (hη : 0 < η) (j : ℕ) : IsCompact (levelSet f η j) := by
  cases j with
  | zero => exact f.hasCompactSupport
  | succ j =>
    exact f.hasCompactSupport.of_isClosed_subset
      (isClosed_le continuous_const f.continuous)
      (levelSet_subset_support f η hη (j + 1))

/-- Pointwise lower steps, including points outside the closed support. -/
private lemma lower_indicator_le (f : CompactlySupportedContinuousMap X ℝ)
    (hf : ∀ x, 0 ≤ f x) (η : ℝ) (hη : 0 < η) (N : ℕ) (x : X) :
    η * (∑ j ∈ Finset.range N, (levelSet f η (j + 1)).indicator (fun _ => (1 : ℝ)) x)
      ≤ f x := by
  classical
  simpa only [levelSet, Specs.D11.Ch19.PositiveContentIntegral.levelSet,
    Set.indicator_apply, Set.mem_ofPred_eq] using lower_step_le (f x) (hf x) η hη.le N

/-- Pointwise upper steps. The zero level is the support, so there is no
constant function on an infinite-mass ambient space in this comparison. -/
private lemma le_upper_indicator (f : CompactlySupportedContinuousMap X ℝ)
    (hf : ∀ x, 0 ≤ f x) (η : ℝ) (hη : 0 < η) (N : ℕ) (hN : ‖f.toBoundedContinuousFunction‖ ≤ (N : ℝ) * η)
    (x : X) :
    f x ≤ η * (∑ j ∈ Finset.range N,
      (levelSet f η j).indicator (fun _ => (1 : ℝ)) x) := by
  classical
  by_cases hx : x ∈ tsupport f
  · change x ∈ closure {x | f x ≠ 0} at hx
    have hb : f x ≤ (N : ℝ) * η :=
      (le_abs_self _).trans ((f.toBoundedContinuousFunction.norm_coe_le_norm x).trans hN)
    have heq : ∀ j, (levelSet f η j).indicator (fun _ => (1 : ℝ)) x =
        if (j : ℝ) * η ≤ f x then 1 else 0 := by
      intro j
      cases j with
      | zero =>
        simp [levelSet, Specs.D11.Ch19.PositiveContentIntegral.levelSet, hx, hf x]
      | succ j => rfl
    simp_rw [heq]
    exact le_upper_step (f x) η hη.le N hb
  · have hz : f x = 0 := image_eq_zero_of_notMem_tsupport hx
    have he : ∀ j, x ∉ levelSet f η j := fun j hj =>
      hx (levelSet_subset_support f η hη j hj)
    simp [hz, Set.indicator_of_notMem, he]

/-- The difference between adjacent finite sums telescopes, also at N = 0. -/
private lemma adjacent_sum_gap (g : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N, g j) - (∑ j ∈ Finset.range N, g (j + 1)) = g 0 - g N := by
  induction N with
  | zero => simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    linarith

/-- Both the given functional and its constructed integral have the exact
lower and upper level bounds and the stated finite error. -/
theorem level_sums (f : CompactlySupportedContinuousMap X ℝ) (hf : ∀ x, 0 ≤ f x)
    (η : ℝ) (hη : 0 < η) (N : ℕ)
    (hN : ‖f.toBoundedContinuousFunction‖ ≤ (N : ℝ) * η) :
    letI : MeasurableSpace X := borel X
    (∀ j, IsCompact (levelSet f η j)) ∧
    (∀ j, borelMeasure I hI (levelSet f η j) < ∞) ∧
    lowerSum I hI f η N ≤ I f ∧ I f ≤ upperSum I hI f η N ∧
    lowerSum I hI f η N ≤ ∫ x, f x ∂(borelMeasure I hI) ∧
    (∫ x, f x ∂(borelMeasure I hI)) ≤ upperSum I hI f η N ∧
    0 ≤ upperSum I hI f η N - lowerSum I hI f η N ∧
    upperSum I hI f η N - lowerSum I hI f η N ≤
      η * (borelMeasure I hI).real (closure {x | f x ≠ 0}) := by
  classical
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  let μ := borelMeasure I hI
  have hc (j : ℕ) : IsCompact (levelSet f η j) := levelSet_isCompact f η hη j
  have hm (j : ℕ) : MeasurableSet (levelSet f η j) := (hc j).measurableSet
  have hfin (j : ℕ) : μ (levelSet f η j) < ∞ := (hc j).measure_lt_top
  let q (j : ℕ) : X → ℝ := (levelSet f η j).indicator (fun _ => 1)
  have hq (j : ℕ) : Integrable (q j) μ :=
    (integrable_indicator_iff (hm j)).mpr (integrableOn_const (hfin j).ne)
  have hqint (j : ℕ) : (∫ x, q j x ∂μ) = μ.real (levelSet f η j) := by
    exact integral_indicator_one (hm j)
  have hfi : Integrable f μ := f.integrable
  have hlint : (∫ x, η * (∑ j ∈ Finset.range N, q (j + 1) x) ∂μ) =
      lowerSum I hI f η N := by
    rw [integral_const_mul, integral_finsetSum _ (fun j _ => hq (j + 1))]
    simp_rw [hqint]
    rfl
  have huint : (∫ x, η * (∑ j ∈ Finset.range N, q j x) ∂μ) =
      upperSum I hI f η N := by
    rw [integral_const_mul, integral_finsetSum _ (fun j _ => hq j)]
    simp_rw [hqint]
    rfl
  have hli : Integrable (fun x => η * (∑ j ∈ Finset.range N, q (j + 1) x)) μ :=
    (integrable_finsetSum _ (fun j _ => hq (j + 1))).const_mul η
  have hui : Integrable (fun x => η * (∑ j ∈ Finset.range N, q j x)) μ :=
    (integrable_finsetSum _ (fun j _ => hq j)).const_mul η
  have hl : lowerSum I hI f η N ≤ ∫ x, f x ∂μ := by
    rw [← hlint]
    exact integral_mono hli hfi (lower_indicator_le f hf η hη N)
  have hu : (∫ x, f x ∂μ) ≤ upperSum I hI f η N := by
    rw [← huint]
    exact integral_mono hfi hui (le_upper_indicator f hf η hη N hN)
  have heq : (∫ x, f x ∂μ) = I f :=
    RealRMK.integral_rieszMeasure (positiveFunctional I hI) f
  have hgap : upperSum I hI f η N - lowerSum I hI f η N ≤
      η * μ.real (closure {x | f x ≠ 0}) := by
    change η * (∑ j ∈ Finset.range N, μ.real (levelSet f η j)) -
      η * (∑ j ∈ Finset.range N, μ.real (levelSet f η (j + 1))) ≤ _
    rw [← mul_sub, adjacent_sum_gap]
    have hz : 0 ≤ μ.real (levelSet f η N) := measureReal_nonneg
    have hs : μ.real (levelSet f η 0) = μ.real (closure {x | f x ≠ 0}) := rfl
    rw [hs]
    exact mul_le_mul_of_nonneg_left (sub_le_self _ hz) hη.le
  exact ⟨hc, hfin, heq ▸ hl, heq ▸ hu, hl, hu, sub_nonneg.mpr (hl.trans hu), hgap⟩

/-- The positive and negative parts remain in Cc and are separately absolutely
integrable, so subtraction recovers the integral of every real f. -/
theorem real_parts (f : CompactlySupportedContinuousMap X ℝ) :
    letI : MeasurableSpace X := borel X
    let p := f ⊔ 0
    let n := (-f) ⊔ 0
    (∀ x, p x = max (f x) 0 ∧ n x = max (-f x) 0) ∧
    f = p - n ∧
    D11.Ch06.ScalarIntegral.scalarIntegrable (borelMeasure I hI) p ∧
    D11.Ch06.ScalarIntegral.scalarIntegrable (borelMeasure I hI) n ∧
    I f = I p - I n ∧
    (∫ x, f x ∂(borelMeasure I hI)) =
      (∫ x, p x ∂(borelMeasure I hI)) - ∫ x, n x ∂(borelMeasure I hI) := by
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  let p := f ⊔ 0
  let n := (-f) ⊔ 0
  have hsplit : f = p - n := by
    ext x
    change f x = max (f x) 0 - max (-f x) 0
    by_cases hx : 0 ≤ f x
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
    · rw [max_eq_right (le_of_not_ge hx), max_eq_left (neg_nonneg.mpr (le_of_not_ge hx))]
      simp
  refine ⟨fun x => ⟨rfl, rfl⟩, hsplit,
    scalar_integrable I hI p, scalar_integrable I hI n, ?_, ?_⟩
  · conv_lhs => rw [hsplit, map_sub]
  · have hi := integral_sub (p.integrable (μ := borelMeasure I hI))
        (n.integrable (μ := borelMeasure I hI))
    simpa only [← CompactlySupportedContinuousMap.sub_apply, ← hsplit] using hi

end D11.Ch19.PositiveContentIntegral
