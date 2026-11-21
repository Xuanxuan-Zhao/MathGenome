import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.Definitions
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
open scoped InnerProductSpace ComplexConjugate
open MeasureTheory Set Filter
open Classical

namespace ExpandedFA.SpectralMeasure
universe u v

abbrev PVM : Spec.PVMType.{u, v} := Spec.PVMValue

variable {S : Type u} {H : Type v} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev coefficient : Spec.CoefficientType (S := S) (H := H) := Spec.CoefficientValue

namespace ProjectionValuedMeasure

variable (E : ProjectionValuedMeasure S H)

@[simp] theorem map_empty : E ∅ = 0 := by
  ext x
  have h := (E.iUnion (fun _ => ∅) (fun _ => MeasurableSet.empty)
    (fun _ _ _ => disjoint_bot_left) x).summable
  exact (summable_const_iff (E ∅ x)).mp h

theorem idempotent (B : Set S) (hB : MeasurableSet B) : E B * E B = E B := by
  simpa using E.inter B B hB hB

theorem inner_left (B : Set S) (hB : MeasurableSet B) (x y : H) :
    ⟪E B x, y⟫_ℂ = ⟪x, E B y⟫_ℂ :=
  (E.selfAdjoint B hB).isSymmetric x y

theorem coefficient_projection (B : Set S) (hB : MeasurableSet B) (x y : H) :
    coefficient E x y B = ⟪E B x, E B y⟫_ℂ := by
  change ⟪x, E B y⟫_ℂ = _
  rw [E.inner_left B hB]
  have h := congrArg (fun T : H →L[ℂ] H => T y) (E.idempotent B hB)
  change E B (E B y) = E B y at h
  rw [h]

theorem norm_apply_le (B : Set S) (hB : MeasurableSet B) (x : H) :
    ‖E B x‖ ≤ ‖x‖ := by
  have h : ‖E B x‖ ^ 2 ≤ ‖x‖ * ‖E B x‖ := by
    calc
      ‖E B x‖ ^ 2 = ‖⟪E B x, E B x⟫_ℂ‖ := by
        rw [← inner_self_re_eq_norm, inner_self_eq_norm_sq]
      _ = ‖⟪x, E B x⟫_ℂ‖ := congrArg norm (E.coefficient_projection B hB x x).symm
      _ ≤ ‖x‖ * ‖E B x‖ := norm_inner_le_norm _ _
  nlinarith [norm_nonneg x, norm_nonneg (E B x)]

theorem norm_le_one (B : Set S) (hB : MeasurableSet B) : ‖E B‖ ≤ 1 := by
  apply (E B).opNorm_le_bound (by norm_num : (0 : ℝ) ≤ 1)
  intro x
  simpa using E.norm_apply_le B hB x

theorem orthogonality (B C : Set S) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBC : Disjoint B C) (x y : H) : ⟪E B x, E C y⟫_ℂ = 0 := by
  rw [E.inner_left B hB]
  have h := congrArg (fun T : H →L[ℂ] H => T y) (E.inter B C hB hC)
  change E B (E C y) = E (B ∩ C) y at h
  rw [h, Set.disjoint_iff_inter_eq_empty.mp hBC, E.map_empty]
  simp

/-- Actual scalar complex measure, not a finitely additive set function.
Nonmeasurable sets are sent to zero as required by Mathlib's convention. -/
def coefficientMeasure (x y : H) : ComplexMeasure S where
  measureOf' B := if MeasurableSet B then coefficient E x y B else 0
  empty' := by simp [coefficient, Spec.CoefficientValue]
  not_measurable' B hB := ite_eq_right hB
  m_iUnion' B hB hdisj := by
    simp only [ite_eq_left (MeasurableSet.iUnion hB)]
    have h := (innerSL ℂ x).hasSum (E.iUnion B hB hdisj y)
    simpa [coefficient, Spec.CoefficientValue, hB] using h

@[simp] theorem coefficientMeasure_apply (x y : H) (B : Set S) (hB : MeasurableSet B) :
    E.coefficientMeasure x y B = coefficient E x y B := by
  simp only [coefficientMeasure, VectorMeasure.coe_mk, ite_eq_left hB]

theorem diagonal_nonneg (x : H) (B : Set S) (hB : MeasurableSet B) :
    0 ≤ (E.coefficientMeasure x x B).re := by
  rw [E.coefficientMeasure_apply x x B hB, E.coefficient_projection B hB]
  exact inner_self_nonneg (𝕜 := ℂ) (x := E B x)

def diagonalMeasure (x : H) : Measure S :=
  (ComplexMeasure.re (E.coefficientMeasure x x)).toMeasureOfZeroLE Set.univ MeasurableSet.univ
    (by
      rw [VectorMeasure.le_restrict_univ_iff_le]
      intro B hB
      exact E.diagonal_nonneg x B hB)

instance diagonalMeasure_finite (x : H) : IsFiniteMeasure (E.diagonalMeasure x) :=
  inferInstanceAs (IsFiniteMeasure ((ComplexMeasure.re (E.coefficientMeasure x x)).toMeasureOfZeroLE
    Set.univ MeasurableSet.univ _))

theorem diagonalMeasure_real_apply (x : H) (B : Set S) (hB : MeasurableSet B) :
    (E.diagonalMeasure x).real B = ‖E B x‖ ^ 2 := by
  rw [diagonalMeasure, SignedMeasure.toMeasureOfZeroLE_real_apply _ _ _ hB, Set.univ_inter]
  change (E.coefficientMeasure x x B).re = _
  rw [E.coefficientMeasure_apply x x B hB, E.coefficient_projection B hB]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

theorem diagonalMeasure_apply (x : H) (B : Set S) (hB : MeasurableSet B) :
    E.diagonalMeasure x B = ENNReal.ofReal (‖E B x‖ ^ 2) := by
  rw [← E.diagonalMeasure_real_apply x B hB, measureReal_def]
  exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm

theorem coefficientMeasure_diagonal (x : H) (B : Set S) (hB : MeasurableSet B) :
    E.coefficientMeasure x x B = ((E.diagonalMeasure x).real B : ℂ) := by
  rw [E.coefficientMeasure_apply x x B hB, E.coefficient_projection B hB,
    E.diagonalMeasure_real_apply x B hB, inner_self_eq_norm_sq_to_K,
    RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow]

@[simp] theorem diagonalMeasure_univ (x : H) :
    E.diagonalMeasure x Set.univ = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [E.diagonalMeasure_apply x Set.univ MeasurableSet.univ, E.univ]
  rfl

/-- Bessel's inequality for any finite disjoint measurable family. -/
theorem sum_norm_sq_le {ι : Type*} (t : Finset ι) (B : ι → Set S)
    (hB : ∀ i ∈ t, MeasurableSet (B i))
    (hd : Set.PairwiseDisjoint (↑t) B) (x : H) :
    ∑ i ∈ t, ‖E (B i) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have h := sum_measureReal_le_measureReal_univ (μ := E.diagonalMeasure x) hB hd
  simpa only [E.diagonalMeasure_real_apply x _ MeasurableSet.univ, E.univ,
    one_apply_eq_self] using
    (calc
      ∑ i ∈ t, ‖E (B i) x‖ ^ 2 = ∑ i ∈ t, (E.diagonalMeasure x).real (B i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (E.diagonalMeasure_real_apply x (B i) (hB i hi)).symm
      _ ≤ (E.diagonalMeasure x).real Set.univ := h)

/-- The finite-partition Schwarz estimate needed for total variation. -/
theorem sum_coefficient_norm_le {ι : Type*} (t : Finset ι) (B : ι → Set S)
    (hB : ∀ i ∈ t, MeasurableSet (B i))
    (hd : Set.PairwiseDisjoint (↑t) B) (x y : H) :
    ∑ i ∈ t, ‖E.coefficientMeasure x y (B i)‖ ≤ ‖x‖ * ‖y‖ := by
  calc
    ∑ i ∈ t, ‖E.coefficientMeasure x y (B i)‖
        ≤ ∑ i ∈ t, ‖E (B i) x‖ * ‖E (B i) y‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [E.coefficientMeasure_apply x y (B i) (hB i hi),
        E.coefficient_projection (B i) (hB i hi)]
      exact norm_inner_le_norm _ _
    _ ≤ Real.sqrt (∑ i ∈ t, ‖E (B i) x‖ ^ 2) *
        Real.sqrt (∑ i ∈ t, ‖E (B i) y‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt t _ _
    _ ≤ Real.sqrt (‖x‖ ^ 2) * Real.sqrt (‖y‖ ^ 2) :=
      mul_le_mul (Real.sqrt_le_sqrt (E.sum_norm_sq_le t B hB hd x))
        (Real.sqrt_le_sqrt (E.sum_norm_sq_le t B hB hd y)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = ‖x‖ * ‖y‖ := by rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_norm, abs_norm]

/-- The sharp bound, with no nonzero-vector or nonempty-space hypothesis. -/
theorem coefficientMeasure_variation_le (x y : H) :
    (E.coefficientMeasure x y).variation Set.univ ≤ ENNReal.ofReal (‖x‖ * ‖y‖) := by
  apply le_of_not_gt
  intro h
  obtain ⟨P, _, hd, hP, hlt⟩ :=
    (E.coefficientMeasure x y).exists_lt_sum_of_lt_variation MeasurableSet.univ h
  have hle := E.sum_coefficient_norm_le P id hP hd x y
  have hle' := ENNReal.ofReal_le_ofReal hle
  rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)] at hle'
  simp only [ofReal_norm] at hle'
  exact (not_lt_of_ge hle') hlt

instance coefficientMeasure_variation_finite (x y : H) :
    IsFiniteMeasure (E.coefficientMeasure x y).variation :=
  ⟨(E.coefficientMeasure_variation_le x y).trans_lt ENNReal.ofReal_lt_top⟩

/-- The source's finite spectral sum, independent of any later calculus. -/
abbrev simpleIntegral (f : SimpleFunc S ℂ) : H →L[ℂ] H := Spec.SimpleIntegralValue E f

@[simp] theorem simpleIntegral_apply (f : SimpleFunc S ℂ) (x : H) :
    E.simpleIntegral f x = ∑ c ∈ f.range, c • E (f ⁻¹' {c}) x := by
  simp [simpleIntegral, Spec.SimpleIntegralValue]

theorem simpleIntegral_coefficient (f : SimpleFunc S ℂ) (x y : H) :
    ⟪x, E.simpleIntegral f y⟫_ℂ =
      (E.coefficientMeasure x y).integral f (ContinuousLinearMap.mul ℝ ℂ) := by
  rw [VectorMeasure.integral_eq_setToFun,
    setToFun_simpleFunc _ f f.integrable_of_isFiniteMeasure, E.simpleIntegral_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [inner_smul_right]
  change c * coefficient E x y (f ⁻¹' {c}) = c * E.coefficientMeasure x y (f ⁻¹' {c})
  rw [E.coefficientMeasure_apply x y _ (f.measurableSet_fiber c)]

private theorem norm_sum_sq_of_orthogonal {ι : Type*} (t : Finset ι) (v : ι → H)
    (hv : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → ⟪v i, v j⟫_ℂ = 0) :
    ‖∑ i ∈ t, v i‖ ^ 2 = ∑ i ∈ t, ‖v i‖ ^ 2 := by
  classical
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), sum_inner]
  simp only [inner_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · exact inner_self_eq_norm_sq (𝕜 := ℂ) (v i)
  · intro j hj hji
    rw [hv i hi j hj hji.symm]
    rfl
  · exact fun h => (h hi).elim

/-- Orthogonal series converge unconditionally exactly when their ordered
partial sums converge. This checks the original norm-convergence hypothesis. -/
theorem hasSum_iff_partialSums_of_orthogonal (v : ℕ → H)
    (hv : Pairwise (fun i j => ⟪v i, v j⟫_ℂ = 0)) (z : H) :
    HasSum v z ↔ Tendsto (fun N => ∑ i ∈ Finset.range N, v i) atTop (nhds z) := by
  constructor
  · exact HasSum.tendsto_sum_nat
  · intro hz
    let M : ℕ → Submodule ℂ H := fun i => ℂ ∙ v i
    let w : ∀ i, M i := fun i => ⟨v i, Submodule.mem_span_singleton_self (v i)⟩
    have hM : OrthogonalFamily ℂ (fun i => M i) (fun i => (M i).subtypeₗᵢ) := by
      intro i j hij a b
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp a.property
      obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp b.property
      change ⟪(a : H), (b : H)⟫_ℂ = 0
      rw [← hc, ← hd, inner_smul_left, inner_smul_right, hv hij]
      simp
    have hsq : HasSum (fun i => ‖w i‖ ^ 2) (‖z‖ ^ 2) := by
      apply (hasSum_iff_tendsto_nat_of_nonneg (fun i => sq_nonneg _) _).mpr
      have ht := hz.norm.pow 2
      have heq (N : ℕ) : ‖∑ i ∈ Finset.range N, v i‖ ^ 2 =
          ∑ i ∈ Finset.range N, ‖w i‖ ^ 2 :=
        norm_sum_sq_of_orthogonal _ v (fun i _ j _ hij => hv hij)
      simpa only [heq] using ht
    have hsum : Summable v := (hM.summable_iff_norm_sq_summable w).mpr hsq.summable
    exact hsum.hasSum_iff_tendsto_nat.mpr hz

/-- Pythagoras for the disjoint fibres of a simple function. -/
theorem simpleIntegral_norm_sq (f : SimpleFunc S ℂ) (x : H) :
    ‖E.simpleIntegral f x‖ ^ 2 =
      ∑ c ∈ f.range, ‖c‖ ^ 2 * (E.diagonalMeasure x).real (f ⁻¹' {c}) := by
  rw [E.simpleIntegral_apply, norm_sum_sq_of_orthogonal]
  · apply Finset.sum_congr rfl
    intro c hc
    rw [norm_smul, mul_pow, E.diagonalMeasure_real_apply x _ (f.measurableSet_fiber c)]
  · intro c hc d hd hcd
    rw [inner_smul_left, inner_smul_right,
      E.orthogonality _ _ (f.measurableSet_fiber c) (f.measurableSet_fiber d)]
    · simp
    · exact (Set.disjoint_singleton.mpr hcd).preimage f

theorem simpleIntegral_norm_apply_le (f : SimpleFunc S ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hf : ∀ s, ‖f s‖ ≤ C) (x : H) :
    ‖E.simpleIntegral f x‖ ≤ C * ‖x‖ := by
  have h : ‖E.simpleIntegral f x‖ ^ 2 ≤ C ^ 2 * ‖x‖ ^ 2 := by
    rw [E.simpleIntegral_norm_sq]
    calc
      ∑ c ∈ f.range, ‖c‖ ^ 2 * (E.diagonalMeasure x).real (f ⁻¹' {c})
          ≤ ∑ c ∈ f.range, C ^ 2 * (E.diagonalMeasure x).real (f ⁻¹' {c}) := by
        apply Finset.sum_le_sum
        intro c hc
        obtain ⟨s, rfl⟩ := SimpleFunc.mem_range.mp hc
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hf s) 2)
          ENNReal.toReal_nonneg
      _ = C ^ 2 * ∑ c ∈ f.range, ‖E (f ⁻¹' {c}) x‖ ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c hc
        rw [E.diagonalMeasure_real_apply x _ (f.measurableSet_fiber c)]
      _ ≤ C ^ 2 * ‖x‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
        apply E.sum_norm_sq_le
        · intro c _
          exact f.measurableSet_fiber c
        · intro c hc d hd hcd
          exact (Set.disjoint_singleton.mpr hcd).preimage f
  have h0 : 0 ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg x)
  nlinarith [norm_nonneg (E.simpleIntegral f x)]

theorem simpleIntegral_norm_le (f : SimpleFunc S ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hf : ∀ s, ‖f s‖ ≤ C) : ‖E.simpleIntegral f‖ ≤ C :=
  (E.simpleIntegral f).opNorm_le_bound hC (E.simpleIntegral_norm_apply_le f C hC hf)

theorem simpleIntegral_norm_sq_integral (f : SimpleFunc S ℂ) (x : H) :
    ‖E.simpleIntegral f x‖ ^ 2 = ∫ s, ‖f s‖ ^ 2 ∂E.diagonalMeasure x := by
  let g : SimpleFunc S ℝ := f.map (fun c => ‖c‖ ^ 2)
  have hg : (fun s => ‖f s‖ ^ 2) = g := rfl
  rw [hg, ← g.integral_eq_integral g.integrable_of_isFiniteMeasure]
  rw [SimpleFunc.map_integral f (fun c => ‖c‖ ^ 2) f.integrable_of_isFiniteMeasure (by simp)]
  simpa only [smul_eq_mul, mul_comm] using E.simpleIntegral_norm_sq f x

private theorem simpleIntegral_coefficient_setToSimpleFunc (f : SimpleFunc S ℂ) (x y : H) :
    ⟪x, E.simpleIntegral f y⟫_ℂ = f.setToSimpleFunc
      ((E.coefficientMeasure x y).transpose (ContinuousLinearMap.mul ℝ ℂ)) := by
  rw [E.simpleIntegral_coefficient, VectorMeasure.integral_eq_setToFun,
    setToFun_simpleFunc_eq_setToSimpleFunc _ f f.integrable_of_isFiniteMeasure]

theorem simpleIntegral_add (f g : SimpleFunc S ℂ) :
    E.simpleIntegral (f + g) = E.simpleIntegral f + E.simpleIntegral g := by
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [add_apply, inner_add_right]
  simp only [E.simpleIntegral_coefficient_setToSimpleFunc]
  apply SimpleFunc.setToSimpleFunc_add _
    (dominatedFinMeasAdditive_cbmApplyMeasure (E.coefficientMeasure x y)
      (ContinuousLinearMap.mul ℝ ℂ)).1 f.integrable_of_isFiniteMeasure g.integrable_of_isFiniteMeasure

theorem simpleIntegral_smul (c : ℂ) (f : SimpleFunc S ℂ) :
    E.simpleIntegral (c • f) = c • E.simpleIntegral f := by
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [smul_apply, inner_smul_right]
  simp only [E.simpleIntegral_coefficient_setToSimpleFunc]
  exact SimpleFunc.setToSimpleFunc_smul _
    (dominatedFinMeasAdditive_cbmApplyMeasure (E.coefficientMeasure x y)
      (ContinuousLinearMap.mul ℝ ℂ)).1
    (fun c B z => by change (c * z) * _ = c * (z * _); rw [mul_assoc]) c
    f.integrable_of_isFiniteMeasure

theorem simpleIntegral_sub (f g : SimpleFunc S ℂ) :
    E.simpleIntegral (f - g) = E.simpleIntegral f - E.simpleIntegral g := by
  calc
    E.simpleIntegral (f - g) = E.simpleIntegral (f + (-1 : ℂ) • g) := by
      rw [neg_one_smul, sub_eq_add_neg]
    _ = E.simpleIntegral f + E.simpleIntegral ((-1 : ℂ) • g) := E.simpleIntegral_add _ _
    _ = E.simpleIntegral f - E.simpleIntegral g := by
      rw [E.simpleIntegral_smul, neg_one_smul, sub_eq_add_neg]

theorem simpleIntegral_dist_le (f g : SimpleFunc S ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hfg : ∀ s, dist (f s) (g s) ≤ C) :
    dist (E.simpleIntegral f) (E.simpleIntegral g) ≤ C := by
  rw [dist_eq_norm, ← E.simpleIntegral_sub]
  apply E.simpleIntegral_norm_le (f - g) C hC
  simpa only [dist_eq_norm, SimpleFunc.coe_sub, Pi.sub_apply] using hfg

/-- Change of the finite-value parameter; common refinements use this with
pairs of simple functions. No ambient measure on S is chosen. -/
theorem simpleIntegral_map_of_zero {β : Type*} [NormedAddCommGroup β]
    [NormedSpace ℝ β] (f : SimpleFunc S β) (g : β → ℂ) (hg : g 0 = 0) :
    E.simpleIntegral (f.map g) = ∑ b ∈ f.range, g b • E (f ⁻¹' {b}) := by
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [E.simpleIntegral_coefficient_setToSimpleFunc,
    SimpleFunc.map_setToSimpleFunc _
      (dominatedFinMeasAdditive_cbmApplyMeasure (E.coefficientMeasure x y)
        (ContinuousLinearMap.mul ℝ ℂ)).1 f.integrable_of_isFiniteMeasure hg,
    sum_apply, inner_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [smul_apply, inner_smul_right]
  change g b * E.coefficientMeasure x y (f ⁻¹' {b}) = g b * coefficient E x y (f ⁻¹' {b})
  rw [E.coefficientMeasure_apply x y _ (f.measurableSet_fiber b)]

theorem simpleIntegral_star (f : SimpleFunc S ℂ) :
    E.simpleIntegral (star f) = star (E.simpleIntegral f) := by
  change E.simpleIntegral (f.map star) = _
  rw [E.simpleIntegral_map_of_zero f star (star_zero ℂ)]
  simp only [simpleIntegral, Spec.SimpleIntegralValue, star_sum, star_smul]
  apply Finset.sum_congr rfl
  intro c hc
  rw [(E.selfAdjoint _ (f.measurableSet_fiber c)).star_eq]

theorem simpleIntegral_mul (f g : SimpleFunc S ℂ) :
    E.simpleIntegral (f * g) = E.simpleIntegral f * E.simpleIntegral g := by
  rw [SimpleFunc.mul_eq_map₂, E.simpleIntegral_map_of_zero (f.pair g)
    (fun p : ℂ × ℂ => p.1 * p.2) (by simp)]
  have hsubset : (f.pair g).range ⊆ f.range ×ˢ g.range := by
    intro p hp
    obtain ⟨s, rfl⟩ := SimpleFunc.mem_range.mp hp
    exact Finset.mem_product.mpr ⟨f.mem_range_self s, g.mem_range_self s⟩
  calc
    ∑ p ∈ (f.pair g).range, (p.1 * p.2) • E (f.pair g ⁻¹' {p})
        = ∑ p ∈ f.range ×ˢ g.range, (p.1 * p.2) • E (f.pair g ⁻¹' {p}) := by
      apply Finset.sum_subset hsubset
      intro p hp hnot
      have hempty : f.pair g ⁻¹' {p} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro s hs
        exact hnot (SimpleFunc.mem_range.mpr ⟨s, hs⟩)
      rw [hempty, E.map_empty, smul_zero]
    _ = ∑ c ∈ f.range, ∑ d ∈ g.range, (c * d) • E (f ⁻¹' {c} ∩ g ⁻¹' {d}) := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      rw [SimpleFunc.pair_preimage_singleton]
    _ = E.simpleIntegral f * E.simpleIntegral g := by
      simp only [simpleIntegral, Spec.SimpleIntegralValue, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro d hd
      rw [smul_mul_smul_comm, E.inter _ _ (f.measurableSet_fiber d) (g.measurableSet_fiber c)]

end ProjectionValuedMeasure

/-- Uniform simple approximation uses compactness only of bounded subsets
of the scalar plane. The measurable space S has no topological hypotheses. -/
theorem exists_uniform_simple_approx (f : S → ℂ) (hf : Spec.IsBoundedMeasurable f) :
    ∃ a : ℕ → SimpleFunc S ℂ, TendstoUniformly (fun n => a n) f atTop := by
  let e := TopologicalSpace.denseSeq ℂ
  refine ⟨fun n => (SimpleFunc.nearestPt e n).comp f hf.1, ?_⟩
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨C, hC⟩ := hf.2
  have hcover : Metric.closedBall (0 : ℂ) C ⊆ ⋃ n, Metric.ball (e n) ε := by
    intro z hz
    obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq ℂ).exists_dist_lt z hε
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨t, ht⟩ := (isCompact_closedBall (0 : ℂ) C).elim_finite_subcover
    (fun n => Metric.ball (e n) ε) (fun _ => Metric.isOpen_ball) hcover
  filter_upwards [eventually_ge_atTop (t.sup id)] with N hN
  intro s
  have hs : f s ∈ Metric.closedBall (0 : ℂ) C := by simpa using hC s
  obtain ⟨n, hn, hdist⟩ := Set.mem_iUnion₂.mp (ht hs)
  have hnear := SimpleFunc.edist_nearestPt_le e (f s) ((Finset.le_sup hn).trans hN)
  have hnear' := ENNReal.toReal_mono (edist_ne_top (e n) (f s)) hnear
  have hbound : dist ((SimpleFunc.nearestPt e N) (f s)) (f s) ≤ dist (e n) (f s) := by
    simpa [edist_dist] using hnear'
  change dist (f s) ((SimpleFunc.nearestPt e N) (f s)) < ε
  rw [dist_comm]
  exact hbound.trans_lt (by simpa only [Metric.mem_ball, dist_comm] using hdist)

namespace Spec.IsBoundedMeasurable

theorem nonneg_bound {f : S → ℂ} (hf : Spec.IsBoundedMeasurable f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ‖f s‖ ≤ C := by
  obtain ⟨C, hC⟩ := hf.2
  exact ⟨max C 0, le_max_right _ _, fun s => (hC s).trans (le_max_left _ _)⟩

theorem simple (f : SimpleFunc S ℂ) : Spec.IsBoundedMeasurable (f : S → ℂ) := by
  refine ⟨f.measurable, ∑ c ∈ f.range, ‖c‖, ?_⟩
  intro s
  exact Finset.single_le_sum (fun c (_ : c ∈ f.range) => norm_nonneg c) (f.mem_range_self s)

theorem add {f g : S → ℂ} (hf : Spec.IsBoundedMeasurable f) (hg : Spec.IsBoundedMeasurable g) :
    Spec.IsBoundedMeasurable (f + g) := by
  obtain ⟨C, hC⟩ := hf.2
  obtain ⟨D, hD⟩ := hg.2
  exact ⟨hf.1.add hg.1, C + D, fun s => (norm_add_le _ _).trans (add_le_add (hC s) (hD s))⟩

theorem mul {f g : S → ℂ} (hf : Spec.IsBoundedMeasurable f) (hg : Spec.IsBoundedMeasurable g) :
    Spec.IsBoundedMeasurable (f * g) := by
  obtain ⟨C, hC0, hC⟩ := hf.nonneg_bound
  obtain ⟨D, hD0, hD⟩ := hg.nonneg_bound
  refine ⟨hf.1.mul hg.1, C * D, fun s => ?_⟩
  exact (norm_mul_le _ _).trans (mul_le_mul (hC s) (hD s) (norm_nonneg _) hC0)

theorem smul (c : ℂ) {f : S → ℂ} (hf : Spec.IsBoundedMeasurable f) :
    Spec.IsBoundedMeasurable (c • f) := by
  obtain ⟨C, hC⟩ := hf.2
  exact ⟨measurable_const.mul hf.1, ‖c‖ * C,
    fun s => (norm_smul c (f s)).le.trans (mul_le_mul_of_nonneg_left (hC s) (norm_nonneg _))⟩

theorem star {f : S → ℂ} (hf : Spec.IsBoundedMeasurable f) :
    Spec.IsBoundedMeasurable (star f) := by
  obtain ⟨C, hC⟩ := hf.2
  exact ⟨Complex.continuous_conj.measurable.comp hf.1, C, fun s => (norm_star (f s)).le.trans (hC s)⟩

end Spec.IsBoundedMeasurable

namespace ProjectionValuedMeasure
variable (E : ProjectionValuedMeasure S H)

private def uniformApprox (f : S → ℂ) (hf : Spec.IsBoundedMeasurable f) : ℕ → SimpleFunc S ℂ :=
  (exists_uniform_simple_approx f hf).choose

private theorem uniformApprox_tendsto (f : S → ℂ) (hf : Spec.IsBoundedMeasurable f) :
    TendstoUniformly (fun n => uniformApprox f hf n) f atTop :=
  (exists_uniform_simple_approx f hf).choose_spec

/-- Uniform convergence of scalar simple functions makes the spectral sums
Cauchy in operator norm, using the contractive difference estimate. -/
theorem simpleIntegral_cauchy_of_uniform {a : ℕ → SimpleFunc S ℂ} {f : S → ℂ}
    (ha : TendstoUniformly (fun n => a n) f atTop) : CauchySeq (fun n => E.simpleIntegral (a n)) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp ha.tendstoUniformlyOn.uniformCauchySeqOn
    (ε / 2) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  apply (E.simpleIntegral_dist_le (a m) (a n) (ε / 2) (by positivity) ?_).trans_lt (by linarith)
  intro s
  exact (hN m hm n hn s (Set.mem_univ s)).le

/-- The operator norm limit of uniform simple approximations. Unbounded or
nonmeasurable functions are assigned zero only to make the ambient function total. -/
def spectralIntegral (f : S → ℂ) : H →L[ℂ] H :=
  if hf : Spec.IsBoundedMeasurable f then
    atTop.limUnder (fun n => E.simpleIntegral (uniformApprox f hf n)) else 0

/-- Every uniformly convergent simple approximation has the same norm limit. -/
theorem spectralIntegral_tendsto (f : S → ℂ) (hf : Spec.IsBoundedMeasurable f)
    (a : ℕ → SimpleFunc S ℂ) (ha : TendstoUniformly (fun n => a n) f atTop) :
    Tendsto (fun n => E.simpleIntegral (a n)) atTop (nhds (E.spectralIntegral f)) := by
  rw [spectralIntegral, dite_eq_left hf]
  have hb := uniformApprox_tendsto f hf
  have hI := (E.simpleIntegral_cauchy_of_uniform hb).tendsto_limUnder
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hI (ε / 2) (by positivity),
    Metric.tendstoUniformly_iff.mp ha (ε / 4) (by positivity),
    Metric.tendstoUniformly_iff.mp hb (ε / 4) (by positivity)] with n hn han hbn
  have hd : dist (E.simpleIntegral (a n)) (E.simpleIntegral (uniformApprox f hf n)) ≤ ε / 2 := by
    apply E.simpleIntegral_dist_le _ _ _ (by positivity)
    intro s
    have hd := dist_triangle (a n s) (f s) (uniformApprox f hf n s)
    have has := han s
    rw [dist_comm] at has
    linarith [hbn s]
  exact (dist_triangle _ _ _).trans_lt (by linarith)

theorem spectralIntegral_simple (f : SimpleFunc S ℂ) :
    E.spectralIntegral f = E.simpleIntegral f := by
  have h := E.spectralIntegral_tendsto f (Spec.IsBoundedMeasurable.simple f)
    (fun _ => f) (by
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      exact Eventually.of_forall (fun _ _ => by simpa using hε))
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem simpleIntegral_const (c : ℂ) :
    E.simpleIntegral (SimpleFunc.const S c) = c • (1 : H →L[ℂ] H) := by
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [E.simpleIntegral_coefficient]
  change (E.coefficientMeasure x y).integral (fun _ => c) (ContinuousLinearMap.mul ℝ ℂ) = _
  rw [VectorMeasure.integral_const]
  simp [E.coefficientMeasure_apply x y _ MeasurableSet.univ,
    coefficient, Spec.CoefficientValue, E.univ, inner_smul_right]

theorem spectralIntegral_one : E.spectralIntegral (fun _ => 1) = 1 := by
  have h := E.spectralIntegral_simple (SimpleFunc.const S (1 : ℂ))
  rw [E.simpleIntegral_const, one_smul] at h
  exact h

theorem spectralIntegral_add (f g : S → ℂ) (hf : Spec.IsBoundedMeasurable f)
    (hg : Spec.IsBoundedMeasurable g) :
    E.spectralIntegral (f + g) = E.spectralIntegral f + E.spectralIntegral g := by
  let a := uniformApprox f hf
  let b := uniformApprox g hg
  have ha := uniformApprox_tendsto f hf
  have hb := uniformApprox_tendsto g hg
  have h₁ := E.spectralIntegral_tendsto (f + g) (hf.add hg) (fun n => a n + b n) (ha.add hb)
  have h₂ := (E.spectralIntegral_tendsto f hf a ha).add (E.spectralIntegral_tendsto g hg b hb)
  simp only [E.simpleIntegral_add] at h₁
  exact tendsto_nhds_unique h₁ h₂

theorem spectralIntegral_smul (c : ℂ) (f : S → ℂ) (hf : Spec.IsBoundedMeasurable f) :
    E.spectralIntegral (c • f) = c • E.spectralIntegral f := by
  let a := uniformApprox f hf
  have ha := uniformApprox_tendsto f hf
  have has : TendstoUniformly (fun n => (c • a n : SimpleFunc S ℂ)) (c • f) atTop :=
    ((ContinuousLinearMap.lsmul ℂ ℂ) c).uniformContinuous.comp_tendstoUniformly ha
  have h₁ := E.spectralIntegral_tendsto (c • f) (hf.smul c) (fun n => c • a n) has
  have h₂ := (E.spectralIntegral_tendsto f hf a ha).const_smul c
  simp only [E.simpleIntegral_smul] at h₁
  exact tendsto_nhds_unique h₁ h₂

theorem spectralIntegral_star (f : S → ℂ) (hf : Spec.IsBoundedMeasurable f) :
    E.spectralIntegral (star f) = star (E.spectralIntegral f) := by
  let a := uniformApprox f hf
  have ha := uniformApprox_tendsto f hf
  have has : TendstoUniformly (fun n => (star (a n) : SimpleFunc S ℂ)) (star f) atTop :=
    Complex.isometry_conj.uniformContinuous.comp_tendstoUniformly ha
  have h₁ := E.spectralIntegral_tendsto (star f) hf.star (fun n => star (a n)) has
  have h₂ := (E.spectralIntegral_tendsto f hf a ha).star
  simp only [E.simpleIntegral_star] at h₁
  exact tendsto_nhds_unique h₁ h₂

theorem spectralIntegral_norm_le (f : S → ℂ) (hf : Spec.IsBoundedMeasurable f)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ s, ‖f s‖ ≤ C) : ‖E.spectralIntegral f‖ ≤ C := by
  let a := uniformApprox f hf
  have ha := uniformApprox_tendsto f hf
  apply le_of_forall_pos_le_add
  intro ε hε
  apply le_of_tendsto (E.spectralIntegral_tendsto f hf a ha).norm
  filter_upwards [Metric.tendstoUniformly_iff.mp ha ε hε] with n hn
  apply E.simpleIntegral_norm_le _ _ (by positivity)
  intro s
  have ht := dist_triangle (a n s) (f s) 0
  simp only [dist_zero_right] at ht
  have hd := hn s
  rw [dist_comm] at hd
  linarith [hbound s]

private theorem uniformApprox_eventually_bound (f : S → ℂ) (hf : Spec.IsBoundedMeasurable f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ s, ‖uniformApprox f hf n s‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := hf.nonneg_bound
  refine ⟨C + 1, by positivity, ?_⟩
  filter_upwards [Metric.tendstoUniformly_iff.mp (uniformApprox_tendsto f hf) 1 (by positivity)]
    with n hn s
  have ht := dist_triangle (uniformApprox f hf n s) (f s) 0
  simp only [dist_zero_right] at ht
  have hd := hn s
  rw [dist_comm] at hd
  linarith [hC s]

theorem spectralIntegral_coefficient (f : S → ℂ) (hf : Spec.IsBoundedMeasurable f) (x y : H) :
    ⟪x, E.spectralIntegral f y⟫_ℂ =
      (E.coefficientMeasure x y).integral f (ContinuousLinearMap.mul ℝ ℂ) := by
  let a := uniformApprox f hf
  have ha := uniformApprox_tendsto f hf
  have hA := E.spectralIntegral_tendsto f hf a ha
  have hAy := (((ContinuousLinearMap.apply ℂ H) y).continuous.tendsto _).comp hA
  have hinner : Tendsto (fun n => ⟪x, E.simpleIntegral (a n) y⟫_ℂ) atTop
      (nhds ⟪x, E.spectralIntegral f y⟫_ℂ) := tendsto_const_nhds.inner hAy
  have hInt : Tendsto (fun n => (E.coefficientMeasure x y).integral (a n)
      (ContinuousLinearMap.mul ℝ ℂ)) atTop
      (nhds ((E.coefficientMeasure x y).integral f (ContinuousLinearMap.mul ℝ ℂ))) := by
    apply VectorMeasure.tendsto_integral_filter_of_norm_le_const
    · exact Eventually.of_forall (fun n => (a n).measurable.stronglyMeasurable.aestronglyMeasurable)
    · obtain ⟨C, _, hC⟩ := uniformApprox_eventually_bound f hf
      exact ⟨C, hC.mono (fun _ hn => Eventually.of_forall hn)⟩
    · exact Eventually.of_forall (fun s => ha.tendsto_at s)
  simp only [← E.simpleIntegral_coefficient] at hInt
  exact tendsto_nhds_unique hinner hInt

theorem spectralIntegral_norm_sq_integral (f : S → ℂ) (hf : Spec.IsBoundedMeasurable f) (x : H) :
    ‖E.spectralIntegral f x‖ ^ 2 = ∫ s, ‖f s‖ ^ 2 ∂E.diagonalMeasure x := by
  let a := uniformApprox f hf
  have ha := uniformApprox_tendsto f hf
  have hA := E.spectralIntegral_tendsto f hf a ha
  have hAx := (((ContinuousLinearMap.apply ℂ H) x).continuous.tendsto _).comp hA
  have hNorm := hAx.norm.pow 2
  have hInt : Tendsto (fun n => ∫ s, ‖a n s‖ ^ 2 ∂E.diagonalMeasure x) atTop
      (nhds (∫ s, ‖f s‖ ^ 2 ∂E.diagonalMeasure x)) := by
    apply tendsto_integral_filter_of_norm_le_const
    · exact Eventually.of_forall (fun n =>
        ((a n).measurable.norm.pow_const 2).stronglyMeasurable.aestronglyMeasurable)
    · obtain ⟨C, hC0, hC⟩ := uniformApprox_eventually_bound f hf
      refine ⟨C ^ 2, hC.mono (fun n hn => Eventually.of_forall (fun s => ?_))⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hn s) 2
    · exact Eventually.of_forall (fun s => (ha.tendsto_at s).norm.pow 2)
  simp only [← E.simpleIntegral_norm_sq_integral] at hInt
  exact tendsto_nhds_unique hNorm hInt

private theorem uniformApprox_mul (f g : S → ℂ) (hf : Spec.IsBoundedMeasurable f)
    (hg : Spec.IsBoundedMeasurable g) :
    TendstoUniformly (fun n s => uniformApprox f hf n s * uniformApprox g hg n s) (f * g) atTop := by
  obtain ⟨C, hC0, hC⟩ := hf.nonneg_bound
  obtain ⟨D, hD0, hD⟩ := hg.nonneg_bound
  let K := C + D + 1
  have hK : 0 < K := by dsimp [K]; linarith
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  let δ := ε / (2 * K)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have ha := uniformApprox_tendsto f hf
  have hb := uniformApprox_tendsto g hg
  filter_upwards [Metric.tendstoUniformly_iff.mp ha δ hδ,
    Metric.tendstoUniformly_iff.mp hb δ hδ,
    Metric.tendstoUniformly_iff.mp hb 1 (by positivity)] with n han hbn hb1 s
  have hnb : ‖uniformApprox g hg n s‖ ≤ D + 1 := by
    have ht := dist_triangle (uniformApprox g hg n s) (g s) 0
    simp only [dist_zero_right] at ht
    have hd := hb1 s
    rw [dist_comm] at hd
    linarith [hD s]
  have hfa : ‖f s - uniformApprox f hf n s‖ ≤ δ := by simpa [dist_eq_norm] using (han s).le
  have hgb : ‖g s - uniformApprox g hg n s‖ ≤ δ := by simpa [dist_eq_norm] using (hbn s).le
  change dist (f s * g s) (uniformApprox f hf n s * uniformApprox g hg n s) < ε
  rw [dist_eq_norm]
  calc
    ‖f s * g s - uniformApprox f hf n s * uniformApprox g hg n s‖
        = ‖f s * (g s - uniformApprox g hg n s) +
          (f s - uniformApprox f hf n s) * uniformApprox g hg n s‖ := by congr 1; ring
    _ ≤ ‖f s‖ * ‖g s - uniformApprox g hg n s‖ +
        ‖f s - uniformApprox f hf n s‖ * ‖uniformApprox g hg n s‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ C * δ + δ * (D + 1) := add_le_add
      (mul_le_mul (hC s) hgb (norm_nonneg _) hC0)
      (mul_le_mul hfa hnb (norm_nonneg _) hδ.le)
    _ = ε / 2 := by dsimp [δ, K]; field_simp; ring
    _ < ε := by linarith

theorem spectralIntegral_mul (f g : S → ℂ) (hf : Spec.IsBoundedMeasurable f)
    (hg : Spec.IsBoundedMeasurable g) :
    E.spectralIntegral (f * g) = E.spectralIntegral f * E.spectralIntegral g := by
  let a := uniformApprox f hf
  let b := uniformApprox g hg
  have ha := uniformApprox_tendsto f hf
  have hb := uniformApprox_tendsto g hg
  have h₁ := E.spectralIntegral_tendsto (f * g) (hf.mul hg) (fun n => a n * b n)
    (uniformApprox_mul f g hf hg)
  have h₂ := (E.spectralIntegral_tendsto f hf a ha).mul (E.spectralIntegral_tendsto g hg b hb)
  simp only [E.simpleIntegral_mul] at h₁
  exact tendsto_nhds_unique h₁ h₂

end ProjectionValuedMeasure

 theorem empty : Spec.Empty (S := S) (H := H) := ProjectionValuedMeasure.map_empty
 theorem projection_laws : Spec.ProjectionLaws (S := S) (H := H) := by
  intro E B hB
  exact ⟨E.selfAdjoint B hB, E.idempotent B hB, E.norm_le_one B hB, E.norm_apply_le B hB⟩
 theorem coefficient_projection : Spec.CoefficientProjection (S := S) (H := H) :=
  ProjectionValuedMeasure.coefficient_projection
 theorem orthogonality : Spec.Orthogonality (S := S) (H := H) :=
  ProjectionValuedMeasure.orthogonality

theorem scalar_measures : Spec.ScalarMeasures (S := S) (H := H) := by
  intro E
  exact ⟨E.coefficientMeasure, E.diagonalMeasure, E.coefficientMeasure_apply,
    E.diagonalMeasure_finite, E.diagonalMeasure_apply, E.coefficientMeasure_diagonal,
    E.diagonalMeasure_univ, E.coefficientMeasure_variation_le⟩

/-- Realization of precisely the printed PVM axioms. -/
theorem source_realization : Spec.SourceRealization (S := S) (H := H) := by
  intro F
  constructor
  · rintro ⟨h1, hself, hinter, hadd⟩
    have h0 (x : H) : F ∅ x = 0 := by
      let a : ℕ → H := fun N => ∑ n ∈ Finset.range N, F ∅ x
      have ha : Tendsto a atTop (nhds (F ∅ x)) := by
        simpa only [Set.iUnion_const] using hadd (fun _ => ∅)
          (fun _ => MeasurableSet.empty) (fun _ _ _ => disjoint_bot_left) x
      have hdiff := (ha.comp (tendsto_add_atTop_nat 1)).sub ha
      have heq : (fun N => a (N + 1) - a N) = fun _ => F ∅ x := by
        funext N
        simp only [a, Finset.sum_range_succ, add_sub_cancel_left]
      change Tendsto (fun N => a (N + 1) - a N) atTop (nhds (F ∅ x - F ∅ x)) at hdiff
      rw [heq, sub_self] at hdiff
      exact tendsto_nhds_unique tendsto_const_nhds hdiff
    let E : ProjectionValuedMeasure S H := {
      toFun := F
      univ := h1
      selfAdjoint := hself
      inter := hinter
      iUnion := by
        intro B hB hd x
        apply (ProjectionValuedMeasure.hasSum_iff_partialSums_of_orthogonal _ ?_ _).mpr
          (hadd B hB hd x)
        intro i j hij
        have hs : ⟪F (B i) x, F (B j) x⟫_ℂ = ⟪x, F (B i) (F (B j) x)⟫_ℂ :=
          (hself (B i) (hB i)).isSymmetric x (F (B j) x)
        rw [hs]
        have hm := congrArg (fun T : H →L[ℂ] H => T x) (hinter _ _ (hB i) (hB j))
        change F (B i) (F (B j) x) = F (B i ∩ B j) x at hm
        rw [hm, Set.disjoint_iff_inter_eq_empty.mp (hd hij), h0]
        exact inner_zero_right _ }
    exact ⟨E, rfl⟩
  · rintro ⟨E, rfl⟩
    exact ⟨E.univ, E.selfAdjoint, E.inter, fun B hB hd x => (E.iUnion B hB hd x).tendsto_sum_nat⟩

/-- The complete source obligation, including the construction and all
identities for bounded measurable functions. -/
theorem functional_calculus : Spec.FunctionalCalculus (S := S) (H := H) := by
  intro E
  refine ⟨E.coefficientMeasure, E.diagonalMeasure, E.spectralIntegral,
    E.coefficientMeasure_apply, E.diagonalMeasure_finite, E.diagonalMeasure_apply,
    E.coefficientMeasure_diagonal, E.diagonalMeasure_univ,
    E.coefficientMeasure_variation_le, E.spectralIntegral_simple,
    exists_uniform_simple_approx, E.spectralIntegral_tendsto,
    E.spectralIntegral_one, E.spectralIntegral_add, E.spectralIntegral_smul,
    E.spectralIntegral_mul, E.spectralIntegral_star, ?_, E.spectralIntegral_coefficient,
    E.spectralIntegral_norm_sq_integral⟩
  intro f C hf hC hbound
  exact E.spectralIntegral_norm_le f hf C hC hbound

end ExpandedFA.SpectralMeasure
