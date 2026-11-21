import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SpectralMeasure.RealDefinitions
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
import Mathlib.MeasureTheory.VectorMeasure.Order
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.RieszRepresentation
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic

noncomputable section
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace NNReal ENNReal

namespace ExpandedFA.SpectralMeasure
universe u v
variable {S : Type u} {H : Type v} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

namespace RealBoundedFunction

@[ext] theorem ext {f g : RealBoundedFunction S} (h : ∀ s, f s = g s) : f = g := by
  cases f
  cases g
  congr
  exact funext h

/-- Uniform quantization of a bounded measurable real function. -/
def floorApprox (f : RealBoundedFunction S) (n : ℕ) : SimpleFunc S ℝ := by
  classical
  let M : ℝ := (n : ℝ) + 1
  let C := f.bounded.choose
  have hC := f.bounded.choose_spec.2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let q : S → ℝ := fun s => (⌊M * f s⌋ : ℤ) / M
  have hq : Measurable q := by
    exact ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
      (Int.measurable_floor.comp (measurable_const.mul f.measurable))).div_const M
  refine ⟨q, fun c => hq (measurableSet_singleton c), ?_⟩
  apply ((Set.finite_Icc (⌊-M * C⌋ : ℤ) ⌊M * C⌋).image (fun z : ℤ => (z : ℝ) / M)).subset
  rintro z ⟨s, rfl⟩
  refine ⟨⌊M * f s⌋, ?_, rfl⟩
  obtain ⟨hl, hu⟩ := abs_le.mp (hC s)
  constructor
  · apply Int.floor_mono
    nlinarith
  · exact Int.floor_mono (mul_le_mul_of_nonneg_left hu hM)

@[simp] theorem floorApprox_apply (f : RealBoundedFunction S) (n : ℕ) (s : S) :
    f.floorApprox n s = (⌊((n : ℝ) + 1) * f s⌋ : ℤ) / ((n : ℝ) + 1) := rfl

theorem floorApprox_error (f : RealBoundedFunction S) (n : ℕ) (s : S) :
    dist (f s) (f.floorApprox n s) < 1 / ((n : ℝ) + 1) := by
  rw [floorApprox_apply, Real.dist_eq]
  have hM : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hl := Int.floor_le (((n : ℝ) + 1) * f s)
  have hu := Int.lt_floor_add_one (((n : ℝ) + 1) * f s)
  have hq : (⌊((n : ℝ) + 1) * f s⌋ : ℤ) / ((n : ℝ) + 1) ≤ f s := by
    apply (div_le_iff₀ hM).2
    nlinarith
  rw [abs_of_nonneg (sub_nonneg.mpr hq), sub_lt_iff_lt_add, ← add_div]
  apply (lt_div_iff₀ hM).2
  nlinarith

theorem tendstoUniformly_floorApprox (f : RealBoundedFunction S) :
    TendstoUniformly (fun n => (f.floorApprox n : S → ℝ)) f atTop := by
  apply Metric.tendstoUniformly_iff.2
  intro ε hε
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
    (gt_mem_nhds hε)
  filter_upwards [h] with n hn
  intro s
  exact (f.floorApprox_error n s).trans hn

end RealBoundedFunction

namespace RealProjectionValuedMeasure
variable (E : RealProjectionValuedMeasure S H)

@[simp] theorem empty : E ∅ = 0 := by
  ext x
  have h := E.countablyAdditive (fun _ => ∅) (fun _ => MeasurableSet.empty)
    (fun _ _ _ => by simp) x
  exact (summable_const_iff (E ∅ x)).mp h.summable

@[simp] theorem idempotent {B : Set S} (hB : MeasurableSet B) : E B * E B = E B := by
  simpa using E.inter B B hB hB

@[simp] theorem idempotent_apply {B : Set S} (hB : MeasurableSet B) (x : H) :
    E B (E B x) = E B x := by
  exact congrArg (fun T : H →L[ℝ] H => T x) (E.idempotent hB)

theorem star_eq {B : Set S} (hB : MeasurableSet B) : star (E B) = E B := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℝ
  intro x
  exact (ContinuousLinearMap.adjoint_inner_right (E B) x y).trans
    (E.selfAdjoint B hB x y)

theorem inner_projected {B : Set S} (hB : MeasurableSet B) (x y : H) :
    ⟪E B x, E B y⟫_ℝ = ⟪x, E B y⟫_ℝ := by
  rw [E.selfAdjoint B hB, E.idempotent_apply hB]

theorem inner_self_projected {B : Set S} (hB : MeasurableSet B) (x : H) :
    ⟪x, E B x⟫_ℝ = ‖E B x‖ ^ 2 := by
  rw [← E.inner_projected hB, real_inner_self_eq_norm_sq]

theorem norm_apply_le {B : Set S} (hB : MeasurableSet B) (x : H) : ‖E B x‖ ≤ ‖x‖ := by
  have h := real_inner_le_norm x (E B x)
  rw [E.inner_self_projected hB] at h
  nlinarith [norm_nonneg (E B x), norm_nonneg x]

theorem norm_le_one {B : Set S} (hB : MeasurableSet B) : ‖E B‖ ≤ 1 := by
  exact (E B).opNorm_le_bound zero_le_one (fun x => by simpa using E.norm_apply_le hB x)

theorem disjoint_mul {B C : Set S} (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBC : Disjoint B C) : E B * E C = 0 := by
  rw [E.inter B C hB hC, hBC.inter_eq, E.empty]

theorem disjoint_orthogonal {B C : Set S} (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBC : Disjoint B C) (x y : H) : ⟪E B x, E C y⟫_ℝ = 0 := by
  rw [E.selfAdjoint B hB]
  have h := congrArg (fun T : H →L[ℝ] H => T y) (E.disjoint_mul hB hC hBC)
  change E B (E C y) = 0 at h
  rw [h, inner_zero_right]

/-- Actual signed measures, with the conventional irrelevant value zero off Σ. -/
def coefficient (x y : H) : SignedMeasure S := by
 classical
 exact {
  measureOf' B := if MeasurableSet B then ⟪x, E B y⟫_ℝ else 0
  empty' := by simp [E.empty]
  not_measurable' B h := ite_eq_right h
  m_iUnion' {B} hB hd := by
    have h := (innerSL ℝ x).hasSum (E.countablyAdditive B hB hd y)
    simpa only [hB, MeasurableSet.iUnion hB, ite_true, innerSL_apply_apply] using h
 }

@[simp] theorem coefficient_apply (x y : H) {B : Set S} (hB : MeasurableSet B) :
    E.coefficient x y B = ⟪x, E B y⟫_ℝ := by
  simp [coefficient, hB]


theorem coefficient_nonneg (x : H) : 0 ≤ E.coefficient x x := by
  intro B hB
  simp only [zero_apply, E.coefficient_apply x x hB,
    E.inner_self_projected hB]
  positivity

/-- The positive scalar measure, built from the positive diagonal signed measure. -/
def scalar (x : H) : Measure S :=
  (E.coefficient x x).toMeasureOfZeroLE Set.univ MeasurableSet.univ
    ((VectorMeasure.le_restrict_univ_iff_le _ _).2 (E.coefficient_nonneg x))

instance scalar_finite (x : H) : IsFiniteMeasure (E.scalar x) := by
  unfold scalar
  infer_instance

@[simp] theorem scalar_apply (x : H) {B : Set S} (hB : MeasurableSet B) :
    E.scalar x B = ENNReal.ofReal (‖E B x‖ ^ 2) := by
  rw [scalar, SignedMeasure.toMeasureOfZeroLE_apply _ _ MeasurableSet.univ hB]
  simp only [univ_inter, E.coefficient_apply x x hB, E.inner_self_projected hB]
  exact (ENNReal.ofReal_eq_coe_nnreal (by positivity)).symm

@[simp] theorem scalar_mass (x : H) :
    E.scalar x Set.univ = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [E.scalar_apply x MeasurableSet.univ]
  simp [E.univ]

theorem scalar_real_apply (x : H) {B : Set S} (hB : MeasurableSet B) :
    (E.scalar x).real B = ‖E B x‖ ^ 2 := by
  rw [measureReal_def, E.scalar_apply x hB, ENNReal.toReal_ofReal (sq_nonneg _)]

theorem coefficient_diagonal (x : H) : E.coefficient x x = (E.scalar x).toSignedMeasure := by
  apply VectorMeasure.ext
  intro B hB
  rw [Measure.toSignedMeasure_apply_measurable hB, E.scalar_real_apply x hB,
    E.coefficient_apply x x hB, E.inner_self_projected hB]

@[simp] theorem coefficient_zero_left (y : H) : E.coefficient 0 y = 0 := by
  ext B hB
  simp [E.coefficient_apply _ _ hB]

@[simp] theorem coefficient_zero_right (x : H) : E.coefficient x 0 = 0 := by
  ext B hB
  simp [E.coefficient_apply _ _ hB]

theorem coefficient_smul_left (c : ℝ) (x y : H) :
    E.coefficient (c • x) y = c • E.coefficient x y := by
  ext B hB
  simp [E.coefficient_apply _ _ hB, real_inner_smul_left]

theorem coefficient_smul_right (c : ℝ) (x y : H) :
    E.coefficient x (c • y) = c • E.coefficient x y := by
  ext B hB
  simp [E.coefficient_apply _ _ hB, real_inner_smul_right]


/-- Quadratic domination gives a measure bound on variation. Rescaling the
vectors separately below sharpens the quadratic estimate to the product. -/
theorem variation_quadratic (x y : H) :
    (E.coefficient x y).variation Set.univ ≤
      ENNReal.ofReal ((‖x‖ ^ 2 + ‖y‖ ^ 2) / 2) := by
  let m : Measure S := ENNReal.ofReal (1 / 2 : ℝ) • (E.scalar x + E.scalar y)
  have hdom : (E.coefficient x y).variation ≤ m := by
    apply VectorMeasure.variation_le_of_forall_enorm_le
    intro B hB
    dsimp [m]
    rw [E.scalar_apply x hB,
      E.scalar_apply y hB, E.coefficient_apply x y hB,
      Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    apply ENNReal.ofReal_le_ofReal
    rw [← E.inner_projected hB]
    have hc := abs_real_inner_le_norm (E B x) (E B y)
    nlinarith [sq_nonneg (‖E B x‖ - ‖E B y‖)]
  calc
    (E.coefficient x y).variation Set.univ ≤ m Set.univ := hdom _
    _ = ENNReal.ofReal ((‖x‖ ^ 2 + ‖y‖ ^ 2) / 2) := by
      simp only [m, Measure.smul_apply, Measure.add_apply, E.scalar_mass, smul_eq_mul]
      rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      congr 1
      ring

theorem variation_bound (x y : H) :
    (E.coefficient x y).variation Set.univ ≤ ENNReal.ofReal (‖x‖ * ‖y‖) := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  let a : H := ‖x‖⁻¹ • x
  let b : H := ‖y‖⁻¹ • y
  have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hny : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
  have ha : ‖a‖ = 1 := by simp [a, norm_smul, hnx]
  have hb : ‖b‖ = 1 := by simp [b, norm_smul, hny]
  have hc : E.coefficient x y = (‖x‖ * ‖y‖) • E.coefficient a b := by
    rw [mul_smul, ← E.coefficient_smul_right, ← E.coefficient_smul_left]
    simp [a, b, smul_smul, hnx, hny]
  rw [hc, VectorMeasure.variation_smul, Measure.smul_apply,
    Measure.nnreal_smul_coe_apply]
  have hv : (E.coefficient a b).variation Set.univ ≤ 1 := by
    simpa [ha, hb] using E.variation_quadratic a b
  calc
    _ ≤ (‖(‖x‖ * ‖y‖ : ℝ)‖₊ : ℝ≥0∞) * 1 := by gcongr
    _ = ENNReal.ofReal (‖x‖ * ‖y‖) := by
      rw [mul_one, ← enorm_eq_nnnorm, Real.enorm_eq_ofReal (mul_nonneg (norm_nonneg _) (norm_nonneg _))]

instance coefficient_variation_finite (x y : H) :
    IsFiniteMeasure (E.coefficient x y).variation :=
  ⟨(E.variation_bound x y).trans_lt ENNReal.ofReal_lt_top⟩

theorem coefficient_integrable (f : RealBoundedFunction S) (x y : H) :
    Integrable (f : S → ℝ) (E.coefficient x y).variation := by
  obtain ⟨C, _, hC⟩ := f.bounded
  exact Integrable.of_bound f.measurable.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun s => by simpa only [Real.norm_eq_abs] using hC s))


theorem coefficient_add_left (x z y : H) :
    E.coefficient (x + z) y = E.coefficient x y + E.coefficient z y := by
  ext B hB
  simp [E.coefficient_apply _ _ hB, inner_add_left]

theorem coefficient_add_right (x y z : H) :
    E.coefficient x (y + z) = E.coefficient x y + E.coefficient x z := by
  ext B hB
  simp [E.coefficient_apply _ _ hB, inner_add_right]

theorem coefficient_symm (x y : H) : E.coefficient x y = E.coefficient y x := by
  ext B hB
  rw [E.coefficient_apply _ _ hB, E.coefficient_apply _ _ hB,
    ← E.selfAdjoint B hB, real_inner_comm]

/-- Native integration against the signed coefficient measure. -/
def coefficientIntegral (f : RealBoundedFunction S) (x y : H) : ℝ :=
  (E.coefficient x y).integral f (ContinuousLinearMap.lsmul ℝ ℝ)

theorem coefficientIntegral_bound (f : RealBoundedFunction S) {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ s, |f s| ≤ C) (x y : H) :
    ‖E.coefficientIntegral f x y‖ ≤ C * ‖x‖ * ‖y‖ := by
  have h := VectorMeasure.norm_integral_le_of_norm_le_const
    (μ := E.coefficient x y) (B := ContinuousLinearMap.lsmul ℝ ℝ)
    (f := (f : S → ℝ)) (Filter.Eventually.of_forall (fun s => hf s))
  simp only [ContinuousLinearMap.opNorm_lsmul, mul_one] at h
  have hv : (E.coefficient x y).variation.real Set.univ ≤ ‖x‖ * ‖y‖ := by
    rw [measureReal_def]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (E.variation_bound x y)).trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  exact h.trans ((mul_le_mul_of_nonneg_left hv hC).trans_eq (mul_assoc _ _ _).symm)

/-- The integral coefficient form has precisely the real bilinearity required
by Riesz representation. Its bound is proved, rather than supplied as data. -/
def integralForm (f : RealBoundedFunction S) : H →L⋆[ℝ] H →L[ℝ] ℝ := by
  let A : H →ₗ⋆[ℝ] H →ₗ[ℝ] ℝ := LinearMap.mk₂'ₛₗ _ _
    (E.coefficientIntegral f)
    (fun x z y => by
      simp only [coefficientIntegral, E.coefficient_add_left]
      exact VectorMeasure.integral_add_vectorMeasure
        (E.coefficient_integrable f x y) (E.coefficient_integrable f z y))
    (fun c x y => by
      simp [coefficientIntegral, E.coefficient_smul_left,
        VectorMeasure.integral_smul_vectorMeasure])
    (fun x y z => by
      simp only [coefficientIntegral, E.coefficient_add_right]
      exact VectorMeasure.integral_add_vectorMeasure
        (E.coefficient_integrable f x y) (E.coefficient_integrable f x z))
    (fun c x y => by
      simp [coefficientIntegral, E.coefficient_smul_right,
        VectorMeasure.integral_smul_vectorMeasure])
  exact A.mkContinuous₂ f.bounded.choose
    (E.coefficientIntegral_bound f f.bounded.choose_spec.1 f.bounded.choose_spec.2)

@[simp] theorem integralForm_apply (f : RealBoundedFunction S) (x y : H) :
    E.integralForm f x y = E.coefficientIntegral f x y := by
  rfl

/-- Riesz constructs the operator; uniform simple approximation below also
characterizes it as the operator-norm limit specified by the manuscript. -/
def integral (f : RealBoundedFunction S) : H →L[ℝ] H :=
  (ExpandedFA.Hilbert.RieszRepresentation.form_representation ℝ H (E.integralForm f)).choose

theorem integral_coefficient (f : RealBoundedFunction S) (x y : H) :
    ⟪x, E.integral f y⟫_ℝ = E.coefficientIntegral f x y := by
  simpa only [integral, integralForm_apply] using
    ((ExpandedFA.Hilbert.RieszRepresentation.form_representation ℝ H
      (E.integralForm f)).choose_spec.1 x y).symm

theorem integral_bound (f : RealBoundedFunction S) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ s, |f s| ≤ C) : ‖E.integral f‖ ≤ C := by
  rw [integral, (ExpandedFA.Hilbert.RieszRepresentation.form_representation ℝ H
    (E.integralForm f)).choose_spec.2.1]
  exact (E.integralForm f).opNorm_le_bound₂ hC (by
    intro x y
    simpa only [E.integralForm_apply] using E.coefficientIntegral_bound f hC hf x y)

theorem integral_const (c : ℝ) : E.integral (.const c) = c • (1 : H →L[ℝ] H) := by
  ext y
  apply ext_inner_left ℝ
  intro x
  rw [E.integral_coefficient]
  simp [coefficientIntegral, RealBoundedFunction.const,
    E.coefficient_apply _ _ MeasurableSet.univ, E.univ, inner_smul_right]

theorem integral_add (f g : RealBoundedFunction S) :
    E.integral (.add f g) = E.integral f + E.integral g := by
  ext y
  apply ext_inner_left ℝ
  intro x
  simp only [E.integral_coefficient, add_apply, inner_add_right,
    coefficientIntegral, RealBoundedFunction.add]
  exact VectorMeasure.integral_fun_add (E.coefficient_integrable f x y)
    (E.coefficient_integrable g x y)

theorem integral_smul (c : ℝ) (f : RealBoundedFunction S) :
    E.integral (.smul c f) = c • E.integral f := by
  ext y
  apply ext_inner_left ℝ
  intro x
  simp only [E.integral_coefficient, smul_apply, inner_smul_right,
    coefficientIntegral, RealBoundedFunction.smul]
  exact VectorMeasure.integral_fun_smul _ _ c _

theorem integral_star (f : RealBoundedFunction S) : star (E.integral f) = E.integral f := by
  ext y
  apply ext_inner_left ℝ
  intro x
  change ⟪x, ContinuousLinearMap.adjoint (E.integral f) y⟫_ℝ = _
  rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm y (E.integral f x),
    E.integral_coefficient, E.integral_coefficient]
  simp only [coefficientIntegral, E.coefficient_symm x y]

theorem integral_indicator (B : Set S) (hB : MeasurableSet B) :
    E.integral (.indicator B hB) = E B := by
  ext y
  apply ext_inner_left ℝ
  intro x
  rw [E.integral_coefficient]
  change (E.coefficient x y).integral (B.indicator (fun _ => (1 : ℝ))) _ = _
  rw [VectorMeasure.integral_indicator_const 1 hB]
  simp [E.coefficient_apply _ _ hB]


/-- Equality of the Riesz realization with the full-fibre finite spectral sum. -/
theorem integral_simple (f : SimpleFunc S ℝ) :
    E.integral (.ofSimple f) = realSimpleSpectralIntegral E f := by
  classical
  ext y
  apply ext_inner_left ℝ
  intro x
  rw [E.integral_coefficient]
  have hrepr : (f : S → ℝ) = fun s =>
      ∑ c ∈ f.range, (f ⁻¹' {c}).indicator (fun _ => c) s := by
    funext s
    simp [Set.indicator, eq_comm, f.mem_range_self s]
  change (E.coefficient x y).integral (f : S → ℝ) _ = _
  rw [hrepr, VectorMeasure.integral_finsetSum]
  · simp only [realSimpleSpectralIntegral, sum_apply,
      inner_sum, smul_apply, inner_smul_right]
    apply Finset.sum_congr rfl
    intro c hc
    rw [VectorMeasure.integral_indicator_const c (f.measurableSet_fiber c)]
    simp [E.coefficient_apply _ _ (f.measurableSet_fiber c)]
  · intro c hc
    exact (integrable_const c).indicator (f.measurableSet_fiber c)

/-- The intersection law identifies the actual restricted signed measure. -/
theorem coefficient_project_right (x y : H) {B : Set S} (hB : MeasurableSet B) :
    E.coefficient x (E B y) = (E.coefficient x y).restrict B := by
  ext C hC
  rw [VectorMeasure.restrict_apply _ hB hC, E.coefficient_apply _ _ hC,
    E.coefficient_apply _ _ (hC.inter hB)]
  have hi := congrArg (fun T : H →L[ℝ] H => T y) (E.inter C B hC hB)
  change E C (E B y) = E (C ∩ B) y at hi
  rw [hi]

theorem integral_mul_indicator (f : RealBoundedFunction S) {B : Set S}
    (hB : MeasurableSet B) :
    E.integral (.mul f (.indicator B hB)) = E.integral f * E B := by
  ext y
  apply ext_inner_left ℝ
  intro x
  simp only [mul_apply_eq_comp, E.integral_coefficient, coefficientIntegral,
    E.coefficient_project_right x y hB]
  have heq : ((RealBoundedFunction.mul f (.indicator B hB)) : S → ℝ) =
      B.indicator f := by
    funext s
    by_cases hs : s ∈ B <;> simp [RealBoundedFunction.mul, RealBoundedFunction.indicator, hs]
  rw [heq, VectorMeasure.integral_indicator hB]


/-- Operator norm continuity for uniform convergence on the measurable base. -/
theorem integral_sub_bound (f g : RealBoundedFunction S) {C : ℝ} (hC : 0 ≤ C)
    (hfg : ∀ s, |f s - g s| ≤ C) : ‖E.integral f - E.integral g‖ ≤ C := by
  have h := E.integral_bound (.add f (.smul (-1) g)) hC (by
    intro s
    simpa [RealBoundedFunction.add, RealBoundedFunction.smul, sub_eq_add_neg] using hfg s)
  simpa [E.integral_add, E.integral_smul, sub_eq_add_neg] using h

theorem integral_tendsto_of_uniform (f : RealBoundedFunction S)
    (a : ℕ → RealBoundedFunction S)
    (ha : TendstoUniformly (fun n => (a n : S → ℝ)) f atTop) :
    Tendsto (fun n => E.integral (a n)) atTop (𝓝 (E.integral f)) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (Metric.tendstoUniformly_iff.1 ha (ε / 2) (half_pos hε))
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (E.integral_sub_bound _ _ (half_pos hε).le ?_) (half_lt_self hε)
  intro s
  simpa only [Real.dist_eq, abs_sub_comm] using (hN n hn s).le

theorem integral_uniform_limit (f : RealBoundedFunction S) (a : ℕ → SimpleFunc S ℝ)
    (ha : TendstoUniformly (fun n => (a n : S → ℝ)) f atTop) :
    Tendsto (fun n => realSimpleSpectralIntegral E (a n)) atTop (𝓝 (E.integral f)) := by
  simpa only [E.integral_simple] using
    E.integral_tendsto_of_uniform f (fun n => .ofSimple (a n)) ha

/-- The product law when the second factor is simple, from its fibre expansion. -/
theorem integral_mul_simple (f : RealBoundedFunction S) (g : SimpleFunc S ℝ) :
    E.integral (.mul f (.ofSimple g)) = E.integral f * E.integral (.ofSimple g) := by
  classical
  ext y
  apply ext_inner_left ℝ
  intro x
  rw [E.integral_coefficient, E.integral_simple]
  have hrepr : ((RealBoundedFunction.mul f (.ofSimple g)) : S → ℝ) =
      fun s => ∑ c ∈ g.range, c • (g ⁻¹' {c}).indicator f s := by
    funext s
    simp [RealBoundedFunction.mul, RealBoundedFunction.ofSimple,
      Set.indicator, eq_comm, g.mem_range_self s, mul_comm]
  unfold coefficientIntegral
  rw [hrepr, VectorMeasure.integral_finsetSum]
  · simp only [realSimpleSpectralIntegral, Finset.mul_sum, mul_smul_comm,
      sum_apply, smul_apply, mul_apply_eq_comp, inner_sum, inner_smul_right]
    apply Finset.sum_congr rfl
    intro c hc
    rw [VectorMeasure.integral_fun_smul, VectorMeasure.integral_indicator (g.measurableSet_fiber c),
      ← E.coefficient_project_right x y (g.measurableSet_fiber c)]
    change c * E.coefficientIntegral f x (E _ y) = _
    rw [← E.integral_coefficient]
  · intro c hc
    exact ((E.coefficient_integrable f x y).indicator (g.measurableSet_fiber c)).smul c

theorem integral_mul (f g : RealBoundedFunction S) :
    E.integral (.mul f g) = E.integral f * E.integral g := by
  let a : ℕ → RealBoundedFunction S := fun n => .ofSimple (g.floorApprox n)
  have ha : TendstoUniformly (fun n => (a n : S → ℝ)) g atTop :=
    g.tendstoUniformly_floorApprox
  have hmul : TendstoUniformly
      (fun n s => f s * a n s) (fun s => f s * g s) atTop := by
    apply Metric.tendstoUniformly_iff.2
    intro ε hε
    obtain ⟨C, hC, hf⟩ := f.bounded
    have hδ : 0 < ε / (C + 1) := div_pos hε (by linarith)
    filter_upwards [Metric.tendstoUniformly_iff.1 ha _ hδ] with n hn
    intro s
    rw [Real.dist_eq, ← mul_sub, abs_mul]
    have hg : |g s - a n s| < ε / (C + 1) := by
      simpa only [Real.dist_eq] using hn s
    calc
      |f s| * |g s - a n s| ≤ C * |g s - a n s| :=
        mul_le_mul_of_nonneg_right (hf s) (abs_nonneg _)
      _ < (C + 1) * (ε / (C + 1)) := by
        exact (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1)
          (abs_nonneg _)).trans_lt (mul_lt_mul_of_pos_left hg (by linarith))
      _ = ε := mul_div_cancel₀ ε (by linarith)
  have hleft := E.integral_tendsto_of_uniform (.mul f g) (fun n => .mul f (a n)) hmul
  have hright : Tendsto (fun n => E.integral f * E.integral (a n)) atTop
      (𝓝 (E.integral f * E.integral g)) :=
    tendsto_const_nhds.mul (E.integral_tendsto_of_uniform g a ha)
  have heq : (fun n => E.integral (.mul f (a n))) =
      (fun n => E.integral f * E.integral (a n)) := by
    funext n
    exact E.integral_mul_simple f (g.floorApprox n)
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright

/-- The signed diagonal integral is the ordinary integral for μ_x. -/
theorem coefficientIntegral_diagonal (f : RealBoundedFunction S) (x : H) :
    E.coefficientIntegral f x x = ∫ s, f s ∂(E.scalar x) := by
  unfold coefficientIntegral
  rw [E.coefficient_diagonal]
  have hflip : (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) =
      (ContinuousLinearMap.lsmul ℝ ℝ).flip := by
    apply ContinuousLinearMap.ext
    intro a
    apply ContinuousLinearMap.ext
    intro b
    exact mul_comm a b
  rw [hflip, VectorMeasure.integral_toSignedMeasure]

theorem integral_norm_square (f : RealBoundedFunction S) (x : H) :
    ‖E.integral f x‖ ^ 2 = ∫ s, |f s| ^ 2 ∂(E.scalar x) := by
  have hself (y z : H) : ⟪E.integral f y, z⟫_ℝ = ⟪y, E.integral f z⟫_ℝ := by
    simpa only [← ContinuousLinearMap.star_eq_adjoint, E.integral_star] using
      (ContinuousLinearMap.adjoint_inner_right (E.integral f) y z).symm
  rw [← real_inner_self_eq_norm_sq, hself, ← mul_apply_eq_comp, ← E.integral_mul,
    E.integral_coefficient, E.coefficientIntegral_diagonal]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun s => by
    change f s * f s = |f s| ^ 2
    rw [sq_abs, pow_two])


/-- The complete bounded realization, with no unbounded-calculus assumptions. -/
def boundedRealization : RealBoundedRealization E where
  coefficient := E.coefficient
  coefficient_apply := fun x y _ hB => E.coefficient_apply x y hB
  variation_bound := E.variation_bound
  scalar := E.scalar
  scalar_finite := E.scalar_finite
  scalar_apply := fun x _ hB => E.scalar_apply x hB
  scalar_mass := E.scalar_mass
  coefficient_diagonal := E.coefficient_diagonal
  integral := E.integral
  integral_const := E.integral_const
  integral_add := E.integral_add
  integral_smul := E.integral_smul
  integral_mul := E.integral_mul
  integral_star := E.integral_star
  integral_bound := fun f _ hC hf => E.integral_bound f hC hf
  integral_simple := E.integral_simple
  integral_indicator := E.integral_indicator
  simple_approximation := fun f => ⟨f.floorApprox, f.tendstoUniformly_floorApprox⟩
  integral_uniform_limit := E.integral_uniform_limit
  coefficient_integrable := E.coefficient_integrable
  coefficient_integral := E.integral_coefficient
  norm_square := E.integral_norm_square

end RealProjectionValuedMeasure

namespace RealDefinitions

/-- The full finite-fibre sum, with an independent value binding. The shared
canonical PVM and realization types themselves are defined in the Specs. -/
def simpleIntegral : Spec.SimpleIntegralType.{u, v} :=
  fun _ _ _ _ _ _ E f => ∑ c ∈ f.range, c • E (f ⁻¹' {c})

theorem projection_properties_for : Spec.ProjectionPropertiesFor (S := S) (H := H) := by
  intro E
  exact ⟨E.empty, fun _ hB => ⟨E.idempotent hB, E.star_eq hB⟩,
    fun _ hB => E.norm_le_one hB,
    fun _ _ hB hC hd x y => E.disjoint_orthogonal hB hC hd x y⟩


/-- For an orthogonal series ordered norm convergence is equivalent to
unconditional convergence. No countable-additivity hypothesis is used here. -/
theorem countable_additivity_equivalence :
    Spec.CountableAdditivityEquivalence (S := S) (H := H) := by
  intro P hself hinter hempty B hB hd x
  constructor
  · exact HasSum.tendsto_sum_nat
  intro h
  let G (n : ℕ) : Type v := (P (B n)).range
  let V (n : ℕ) : G n →ₗᵢ[ℝ] H := (P (B n)).range.subtypeₗᵢ
  have hV : OrthogonalFamily ℝ G V := by
    intro i j hij a b
    obtain ⟨a', ha⟩ := a.property
    obtain ⟨b', hb⟩ := b.property
    change ⟪(a : H), (b : H)⟫_ℝ = 0
    rw [← ha, ← hb]
    change ⟪P (B i) a', P (B j) b'⟫_ℝ = 0
    rw [hself _ (hB i)]
    have hp : P (B i) (P (B j) b') = 0 := by
      have := congrArg (fun T : H →L[ℝ] H => T b') (hinter _ _ (hB i) (hB j))
      simpa only [mul_apply_eq_comp, (hd hij).inter_eq, hempty,
        zero_apply] using this
    rw [hp, inner_zero_right]
  let a (n : ℕ) : G n := ⟨P (B n) x, ⟨x, rfl⟩⟩
  have hs : HasSum (fun n => ‖a n‖ ^ 2) (‖P (⋃ n, B n) x‖ ^ 2) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => sq_nonneg ‖a n‖) _).2
    have ht := h.norm.pow 2
    convert ht using 1
    ext N
    exact (hV.norm_sum a (Finset.range N)).symm
  have hvsum := (hV.summable_iff_norm_sq_summable a).2 hs.summable
  have hv : Summable (fun n => P (B n) x) := hvsum
  have heq := tendsto_nhds_unique hv.hasSum.tendsto_sum_nat h
  exact heq ▸ hv.hasSum


theorem ordered_additivity_equivalence_for :
    Spec.OrderedAdditivityEquivalenceFor (S := S) (H := H) := by
  intro P hself hinter
  constructor
  · intro h B hB hd x
    exact (h B hB hd x).tendsto_sum_nat
  intro h
  have hempty : P ∅ = 0 := by
    ext x
    have ht := h (fun _ => ∅) (fun _ => MeasurableSet.empty)
      (fun _ _ _ => by simp) x
    simp only [Set.iUnion_empty] at ht
    have hs := (Filter.tendsto_add_atTop_iff_nat 1).2 ht
    have hz : Tendsto (fun _ : ℕ => P ∅ x) atTop (𝓝 (0 : H)) := by
      simpa only [Finset.sum_range_succ, add_sub_cancel_left, sub_self] using hs.sub ht
    exact tendsto_nhds_unique tendsto_const_nhds hz
  intro B hB hd x
  exact (countable_additivity_equivalence P hself hinter hempty B hB hd x).2 (h B hB hd x)

theorem bounded_realization_exists_for : Spec.BoundedRealizationExistsFor (S := S) (H := H) := by
  intro E
  exact ⟨E.boundedRealization⟩


theorem projection_properties : Spec.ProjectionProperties.{u, v} := by
  intro S H _ _ _ _
  exact projection_properties_for (S := S) (H := H)

theorem ordered_additivity_equivalence : Spec.OrderedAdditivityEquivalence.{u, v} := by
  intro S H _ _ _ _
  exact ordered_additivity_equivalence_for (S := S) (H := H)

theorem bounded_realization_exists : Spec.BoundedRealizationExists.{u, v} := by
  intro S H _ _ _ _
  exact bounded_realization_exists_for (S := S) (H := H)

end RealDefinitions
end ExpandedFA.SpectralMeasure
