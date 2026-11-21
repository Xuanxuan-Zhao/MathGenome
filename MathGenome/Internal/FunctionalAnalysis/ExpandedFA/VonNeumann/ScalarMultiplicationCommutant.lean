import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.VonNeumann.ScalarMultiplicationCommutant
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace

namespace ExpandedFA.VonNeumann.ScalarMultiplicationCommutant
universe v u
variable {𝕜 : Type v} [RCLike 𝕜]
variable {X : Type u} [MeasurableSpace X] (μ : Measure X)

lemma multiplier_apply (h : Lp 𝕜 ∞ μ) (f : Lp 𝕜 2 μ) :
    Spec.multiplier (𝕜 := 𝕜) μ h f =ᵐ[μ] fun x => h x * f x := by
  simpa only [Spec.multiplier, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply'] using
    (ContinuousLinearMap.mul 𝕜 𝕜).coeFn_holder (r := 2) h f

lemma multiplier_norm_le (h : Lp 𝕜 ∞ μ) : ‖Spec.multiplier (𝕜 := 𝕜) μ h‖ ≤ ‖h‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg h)
  intro f
  exact (ContinuousLinearMap.mul 𝕜 𝕜).norm_holder_apply_apply_le h f |>.trans_eq
    (by simp)

lemma multipliers_commute (h g : Lp 𝕜 ∞ μ) :
    (Spec.multiplier (𝕜 := 𝕜) μ h).comp (Spec.multiplier (𝕜 := 𝕜) μ g) =
      (Spec.multiplier (𝕜 := 𝕜) μ g).comp (Spec.multiplier (𝕜 := 𝕜) μ h) := by
  ext f : 1
  apply Lp.ext
  filter_upwards [multiplier_apply μ h (Spec.multiplier (𝕜 := 𝕜) μ g f),
    multiplier_apply μ g (Spec.multiplier (𝕜 := 𝕜) μ h f),
    multiplier_apply μ g f, multiplier_apply μ h f] with x hx₁ hx₂ hx₃ hx₄
  simp only [ContinuousLinearMap.comp_apply]
  rw [hx₁, hx₂, hx₃, hx₄]
  ring

/-- A measurable indicator as an L∞ coefficient; the set need not have finite measure. -/
def boundedIndicator {s : Set X} (hs : MeasurableSet s) : Lp 𝕜 ∞ μ :=
  (memLp_top_of_bound (stronglyMeasurable_const.indicator hs).aestronglyMeasurable
    1 (Eventually.of_forall fun x => by
      by_cases hx : x ∈ s <;> simp [hx])).toLp (s.indicator fun _ => (1 : 𝕜))

lemma boundedIndicator_apply {s : Set X} (hs : MeasurableSet s) :
    boundedIndicator (𝕜 := 𝕜) μ hs =ᵐ[μ] s.indicator (fun _ => (1 : 𝕜)) :=
  MemLp.coeFn_toLp _

lemma indicator_multiplier_apply {s : Set X} (hs : MeasurableSet s) (f : Lp 𝕜 2 μ) :
    Spec.multiplier (𝕜 := 𝕜) μ (boundedIndicator (𝕜 := 𝕜) μ hs) f =ᵐ[μ] s.indicator f := by
  filter_upwards [multiplier_apply μ (boundedIndicator (𝕜 := 𝕜) μ hs) f,
    boundedIndicator_apply (𝕜 := 𝕜) μ hs] with x hx hi
  rw [hx, hi]
  by_cases hxs : x ∈ s <;> simp [hxs]

lemma l2_norm_sq (f : Lp 𝕜 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜), L2.inner_def,
    ← integral_re (L2.integrable_inner f f)]
  congr 1
  funext x
  exact inner_self_eq_norm_sq (𝕜 := 𝕜) (f x)

lemma integrable_norm_sq (f : Lp 𝕜 2 μ) : Integrable (fun x => ‖f x‖ ^ 2) μ := by
  simpa only [inner_self_eq_norm_sq (𝕜 := 𝕜)] using (L2.integrable_inner (𝕜 := 𝕜) f f).re

/-- Comparing all finite-set localizations compares the pointwise norms.
This uses only scalar integration and works for arbitrary measures. -/
lemma ae_norm_le_of_localized_norm_le (f g : Lp 𝕜 2 μ)
    (h : ∀ (s : Set X) (hs : MeasurableSet s), μ s < ∞ →
      ‖Spec.multiplier (𝕜 := 𝕜) μ (boundedIndicator (𝕜 := 𝕜) μ hs) f‖ ≤
        ‖Spec.multiplier (𝕜 := 𝕜) μ (boundedIndicator (𝕜 := 𝕜) μ hs) g‖) :
    ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖ := by
  have hf := integrable_norm_sq μ f
  have hg := integrable_norm_sq μ g
  have hh : ∀ᵐ x ∂μ, ‖f x‖ ^ 2 ≤ ‖g x‖ ^ 2 := by
    apply ae_le_of_forall_setIntegral_le hf hg
    intro s hs hμs
    have hid (v : Lp 𝕜 2 μ) :
        ‖Spec.multiplier (𝕜 := 𝕜) μ (boundedIndicator (𝕜 := 𝕜) μ hs) v‖ ^ 2 =
          ∫ x in s, ‖v x‖ ^ 2 ∂μ := by
      rw [l2_norm_sq]
      rw [← integral_indicator hs]
      apply integral_congr_ae
      filter_upwards [indicator_multiplier_apply μ hs v] with x hx
      rw [hx]
      by_cases hxs : x ∈ s <;> simp [hxs]
    rw [← hid f, ← hid g]
    exact pow_le_pow_left₀ (norm_nonneg _) (h s hs hμs) 2
  filter_upwards [hh] with x hx
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hx

/-- A module operator is bounded pointwise by its operator norm. -/
lemma commuting_pointwise_bound (T : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ)
    (hT : Spec.CommutesWithMultipliers μ T) (f : Lp 𝕜 2 μ) :
    ∀ᵐ x ∂μ, ‖T f x‖ ≤ ‖T‖ * ‖f x‖ := by
  have hh := ae_norm_le_of_localized_norm_le μ (T f) ((‖T‖ : 𝕜) • f) (by
    intro s hs _
    have hc := congrArg (fun A : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ => A f)
      (hT (boundedIndicator (𝕜 := 𝕜) μ hs))
    simp only [ContinuousLinearMap.comp_apply] at hc
    rw [← hc, map_smul, norm_smul]
    simpa using T.le_opNorm (Spec.multiplier (𝕜 := 𝕜) μ (boundedIndicator (𝕜 := 𝕜) μ hs) f))
  filter_upwards [hh, Lp.coeFn_smul (‖T‖ : 𝕜) f] with x hx hc
  simpa only [hc, Pi.smul_apply, norm_smul, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg T)] using hx

/-- An indicator vector for a set of finite measure. -/
abbrev chi {s : Set X} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) : Lp 𝕜 2 μ :=
  indicatorConstLp 2 hs hμs (1 : 𝕜)

lemma chi_apply {s : Set X} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    chi (𝕜 := 𝕜) μ hs hμs =ᵐ[μ] s.indicator (fun _ => (1 : 𝕜)) :=
  indicatorConstLp_coeFn

lemma localize_chi_swap {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) :
    Spec.multiplier (𝕜 := 𝕜) μ (boundedIndicator (𝕜 := 𝕜) μ hs) (chi (𝕜 := 𝕜) μ ht hμt) =
      Spec.multiplier (𝕜 := 𝕜) μ (boundedIndicator (𝕜 := 𝕜) μ ht) (chi (𝕜 := 𝕜) μ hs hμs) := by
  apply Lp.ext
  filter_upwards [indicator_multiplier_apply μ hs (chi (𝕜 := 𝕜) μ ht hμt),
    indicator_multiplier_apply μ ht (chi (𝕜 := 𝕜) μ hs hμs), chi_apply (𝕜 := 𝕜) μ hs hμs,
    chi_apply (𝕜 := 𝕜) μ ht hμt] with x hx₁ hx₂ hx₃ hx₄
  rw [hx₁, hx₂]
  by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;> simp [hxs, hxt, hx₃, hx₄]

lemma commuting_chi_swap (T : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ)
    (hT : Spec.CommutesWithMultipliers μ T)
    {s t : Set X} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞) :
    Spec.multiplier (𝕜 := 𝕜) μ (boundedIndicator (𝕜 := 𝕜) μ hs) (T (chi (𝕜 := 𝕜) μ ht hμt)) =
      Spec.multiplier (𝕜 := 𝕜) μ (boundedIndicator (𝕜 := 𝕜) μ ht) (T (chi (𝕜 := 𝕜) μ hs hμs)) := by
  have hc (v : Lp 𝕜 2 μ) {b : Set X} (hb : MeasurableSet b) :=
    congrArg (fun A : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ => A v)
      (hT (boundedIndicator (𝕜 := 𝕜) μ hb))
  simp only [ContinuousLinearMap.comp_apply] at hc
  rw [← hc, ← hc, localize_chi_swap μ hs ht hμs hμt]

/-- The finite-piece coefficient, with a uniform bound independent of the piece. -/
lemma commuting_chi_bound (T : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ)
    (hT : Spec.CommutesWithMultipliers μ T)
    {s : Set X} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    ∀ᵐ x ∂μ, ‖T (chi (𝕜 := 𝕜) μ hs hμs) x‖ ≤ ‖T‖ := by
  filter_upwards [commuting_pointwise_bound μ T hT (chi (𝕜 := 𝕜) μ hs hμs),
    chi_apply (𝕜 := 𝕜) μ hs hμs] with x hx hc
  apply hx.trans
  rw [hc]
  by_cases hxs : x ∈ s <;> simp [hxs]

section SigmaFinite
variable [SigmaFinite μ]

/-- Glue the finite-piece coefficients along a measurable finite-measure cover. -/
def coefficient (T : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ) (x : X) : 𝕜 :=
  T (chi (𝕜 := 𝕜) μ (measurableSet_spanningSets μ (spanningSetsIndex μ x))
    (measure_spanningSets_lt_top μ (spanningSetsIndex μ x)).ne) x

lemma coefficient_measurable (T : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ) :
    Measurable (coefficient μ T) := by
  classical
  let f : ℕ → X → 𝕜 := fun n => T (chi (𝕜 := 𝕜) μ (measurableSet_spanningSets μ n)
    (measure_spanningSets_lt_top μ n).ne)
  have hm (n : ℕ) : Measurable (f n) :=
    (Lp.stronglyMeasurable (T (chi (𝕜 := 𝕜) μ (measurableSet_spanningSets μ n)
      (measure_spanningSets_lt_top μ n).ne))).measurable
  exact Measurable.find (f := f) (p := fun n x => x ∈ spanningSets μ n)
    hm (measurableSet_spanningSets μ) (iUnion_eq_univ_iff.mp (iUnion_spanningSets μ))

lemma coefficient_bound (T : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ)
    (hT : Spec.CommutesWithMultipliers μ T) :
    ∀ᵐ x ∂μ, ‖coefficient μ T x‖ ≤ ‖T‖ := by
  have hh : ∀ᵐ x ∂μ, ∀ n : ℕ,
      ‖T (chi (𝕜 := 𝕜) μ (measurableSet_spanningSets μ n)
        (measure_spanningSets_lt_top μ n).ne) x‖ ≤ ‖T‖ :=
    ae_all_iff.mpr fun n => commuting_chi_bound μ T hT _ _
  exact hh.mono fun x hx => hx (spanningSetsIndex μ x)

/-- The glued coefficient is an actual L∞ equivalence class. -/
def coefficientLp (T : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ)
    (hT : Spec.CommutesWithMultipliers μ T) : Lp 𝕜 ∞ μ :=
  (memLp_top_of_bound (coefficient_measurable μ T).aestronglyMeasurable ‖T‖
    (coefficient_bound μ T hT)).toLp (coefficient μ T)

lemma coefficientLp_apply (T : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ)
    (hT : Spec.CommutesWithMultipliers μ T) :
    coefficientLp μ T hT =ᵐ[μ] coefficient μ T := MemLp.coeFn_toLp _

lemma coefficient_represents_chi (T : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ)
    (hT : Spec.CommutesWithMultipliers μ T)
    {s : Set X} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    T (chi (𝕜 := 𝕜) μ hs hμs) = Spec.multiplier (𝕜 := 𝕜) μ (coefficientLp μ T hT) (chi (𝕜 := 𝕜) μ hs hμs) := by
  have hloc (n : ℕ) : ∀ᵐ x ∂μ, x ∈ spanningSets μ n →
      T (chi (𝕜 := 𝕜) μ hs hμs) x =
        s.indicator (T (chi (𝕜 := 𝕜) μ (measurableSet_spanningSets μ n)
          (measure_spanningSets_lt_top μ n).ne)) x := by
    have he := commuting_chi_swap μ T hT (measurableSet_spanningSets μ n) hs
      (measure_spanningSets_lt_top μ n).ne hμs
    filter_upwards [indicator_multiplier_apply μ (measurableSet_spanningSets μ n)
      (T (chi (𝕜 := 𝕜) μ hs hμs)),
      indicator_multiplier_apply μ hs
        (T (chi (𝕜 := 𝕜) μ (measurableSet_spanningSets μ n)
          (measure_spanningSets_lt_top μ n).ne))] with x hx hy hxn
    rw [he] at hx
    simpa only [Set.indicator_of_mem hxn] using hx.symm.trans hy
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr hloc, coefficientLp_apply μ T hT,
    multiplier_apply μ (coefficientLp μ T hT) (chi (𝕜 := 𝕜) μ hs hμs),
    chi_apply (𝕜 := 𝕜) μ hs hμs] with x hlocx hh hm hc
  rw [hm, hh, hc, hlocx (spanningSetsIndex μ x) (mem_spanningSetsIndex μ x)]
  by_cases hxs : x ∈ s <;> simp [hxs, coefficient]

/-- Density of finite-measure simple functions extends the local identity to L². -/
lemma coefficient_represents (T : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ)
    (hT : Spec.CommutesWithMultipliers μ T) :
    T = Spec.multiplier (𝕜 := 𝕜) μ (coefficientLp μ T hT) := by
  ext f : 1
  apply Lp.induction (by simp : (2 : ℝ≥0∞) ≠ ∞)
    (fun f => T f = Spec.multiplier (𝕜 := 𝕜) μ (coefficientLp μ T hT) f)
  · intro c s hs hμs
    simp only [Lp.simpleFunc.coe_indicatorConst]
    have he : indicatorConstLp 2 hs hμs.ne c = c • chi (𝕜 := 𝕜) μ hs hμs.ne := by
      apply Lp.ext
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs.ne) (c := c),
        Lp.coeFn_smul c (chi (𝕜 := 𝕜) μ hs hμs.ne), chi_apply (𝕜 := 𝕜) μ hs hμs.ne] with x hc hm hχ
      rw [hc, hm]
      by_cases hxs : x ∈ s <;> simp [hxs, hχ]
    rw [he, map_smul, map_smul, coefficient_represents_chi (𝕜 := 𝕜) μ T hT hs hμs.ne]
  · intro f g hf hg _ hfe hge
    simp only [map_add, hfe, hge]
  · exact isClosed_eq T.continuous (Spec.multiplier (𝕜 := 𝕜) μ (coefficientLp μ T hT)).continuous

omit [SigmaFinite μ] in
lemma norm_top_le_of_bound (h : Lp 𝕜 ∞ μ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ x ∂μ, ‖h x‖ ≤ C) : ‖h‖ ≤ C := by
  have he : eLpNorm h ∞ μ ≤ ENNReal.ofReal C := by
    rw [eLpNorm_exponent_top (Lp.aestronglyMeasurable h)]
    exact eLpNormEssSup_le_of_ae_bound hb
  calc
    ‖h‖ = (eLpNorm h ∞ μ).toReal := Lp.norm_def _
    _ ≤ (ENNReal.ofReal C).toReal := ENNReal.toReal_mono (by finiteness) he
    _ = C := ENNReal.toReal_ofReal hC

lemma multiplier_norm (h : Lp 𝕜 ∞ μ) : ‖Spec.multiplier (𝕜 := 𝕜) μ h‖ = ‖h‖ := by
  apply le_antisymm (multiplier_norm_le μ h)
  apply norm_top_le_of_bound μ h (norm_nonneg _)
  have hb (n : ℕ) : ∀ᵐ x ∂μ, x ∈ spanningSets μ n →
      ‖h x‖ ≤ ‖Spec.multiplier (𝕜 := 𝕜) μ h‖ := by
    let f := chi (𝕜 := 𝕜) μ (measurableSet_spanningSets μ n)
      (measure_spanningSets_lt_top μ n).ne
    have hc : Spec.CommutesWithMultipliers μ (Spec.multiplier (𝕜 := 𝕜) μ h) :=
      fun g => multipliers_commute μ h g
    filter_upwards [commuting_pointwise_bound μ (Spec.multiplier (𝕜 := 𝕜) μ h) hc f,
      multiplier_apply μ h f, chi_apply (𝕜 := 𝕜) μ (measurableSet_spanningSets μ n)
        (measure_spanningSets_lt_top μ n).ne] with x hx hm hf hxn
    change f x = _ at hf
    rw [hf, Set.indicator_of_mem hxn] at hx hm
    simpa [hm] using hx
  filter_upwards [ae_all_iff.mpr hb] with x hx
  exact hx (spanningSetsIndex μ x) (mem_spanningSetsIndex μ x)

lemma multiplier_injective : Function.Injective (Spec.multiplier (𝕜 := 𝕜) μ) := by
  intro h g he
  have hz : Spec.multiplier (𝕜 := 𝕜) μ (h - g) = 0 := by
    simpa only [Spec.multiplier, map_sub, sub_eq_zero] using he
  have hn : ‖h - g‖ = 0 := by rw [← multiplier_norm μ, hz, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- The sigma-finite scalar multiplication algebra is its own commutant. -/
theorem sigmaFinite_commutant : Spec.SigmaFiniteCommutant.{v, u} := by
  intro 𝕜 _ X _ μ _ T hT
  refine ⟨coefficientLp μ T hT, ⟨coefficient_represents μ T hT, ?_⟩, ?_⟩
  · exact (congrArg norm (coefficient_represents μ T hT)).trans
      (multiplier_norm μ (coefficientLp μ T hT))
  · intro g hg
    apply multiplier_injective μ
    exact hg.1.symm.trans (coefficient_represents μ T hT)

/-- The original finite-measure statement, including zero mass. -/
theorem finite_commutant : Spec.FiniteCommutant.{v, u} := by
  intro 𝕜 _ X _ μ _ T hT
  exact sigmaFinite_commutant 𝕜 X μ T hT

/-- Conversely all scalar multiplications commute, and the representation is isometric. -/
theorem multiplication_properties : Spec.MultiplicationProperties.{v, u} := by
  intro 𝕜 _ X _ μ _ h
  exact ⟨fun g => multipliers_commute μ h g, multiplier_norm μ h⟩

end SigmaFinite

end ExpandedFA.VonNeumann.ScalarMultiplicationCommutant
