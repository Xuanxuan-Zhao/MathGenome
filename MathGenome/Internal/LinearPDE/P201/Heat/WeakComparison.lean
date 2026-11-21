import MathGenome.Internal.LinearPDE.P201Specs.Heat.WeakComparison
import MathGenome.Internal.LinearPDE.P201.Heat.OrderedTraceChain
import MathGenome.Internal.FourierSobolev.P102.U4.SlabPoincare
import Mathlib.MeasureTheory.Measure.SeparableMeasure

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
namespace P201.Heat.WeakComparison
open P201Specs.Heat.WeakComparison
open P201Specs.OrderedTraceChain

lemma matrixAction_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (ξ : Space n) (i : Fin n) :
    matrixAction A ξ i = ∑ j, A i j * ξ j := rfl

lemma matrix_form : MatrixFormStatement := by
  intro n Ω A u v
  apply integral_congr_ae
  filter_upwards [Truncation.gradient_ae Ω u, Truncation.gradient_ae Ω v] with x hu hv
  change inner ℝ (matrixAction (A x) (hGradient u x)) (hGradient v x) =
    ∑ i, ∑ j, A x i j * hFirstDerivative u j x * star (hFirstDerivative v i x)
  rw [hu, hv, PiLp.inner_apply]
  simp only [RCLike.inner_apply, matrixAction_apply, starRingEnd_apply, star_trivial,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

def gradientCLM {n : ℕ} (Ω : Domain n) :
    H ℝ Ω 1 →L[ℝ] MeasureTheory.Lp (Space n) 2 (domainMeasure Ω) :=
  P102.U4.SlabPoincareProof.sobolevGradientCLM.comp (hToW ℝ Ω 1).toContinuousLinearMap

@[simp] lemma gradientCLM_apply {n : ℕ} (Ω : Domain n) (u : H ℝ Ω 1) :
    gradientCLM Ω u = hGradient u := by
  simp only [gradientCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, P102.U4.SlabPoincareProof.sobolevGradientCLM_apply]
  rfl

lemma form_representation {n : ℕ} (Ω : Domain n)
    (A : Space n → Space n →L[ℝ] Space n)
    (hm : AEStronglyMeasurable A (domainMeasure Ω)) (M : ℝ)
    (hb : ∀ᵐ x ∂domainMeasure Ω, ‖A x‖ ≤ M) :
    ∃ F : H ℝ Ω 1 →L[ℝ] MeasureTheory.Lp (Space n) 2 (domainMeasure Ω),
      ∀ u v, form Ω A u v = inner ℝ (F u) (gradientCLM Ω v) := by
  let hA := memLp_top_of_bound hm M hb
  let B := ContinuousLinearMap.id ℝ (Space n →L[ℝ] Space n)
  let F := (B.holderL (domainMeasure Ω) ∞ 2 2 (hA.toLp A)).comp (gradientCLM Ω)
  refine ⟨F, fun u v => ?_⟩
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  have he : (F u : Space n → Space n) =ᵐ[domainMeasure Ω]
      fun x => A x (hGradient u x) := by
    have hf := B.coeFn_holder (r := 2) (hA.toLp A) (gradientCLM Ω u)
    filter_upwards [hf, hA.coeFn_toLp] with x hx ha
    simpa only [F, ContinuousLinearMap.comp_apply, ContinuousLinearMap.holderL_apply_apply,
      gradientCLM_apply, ha, B, ContinuousLinearMap.id_apply] using hx
  filter_upwards [he] with x hx
  simp only [hx, gradientCLM_apply]

lemma form_continuous_test {n : ℕ} (Ω : Domain n)
    (A : Space n → Space n →L[ℝ] Space n)
    (hm : AEStronglyMeasurable A (domainMeasure Ω)) (M : ℝ)
    (hb : ∀ᵐ x ∂domainMeasure Ω, ‖A x‖ ≤ M) (u : H ℝ Ω 1) :
    Continuous (fun η : H10 ℝ Ω => form Ω A u η.val) := by
  obtain ⟨F, hF⟩ := form_representation Ω A hm M hb
  simp_rw [hF]
  exact continuous_const.inner ((gradientCLM Ω).continuous.comp continuous_subtype_val)

lemma form_sub_left {n : ℕ} (Ω : Domain n)
    (A : Space n → Space n →L[ℝ] Space n)
    (hm : AEStronglyMeasurable A (domainMeasure Ω)) (M : ℝ)
    (hb : ∀ᵐ x ∂domainMeasure Ω, ‖A x‖ ≤ M) (u v z : H ℝ Ω 1) :
    form Ω A (u - v) z = form Ω A u z - form Ω A v z := by
  obtain ⟨F, hF⟩ := form_representation Ω A hm M hb
  simp only [hF, map_sub, inner_sub_left]

/-- Countably many closed inequalities suffice on the separable nonnegative
cone, even when the original exceptional set depends on the fixed test. -/
theorem common_exceptional_set : CommonExceptionalSetStatement := by
  intro n Ω T A ν hA w dw
  constructor
  · intro hf
    let C := {η : H10 ℝ Ω | Nonnegative Ω η}
    letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
    have : SecondCountableTopology (H10 ℝ Ω) := by
      change SecondCountableTopology ↥(P201Specs.hZeroSubmodule ℝ Ω)
      infer_instance
    obtain ⟨D, hD, hd⟩ := TopologicalSpace.exists_countable_dense C
    letI : Countable D := hD.to_subtype
    have heach (η : D) : ∀ᵐ t ∂timeMeasure T,
        dw t η.val.val + form Ω (A t) (w t) η.val.val.val ≤ 0 :=
      hf η.val.val η.val.property
    have hall := ae_all_iff.mpr heach
    obtain ⟨hν, hm, M, hM, hb⟩ := hA
    filter_upwards [hall, hm.prodMk_left, Measure.ae_ae_of_ae_prod hb] with t ht hmt hbt
    intro η hη
    have hc : Continuous (fun ζ : C =>
        dw t ζ.val + form Ω (A t) (w t) ζ.val.val) :=
      ((dw t).continuous.add (form_continuous_test Ω (A t) hmt M
        (hbt.mono fun _ hx => hx.1) (w t))).comp continuous_subtype_val
    have hclosed : IsClosed {ζ : C | dw t ζ.val + form Ω (A t) (w t) ζ.val.val ≤ 0} :=
      isClosed_le hc continuous_const
    have hsub : D ⊆ {ζ : C | dw t ζ.val + form Ω (A t) (w t) ζ.val.val ≤ 0} :=
      fun ζ hζ => ht ⟨ζ, hζ⟩
    exact closure_minimal hsub hclosed (hd ⟨η, hη⟩)
  · intro h η hη
    exact h.mono fun t ht => ht η hη

/-- Spatial locality: the positive cutoff can be moved from the test gradient
onto both factors, with no symmetry of the coefficient. -/
theorem form_positivePart {n : ℕ} (Ω : Domain n)
    (A : Space n → Space n →L[ℝ] Space n) (u : H ℝ Ω 1) :
    form Ω A u (Truncation.positivePart Ω u) =
      form Ω A (Truncation.positivePart Ω u) (Truncation.positivePart Ω u) := by
  apply integral_congr_ae
  filter_upwards [(Truncation.positivePart_formula Ω u).2] with x hx
  rw [hx]
  split_ifs <;> simp

/-- Ellipticity is used on the actual truncated spatial gradient. -/
theorem form_positivePart_nonneg {n : ℕ} (Ω : Domain n)
    (A : Space n → Space n →L[ℝ] Space n) (ν : ℝ) (hν : 0 ≤ ν)
    (hA : ∀ᵐ x ∂domainMeasure Ω, ∀ ξ : Space n,
      ν * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ) (u : H ℝ Ω 1) :
    0 ≤ form Ω A u (Truncation.positivePart Ω u) := by
  rw [form_positivePart]
  apply integral_nonneg_of_ae
  filter_upwards [hA] with x hx
  exact (mul_nonneg hν (sq_nonneg _)).trans (hx _)

lemma positiveL2_eq_zero_iff {n : ℕ} (Ω : Domain n) (f : Lp ℝ Ω 2) :
    P201Specs.OrderedTraceChain.positiveL2 Ω f = 0 ↔
      ∀ᵐ x ∂domainMeasure Ω, f x ≤ 0 := by
  constructor
  · intro h
    have he := MeasureTheory.Lp.ext_iff.mp h
    filter_upwards [he, MeasureTheory.Lp.coeFn_posPart f,
      MeasureTheory.Lp.coeFn_zero ℝ 2 (domainMeasure Ω)] with x hx hp hz
    have : max (f x) 0 = 0 := hp.symm.trans (hx.trans hz)
    exact (le_max_left _ _).trans_eq this
  · intro h
    apply MeasureTheory.Lp.ext
    filter_upwards [h, MeasureTheory.Lp.coeFn_posPart f,
      MeasureTheory.Lp.coeFn_zero ℝ 2 (domainMeasure Ω)] with x hx hp hz
    simp only [hp, hz, Pi.zero_apply, max_eq_right hx]

/-- The energy argument for the difference itself. -/
theorem difference_comparison : DifferenceStatement := by
  intro m Ω hΩ tr htr T hT A ν hA w dw W hw htrace hinit hineq t ht
  obtain ⟨hν, hmeas, M, hM, hbounds⟩ := hA
  have hell : ∀ᵐ r ∂timeMeasure T, ∀ᵐ x ∂domainMeasure Ω,
      ∀ ξ : Space (m + 1), ν * ‖ξ‖ ^ 2 ≤ inner ℝ (A r x ξ) ξ :=
    (Measure.ae_ae_of_ae_prod hbounds).mono fun r hr => hr.mono fun x hx => hx.2
  have hmem := P201.OrderedTraceChain.membership Ω hΩ tr htr T w dw W
    hw.spatial hw.derivative hw.continuous hw.representative htrace
  have hsign : ∀ᵐ r ∂timeMeasure T, dw r (zeroPositive Ω (w r)) ≤ 0 := by
    filter_upwards [hineq, hell, hmem.2.1] with r hi he hp
    have hn : Nonnegative Ω (zeroPositive Ω (w r)) := by
      change ∀ᵐ x ∂domainMeasure Ω,
        0 ≤ hUnderlying Ω 1 ((zeroPositive Ω (w r)).val) x
      rw [hp]
      filter_upwards [Truncation.positivePart_underlying Ω (w r)] with x hx
      rw [hx]
      exact le_max_right _ _
    have hi' := hi _ hn
    have hf : 0 ≤ form Ω (A r) (w r) (zeroPositive Ω (w r)).val := by
      rw [hp]
      exact form_positivePart_nonneg Ω (A r) ν hν.le he (w r)
    linarith
  have hrestrict : volume.restrict (Ioc 0 t) ≤ timeMeasure T := by
    unfold timeMeasure
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact Measure.restrict_mono (Ioo_subset_Ioo le_rfl ht.2) le_rfl
  have hnonpos : (∫ r in Ioc 0 t, dw r (zeroPositive Ω (w r))) ≤ 0 :=
    integral_nonpos_of_ae (hsign.filter_mono (ae_mono hrestrict))
  have he := P201.OrderedTraceChain.full_chain_rule.2 Ω hΩ tr htr T hT w dw W
    hw.spatial hw.derivative hw.continuous hw.representative hw.distributional htrace
    0 t le_rfl ht.1 ht.2
  have hzero := (positiveL2_eq_zero_iff Ω (W 0)).mpr hinit
  rw [hzero, norm_zero, zero_pow (by decide), mul_zero, sub_zero] at he
  have hz : P201Specs.OrderedTraceChain.positiveL2 Ω (W t) = 0 := by
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (P201Specs.OrderedTraceChain.positiveL2 Ω (W t)), he, hnonpos]
  exact (positiveL2_eq_zero_iff Ω (W t)).mp hz

lemma integrable_mul_compact {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [BorelSpace X] {μ : Measure X} (f g : X → ℝ)
    (hf : Continuous f) (hfc : HasCompactSupport f) (hg : Integrable g μ) :
    Integrable (fun x => f x * g x) μ := by
  obtain ⟨C, hC⟩ := hfc.exists_bound_of_continuous hf
  exact hg.bdd_mul hf.aestronglyMeasurable (Eventually.of_forall hC)

lemma energyPath_sub {n : ℕ} (Ω : P201Specs.Domain n) (T : ℝ)
    (u v : ℝ → P201Specs.H ℝ Ω 1) (du dv : ℝ → P201Specs.Hminus1 ℝ Ω) (U V : ℝ → P201Specs.Lp ℝ Ω 2)
    (hu : EnergyPath Ω T u du U) (hv : EnergyPath Ω T v dv V) :
    EnergyPath Ω T (u - v) (du - dv) (U - V) := by
  letI : NormedSpace ℝ (P201Specs.H10 ℝ Ω) := inferInstanceAs
    (NormedSpace ℝ ↥(P201Specs.hZeroSubmodule ℝ Ω))
  letI : NormedAddCommGroup (P201Specs.Hminus1 ℝ Ω) := inferInstanceAs
    (NormedAddCommGroup (↥(P201Specs.hZeroSubmodule ℝ Ω) →L[ℝ] ℝ))
  have hs : MemLp (u - v) 2 (timeMeasure T) := hu.spatial.sub hv.spatial
  have hd : MemLp (du - dv) 2 (timeMeasure T) := hu.derivative.sub hv.derivative
  refine ⟨hs, hd, hu.continuous.sub hv.continuous, ?_, ?_⟩
  · filter_upwards [hu.representative, hv.representative] with t hut hvt
    simp only [Pi.sub_apply, hut, hvt, map_sub]
  · intro η φ
    have hUi : Integrable U (timeMeasure T) :=
      ((P201Specs.hUnderlying (𝕜 := ℝ) Ω 1).integrable_comp (hu.spatial.integrable (by norm_num))).congr
        (Filter.EventuallyEq.symm hu.representative)
    have hVi : Integrable V (timeMeasure T) :=
      ((P201Specs.hUnderlying (𝕜 := ℝ) Ω 1).integrable_comp (hv.spatial.integrable (by norm_num))).congr
        (Filter.EventuallyEq.symm hv.representative)
    have hdui : Integrable (fun t => du t η) (timeMeasure T) :=
      P201.OrderedTraceChain.dual_pairing_integrable (E := P201Specs.H10 ℝ Ω)
        hu.derivative (memLp_const η)
    have hdvi : Integrable (fun t => dv t η) (timeMeasure T) :=
      P201.OrderedTraceChain.dual_pairing_integrable (E := P201Specs.H10 ℝ Ω)
        hv.derivative (memLp_const η)
    have hφd : Continuous (deriv φ) := φ.contDiff.continuous_deriv (by simp)
    have hLu := integrable_mul_compact (deriv φ) _ hφd φ.hasCompactSupport.deriv
      (hUi.inner_const (𝕜 := ℝ) (P201Specs.hZeroUnderlying Ω η))
    have hLv := integrable_mul_compact (deriv φ) _ hφd φ.hasCompactSupport.deriv
      (hVi.inner_const (𝕜 := ℝ) (P201Specs.hZeroUnderlying Ω η))
    have hRu := integrable_mul_compact φ _ φ.continuous φ.hasCompactSupport hdui
    have hRv := integrable_mul_compact φ _ φ.continuous φ.hasCompactSupport hdvi
    simp only [Pi.sub_apply, inner_sub_left, sub_apply, mul_sub]
    rw [integral_sub hLu hLv, integral_sub hRu hRv,
      hu.distributional η φ, hv.distributional η φ]
    ring

lemma lateralOrder_sub {m : ℕ} (Ω : P201Specs.Domain (m + 1)) (hΩ : P201Specs.IsBoundedLipschitzOpen Ω)
    (tr : P201Specs.H ℝ Ω 1 →L[ℝ] P201Specs.Hhalf Ω hΩ) (T : ℝ)
    (u v : ℝ → P201Specs.H ℝ Ω 1) (h : LateralOrder Ω hΩ tr T u v) :
    NonpositiveTrace Ω hΩ tr (u - v) T := by
  filter_upwards [h] with t ht
  have he := MeasureTheory.Lp.coeFn_sub
    (P201Specs.Trace.inclusion Ω hΩ (tr (u t)))
    (P201Specs.Trace.inclusion Ω hΩ (tr (v t)))
  simp only [Pi.sub_apply, map_sub]
  filter_upwards [ht, he] with x hx he
  rw [he]
  exact sub_nonpos.mpr hx

lemma bulkOrder_sub_iff {n : ℕ} (Ω : P201Specs.Domain n) (f g : P201Specs.Lp ℝ Ω 2) :
    (∀ᵐ x ∂P201Specs.domainMeasure Ω, (f - g) x ≤ 0) ↔ BulkOrder Ω f g := by
  have he := MeasureTheory.Lp.coeFn_sub f g
  constructor
  · intro h
    filter_upwards [h, he] with x hx he
    rw [he] at hx
    exact sub_nonpos.mp hx
  · intro h
    filter_upwards [h, he] with x hx he
    rw [he]
    exact sub_nonpos.mpr hx

/-- Comparison for two full energy paths with ordered initial and lateral data. -/
theorem comparison : ComparisonStatement := by
  intro m Ω hΩ tr htr T hT A ν hA u v du dv U V hu hv hinit hlat hineq
  have hw := energyPath_sub Ω T u v du dv U V hu hv
  have hwtrace := lateralOrder_sub Ω hΩ tr T u v hlat
  have hwinit : ∀ᵐ x ∂domainMeasure Ω, (U - V) 0 x ≤ 0 :=
    (bulkOrder_sub_iff Ω (U 0) (V 0)).mpr hinit
  have hwres := difference_comparison Ω hΩ tr htr T hT A ν hA
    (u - v) (du - dv) (U - V) hw hwtrace hwinit hineq
  intro t ht
  exact (bulkOrder_sub_iff Ω (U t) (V t)).mp (hwres t ht)

/-- The fixed-test formulation has the same conclusion, after choosing a
common null set using the separability and continuity theorem above. -/
theorem comparison_fixed_tests : FixedTestComparisonStatement := by
  intro m Ω hΩ tr htr T hT A ν hA u v du dv U V hu hv hinit hlat hineq
  exact comparison Ω hΩ tr htr T hT A ν hA u v du dv U V hu hv hinit hlat
    ((common_exceptional_set Ω T A ν hA (u - v) (du - dv)).mp hineq)

/-- Subtracting the weak equations puts ordered sources in the dual cone
required by comparison. No symmetry or homogeneous lateral data is used. -/
theorem comparison_ordered_sources : OrderedSourcesStatement := by
  intro m Ω hΩ tr htr T hT A ν hA u v du dv f g U V hu hv hinit hlat heu hev hfg
  apply comparison Ω hΩ tr htr T hT A ν hA u v du dv U V hu hv hinit hlat
  obtain ⟨M, hM, hb⟩ := hA.2.2
  filter_upwards [heu, hev, hfg, hA.2.1.prodMk_left, Measure.ae_ae_of_ae_prod hb]
    with t hu' hv' hfg' hm hb'
  intro η hη
  have hsub := form_sub_left Ω (A t) hm M (hb'.mono fun _ hx => hx.1)
    (u t) (v t) η.val
  change (du t - dv t) η + form Ω (A t) (u t - v t) η.val ≤ 0
  rw [sub_apply, hsub]
  linarith [hu' η, hv' η, hfg' η hη]

end P201.Heat.WeakComparison
