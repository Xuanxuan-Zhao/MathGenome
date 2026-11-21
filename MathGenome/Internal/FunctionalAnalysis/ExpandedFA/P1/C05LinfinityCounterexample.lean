import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C05LinfinityCounterexample
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05NormExtension

/-! A norm-one extension of the limit, and its nonrepresentation by ℓ¹ or by
an L¹ density for counting measure. The endpoint identifications below are
proved directly using the ordinary Mathlib Lp quotients. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal
universe u
namespace ExpandedFA.P1.C05LinfinityCounterexample
open C01SequenceSpaces

private def sequenceLimit {𝕜 : Type u} [RCLike 𝕜] (x : convergentSequences 𝕜) : 𝕜 :=
  Classical.choose x.property

private theorem sequenceLimit_tendsto {𝕜 : Type u} [RCLike 𝕜]
    (x : convergentSequences 𝕜) :
    Tendsto (fun n => x.val n) atTop (𝓝 (sequenceLimit x)) :=
  Classical.choose_spec x.property

private theorem sequenceLimit_eq {𝕜 : Type u} [RCLike 𝕜]
    (x : convergentSequences 𝕜) (l : 𝕜)
    (hl : Tendsto (fun n => x.val n) atTop (𝓝 l)) : sequenceLimit x = l :=
  tendsto_nhds_unique (sequenceLimit_tendsto x) hl

private def limitLinearMap (𝕜 : Type u) [RCLike 𝕜] :
    convergentSequences 𝕜 →ₗ[𝕜] 𝕜 where
  toFun := sequenceLimit
  map_add' x y := sequenceLimit_eq _ _ ((sequenceLimit_tendsto x).add (sequenceLimit_tendsto y))
  map_smul' a x := sequenceLimit_eq _ _ ((sequenceLimit_tendsto x).const_smul a)

private theorem sequenceLimit_bound {𝕜 : Type u} [RCLike 𝕜]
    (x : convergentSequences 𝕜) : ‖sequenceLimit x‖ ≤ ‖x‖ := by
  exact le_of_tendsto (sequenceLimit_tendsto x).norm
    (Eventually.of_forall fun n => lp.norm_apply_le_norm ENNReal.top_ne_zero x.val n)

private def limitContinuousLinearMap (𝕜 : Type u) [RCLike 𝕜] :
    convergentSequences 𝕜 →L[𝕜] 𝕜 :=
  (limitLinearMap 𝕜).mkContinuous 1 (by
    intro x
    simpa [limitLinearMap] using sequenceLimit_bound x)

private def convergentOne (𝕜 : Type u) [RCLike 𝕜] : convergentSequences 𝕜 :=
  ⟨1, 1, by simp⟩

private theorem convergentOne_norm (𝕜 : Type u) [RCLike 𝕜] :
    ‖convergentOne 𝕜‖ = 1 := by
  change ‖(1 : SequenceLInfinity 𝕜)‖ = 1
  rw [lp.norm_eq_ciSup]
  simp

private theorem limit_norm (𝕜 : Type u) [RCLike 𝕜] :
    ‖limitContinuousLinearMap 𝕜‖ = 1 := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by
      intro x
      simpa [limitContinuousLinearMap, limitLinearMap] using sequenceLimit_bound x)
  · have h := (limitContinuousLinearMap 𝕜).le_opNorm (convergentOne 𝕜)
    have hv : limitContinuousLinearMap 𝕜 (convergentOne 𝕜) = 1 :=
      sequenceLimit_eq _ _ (by simp [convergentOne])
    change ‖limitContinuousLinearMap 𝕜 (convergentOne 𝕜)‖ ≤
      ‖limitContinuousLinearMap 𝕜‖ * ‖convergentOne 𝕜‖ at h
    simpa only [hv, norm_one, convergentOne_norm, mul_one] using h

theorem limit_functional : Spec.LimitFunctional := by
  intro 𝕜 _
  exact ⟨limitContinuousLinearMap 𝕜, fun x l hl => sequenceLimit_eq x l hl, limit_norm 𝕜⟩

theorem linfinity_extension_counterexample :
    Spec.ExtensionCounterexample := by
  intro 𝕜 _
  classical
  obtain ⟨L, hL, hnorm⟩ := C05NormExtension.norm_preserving_extension 𝕜 (SequenceLInfinity 𝕜)
    (convergentSequences 𝕜) (limitContinuousLinearMap 𝕜)
  have hlim (x : SequenceLInfinity 𝕜) (l : 𝕜)
      (hx : Tendsto (fun n => x n) atTop (𝓝 l)) : L x = l := by
    rw [hL ⟨x, l, hx⟩]
    exact sequenceLimit_eq _ l hx
  have he (j : ℕ) : L (lp.single ∞ j (1 : 𝕜)) = 0 := by
    apply hlim
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop j] with n hn
    simp [lp.single_apply, ne_of_gt hn]
  have hone : L (1 : SequenceLInfinity 𝕜) = 1 :=
    hlim _ _ (by simp)
  refine ⟨L, hnorm.trans (limit_norm 𝕜), hlim, he, hone, ?_⟩
  rintro ⟨a, ha⟩
  have haz (j : ℕ) : a j = 0 := by
    have h := ha (lp.single ∞ j (1 : 𝕜))
    simpa [he, lp.single_apply, Pi.single_apply, eq_comm] using h.symm
  have h := ha 1
  simp only [haz, zero_mul, tsum_zero] at h
  exact one_ne_zero (hone.symm.trans h)

/-- Counting measure has no nonempty null sets. Thus its Lp quotient retains
all coordinates, and the two endpoint membership conditions are literal. -/
private theorem count_memLp_iff {𝕜 : Type u} [RCLike 𝕜] (f : ℕ → 𝕜)
    (p : ℝ≥0∞) (hp : p = 1 ∨ p = ∞) :
    MemLp f p Measure.count ↔ Memℓp f p := by
  rcases hp with rfl | rfl
  · rw [memLp_one_iff_integrable, integrable_count_iff, memℓp_gen_iff (by simp)]
    simp
  · constructor
    · intro hf
      have hfin : eLpNormEssSup f Measure.count < ∞ := by
        simpa only [eLpNorm_exponent_top hf.aestronglyMeasurable] using hf.eLpNorm_lt_top
      obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp hfin
      apply memℓp_infty
      refine ⟨(C : ℝ), ?_⟩
      rintro _ ⟨n, rfl⟩
      exact (Measure.ae_count_iff.mp hC n : ‖f n‖₊ ≤ C)
    · intro hf
      obtain ⟨C, hC⟩ := memℓp_infty_iff.mp hf
      exact memLp_top_of_bound (.of_discrete) C (Eventually.of_forall fun n => hC ⟨n, rfl⟩)

private def sequenceToCount {𝕜 : Type u} [RCLike 𝕜] (p : ℝ≥0∞)
    (hp : p = 1 ∨ p = ∞) (x : SequenceLp 𝕜 p) :
    Lp 𝕜 p (Measure.count : Measure ℕ) :=
  ((count_memLp_iff (fun n => x n) p hp).mpr x.property).toLp (fun n => x n)

private theorem sequenceToCount_apply {𝕜 : Type u} [RCLike 𝕜] (p : ℝ≥0∞)
    (hp : p = 1 ∨ p = ∞) (x : SequenceLp 𝕜 p) (n : ℕ) :
    sequenceToCount p hp x n = x n :=
  Measure.ae_count_iff.mp (MemLp.coeFn_toLp _) n

private theorem sequenceToCount_norm {𝕜 : Type u} [RCLike 𝕜] (p : ℝ≥0∞)
    (hp : p = 1 ∨ p = ∞) (x : SequenceLp 𝕜 p) :
    ‖sequenceToCount p hp x‖ = ‖x‖ := by
  rw [sequenceToCount, Lp.norm_toLp]
  rcases hp with rfl | rfl
  · rw [eLpNorm_one_eq_lintegral_enorm (.of_discrete), lintegral_count]
    have hs : Summable (fun n => ‖x n‖) := by simpa using x.property.summable (by simp)
    have he : (∑' n, ‖x n‖ₑ) = ENNReal.ofReal (∑' n, ‖x n‖) := by
      simpa only [ofReal_norm] using
        (ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg (x n)) hs).symm
    rw [he, ENNReal.toReal_ofReal (tsum_nonneg fun n => norm_nonneg (x n)),
      lp.norm_eq_tsum_rpow (by simp)]
    simp
  · rw [eLpNorm_exponent_top (.of_discrete), eLpNormEssSup_count,
      ENNReal.toReal_iSup (fun n => enorm_ne_top), lp.norm_eq_ciSup]
    simp

private def countingIsometry (𝕜 : Type u) [RCLike 𝕜] (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (hp : p = 1 ∨ p = ∞) :
    SequenceLp 𝕜 p ≃ₗᵢ[𝕜] Lp 𝕜 p (Measure.count : Measure ℕ) := by
  let T : SequenceLp 𝕜 p →ₗᵢ[𝕜] Lp 𝕜 p (Measure.count : Measure ℕ) :=
    { toFun := sequenceToCount p hp
      map_add' := by
        intro x y
        apply Lp.ext
        apply Measure.ae_count_iff.mpr
        intro n
        rw [sequenceToCount_apply,
          Measure.ae_count_iff.mp (Lp.coeFn_add _ _) n,
          Pi.add_apply, sequenceToCount_apply, sequenceToCount_apply]
        rfl
      map_smul' := by
        intro a x
        apply Lp.ext
        apply Measure.ae_count_iff.mpr
        intro n
        rw [sequenceToCount_apply,
          Measure.ae_count_iff.mp (Lp.coeFn_smul _ _) n,
          Pi.smul_apply, sequenceToCount_apply]
        rfl
      norm_map' := sequenceToCount_norm p hp }
  apply LinearIsometryEquiv.ofSurjective T
  intro f
  let x : SequenceLp 𝕜 p := ⟨(fun n => f n), (count_memLp_iff _ p hp).mp (Lp.memLp f)⟩
  refine ⟨x, ?_⟩
  apply Lp.ext
  exact Measure.ae_count_iff.mpr (fun n => sequenceToCount_apply p hp x n)

private theorem countingIsometry_apply {𝕜 : Type u} [RCLike 𝕜] (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (hp : p = 1 ∨ p = ∞) (x : SequenceLp 𝕜 p) (n : ℕ) :
    countingIsometry 𝕜 p hp x n = x n := sequenceToCount_apply p hp x n

/-- Endpoint Hölder for sequences, directly from the supremum bound. -/
theorem sequence_pairing_integrable {𝕜 : Type u} [RCLike 𝕜]
    (a : SequenceLp 𝕜 1) (x : SequenceLInfinity 𝕜) :
    Integrable (fun n => x n * a n) Measure.count := by
  rw [integrable_count_iff]
  have ha : Summable (fun n => ‖a n‖) := by
    simpa using a.property.summable (by simp)
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ (ha.mul_left ‖x‖)
  intro n
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (lp.norm_apply_le_norm ENNReal.top_ne_zero x n) (norm_nonneg _)

theorem counting_identification : Spec.CountingIdentification.{u} := by
  intro 𝕜 _
  let Utop := countingIsometry 𝕜 ∞ (Or.inr rfl)
  let U₁ := countingIsometry 𝕜 1 (Or.inl rfl)
  refine ⟨Utop, U₁, countingIsometry_apply _ _, countingIsometry_apply _ _, ?_⟩
  intro a x
  have hi : Integrable (fun n => Utop x n * U₁ a n) Measure.count := by
    simpa only [Utop, U₁, countingIsometry_apply] using sequence_pairing_integrable a x
  refine ⟨hi, ?_⟩
  simpa only [count_real_singleton, one_smul, Utop, U₁,
    countingIsometry_apply, mul_comm] using integral_countable hi

theorem counting_measure_counterexample : Spec.MeasureCounterexample.{u} := by
  intro 𝕜 _
  obtain ⟨L, hnorm, _, _, _, hnonrep⟩ := linfinity_extension_counterexample 𝕜
  obtain ⟨Utop, U₁, _, _, hpair⟩ := counting_identification 𝕜
  let M := L.comp (Utop.symm : Lp 𝕜 ∞ (Measure.count : Measure ℕ) →L[𝕜] SequenceLInfinity 𝕜)
  refine ⟨M, ?_, ?_⟩
  · exact (ContinuousLinearMap.opNorm_comp_linearIsometryEquiv L Utop.symm).trans hnorm
  · rintro ⟨g, hg⟩
    apply hnonrep
    refine ⟨U₁.symm g, fun x => ?_⟩
    have h := hg (Utop x)
    have heq : M (Utop x) = L x := by simp [M]
    rw [heq, ← U₁.apply_symm_apply g, (hpair (U₁.symm g) x).2] at h
    exact h

end ExpandedFA.P1.C05LinfinityCounterexample
