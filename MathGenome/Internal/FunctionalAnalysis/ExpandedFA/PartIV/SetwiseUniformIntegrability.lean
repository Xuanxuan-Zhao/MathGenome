import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SetwiseUniformIntegrability
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Abel
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.ByContra
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
The uniform-control portion of `fa2:p4:hahn-vitali-saks`.
The main specification is deliberately independent of the intermediate Baire
and semivariation estimates. No conclusion of the main theorem is assumed.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal symmDiff

namespace ExpandedFA.PartIV.SetwiseUniformIntegrability

/-- Measurable sets are complete for the symmetric-difference pseudometric.
The use of a pseudometric retains all measurable representatives, including on
an incomplete measure space. -/
theorem measuredSets_complete {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] : CompleteSpace (MeasuredSets ν) := by
  classical
  apply Metric.complete_of_convergent_controlled_sequences
    (fun n => (2 : ℝ)⁻¹ ^ n) (fun n => pow_pos (by norm_num) n)
  intro u hu
  have hs : (∑' n, ν ((u (n + 1) : Set α) ∆ (u n : Set α))) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show (∑' n, (2⁻¹ : ℝ≥0∞) ^ n) ≠ ⊤ by simp)
    apply ENNReal.tsum_le_tsum
    intro n
    have h := (hu n (n + 1) n (Nat.le_succ n) le_rfl).le
    rw [MeasuredSets.dist_def] at h
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by finiteness)).mp (by
      simpa only [ENNReal.toReal_pow, ENNReal.toReal_inv, ENNReal.toReal_ofNat, Measure.real] using h)
  have ha := ae_eventually_notMem hs
  let A : Set α := ⋃ N : ℕ, ⋂ n ≥ N, (u n : Set α)
  have hA : MeasurableSet A := MeasurableSet.iUnion fun N =>
    MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ => (u n).property
  have hstab : ∀ᵐ x ∂ν, ∀ᶠ n in atTop, x ∈ (u n : Set α) ↔ x ∈ A := by
    filter_upwards [ha] with x hx
    obtain ⟨N, hN⟩ := eventually_atTop.mp hx
    have heq : ∀ n ≥ N, (x ∈ (u n : Set α) ↔ x ∈ (u N : Set α)) := by
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => rfl
      | succ n hn ih =>
        have h := hN n hn
        simp only [mem_symmDiff, not_or, not_and] at h
        tauto
    have hAx : x ∈ A ↔ x ∈ (u N : Set α) := by
      simp only [A, mem_iUnion, mem_iInter]
      constructor
      · rintro ⟨M, hM⟩
        exact (heq (max M N) (le_max_right _ _)).mp (hM _ (le_max_left _ _))
      · intro hxN
        exact ⟨N, fun n hn => (heq n hn).mpr hxN⟩
    exact eventually_atTop.mpr ⟨N, fun n hn => (heq n hn).trans hAx.symm⟩
  let a : MeasuredSets ν := ⟨A, hA⟩
  refine ⟨a, ?_⟩
  have ht : Tendsto (fun n => ν ((u n : Set α) ∆ A)) atTop (𝓝 0) := by
    have hlim : ∀ᵐ x ∂ν, ∀ᶠ n in atTop,
        x ∈ ((u n : Set α) ∆ A) ↔ x ∈ (∅ : Set α) := by
      filter_upwards [hstab] with x hx
      filter_upwards [hx] with n hn
      simp only [mem_symmDiff, mem_empty_iff_false]
      tauto
    convert (tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
        (μ := ν) atTop MeasurableSet.empty
        (fun n => (u n).property.symmDiff hA) hlim) using 1
    simp
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have htr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (htr.eventually (gt_mem_nhds (by simpa using hε)))
  refine ⟨N, fun n hn => ?_⟩
  rw [MeasuredSets.dist_def]
  convert hN n hn using 1
  rfl

/-- Epsilon-delta absolute continuity for a finite measure. The reference
measure need not be finite or sigma-finite. -/
theorem finite_measure_absolutelyContinuous_epsilon_delta
    {α : Type*} [MeasurableSpace α] {ρ ν : Measure α} [IsFiniteMeasure ρ]
    (hac : ρ ≪ ν) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Set α, MeasurableSet A →
      ν A < ENNReal.ofReal δ → ρ.real A < ε := by
  classical
  by_contra! h
  have hb : ∀ n : ℕ, ∃ A : Set α, MeasurableSet A ∧
      ν A < ENNReal.ofReal ((2 : ℝ)⁻¹ ^ n) ∧ ε ≤ ρ.real A :=
    fun n => h _ (pow_pos (by norm_num) n)
  choose A hA hν hρ using hb
  have hsum : (∑' n, ν (A n)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show (∑' n, (2⁻¹ : ℝ≥0∞) ^ n) ≠ ⊤ by simp)
    apply ENNReal.tsum_le_tsum
    intro n
    simpa only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2⁻¹),
      ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]
      using (hν n).le
  have hae : ∀ᵐ x ∂ρ, ∀ᶠ n in atTop, x ∉ A n :=
    (ae_eventually_notMem hsum).filter_mono hac.ae_le
  have ht : Tendsto (fun n => ρ (A n)) atTop (𝓝 0) := by
    simpa only [measure_empty] using
      (tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
        (μ := ρ) atTop MeasurableSet.empty hA
        (hae.mono fun x hx => hx.mono fun n hn => by simp [hn]))
  have htr : Tendsto (fun n => ρ.real (A n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Measure.real, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  obtain ⟨n, hn⟩ := (htr.eventually (gt_mem_nhds hε)).exists
  exact (not_lt_of_ge (hρ n)) hn

/-- The change in a set integral is bounded by the norm integral on the
symmetric difference. -/
theorem norm_setIntegral_sub_le_symmDiff
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {μ : Measure α} {f : α → E}
    (hf : Integrable f μ) {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ‖(∫ x in A, f x ∂μ) - (∫ x in B, f x ∂μ)‖ ≤
      ∫ x in A ∆ B, ‖f x‖ ∂μ := by
  rw [← integral_indicator hA, ← integral_indicator hB,
    ← integral_sub (hf.indicator hA) (hf.indicator hB)]
  calc
    _ ≤ ∫ x, ‖A.indicator f x - B.indicator f x‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ x, (A ∆ B).indicator (fun x => ‖f x‖) x ∂μ := by
      congr 1
      funext x
      by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;>
        simp [ha, hb, mem_symmDiff]
    _ = _ := integral_indicator (hA.symmDiff hB)

/-- Integrals of an integrable function are small on sets of small finite
control measure whenever the original measure is absolutely continuous with
respect to that control measure. -/
theorem integral_norm_small_of_control
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ ν : Measure α} (hac : μ ≪ ν) {f : α → E} (hf : Integrable f μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Set α, MeasurableSet A →
      ν A < ENNReal.ofReal δ → (∫ x in A, ‖f x‖ ∂μ) < ε := by
  let ρ := μ.withDensity (fun x => ‖f x‖ₑ)
  let : IsFiniteMeasure ρ := isFiniteMeasure_withDensity
    (hasFiniteIntegral_iff_enorm.mp hf.2).ne
  obtain ⟨δ, hδ, hs⟩ := finite_measure_absolutelyContinuous_epsilon_delta
    ((withDensity_absolutelyContinuous μ (fun x => ‖f x‖ₑ)).trans hac) hε
  refine ⟨δ, hδ, fun A hA hsmall => ?_⟩
  have he : ρ.real A = ∫ x in A, ‖f x‖ ∂μ := by
    rw [withDensity_real_apply _ hA,
      integral_norm_eq_lintegral_enorm hf.restrict.aestronglyMeasurable]
  rw [← he]
  exact hs A hA hsmall

/-- Continuity of set integrals for the symmetric-difference pseudometric
of any finite control measure dominating the original measure. -/
theorem continuous_setIntegral_of_control
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    {μ ν : Measure α} [IsFiniteMeasure ν]
    (hac : μ ≪ ν) {f : α → E} (hf : Integrable f μ) :
    Continuous (fun A : MeasuredSets ν => ∫ x in (A : Set α), f x ∂μ) := by
  apply Metric.continuous_iff.mpr
  intro A ε hε
  obtain ⟨δ, hδ, hs⟩ := integral_norm_small_of_control hac hf hε
  refine ⟨δ, hδ, fun B hB => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (norm_setIntegral_sub_le_symmDiff hf B.property A.property)
  apply hs _ (B.property.symmDiff A.property)
  apply (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hδ.le]
  exact hB

/-- The category-theoretic step in Hahn–Vitali–Saks. Pointwise Cauchyness
of continuous maps gives uniform Cauchyness on some nonempty open ball,
for each fixed positive error. Pseudometrics suffice. -/
theorem exists_ball_uniform_cauchy
    {X E : Type*} [PseudoMetricSpace X] [Nonempty X] [BaireSpace X]
    [SeminormedAddCommGroup E] (T : ℕ → X → E)
    (hT : ∀ n, Continuous (T n))
    (hC : ∀ x, CauchySeq (fun n => T n x))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ x : X, ∃ r : ℝ, 0 < r ∧
      ∀ y, dist y x < r → ∀ n ≥ N, ∀ m ≥ N, ‖T n y - T m y‖ ≤ ε := by
  let F : ℕ → Set X := fun N =>
    {x | ∀ n ≥ N, ∀ m ≥ N, ‖T n x - T m x‖ ≤ ε}
  have hclosed : ∀ N, IsClosed (F N) := by
    intro N
    change IsClosed {x | ∀ n ≥ N, ∀ m ≥ N, ‖T n x - T m x‖ ≤ ε}
    simp only [ofPred_forall]
    exact isClosed_iInter fun n => isClosed_iInter fun _ =>
      isClosed_iInter fun m => isClosed_iInter fun _ =>
        isClosed_le (((hT n).sub (hT m)).norm) continuous_const
  have hcover : (⋃ N, F N) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hC x) ε hε
    exact mem_iUnion.mpr ⟨N, fun n hn m hm => by
      simpa only [dist_eq_norm] using (hN n hn m hm).le⟩
  obtain ⟨N, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  exact ⟨N, x, r, hr, fun y hy => interior_subset (hball hy)⟩

/-- On each individual measurable set, the setwise hypothesis really gives
Cauchyness; this does not assert a uniform L¹ bound. -/
theorem setwise_cauchy
    {α 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → 𝕜}
    (h : Spec.SetwiseConvergent μ f) (A : Set α) (hA : MeasurableSet A) :
    CauchySeq (fun n => ∫ x in A, f n x ∂μ) := by
  obtain ⟨z, hz⟩ := h A hA
  exact hz.cauchySeq

/-- The same hypothesis gives a bound depending on the test set. Uniformity
in that test set is a separate, substantive obligation. -/
theorem setwise_bounded
    {α 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → 𝕜}
    (h : Spec.SetwiseConvergent μ f) (A : Set α) (hA : MeasurableSet A) :
    ∃ C : ℝ, ∀ n, ‖∫ x in A, f n x ∂μ‖ ≤ C := by
  obtain ⟨z, hz⟩ := h A hA
  obtain ⟨C, hC⟩ := hz.cauchySeq.isBounded_range.exists_norm_le
  exact ⟨C, fun n => hC _ (mem_range_self n)⟩

/-- For a real function, its L¹ norm is bounded by twice a bound for its
integrals on measurable subsets. The measurable representative removes any
need to assume completeness of the underlying measure space. -/
theorem integral_norm_le_two_of_setIntegral_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Integrable f μ) {C : ℝ}
    (hC : ∀ A : Set α, MeasurableSet A → |∫ x in A, f x ∂μ| ≤ C) :
    (∫ x, ‖f x‖ ∂μ) ≤ 2 * C := by
  let g := hf.aestronglyMeasurable.mk f
  have hfg : f =ᵐ[μ] g := hf.aestronglyMeasurable.ae_eq_mk
  have hg : Integrable g μ := hf.congr hfg
  have hgm : Measurable g := hf.aestronglyMeasurable.measurable_mk
  have hCg : ∀ A : Set α, MeasurableSet A → |∫ x in A, g x ∂μ| ≤ C := by
    intro A hA
    rw [← setIntegral_congr_ae hA (hfg.mono fun _ hx _ => hx)]
    exact hC A hA
  have hp := hCg {x | 0 ≤ g x} (measurableSet_le measurable_const hgm)
  have hn := hCg {x | g x ≤ 0} (measurableSet_le hgm measurable_const)
  have hnorm := integral_norm_eq_pos_sub_neg hg
  calc
    (∫ x, ‖f x‖ ∂μ) = ∫ x, ‖g x‖ ∂μ := integral_congr_ae (hfg.fun_comp norm)
    _ ≤ 2 * C := by linarith [(le_abs_self (∫ x in {x | 0 ≤ g x}, g x ∂μ)),
      (neg_abs_le (∫ x in {x | g x ≤ 0}, g x ∂μ))]

/-- Scalar semivariation controls the L¹ norm, for both real and complex
scalars. The constant four is independent of the measure space. -/
theorem integral_norm_le_four_of_setIntegral_le
    {α 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace α] {μ : Measure α}
    {f : α → 𝕜} (hf : Integrable f μ) {C : ℝ}
    (hC : ∀ A : Set α, MeasurableSet A → ‖∫ x in A, f x ∂μ‖ ≤ C) :
    (∫ x, ‖f x‖ ∂μ) ≤ 4 * C := by
  have hr : (∫ x, ‖RCLike.re (f x)‖ ∂μ) ≤ 2 * C := by
    apply integral_norm_le_two_of_setIntegral_le hf.re
    intro A hA
    rw [integral_re hf.restrict]
    exact (RCLike.abs_re_le_norm _).trans (hC A hA)
  have hi : (∫ x, ‖RCLike.im (f x)‖ ∂μ) ≤ 2 * C := by
    apply integral_norm_le_two_of_setIntegral_le hf.im
    intro A hA
    rw [integral_im hf.restrict]
    exact (RCLike.abs_im_le_norm _).trans (hC A hA)
  have hpoint (z : 𝕜) : ‖z‖ ≤ ‖RCLike.re z‖ + ‖RCLike.im z‖ := by
    have hsq := RCLike.norm_sq_eq_def (z := z)
    have habs : 0 ≤ |RCLike.re z| * |RCLike.im z| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have ha := sq_abs (RCLike.re z)
    have hb := sq_abs (RCLike.im z)
    simp only [Real.norm_eq_abs]
    nlinarith [norm_nonneg z, abs_nonneg (RCLike.re z), abs_nonneg (RCLike.im z)]
  calc
    (∫ x, ‖f x‖ ∂μ) ≤ ∫ x, ‖RCLike.re (f x)‖ + ‖RCLike.im (f x)‖ ∂μ :=
      integral_mono hf.norm (hf.re.norm.add hf.im.norm) (fun x => hpoint (f x))
    _ = (∫ x, ‖RCLike.re (f x)‖ ∂μ) + (∫ x, ‖RCLike.im (f x)‖ ∂μ) :=
      integral_add hf.re.norm hf.im.norm
    _ ≤ 4 * C := by linarith

/-- Local version of the semivariation estimate. Tests are genuine measurable
subsets of `B`, which is needed in the Baire argument. -/
theorem setIntegral_norm_le_four_of_subsets
    {α 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace α] {μ : Measure α}
    {f : α → 𝕜} (hf : Integrable f μ) {B : Set α} (hB : MeasurableSet B)
    {C : ℝ}
    (hC : ∀ A : Set α, MeasurableSet A → A ⊆ B → ‖∫ x in A, f x ∂μ‖ ≤ C) :
    (∫ x in B, ‖f x‖ ∂μ) ≤ 4 * C := by
  apply integral_norm_le_four_of_setIntegral_le hf.restrict
  intro A hA
  rw [Measure.restrict_restrict hA]
  exact hC (A ∩ B) (hA.inter hB) inter_subset_right

/-- The Boolean-algebra part of the Baire argument: uniform Cauchyness on
one ball implies uniform Cauchyness on all sets of small control measure.
Completeness/continuity of the measurable-set space are separate obligations. -/
theorem exists_small_set_uniform_cauchy
    {α 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace α]
    {μ ν : Measure α} [IsFiniteMeasure ν] [BaireSpace (MeasuredSets ν)]
    {f : ℕ → α → 𝕜} (hf : ∀ n, Integrable (f n) μ)
    (hconv : Spec.SetwiseConvergent μ f)
    (hcont : ∀ n, Continuous (fun A : MeasuredSets ν => ∫ x in (A : Set α), f n x ∂μ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ δ : ℝ, 0 < δ ∧
      ∀ B : Set α, MeasurableSet B → ν.real B < δ →
        ∀ n ≥ N, ∀ m ≥ N,
          ‖(∫ x in B, f n x ∂μ) - (∫ x in B, f m x ∂μ)‖ ≤ 2 * ε := by
  let : Nonempty (MeasuredSets ν) := ⟨⟨∅, MeasurableSet.empty⟩⟩
  obtain ⟨N, A, r, hr, hball⟩ := exists_ball_uniform_cauchy
    (fun n (A : MeasuredSets ν) => ∫ x in (A : Set α), f n x ∂μ)
    hcont (fun A => setwise_cauchy hconv A A.property) hε
  refine ⟨N, r, hr, ?_⟩
  intro B hB hBr n hn m hm
  let U : MeasuredSets ν := ⟨(A : Set α) ∪ B, A.property.union hB⟩
  let D : MeasuredSets ν := ⟨(A : Set α) \ B, A.property.diff hB⟩
  have hU : dist U A < r := by
    apply lt_of_le_of_lt _ hBr
    rw [MeasuredSets.dist_def]
    apply ENNReal.toReal_mono (measure_ne_top ν B)
    apply measure_mono
    intro x hx
    change x ∈ (((A : Set α) ∪ B) ∆ (A : Set α)) at hx
    simp only [mem_symmDiff, mem_union] at hx
    tauto
  have hD : dist D A < r := by
    apply lt_of_le_of_lt _ hBr
    rw [MeasuredSets.dist_def]
    apply ENNReal.toReal_mono (measure_ne_top ν B)
    apply measure_mono
    intro x hx
    change x ∈ (((A : Set α) \ B) ∆ (A : Set α)) at hx
    simp only [mem_symmDiff, Set.mem_sdiff] at hx
    tauto
  have hu := hball U hU n hn m hm
  have hd := hball D hD n hn m hm
  have hdiff (k : ℕ) :
      (∫ x in B, f k x ∂μ) =
        (∫ x in (U : Set α), f k x ∂μ) - (∫ x in (D : Set α), f k x ∂μ) := by
    have hsub : (D : Set α) ⊆ (U : Set α) := by
      exact sdiff_subset.trans subset_union_left
    have heq : (U : Set α) \ (D : Set α) = B := by
      change ((A : Set α) ∪ B) \ ((A : Set α) \ B) = B
      ext x
      simp only [Set.mem_sdiff, mem_union]
      tauto
    calc
      _ = ∫ x in (U : Set α) \ (D : Set α), f k x ∂μ := by rw [heq]
      _ = _ := setIntegral_sdiff D.property (hf k).integrableOn hsub
  rw [hdiff n, hdiff m]
  calc
    ‖((∫ x in (U : Set α), f n x ∂μ) - (∫ x in (D : Set α), f n x ∂μ)) -
      ((∫ x in (U : Set α), f m x ∂μ) - (∫ x in (D : Set α), f m x ∂μ))‖ =
      ‖((∫ x in (U : Set α), f n x ∂μ) - (∫ x in (U : Set α), f m x ∂μ)) -
      ((∫ x in (D : Set α), f n x ∂μ) - (∫ x in (D : Set α), f m x ∂μ))‖ := by
        congr 1
        abel
    _ ≤ ‖(∫ x in (U : Set α), f n x ∂μ) - (∫ x in (U : Set α), f m x ∂μ)‖ +
      ‖(∫ x in (D : Set α), f n x ∂μ) - (∫ x in (D : Set α), f m x ∂μ)‖ := norm_sub_le _ _
    _ ≤ 2 * ε := by linarith

/-- Conditional finite-control Hahn–Vitali–Saks estimate, with the topological
infrastructure stated explicitly. This is a proved intermediate theorem, not
a replacement for the unconditional σ-finite specification. -/
theorem uniform_small_set_integrals_of_baire
    {α 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace α]
    {μ ν : Measure α} [IsFiniteMeasure ν] [BaireSpace (MeasuredSets ν)]
    {f : ℕ → α → 𝕜} (hf : ∀ n, Integrable (f n) μ)
    (hconv : Spec.SetwiseConvergent μ f)
    (hcont : ∀ n, Continuous (fun A : MeasuredSets ν => ∫ x in (A : Set α), f n x ∂μ)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ B : Set α, MeasurableSet B → ν.real B < δ →
        ∀ n, ‖∫ x in B, f n x ∂μ‖ < ε := by
  intro ε hε
  obtain ⟨N, r, hr, hc⟩ := exists_small_set_uniform_cauchy hf hconv hcont
    (show 0 < ε / 8 by linarith)
  let O : MeasuredSets ν := ⟨∅, MeasurableSet.empty⟩
  have hev : ∀ᶠ B : MeasuredSets ν in 𝓝 O,
      ∀ n ∈ Finset.range (N + 1), ‖∫ x in (B : Set α), f n x ∂μ‖ < ε / 2 := by
    apply (eventually_all_finset _).mpr
    intro n hn
    have hz : Tendsto (fun B : MeasuredSets ν => ‖∫ x in (B : Set α), f n x ∂μ‖)
        (𝓝 O) (𝓝 0) := by
      have hzero : (∫ x in (O : Set α), f n x ∂μ) = 0 := by
        change (∫ x in ∅, f n x ∂μ) = 0
        simp
      have ht := (hcont n).norm.continuousAt (x := O)
      change Tendsto _ (𝓝 O) (𝓝 ‖∫ x in (O : Set α), f n x ∂μ‖) at ht
      rw [hzero, norm_zero] at ht
      exact ht
    exact hz.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))
  obtain ⟨d, hd, hbd⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨min r d, lt_min hr hd, ?_⟩
  intro B hB hsmall n
  let b : MeasuredSets ν := ⟨B, hB⟩
  have hbO : dist b O < d := by
    rw [MeasuredSets.dist_def]
    change ν.real (B ∆ ∅) < d
    have he : B ∆ (∅ : Set α) = B := by ext x; simp [mem_symmDiff]
    rw [he]
    exact hsmall.trans_le (min_le_right r d)
  have hinit (k : ℕ) (hk : k ≤ N) : ‖∫ x in B, f k x ∂μ‖ < ε / 2 :=
    hbd hbO k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  by_cases hn : n ≤ N
  · exact (hinit n hn).trans (by linarith)
  · have hdiff := hc B hB (hsmall.trans_le (min_le_left r d)) n (Nat.le_of_not_ge hn) N le_rfl
    have hN := hinit N le_rfl
    calc
      ‖∫ x in B, f n x ∂μ‖ ≤
        ‖(∫ x in B, f n x ∂μ) - (∫ x in B, f N x ∂μ)‖ +
          ‖∫ x in B, f N x ∂μ‖ := norm_le_norm_sub_add _ _
      _ < ε := by linarith

/-- Uniform norm-integral control with respect to the finite control measure,
once the Baire infrastructure has been established. -/
theorem uniform_small_set_norm_integrals_of_baire
    {α 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace α]
    {μ ν : Measure α} [IsFiniteMeasure ν] [BaireSpace (MeasuredSets ν)]
    {f : ℕ → α → 𝕜} (hf : ∀ n, Integrable (f n) μ)
    (hconv : Spec.SetwiseConvergent μ f)
    (hcont : ∀ n, Continuous (fun A : MeasuredSets ν => ∫ x in (A : Set α), f n x ∂μ)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ B : Set α, MeasurableSet B → ν.real B < δ →
        ∀ n, (∫ x in B, ‖f n x‖ ∂μ) < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hs⟩ := uniform_small_set_integrals_of_baire hf hconv hcont
    (ε / 8) (by linarith)
  refine ⟨δ, hδ, fun B hB hsmall n => ?_⟩
  have hb : (∫ x in B, ‖f n x‖ ∂μ) ≤ 4 * (ε / 8) := by
    apply setIntegral_norm_le_four_of_subsets (hf n) hB
    intro A hA hAB
    exact (hs A hA ((measureReal_mono hAB).trans_lt hsmall) n).le
  linarith

/-- Local uniform norm control and setwise boundedness imply a uniform L¹
bound. Induction on a bound for the finite control mass handles atoms without
any nonatomicity hypothesis or atom classification. -/
theorem uniform_integral_norm_bounded_of_control
    {α 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace α]
    {μ ν : Measure α} [IsFiniteMeasure ν]
    {f : ℕ → α → 𝕜} (hf : ∀ n, Integrable (f n) μ)
    (hbounded : ∀ B : Set α, MeasurableSet B →
      ∃ C : ℝ, ∀ n, ‖∫ x in B, f n x ∂μ‖ ≤ C)
    (hlocal : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ B : Set α, MeasurableSet B → ν.real B < δ →
        ∀ n, (∫ x in B, ‖f n x‖ ∂μ) < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, (∫ x, ‖f n x‖ ∂μ) ≤ C := by
  classical
  obtain ⟨δ, hδ, hs⟩ := hlocal 1 zero_lt_one
  have hb : ∀ k : ℕ, ∀ B : Set α, MeasurableSet B → ν.real B ≤ k * δ →
      ∃ C : ℝ, ∀ n, (∫ x in B, ‖f n x‖ ∂μ) ≤ C := by
    intro k
    induction k with
    | zero =>
      intro B hB hsize
      simp only [Nat.cast_zero, zero_mul] at hsize
      exact ⟨1, fun n => (hs B hB (hsize.trans_lt hδ) n).le⟩
    | succ k ih =>
      intro B hB hsize
      by_cases hsplit : ∃ A : Set α, MeasurableSet A ∧ A ⊆ B ∧
          δ ≤ ν.real A ∧ δ ≤ ν.real (B \ A)
      · obtain ⟨A, hA, hAB, hlargeA, hlargeD⟩ := hsplit
        have hmass := measureReal_sdiff_add_inter (μ := ν) (s := B) hA
        rw [inter_eq_right.mpr hAB] at hmass
        have hsizeA : ν.real A ≤ k * δ := by
          simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] at hsize
          linarith
        have hsizeD : ν.real (B \ A) ≤ k * δ := by
          simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] at hsize
          linarith
        obtain ⟨C, hC⟩ := ih A hA hsizeA
        obtain ⟨D, hD⟩ := ih (B \ A) (hB.diff hA) hsizeD
        refine ⟨C + D, fun n => ?_⟩
        have he := setIntegral_sdiff hA (hf n).norm.integrableOn hAB
        linarith [hC n, hD n]
      · obtain ⟨C, hC⟩ := hbounded B hB
        have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
        refine ⟨4 * (C + 1), fun n => ?_⟩
        apply setIntegral_norm_le_four_of_subsets (hf n) hB
        intro A hA hAB
        by_cases hsmall : ν.real A < δ
        · exact (norm_integral_le_integral_norm _).trans
            ((hs A hA hsmall n).le.trans (by linarith))
        · have hsmallD : ν.real (B \ A) < δ := by
            by_contra! hlargeD
            exact hsplit ⟨A, hA, hAB, le_of_not_gt hsmall, hlargeD⟩
          have he := setIntegral_sdiff hA (hf n).integrableOn hAB
          have he' : (∫ x in A, f n x ∂μ) =
              (∫ x in B, f n x ∂μ) - (∫ x in B \ A, f n x ∂μ) := by
            rw [he]
            abel
          rw [he']
          apply (norm_sub_le _ _).trans
          have hd := (norm_integral_le_integral_norm (f n) (μ := μ.restrict (B \ A))).trans
            (hs _ (hB.diff hA) hsmallD n).le
          linarith [hC n]
  obtain ⟨k, hk⟩ := exists_nat_gt (ν.real univ / δ)
  have hsize : ν.real univ ≤ k * δ := by
    exact ((div_lt_iff₀ hδ).mp hk).le
  obtain ⟨C, hC⟩ := hb k univ MeasurableSet.univ hsize
  refine ⟨max C 0, le_max_right _ _, fun n => ?_⟩
  simpa only [Measure.restrict_univ] using (hC n).trans (le_max_left C 0)

/-- A finite control measure turns uniform local norm-integral control into
common finite-μ-measure spatial tails, even when μ has infinite total mass. -/
theorem uniform_finite_measure_tails_of_control
    {α 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace α]
    {μ ν : Measure α} [SigmaFinite μ] [IsFiniteMeasure ν]
    {f : ℕ → α → 𝕜}
    (hlocal : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ B : Set α, MeasurableSet B → ν.real B < δ →
        ∀ n, (∫ x in B, ‖f n x‖ ∂μ) < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ F : Set α, MeasurableSet F ∧ μ F < ⊤ ∧
      ∀ n, (∫ x in Fᶜ, ‖f n x‖ ∂μ) < ε := by
  intro ε hε
  obtain ⟨δ, hδ, hs⟩ := hlocal ε hε
  have hi : (⋂ k, (spanningSets μ k)ᶜ) = (∅ : Set α) := by
    rw [← compl_iUnion, iUnion_spanningSets]
    exact compl_univ
  have ht : Tendsto (fun k => ν (spanningSets μ k)ᶜ) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop
      (fun k => (measurableSet_spanningSets μ k).compl.nullMeasurableSet)
      (fun i j hij => compl_subset_compl.mpr (monotone_spanningSets μ hij))
      (show ∃ k : ℕ, ν (spanningSets μ k)ᶜ ≠ ⊤ from ⟨0, measure_ne_top _ _⟩)
    simpa only [hi, measure_empty, Function.comp_def] using h
  have htr : Tendsto (fun k => ν.real (spanningSets μ k)ᶜ) atTop (𝓝 0) := by
    simpa only [ENNReal.toReal_zero, Function.comp_def, Measure.real] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  obtain ⟨k, hk⟩ := (htr.eventually (gt_mem_nhds hδ)).exists
  exact ⟨spanningSets μ k, measurableSet_spanningSets μ k,
    measure_spanningSets_lt_top μ k, hs _ (measurableSet_spanningSets μ k).compl hk⟩

/-- Setwise convergence on a sigma-finite space gives all three uniform L¹
controls: bounded norms, absolute continuity on small sets, and a common
finite-measure set outside which the norm integrals are small. -/
theorem setwise_uniform_integrability : Spec.MainStatement := by
  intro α 𝕜 _ _ μ _ f hf hconv
  obtain ⟨ν, hν, hμν, hνμ⟩ := exists_isFiniteMeasure_absolutelyContinuous μ
  let : IsFiniteMeasure ν := hν
  let : CompleteSpace (MeasuredSets ν) := measuredSets_complete ν
  have hc : ∀ n, Continuous (fun A : MeasuredSets ν => ∫ x in (A : Set α), f n x ∂μ) :=
    fun n => continuous_setIntegral_of_control hμν (hf n)
  have hl := uniform_small_set_norm_integrals_of_baire hf hconv hc
  refine ⟨uniform_integral_norm_bounded_of_control hf (setwise_bounded hconv) hl, ?_,
    uniform_finite_measure_tails_of_control hl⟩
  intro ε hε
  obtain ⟨δ, hδ, hs⟩ := hl ε hε
  obtain ⟨η, hη, ht⟩ := finite_measure_absolutelyContinuous_epsilon_delta hνμ hδ
  exact ⟨η, hη, fun A hA hsmall n => hs A hA (ht A hA hsmall) n⟩

end ExpandedFA.PartIV.SetwiseUniformIntegrability
