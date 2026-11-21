import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyLevelDecomposition
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyMaximalInterfaces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyWhitney
import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Abel

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff

namespace ExpandedFA.PartIV.HardyLevel

open ExpandedFA.Distributions ExpandedFA.Fourier HardyWhitney HardyMaximalSpec

abbrev dyadicThreshold : Specs.ExpandedFA.PartIV.HardyLevelDecomposition.thresholdType := threshold

lemma threshold_pos (k : ℤ) : 0 < threshold k := zpow_pos (by norm_num) _

lemma sum_threshold_le (S : Finset ℤ) :
    ∀ m : ℤ, (∀ k ∈ S, k ≤ m) → ∑ k ∈ S, threshold k ≤ threshold (m + 1) := by
  induction S using Finset.induction_on_max with
  | empty => intro m _; simpa using (threshold_pos (m + 1)).le
  | @insert a S ha ih =>
    intro m hm
    have han : a ∉ S := fun h => (lt_irrefl a) (ha a h)
    have hS := ih (a - 1) (fun k hk => by have := ha k hk; omega)
    have ham : a ≤ m := hm a (Finset.mem_insert_self a S)
    have hpow : threshold (a + 1) ≤ threshold (m + 1) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    have heq : threshold (a - 1 + 1) = threshold a := by congr 1; omega
    rw [heq] at hS
    rw [Finset.sum_insert han]
    calc
      threshold a + ∑ k ∈ S, threshold k ≤ threshold a + threshold a :=
        add_le_add (le_refl _) hS
      _ = threshold (a + 1) := by
        simp [threshold, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; ring
      _ ≤ threshold (m + 1) := hpow

lemma finite_layer_bound (S : Finset ℤ) (y : ℝ≥0∞) :
    (∑ k ∈ S, if ENNReal.ofReal (threshold k) < y then
      ENNReal.ofReal (threshold k) else 0) ≤ 2 * y := by
  classical
  let T := S.filter fun k => ENNReal.ofReal (threshold k) < y
  have heq : (∑ k ∈ S, if ENNReal.ofReal (threshold k) < y then
      ENNReal.ofReal (threshold k) else 0) = ∑ k ∈ T, ENNReal.ofReal (threshold k) := by
    simp [T, Finset.sum_filter]
  rw [heq]
  by_cases hT : T.Nonempty
  · let m := T.max' hT
    have hm : m ∈ T := Finset.max'_mem T hT
    have hb := sum_threshold_le T m (fun k hk => Finset.le_max' T k hk)
    calc
      ∑ k ∈ T, ENNReal.ofReal (threshold k) = ENNReal.ofReal (∑ k ∈ T, threshold k) :=
        (ENNReal.ofReal_sum_of_nonneg (fun k _ => (threshold_pos k).le)).symm
      _ ≤ ENNReal.ofReal (threshold (m + 1)) := ENNReal.ofReal_le_ofReal hb
      _ = 2 * ENNReal.ofReal (threshold m) := by
        rw [show threshold (m + 1) = 2 * threshold m by
          simp [threshold, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), mul_comm]]
        rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
      _ ≤ 2 * y := mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hm).2.le (by norm_num)
  · simp [Finset.not_nonempty_iff_eq_empty.mp hT]

lemma pointwise_layer_bound (y : ℝ≥0∞) :
    (∑' k : ℤ, if ENNReal.ofReal (threshold k) < y then
      ENNReal.ofReal (threshold k) else 0) ≤ 2 * y := by
  exact ENNReal.summable.tsum_le_of_sum_le fun S => finite_layer_bound S y

theorem dyadic_layer_bound :
    Specs.ExpandedFA.PartIV.HardyLevelDecomposition.dyadicLayerBoundType := by
  intro X _ μ G hG
  classical
  let F : ℤ → X → ℝ≥0∞ := fun k =>
    (level G k).indicator (fun _ => ENNReal.ofReal (threshold k))
  have hm (k : ℤ) : MeasurableSet (level G k) :=
    measurableSet_lt measurable_const hG
  have hF (k : ℤ) : Measurable (F k) := measurable_const.indicator (hm k)
  calc
    (∑' k : ℤ, ENNReal.ofReal (threshold k) * μ (level G k)) =
        ∑' k : ℤ, ∫⁻ x, F k x ∂μ := by
      congr 1
      funext k
      simp [F, lintegral_indicator (hm k)]
    _ = ∫⁻ x, ∑' k : ℤ, F k x ∂μ :=
      (lintegral_tsum (fun k => (hF k).aemeasurable)).symm
    _ ≤ ∫⁻ x, 2 * G x ∂μ := by
      apply lintegral_mono
      intro x
      simpa [F, level, Set.indicator_apply] using pointwise_layer_bound (G x)
    _ = 2 * ∫⁻ x, G x ∂μ := lintegral_const_mul _ hG

theorem level_measure_finite :
    Specs.ExpandedFA.PartIV.HardyLevelDecomposition.levelMeasureFiniteType := by
  intro X _ μ G hG hI k
  have hb : ENNReal.ofReal (threshold k) * μ (level G k) ≤ ∫⁻ x, G x ∂μ := by
    calc
      _ ≤ ENNReal.ofReal (threshold k) * μ {x | ENNReal.ofReal (threshold k) ≤ G x} :=
        by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply measure_mono
          intro x hx
          change ENNReal.ofReal (threshold k) ≤ G x
          exact le_of_lt (show ENNReal.ofReal (threshold k) < G x from hx)
      _ ≤ _ := mul_meas_ge_le_lintegral hG _
  have hne : ENNReal.ofReal (threshold k) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (threshold_pos k))
  exact ENNReal.lt_top_of_mul_ne_top_right (hb.trans_lt hI).ne hne

theorem grand_level_open :
    Specs.ExpandedFA.PartIV.HardyLevelDecomposition.grandLevelOpenType := by
  intro 𝕜 _ d N f hf k
  exact (HardyMaximal.grand_regularity N f hf).1.isOpen_preimage _

lemma level_antitone {X : Type*} (G : X → ℝ≥0∞) {k l : ℤ} (hkl : k ≤ l) :
    level G l ⊆ level G k := by
  intro x hx
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal
    (zpow_le_zpow_right₀ (by norm_num) hkl)) hx

theorem coordinate_levels :
    Specs.ExpandedFA.PartIV.HardyLevelDecomposition.coordinateLevelsType := by
  intro 𝕜 _ d N f hf hI k
  have hm := (grand_level_open N f hf k).measurableSet
  have hp := PiLp.volume_preserving_toLp (Fin d)
  refine ⟨(grand_level_open N f hf k).preimage (PiLp.continuous_toLp 2 _), ?_, ?_⟩
  · unfold coordinateLevel
    rw [hp.measure_preimage hm.nullMeasurableSet]
    exact level_measure_finite volume _ (HardyMaximal.grand_regularity N f hf).2 hI k
  · exact preimage_mono (level_antitone _ (show k ≤ k + 1 by omega))

theorem cube_volume :
    Specs.ExpandedFA.PartIV.HardyLevelDecomposition.cubeVolumeType := by
  intro d Q
  exact (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    (show NullMeasurableSet Q.carrier volume from
      (Metric.isClosed_closedBall.measurableSet).nullMeasurableSet)

theorem empty_good :
    Specs.ExpandedFA.PartIV.HardyLevelDecomposition.emptyGoodType := by
  intro 𝕜 _ d Ω f W hW
  letI : IsEmpty W.cubes := ⟨fun Q => by simpa [hW] using Q.property⟩
  funext x
  simp [good]

/-- Use the open interiors for disjointness and the equal-volume closed
cubes for the coefficient. This also covers the empty family. -/
theorem partition_volume_le {d : ℕ} {Ω : TopologicalSpace.Opens (Domain d)}
    {c C : ℝ} {A : ℕ → ℝ} {M : ℕ} {W : Partition Ω}
    (hW : PartitionEstimates c C A M W) :
    (∑' Q : W.cubes, volume (cubeRegion Q.val 1)) ≤ volume (Ω : Set (Domain d)) := by
  let B : W.cubes → Set (Domain d) :=
    fun Q => Metric.ball Q.val.center (Q.val.side / 2)
  have hBint (Q : W.cubes) : B Q ⊆ interior Q.val.carrier := by
    simpa only [DyadicCube.carrier, DyadicCube.dilate, one_mul] using
      (Metric.ball_subset_interior_closedBall (x := Q.val.center) (ε := Q.val.side / 2))
  have hBsub (Q : W.cubes) : B Q ⊆ (Ω : Set (Domain d)) :=
    (hBint Q).trans (interior_subset.trans
      (Q.val.carrier_subset_star.trans (hW.2.2.1 Q).2))
  have hBvol (Q : W.cubes) : volume (B Q) = volume (cubeRegion Q.val 1) := by
    rw [cube_volume, DyadicCube.volume_carrier]
    dsimp [B]
    rw [Real.volume_pi_ball _ (div_pos Q.val.side_pos (by norm_num))]
    simp only [Fintype.card_fin]
    congr 1
    congr 1
    ring
  have hdisj : Pairwise (fun Q R : W.cubes => Disjoint (B Q) (B R)) := by
    intro Q R hne
    exact (hW.2.1 Q.property R.property
      (fun heq => hne (Subtype.ext heq))).mono (hBint Q) (hBint R)
  calc
    (∑' Q : W.cubes, volume (cubeRegion Q.val 1)) = ∑' Q : W.cubes, volume (B Q) :=
      tsum_congr (fun Q => (hBvol Q).symm)
    _ = volume (⋃ Q : W.cubes, B Q) :=
      (measure_iUnion hdisj (fun _ => Metric.isOpen_ball.measurableSet)).symm
    _ ≤ volume (Ω : Set (Domain d)) := measure_mono (iUnion_subset hBsub)

/-- The all-integer coefficient estimate for any Whitney partitions of the
actual levels; no good-function or cancellation conclusions are assumed. -/
theorem coefficient_bound {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    (f : Euclidean d → 𝕜) (hf : Integrable f)
    (Ω : ℤ → TopologicalSpace.Opens (Domain d)) (W : ∀ k, Partition (Ω k))
    (hΩ : ∀ k, (Ω k : Set (Domain d)) = coordinateLevel N f k)
    {c C : ℝ} {A : ℕ → ℝ} {M : ℕ} (hC : 0 ≤ C)
    (hW : ∀ k, PartitionEstimates c C A M (W k)) :
    (∑' k : ℤ, ∑' Q : (W k).cubes,
      ENNReal.ofReal (C * threshold k) * volume (cubeRegion Q.val 1)) ≤
        2 * ENNReal.ofReal C * ∫⁻ x, grand N f x := by
  have hmeasure (k : ℤ) : volume (Ω k : Set (Domain d)) =
      volume (level (grand N f) k) := by
    rw [hΩ k]
    exact (PiLp.volume_preserving_toLp (Fin d)).measure_preimage
      (grand_level_open N f hf k).measurableSet.nullMeasurableSet
  calc
    _ = ENNReal.ofReal C * ∑' k : ℤ,
        ENNReal.ofReal (threshold k) * ∑' Q : (W k).cubes,
          volume (cubeRegion Q.val 1) := by
      simp_rw [ENNReal.ofReal_mul hC, ENNReal.tsum_mul_left, mul_assoc]
      rw [ENNReal.tsum_mul_left]
    _ ≤ ENNReal.ofReal C * ∑' k : ℤ,
        ENNReal.ofReal (threshold k) * volume (level (grand N f) k) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply ENNReal.tsum_le_tsum
      intro k
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← hmeasure]
      exact partition_volume_le (hW k)
    _ ≤ ENNReal.ofReal C * (2 * ∫⁻ x, grand N f x) :=
      mul_le_mul_of_nonneg_left
        (dyadic_layer_bound volume _ (HardyMaximal.grand_regularity N f hf).2) (by positivity)
    _ = _ := by ring

/-- Empty levels use an actual empty index type. -/
def emptyPartition {d : ℕ} (Ω : TopologicalSpace.Opens (Domain d)) : Partition Ω where
  cubes := ∅
  weight := fun Q => False.elim (Set.notMem_empty _ Q.property)

lemma empty_partition_estimates {d : ℕ} {Ω : TopologicalSpace.Opens (Domain d)}
    (hΩ : (Ω : Set (Domain d)) = ∅) (c C : ℝ) (A : ℕ → ℝ) (M : ℕ) :
    PartitionEstimates c C A M (emptyPartition Ω) := by
  classical
  letI : IsEmpty (emptyPartition Ω).cubes := ⟨fun Q => Q.property⟩
  simp only [PartitionEstimates]
  refine ⟨?_, ?_, ?_, locallyFinite_of_finite _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hΩ.symm
  · simp [emptyPartition, Set.Pairwise]
  · exact fun Q => isEmptyElim Q
  · intro x
    have he : {Q : (emptyPartition Ω).cubes | x ∈ Q.val.star} = ∅ := by
      ext Q
      exact isEmptyElim Q
    rw [he]
    exact ⟨finite_empty, by simp⟩
  · exact fun Q => isEmptyElim Q
  · exact fun Q => isEmptyElim Q
  · intro x hx
    change x ∈ (Ω : Set (Domain d)) at hx
    rw [hΩ] at hx
    exact hx.elim
  · exact fun Q => isEmptyElim Q
  · exact fun Q => isEmptyElim Q
  · exact fun Q => isEmptyElim Q

lemma nested_estimates_empty_fine {d : ℕ} {Ω Ω' : TopologicalSpace.Opens (Domain d)}
    (C : ℝ) (M : ℕ) (W : Partition Ω) :
    NestedEstimates C M W (emptyPartition Ω') := by
  letI : IsEmpty (emptyPartition Ω').cubes := ⟨fun Q => Q.property⟩
  exact ⟨fun R => isEmptyElim R, fun R => isEmptyElim R⟩

/-- Extend the simultaneous Whitney choice to all finite-measure open sets.
When a coarse level is empty, every contained fine level is empty too. -/
theorem finite_open_partitions (d : ℕ) (hd : 0 < d) :
    ∃ (c C : ℝ) (A : ℕ → ℝ) (M : ℕ),
      0 < c ∧ 1 ≤ C ∧ (∀ j, 0 < A j) ∧ 0 < M ∧
      ∀ (Ω : ℤ → TopologicalSpace.Opens (Domain d)),
        (∀ k, volume (Ω k : Set (Domain d)) < ⊤) →
        (∀ k, (Ω (k + 1) : Set (Domain d)) ⊆ Ω k) →
        ∃ W : ∀ k, Partition (Ω k),
          (∀ k, PartitionEstimates c C A M (W k)) ∧
          (∀ k, NestedEstimates C M (W k) (W (k + 1))) ∧
          (∀ k, (Ω k : Set (Domain d)) = ∅ → (W k).cubes = ∅) := by
  classical
  obtain ⟨c, C, A, M, hc, hC, hA, hM, V, hV, hVN⟩ :=
    HardyWhitney.smooth_whitney d hd
  refine ⟨c, C, A, M, hc, hC, hA, hM, ?_⟩
  intro Ω hfin hnest
  let W : ∀ k, Partition (Ω k) := fun k =>
    if h : (Ω k : Set (Domain d)).Nonempty then
      V ⟨Ω k, h, hfin k⟩ else emptyPartition (Ω k)
  refine ⟨W, ?_, ?_, ?_⟩
  · intro k
    dsimp only [W]
    split_ifs with h
    · exact hV _
    · exact empty_partition_estimates (not_nonempty_iff_eq_empty.mp h) c C A M
  · intro k
    by_cases h : (Ω (k + 1) : Set (Domain d)).Nonempty
    · have hk : (Ω k : Set (Domain d)).Nonempty := h.mono (hnest k)
      simpa only [W, dite_eq_left h, dite_eq_left hk] using
        hVN ⟨Ω k, hk, hfin k⟩ ⟨Ω (k + 1), h, hfin (k + 1)⟩ (hnest k)
    · simp only [W, dite_eq_right h]
      exact nested_estimates_empty_fine C M _
  · intro k hk
    have h : ¬ (Ω k : Set (Domain d)).Nonempty := by simp [hk]
    simp [W, h, emptyPartition]

theorem level_partitions :
    Specs.ExpandedFA.PartIV.HardyLevelDecomposition.levelPartitionsType := by
  intro d hd
  obtain ⟨c, C, A, M, hc, hC, hA, hM, hpart⟩ := finite_open_partitions d hd
  refine ⟨c, C, A, M, hc, hC, hA, hM, ?_⟩
  intro 𝕜 _ N f hf hI
  let Ω : ℤ → TopologicalSpace.Opens (Domain d) :=
    fun k => ⟨coordinateLevel N f k, (coordinate_levels N f hf hI k).1⟩
  obtain ⟨W, hW, hWN, hWe⟩ := hpart Ω
    (fun k => (coordinate_levels N f hf hI k).2.1)
    (fun k => (coordinate_levels N f hf hI k).2.2)
  refine ⟨Ω, W, fun _ => rfl, hW, hWN, hWe, ?_⟩
  exact coefficient_bound f hf Ω W (fun _ => rfl) (by linarith) hW

section SingleLevel

variable {d : ℕ} {Ω : TopologicalSpace.Opens (Domain d)}
  {c C : ℝ} {A : ℕ → ℝ} {M : ℕ} {W : Partition Ω}

lemma weight_finite_support (hW : PartitionEstimates c C A M W)
    (x : Euclidean d) : Function.HasFiniteSupport (fun Q : W.cubes => weight W Q x) := by
  obtain ⟨_, _, _, _, hoverlap, _, hsupp, _⟩ := hW
  exact (hoverlap (coordinates x)).1.subset fun Q hQ => hsupp Q
    (subset_tsupport (W.weight Q) hQ)

lemma weight_zero_off (Q : W.cubes) {x : Euclidean d}
    (hx : coordinates x ∉ (Ω : Set (Domain d))) : weight W Q x = 0 := by
  by_contra hn
  exact hx ((W.weight Q).tsupport_subset
    (subset_tsupport (W.weight Q) hn))

lemma weight_zero_off_star (hW : PartitionEstimates c C A M W)
    (Q : W.cubes) {x : Euclidean d} (hx : coordinates x ∉ Q.val.star) :
    weight W Q x = 0 := by
  obtain ⟨_, _, _, _, _, _, hsupp, _⟩ := hW
  by_contra hn
  exact hx (hsupp Q (subset_tsupport (W.weight Q) hn))

lemma weight_sum (hW : PartitionEstimates c C A M W)
    {x : Euclidean d} (hx : coordinates x ∈ (Ω : Set (Domain d))) :
    (∑' Q : W.cubes, weight W Q x) = 1 := by
  have hfinite := weight_finite_support hW x
  obtain ⟨_, _, _, _, _, _, _, hsum, _⟩ := hW
  rw [tsum_eq_finsum hfinite]
  exact hsum _ hx

lemma weight_nonneg (hW : PartitionEstimates c C A M W)
    (Q : W.cubes) (x : Euclidean d) : 0 ≤ weight W Q x := by
  obtain ⟨_, _, _, _, _, hpos, _⟩ := hW
  exact hpos Q (coordinates x)

lemma weight_le_one (hW : PartitionEstimates c C A M W)
    (Q : W.cubes) (x : Euclidean d) : weight W Q x ≤ 1 := by
  classical
  by_cases hx : coordinates x ∈ (Ω : Set (Domain d))
  · have hs : Summable (fun R : W.cubes => weight W R x) :=
      summable_of_hasFiniteSupport (weight_finite_support hW x)
    calc
      weight W Q x ≤ ∑' R : W.cubes, weight W R x :=
        hs.le_tsum Q (fun R _ => weight_nonneg hW R x)
      _ = 1 := weight_sum hW hx
  · rw [weight_zero_off Q hx]
    norm_num

lemma weight_continuous (Q : W.cubes) : Continuous (weight W Q) :=
  (W.weight Q).continuous.comp (PiLp.continuous_ofLp 2 _)

lemma weight_integrable (Q : W.cubes) : Integrable (weight W Q) :=
  (PiLp.volume_preserving_ofLp (Fin d)).integrable_comp_of_integrable
    ((W.weight Q).continuous.integrable_of_hasCompactSupport (W.weight Q).hasCompactSupport)

lemma weight_integral_eq (Q : W.cubes) :
    (∫ x, weight W Q x) = ∫ y, W.weight Q y :=
  (PiLp.volume_preserving_ofLp (Fin d)).integral_comp
    (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).measurableEmbedding _

lemma weight_integral_pos (hW : PartitionEstimates c C A M W) (hc : 0 < c)
    (Q : W.cubes) : 0 < ∫ x, weight W Q x := by
  obtain ⟨_, _, _, _, _, _, _, _, hint, _⟩ := hW
  rw [weight_integral_eq]
  exact (mul_pos hc (by rw [DyadicCube.volume_carrier_toReal]; exact pow_pos Q.val.side_pos d)).trans_le
    (hint Q).2

variable {𝕜 : Type} [RCLike 𝕜]

lemma weighted_integrable (hW : PartitionEstimates c C A M W)
    {f : Euclidean d → 𝕜} (hf : Integrable f) (Q : W.cubes) :
    Integrable (fun x => weight W Q x • f x) := by
  exact hf.bdd_smul 1 (weight_continuous Q).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (weight_nonneg hW Q x)]
      exact weight_le_one hW Q x)

lemma bad_integrable (hW : PartitionEstimates c C A M W)
    {f : Euclidean d → 𝕜} (hf : Integrable f) (Q : W.cubes) :
    Integrable (bad f W Q) := by
  apply ((weighted_integrable hW hf Q).sub
    ((weight_integrable Q).smul_const (average f W Q))).congr
  exact Eventually.of_forall fun x => (smul_sub (weight W Q x) (f x) (average f W Q)).symm

lemma bad_integral_zero (hW : PartitionEstimates c C A M W) (hc : 0 < c)
    {f : Euclidean d → 𝕜} (hf : Integrable f) (Q : W.cubes) :
    (∫ x, bad f W Q x) = 0 := by
  simp only [bad, smul_sub]
  rw [integral_sub (weighted_integrable hW hf Q)
    ((weight_integrable Q).smul_const (average f W Q)), integral_smul_const]
  simp only [average, smul_smul, mul_inv_cancel₀ (ne_of_gt (weight_integral_pos hW hc Q)),
    one_smul, sub_self]

lemma bad_finite_support (hW : PartitionEstimates c C A M W)
    (f : Euclidean d → 𝕜) (x : Euclidean d) :
    Function.HasFiniteSupport (fun Q : W.cubes => bad f W Q x) := by
  apply (weight_finite_support hW x).subset
  intro Q hQ
  change weight W Q x ≠ 0
  intro hz
  exact hQ (by simp [bad, hz])

lemma good_eq_off (f : Euclidean d → 𝕜) {x : Euclidean d}
    (hx : coordinates x ∉ (Ω : Set (Domain d))) : good f W x = f x := by
  have hzero (Q : W.cubes) : bad f W Q x = 0 := by
    simp [bad, weight_zero_off Q hx]
  simp [good, hzero]

lemma good_eq_on (hW : PartitionEstimates c C A M W)
    (f : Euclidean d → 𝕜) {x : Euclidean d}
    (hx : coordinates x ∈ (Ω : Set (Domain d))) :
    good f W x = ∑' Q : W.cubes, weight W Q x • average f W Q := by
  have hs : Summable (fun Q : W.cubes => weight W Q x) :=
    summable_of_hasFiniteSupport (weight_finite_support hW x)
  have ha : Summable (fun Q : W.cubes => weight W Q x • average f W Q) :=
    summable_of_hasFiniteSupport ((weight_finite_support hW x).smul_left _)
  simp only [good, bad, smul_sub]
  rw [(hs.smul_const (f x)).tsum_sub ha, hs.tsum_smul_const, weight_sum hW hx, one_smul]
  exact sub_sub_cancel _ _

/-- Once the Whitney averages are bounded, the bad series has an integrable
majorant on its level. This lemma does not assume a bound for the good part. -/
lemma bad_norm_sum_le (hW : PartitionEstimates c C A M W)
    (f : Euclidean d → 𝕜) {B : ℝ}
    (havg : ∀ Q : W.cubes, ‖average f W Q‖ ≤ B) (x : Euclidean d) :
    (∑' Q : W.cubes, ‖bad f W Q x‖) ≤
      (coordinates ⁻¹' (Ω : Set (Domain d))).indicator (fun y => ‖f y‖ + B) x := by
  classical
  by_cases hx : coordinates x ∈ (Ω : Set (Domain d))
  · rw [indicator_of_mem (show x ∈ coordinates ⁻¹' (Ω : Set (Domain d)) from hx)]
    have hs : Summable (fun Q : W.cubes => weight W Q x) :=
      summable_of_hasFiniteSupport (weight_finite_support hW x)
    have hn : Summable (fun Q : W.cubes => ‖bad f W Q x‖) := by
      exact (summable_of_hasFiniteSupport (bad_finite_support hW f x) :
        Summable (fun Q : W.cubes => bad f W Q x)).norm
    calc
      _ ≤ ∑' Q : W.cubes, weight W Q x * (‖f x‖ + B) := by
        apply hn.tsum_le_tsum _ (hs.mul_right _)
        intro Q
        rw [bad, norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg hW Q x)]
        exact mul_le_mul_of_nonneg_left
          ((norm_sub_le _ _).trans (add_le_add (le_refl _) (havg Q))) (weight_nonneg hW Q x)
      _ = (∑' Q : W.cubes, weight W Q x) * (‖f x‖ + B) := hs.tsum_mul_right _
      _ = _ := by rw [weight_sum hW hx, one_mul]
  · have hz (Q : W.cubes) : bad f W Q x = 0 := by
      simp [bad, weight_zero_off Q hx]
    simp [hz, indicator_of_notMem (show x ∉ coordinates ⁻¹' (Ω : Set (Domain d)) from hx)]

lemma level_majorant_integrable {f : Euclidean d → 𝕜} (hf : Integrable f)
    (hΩ : volume (Ω : Set (Domain d)) < ⊤) (B : ℝ) :
    Integrable ((coordinates ⁻¹' (Ω : Set (Domain d))).indicator (fun x => ‖f x‖ + B)) := by
  have hm : MeasurableSet (coordinates ⁻¹' (Ω : Set (Domain d))) :=
    Ω.isOpen.measurableSet.preimage (PiLp.continuous_ofLp 2 _).measurable
  have hfin : volume (coordinates ⁻¹' (Ω : Set (Domain d))) ≠ ⊤ := by
    unfold coordinates
    rw [(PiLp.volume_preserving_ofLp (Fin d)).measure_preimage Ω.isOpen.measurableSet.nullMeasurableSet]
    exact hΩ.ne
  exact (hf.norm.integrableOn.add (integrableOn_const hfin)).integrable_indicator hm

lemma bad_norm_sum_integrable (hW : PartitionEstimates c C A M W)
    {f : Euclidean d → 𝕜} (hf : Integrable f)
    (hΩ : volume (Ω : Set (Domain d)) < ⊤) {B : ℝ}
    (havg : ∀ Q : W.cubes, ‖average f W Q‖ ≤ B) :
    Integrable (fun x => ∑' Q : W.cubes, ‖bad f W Q x‖) := by
  apply (level_majorant_integrable hf hΩ B).mono'
    (AEStronglyMeasurable.tsum (fun Q => (bad_integrable hW hf Q).aestronglyMeasurable.norm))
  exact Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
    exact bad_norm_sum_le hW f havg x

lemma bad_absolute_integral_sum (hW : PartitionEstimates c C A M W)
    {f : Euclidean d → 𝕜} (hf : Integrable f)
    (hΩ : volume (Ω : Set (Domain d)) < ⊤) {B : ℝ}
    (havg : ∀ Q : W.cubes, ‖average f W Q‖ ≤ B) :
    (∑' Q : W.cubes, ∫⁻ x, ENNReal.ofReal ‖bad f W Q x‖) < ⊤ := by
  rw [← lintegral_tsum (f := fun Q x => ENNReal.ofReal ‖bad f W Q x‖) (fun Q =>
    ENNReal.measurable_ofReal.comp_aemeasurable (bad_integrable hW hf Q).aestronglyMeasurable.norm.aemeasurable)]
  have hs (x : Euclidean d) : Summable (fun Q : W.cubes => ‖bad f W Q x‖) := by
    exact (summable_of_hasFiniteSupport (bad_finite_support hW f x) :
      Summable (fun Q : W.cubes => bad f W Q x)).norm
  simp_rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hs _)]
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ =>
    tsum_nonneg (fun _ => norm_nonneg _))).mp
      (bad_norm_sum_integrable hW hf hΩ havg).hasFiniteIntegral

lemma good_integrable_of_average_bound (hW : PartitionEstimates c C A M W)
    {f : Euclidean d → 𝕜} (hf : Integrable f)
    (hΩ : volume (Ω : Set (Domain d)) < ⊤) {B : ℝ}
    (havg : ∀ Q : W.cubes, ‖average f W Q‖ ≤ B) : Integrable (good f W) := by
  have hbad : Integrable (fun x => ∑' Q : W.cubes, bad f W Q x) := by
    apply (bad_norm_sum_integrable hW hf hΩ havg).mono'
      (AEStronglyMeasurable.tsum (fun Q => (bad_integrable hW hf Q).aestronglyMeasurable))
    exact Eventually.of_forall fun x => norm_tsum_le_tsum_norm (by
      exact (summable_of_hasFiniteSupport (bad_finite_support hW f x) :
        Summable (fun Q : W.cubes => bad f W Q x)).norm)
  exact hf.sub hbad

lemma good_bound_of_average_bound (hW : PartitionEstimates c C A M W)
    (f : Euclidean d → 𝕜) {B : ℝ}
    (havg : ∀ Q : W.cubes, ‖average f W Q‖ ≤ B)
    (hout : ∀ᵐ x, coordinates x ∉ (Ω : Set (Domain d)) → ‖f x‖ ≤ B) :
    ∀ᵐ x, ‖good f W x‖ ≤ B := by
  filter_upwards [hout] with x hx
  by_cases hmem : coordinates x ∈ (Ω : Set (Domain d))
  · rw [good_eq_on hW f hmem]
    have hs : Summable (fun Q : W.cubes => weight W Q x) :=
      summable_of_hasFiniteSupport (weight_finite_support hW x)
    have hsum : HasSum (fun Q : W.cubes => weight W Q x * B) B := by
      simpa only [weight_sum hW hmem, one_mul] using (hs.hasSum.mul_right B)
    apply tsum_of_norm_bounded hsum
    intro Q
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg hW Q x)]
    exact mul_le_mul_of_nonneg_left (havg Q) (weight_nonneg hW Q x)
  · rw [good_eq_off f hmem]
    exact hx hmem

/-- Quantitative L¹ error bound, ready to apply to high levels once the
grand-test estimate for the actual Whitney averages is proved. -/
lemma good_error_le (hW : PartitionEstimates c C A M W)
    {f : Euclidean d → 𝕜} (hf : Integrable f)
    (hΩ : volume (Ω : Set (Domain d)) < ⊤) {B : ℝ}
    (havg : ∀ Q : W.cubes, ‖average f W Q‖ ≤ B) :
    (∫ x, ‖good f W x - f x‖) ≤
      (∫ x in coordinates ⁻¹' (Ω : Set (Domain d)), ‖f x‖) +
        B * (volume (Ω : Set (Domain d))).toReal := by
  let E := coordinates ⁻¹' (Ω : Set (Domain d))
  have hm : MeasurableSet E :=
    Ω.isOpen.measurableSet.preimage (PiLp.continuous_ofLp 2 _).measurable
  have hvol : volume E = volume (Ω : Set (Domain d)) :=
    (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage Ω.isOpen.measurableSet.nullMeasurableSet
  calc
    _ ≤ ∫ x, E.indicator (fun y => ‖f y‖ + B) x := by
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
        (level_majorant_integrable hf hΩ B)
      apply Eventually.of_forall
      intro x
      have hnorm : ‖good f W x - f x‖ = ‖∑' Q : W.cubes, bad f W Q x‖ := by
        simp [good, sub_sub_cancel_left]
      change ‖good f W x - f x‖ ≤ _
      rw [hnorm]
      exact (norm_tsum_le_tsum_norm (by
        exact (summable_of_hasFiniteSupport (bad_finite_support hW f x) :
          Summable (fun Q : W.cubes => bad f W Q x)).norm)).trans
            (bad_norm_sum_le hW f havg x)
    _ = (∫ x in E, ‖f x‖) + B * (volume E).toReal := by
      rw [integral_indicator hm, integral_add hf.norm.integrableOn
        (integrableOn_const (hvol.trans_ne hΩ.ne)), setIntegral_const]
      simp [measureReal_def, smul_eq_mul, mul_comm]
    _ = _ := by rw [hvol]

end SingleLevel

section TwoLevels

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
  {Ω Ω' : TopologicalSpace.Opens (Domain d)}
  {c C c' C' : ℝ} {A A' : ℕ → ℝ} {M M' : ℕ}
  {W : Partition Ω} {W' : Partition Ω'}

lemma correction_bracket_integrable
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c' C' A' M' W')
    {f : Euclidean d → 𝕜} (hf : Integrable f) (Q : W.cubes) (R : W'.cubes) :
    Integrable (fun x => weight W Q x • bad f W' R x -
      weight W' R x • correction f W W' Q R) := by
  exact (weighted_integrable hW (bad_integrable hW' hf R) Q).sub
    ((weight_integrable R).smul_const _)

lemma correction_bracket_integral_zero
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c' C' A' M' W')
    (hc' : 0 < c') {f : Euclidean d → 𝕜} (hf : Integrable f)
    (Q : W.cubes) (R : W'.cubes) :
    (∫ x, weight W Q x • bad f W' R x -
      weight W' R x • correction f W W' Q R) = 0 := by
  rw [integral_sub (weighted_integrable hW (bad_integrable hW' hf R) Q)
    ((weight_integrable R).smul_const _), integral_smul_const]
  simp only [correction, smul_smul,
    mul_inv_cancel₀ (ne_of_gt (weight_integral_pos hW' hc' R)), one_smul, sub_self]

lemma correction_zero_of_no_inter
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c' C' A' M' W')
    (f : Euclidean d → 𝕜) (Q : W.cubes) (R : W'.cubes)
    (h : ¬ (R.val.star ∩ Q.val.star).Nonempty) : correction f W W' Q R = 0 := by
  have hz (x : Euclidean d) : weight W Q x • bad f W' R x = 0 := by
    by_cases hx : coordinates x ∈ Q.val.star
    · have hr : coordinates x ∉ R.val.star := fun hy => h ⟨coordinates x, hy, hx⟩
      simp [bad, weight_zero_off_star hW' R hr]
    · rw [weight_zero_off_star hW Q hx, zero_smul]
  simp only [correction, hz, integral_zero, smul_zero]

lemma piece_zero_off_dilate
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c' C' A' M' W')
    {D : ℝ} {L : ℕ} (hD : 9 / 8 ≤ D) (hN : NestedEstimates D L W W')
    (f : Euclidean d → 𝕜) (Q : W.cubes) (x : Euclidean d)
    (hx : x ∉ cubeRegion Q.val D) : piece f W W' Q x = 0 := by
  have hstar : Q.val.star ⊆ Q.val.dilate D := by
    apply Metric.closedBall_subset_closedBall
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hD Q.val.side_nonneg)
      (by norm_num)
  have hQ : weight W Q x = 0 :=
    weight_zero_off_star hW Q (fun hy => hx (hstar hy))
  have hz (R : W'.cubes) : weight W Q x • bad f W' R x -
      weight W' R x • correction f W W' Q R = 0 := by
    by_cases h : (R.val.star ∩ Q.val.star).Nonempty
    · have hr : weight W' R x = 0 :=
        weight_zero_off_star hW' R (fun hy => hx ((hN.1 R Q h).2 hy))
      simp [hQ, hr]
    · simp [hQ, correction_zero_of_no_inter hW hW' f Q R h]
  simp only [piece, hz, tsum_zero, sub_zero]
  simp [bad, hQ]

end TwoLevels

lemma threshold_tendsto_atTop : Tendsto threshold atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt b (by norm_num : (1 : ℝ) < 2)
  filter_upwards [eventually_ge_atTop (n : ℤ)] with k hk
  exact hn.le.trans (by
    simpa only [threshold, zpow_natCast] using
      (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk))

lemma threshold_tendsto_atBot : Tendsto threshold atBot (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hs : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨n, hn⟩ := Metric.tendsto_atTop.mp hs ε hε
  filter_upwards [eventually_le_atBot (-(n : ℤ))] with k hk
  rw [Real.dist_eq, sub_zero, abs_of_pos (threshold_pos k)]
  calc
    threshold k ≤ threshold (-(n : ℤ)) := zpow_le_zpow_right₀ (by norm_num) hk
    _ = (1 / 2 : ℝ) ^ n := by simp [threshold, zpow_neg, inv_pow, one_div]
    _ < ε := by simpa [Real.dist_eq, abs_of_nonneg] using hn n le_rfl

/-- An L∞ bound tending to zero implies convergence against every L¹ test.
The eventual application is the low-level limit of the actual good functions. -/
theorem pairing_tendsto_zero {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (g : ℤ → Euclidean d → 𝕜) (C : ℝ)
    (hg : ∀ k, ∀ᵐ x, ‖g k x‖ ≤ C * threshold k)
    (φ : Euclidean d → 𝕜) (hφ : Integrable φ) :
    Tendsto (fun k : ℤ => ∫ x, φ x * g k x) atBot (𝓝 0) := by
  have hb (k : ℤ) : ‖∫ x, φ x * g k x‖ ≤ (C * threshold k) * ∫ x, ‖φ x‖ := by
    calc
      _ ≤ ∫ x, (C * threshold k) * ‖φ x‖ :=
        norm_integral_le_of_norm_le (hφ.norm.const_mul _) (by
          filter_upwards [hg k] with x hx
          rw [norm_mul, mul_comm (C * threshold k)]
          exact mul_le_mul_of_nonneg_left hx (norm_nonneg _))
      _ = _ := integral_const_mul _ _
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) hb
  simpa using (tendsto_const_nhds.mul threshold_tendsto_atBot).mul_const (∫ x, ‖φ x‖)

/-- Integrability of the dyadic layer sum forces every high-level mass to vanish. -/
lemma level_mass_tendsto_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (G : X → ℝ≥0∞) (hG : Measurable G)
    (hI : (∫⁻ x, G x ∂μ) < ⊤) :
    Tendsto (fun k : ℤ => ENNReal.ofReal (threshold k) * μ (level G k)) atTop (𝓝 0) := by
  have hsum : (∑' k : ℤ, ENNReal.ofReal (threshold k) * μ (level G k)) ≠ ⊤ :=
    ne_of_lt ((dyadic_layer_bound μ G hG).trans_lt (by finiteness))
  exact (ENNReal.tendsto_cofinite_zero_of_tsum_ne_top hsum).mono_left atTop_le_cofinite

lemma level_mass_toReal_tendsto_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (G : X → ℝ≥0∞) (hG : Measurable G)
    (hI : (∫⁻ x, G x ∂μ) < ⊤) :
    Tendsto (fun k : ℤ => threshold k * (μ (level G k)).toReal) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (level_mass_tendsto_zero μ G hG hI)
  simpa only [Function.comp_def, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (threshold_pos _).le, ENNReal.toReal_zero] using h

lemma level_measure_tendsto_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (G : X → ℝ≥0∞) (hG : Measurable G)
    (hI : (∫⁻ x, G x ∂μ) < ⊤) :
    Tendsto (fun k : ℤ => μ (level G k)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (level_mass_tendsto_zero μ G hG hI)
  · exact Eventually.of_forall (fun _ => zero_le)
  · filter_upwards [eventually_ge_atTop (0 : ℤ)] with k hk
    have hpow : (1 : ℝ) ≤ threshold k := by
      simpa only [threshold, zpow_zero] using
        (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk)
    have he : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (threshold k) := by
      simpa using ENNReal.ofReal_le_ofReal hpow
    simpa only [one_mul] using mul_le_mul' he (le_refl (μ (level G k)))

lemma level_integral_tendsto_zero {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (G : X → ℝ≥0∞) (hG : Measurable G)
    (hI : (∫⁻ x, G x ∂μ) < ⊤) (f : X → ℝ) (hf : Integrable f μ) :
    Tendsto (fun k : ℤ => ∫ x in level G k, f x ∂μ) atTop (𝓝 0) :=
  hf.tendsto_setIntegral_nhds_zero (level_measure_tendsto_zero μ G hG hI)


lemma good_tendsto_L1_of_average_bound {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    (f : Euclidean d → 𝕜) (hf : Integrable f) (hI : (∫⁻ x, grand N f x) < ⊤)
    (Ω : ℤ → TopologicalSpace.Opens (Domain d)) (W : ∀ k, Partition (Ω k))
    (hΩ : ∀ k, (Ω k : Set (Domain d)) = coordinateLevel N f k)
    {c C : ℝ} {A : ℕ → ℝ} {M : ℕ}
    (hW : ∀ k, PartitionEstimates c C A M (W k)) (B : ℝ)
    (havg : ∀ k (Q : (W k).cubes), ‖average f (W k) Q‖ ≤ B * threshold k) :
    Tendsto (fun k : ℤ => ∫ x, ‖good f (W k) x - f x‖) atTop (𝓝 0) := by
  have hmeas := (HardyMaximal.grand_regularity N f hf).2
  have hmeasure (k : ℤ) : volume (Ω k : Set (Domain d)) =
      volume (level (grand N f) k) := by
    rw [hΩ k]
    exact (PiLp.volume_preserving_toLp (Fin d)).measure_preimage
      (grand_level_open N f hf k).measurableSet.nullMeasurableSet
  have hpreimage (k : ℤ) : coordinates ⁻¹' (Ω k : Set (Domain d)) = level (grand N f) k := by
    rw [hΩ k]
    ext x
    simp [coordinateLevel, coordinates]
  have hbound (k : ℤ) : (∫ x, ‖good f (W k) x - f x‖) ≤
      (∫ x in level (grand N f) k, ‖f x‖) +
        B * (threshold k * (volume (level (grand N f) k)).toReal) := by
    have hfin : volume (Ω k : Set (Domain d)) < ⊤ := by
      rw [hmeasure]
      exact level_measure_finite volume _ hmeas hI k
    simpa only [hpreimage, hmeasure, mul_assoc] using
      good_error_le (hW k) hf hfin (havg k)
  apply squeeze_zero (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hbound
  simpa only [mul_zero, add_zero] using
    (level_integral_tendsto_zero volume _ hmeas hI _ hf.norm).add
      ((level_mass_toReal_tendsto_zero volume _ hmeas hI).const_mul B)


end ExpandedFA.PartIV.HardyLevel


namespace ExpandedFA.PartIV.HardyLevel
open ExpandedFA.Distributions ExpandedFA.Fourier HardyWhitney HardyMaximalSpec

section
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : TopologicalSpace.Opens (Domain d)}
  {c C : ℝ} {A : ℕ → ℝ} {M : ℕ} {W : Partition Ω}

lemma weight_sum_le_one (hW : PartitionEstimates c C A M W) (x : Euclidean d) :
    (∑' Q : W.cubes, weight W Q x) ≤ 1 := by
  by_cases hx : coordinates x ∈ (Ω : Set (Domain d))
  · rw [weight_sum hW hx]
  · simp only [weight_zero_off _ hx, tsum_zero]; norm_num

lemma weighted_norm_integrable (hW : PartitionEstimates c C A M W)
    {f : Euclidean d → 𝕜} (hf : Integrable f) (Q : W.cubes) :
    Integrable (fun x => weight W Q x * ‖f x‖) := by
  simpa only [smul_eq_mul] using weighted_integrable hW hf.norm Q

lemma average_norm_mass_le (hW : PartitionEstimates c C A M W) (hc : 0 < c)
    {f : Euclidean d → 𝕜} (hf : Integrable f) (Q : W.cubes) :
    (∫ x, weight W Q x) * ‖average f W Q‖ ≤ ∫ x, weight W Q x * ‖f x‖ := by
  have hm := weight_integral_pos hW hc Q
  calc
    _ = ‖∫ x, weight W Q x • f x‖ := by
      rw [average, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm)]
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hm), one_mul]
    _ ≤ ∫ x, ‖weight W Q x • f x‖ := norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        change ‖weight W Q x • f x‖ = weight W Q x * ‖f x‖
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg hW Q x)]

lemma bad_integral_norm_le (hW : PartitionEstimates c C A M W) (hc : 0 < c)
    {f : Euclidean d → 𝕜} (hf : Integrable f) (Q : W.cubes) :
    (∫ x, ‖bad f W Q x‖) ≤ 2 * ∫ x, weight W Q x * ‖f x‖ := by
  calc
    _ ≤ ∫ x, weight W Q x * ‖f x‖ + weight W Q x * ‖average f W Q‖ := by
      apply integral_mono (bad_integrable hW hf Q).norm
        ((weighted_norm_integrable hW hf Q).add ((weight_integrable Q).mul_const _))
      intro x
      change ‖bad f W Q x‖ ≤ weight W Q x * ‖f x‖ + weight W Q x * ‖average f W Q‖
      rw [bad, norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg hW Q x), ← mul_add]
      exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (weight_nonneg hW Q x)
    _ = (∫ x, weight W Q x * ‖f x‖) + (∫ x, weight W Q x) * ‖average f W Q‖ := by
      rw [integral_add (weighted_norm_integrable hW hf Q) ((weight_integrable Q).mul_const _),
        integral_mul_const]
    _ ≤ _ := by linarith [average_norm_mass_le hW hc hf Q]

lemma weighted_norm_lintegral_sum_le (hW : PartitionEstimates c C A M W)
    {f : Euclidean d → 𝕜} (hf : Integrable f) :
    (∑' Q : W.cubes, ∫⁻ x, ENNReal.ofReal (weight W Q x * ‖f x‖)) ≤
      ∫⁻ x, ENNReal.ofReal ‖f x‖ := by
  rw [← lintegral_tsum (f := fun (Q : W.cubes) x => ENNReal.ofReal (weight W Q x * ‖f x‖))
    (fun Q => ENNReal.measurable_ofReal.comp_aemeasurable
    (weighted_norm_integrable hW hf Q).aestronglyMeasurable.aemeasurable)]
  apply lintegral_mono
  intro x
  change (∑' Q : W.cubes, ENNReal.ofReal (weight W Q x * ‖f x‖)) ≤ ENNReal.ofReal ‖f x‖
  have hs : Summable (fun Q : W.cubes => weight W Q x) :=
    summable_of_hasFiniteSupport (weight_finite_support hW x)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun Q => mul_nonneg (weight_nonneg hW Q x) (norm_nonneg _))
    (hs.mul_right _), hs.tsum_mul_right]
  exact ENNReal.ofReal_le_ofReal (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (weight_sum_le_one hW x) (norm_nonneg (f x)))

lemma bad_absolute_integral_sum_le (hW : PartitionEstimates c C A M W) (hc : 0 < c)
    {f : Euclidean d → 𝕜} (hf : Integrable f) :
    (∑' Q : W.cubes, ∫⁻ x, ENNReal.ofReal ‖bad f W Q x‖) ≤
      2 * ∫⁻ x, ENNReal.ofReal ‖f x‖ := by
  calc
    _ ≤ ∑' Q : W.cubes, 2 * ∫⁻ x, ENNReal.ofReal (weight W Q x * ‖f x‖) := by
      apply ENNReal.tsum_le_tsum
      intro Q
      rw [← ofReal_integral_eq_lintegral_ofReal (bad_integrable hW hf Q).norm
        (Eventually.of_forall fun _ => norm_nonneg _),
        ← ofReal_integral_eq_lintegral_ofReal (weighted_norm_integrable hW hf Q)
          (Eventually.of_forall fun x => mul_nonneg (weight_nonneg hW Q x) (norm_nonneg _))]
      simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using
        ENNReal.ofReal_le_ofReal (bad_integral_norm_le hW hc hf Q)
    _ = 2 * ∑' Q : W.cubes, ∫⁻ x, ENNReal.ofReal (weight W Q x * ‖f x‖) :=
      ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (weighted_norm_lintegral_sum_le hW hf) (by norm_num)

lemma bad_absolute_integral_sum_finite (hW : PartitionEstimates c C A M W) (hc : 0 < c)
    {f : Euclidean d → 𝕜} (hf : Integrable f) :
    (∑' Q : W.cubes, ∫⁻ x, ENNReal.ofReal ‖bad f W Q x‖) < ⊤ := by
  have hfin : (∫⁻ x, ENNReal.ofReal ‖f x‖) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => norm_nonneg _)).mp hf.norm.hasFiniteIntegral
  exact (bad_absolute_integral_sum_le hW hc hf).trans_lt (by finiteness)

lemma bad_norm_sum_integrable_unconditional (hW : PartitionEstimates c C A M W) (hc : 0 < c)
    {f : Euclidean d → 𝕜} (hf : Integrable f) :
    Integrable (fun x => ∑' Q : W.cubes, ‖bad f W Q x‖) := by
  refine ⟨AEStronglyMeasurable.tsum (fun Q => (bad_integrable hW hf Q).aestronglyMeasurable.norm), ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x =>
    tsum_nonneg (fun Q => norm_nonneg (bad f W Q x)))).mpr
  have hs (x : Euclidean d) : Summable (fun Q : W.cubes => ‖bad f W Q x‖) :=
    (summable_of_hasFiniteSupport (bad_finite_support hW f x) :
      Summable (fun Q : W.cubes => bad f W Q x)).norm
  simp_rw [ENNReal.ofReal_tsum_of_nonneg (fun Q => norm_nonneg (bad f W Q _)) (hs _)]
  rw [lintegral_tsum (f := fun (Q : W.cubes) x => ENNReal.ofReal ‖bad f W Q x‖)
    (fun Q => ENNReal.measurable_ofReal.comp_aemeasurable
    (bad_integrable hW hf Q).aestronglyMeasurable.norm.aemeasurable)]
  exact bad_absolute_integral_sum_finite hW hc hf

lemma bad_sum_integrable (hW : PartitionEstimates c C A M W) (hc : 0 < c)
    {f : Euclidean d → 𝕜} (hf : Integrable f) :
    Integrable (fun x => ∑' Q : W.cubes, bad f W Q x) := by
  apply (bad_norm_sum_integrable_unconditional hW hc hf).mono'
    (AEStronglyMeasurable.tsum (fun Q => (bad_integrable hW hf Q).aestronglyMeasurable))
  exact Eventually.of_forall fun x => norm_tsum_le_tsum_norm (by
    exact (summable_of_hasFiniteSupport (bad_finite_support hW f x) :
      Summable (fun Q : W.cubes => bad f W Q x)).norm)

lemma good_integrable (hW : PartitionEstimates c C A M W) (hc : 0 < c)
    {f : Euclidean d → 𝕜} (hf : Integrable f) : Integrable (good f W) :=
  hf.sub (bad_sum_integrable hW hc hf)

lemma good_integral_eq (hW : PartitionEstimates c C A M W) (hc : 0 < c)
    {f : Euclidean d → 𝕜} (hf : Integrable f) :
    (∫ x, good f W x) = ∫ x, f x := by
  have hsum : (∫ x, ∑' Q : W.cubes, bad f W Q x) = ∑' Q : W.cubes, ∫ x, bad f W Q x := by
    apply integral_tsum (fun Q => (bad_integrable hW hf Q).aestronglyMeasurable)
    simpa only [ofReal_norm] using (bad_absolute_integral_sum_finite hW hc hf).ne
  change (∫ x, f x - ∑' Q : W.cubes, bad f W Q x) = _
  rw [integral_sub hf (bad_sum_integrable hW hc hf), hsum]
  simp only [bad_integral_zero hW hc hf, tsum_zero, sub_zero]

end
end ExpandedFA.PartIV.HardyLevel


namespace ExpandedFA.PartIV.HardyLevel
open ExpandedFA.Fourier HardyMaximalSpec

lemma isTest_of_partial_bound {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    {u : Euclidean d → 𝕜} (hu : ContDiff ℝ ∞ u)
    (hs : tsupport u ⊆ Metric.ball 0 1) {B : ℝ} (hB : 0 < B)
    (hbound : ∀ k ≤ N, ∀ (a : Fin k → Fin d) x,
      ‖coordinatePartial a u x‖ ≤ B) :
    IsTest N (fun x => B⁻¹ • u x) := by
  refine ⟨hu.const_smul (B⁻¹), ?_, ?_⟩
  · exact (tsupport_smul_subset_right (fun _ => B⁻¹) u).trans hs
  · intro k hk a x
    dsimp [coordinatePartial]
    rw [iteratedFDeriv_const_smul_apply']
    · simp only [smul_apply, norm_smul,
        Real.norm_eq_abs, abs_inv, abs_of_pos hB]
      calc
        B⁻¹ * ‖iteratedFDeriv ℝ k u x (fun i => basisVector (a i))‖ ≤ B⁻¹ * B :=
          mul_le_mul_of_nonneg_left (hbound k hk a x) (inv_nonneg.mpr hB.le)
        _ = 1 := inv_mul_cancel₀ hB.ne'
    · exact hu.contDiffAt.of_le (mod_cast le_top)

lemma coordinatePartial_norm_le {𝕜 : Type} [RCLike 𝕜] {d k : ℕ}
    (a : Fin k → Fin d) (u : Euclidean d → 𝕜) (x : Euclidean d) :
    ‖coordinatePartial a u x‖ ≤ ‖iteratedFDeriv ℝ k u x‖ := by
  apply ContinuousMultilinearMap.unit_le_opNorm
  apply pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) |>.mpr
  intro i
  simp [basisVector, EuclideanSpace.single, PiLp.norm_single]

lemma exists_test_normalizer {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (N : ℕ) {u : Euclidean d → 𝕜} (hu : ContDiff ℝ ∞ u)
    (hs : tsupport u ⊆ Metric.ball 0 1) :
    ∃ B : ℝ, 0 < B ∧ IsTest N (fun x => B⁻¹ • u x) := by
  have hc : HasCompactSupport u :=
    (isCompact_closedBall (0 : Euclidean d) 1).of_isClosed_subset (isClosed_tsupport u)
      (hs.trans Metric.ball_subset_closedBall)
  have hb : ∀ k : ℕ, ∃ R : ℝ, ∀ x, ‖iteratedFDeriv ℝ k u x‖ ≤ R := by
    intro k
    have hbb : BddAbove (range fun x => ‖iteratedFDeriv ℝ k u x‖) := by
      apply (hu.continuous_iteratedFDeriv (mod_cast le_top)).norm.bddAbove_range_of_hasCompactSupport
      exact HasCompactSupport.comp_left (hc.iteratedFDeriv k) norm_zero
    obtain ⟨R, hR⟩ := hbb
    exact ⟨R, fun x => hR (mem_range_self x)⟩
  choose R hR using hb
  let B := 1 + ∑ k ∈ Finset.range (N + 1), max (R k) 0
  have hB : 0 < B := by
    dsimp [B]
    positivity
  refine ⟨B, hB, isTest_of_partial_bound hu hs hB ?_⟩
  intro k hk a x
  calc
    ‖coordinatePartial a u x‖ ≤ ‖iteratedFDeriv ℝ k u x‖ := coordinatePartial_norm_le a u x
    _ ≤ R k := hR k x
    _ ≤ max (R k) 0 := le_max_left _ _
    _ ≤ ∑ j ∈ Finset.range (N + 1), max (R j) 0 :=
      Finset.single_le_sum (fun i _ => le_max_right _ _) (by simp; omega)
    _ ≤ B := by dsimp [B]; linarith
end ExpandedFA.PartIV.HardyLevel

namespace ExpandedFA.PartIV.HardyLevel
open ExpandedFA.Fourier HardyMaximalSpec

def unitBump (d : ℕ) : ContDiffBump (0 : Euclidean d) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

def scaledBump {d : ℕ} (t : Scale) : ContDiffBump (0 : Euclidean d) :=
  ⟨t.val / 4, t.val / 2, div_pos t.property (by norm_num), by linarith [t.property]⟩

lemma scaledBump_apply {d : ℕ} (t : Scale) (x : Euclidean d) :
    scaledBump t x = unitBump d (t.val⁻¹ • x) := by
  simp only [ContDiffBump.apply, scaledBump, unitBump, sub_zero]
  congr 1
  · field_simp [t.property.ne']
  · rw [smul_smul]
    congr 1
    field_simp

lemma scaledBump_integral {d : ℕ} (t : Scale) :
    (∫ x, scaledBump (d := d) t x) = t.val ^ d * ∫ x, unitBump d x := by
  simp only [scaledBump_apply]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume _ t.property.le]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]

lemma scaledBump_normed {d : ℕ} (t : Scale) (x : Euclidean d) :
    (scaledBump t).normed volume x =
      (t.val ^ d)⁻¹ * (unitBump d).normed volume (t.val⁻¹ • x) := by
  rw [ContDiffBump.normed_def, scaledBump_integral, scaledBump_apply,
    ContDiffBump.normed_def]
  field_simp

lemma unitBump_normed_support {d : ℕ} :
    tsupport ((unitBump d).normed volume) ⊆ Metric.ball 0 1 := by
  rw [ContDiffBump.tsupport_normed_eq]
  exact Metric.closedBall_subset_ball (by norm_num [unitBump])

lemma unitBump_normed_coe_smooth {𝕜 : Type} [RCLike 𝕜] {d : ℕ} :
    ContDiff ℝ ∞ (fun x => ((unitBump d).normed volume x : 𝕜)) :=
  (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp (unitBump d).contDiff_normed

lemma unitBump_normed_coe_support {𝕜 : Type} [RCLike 𝕜] {d : ℕ} :
    tsupport (fun x => ((unitBump d).normed volume x : 𝕜)) ⊆ Metric.ball 0 1 := by
  exact (tsupport_comp_subset (g := RCLike.ofReal) RCLike.ofReal_zero _).trans
    unitBump_normed_support
end ExpandedFA.PartIV.HardyLevel
namespace ExpandedFA.PartIV.HardyLevel
open ExpandedFA.Fourier HardyMaximalSpec
open scoped Convolution

lemma convolve_normalized_unitBump {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (B : ℝ) (t : Scale) (f : Euclidean d → 𝕜) (x : Euclidean d) :
    convolve (dilate t.val (fun y => B⁻¹ • ((unitBump d).normed volume y : 𝕜))) f x =
      B⁻¹ • (((scaledBump t).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x := by
  simp only [convolve, dilate, convolution_def, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.lsmul_apply, ← integral_smul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  rw [scaledBump_normed]
  simp only [RCLike.real_smul_eq_coe_mul, RCLike.ofReal_mul, RCLike.ofReal_inv]
  ring

lemma normed_bump_convolution_le_grand {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    {B : ℝ} (hB : 0 < B)
    (hψ : IsTest N (fun x => B⁻¹ • ((unitBump d).normed volume x : 𝕜)))
    (t : Scale) (f : Euclidean d → 𝕜) (x : Euclidean d) :
    ENNReal.ofReal ‖(((scaledBump t).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x‖ ≤
      ENNReal.ofReal B * grand N f x := by
  let ψ : Tests 𝕜 d N := ⟨_, hψ⟩
  have ht : ENNReal.ofReal ‖convolve (dilate t.val ψ.val) f x‖ ≤ grand N f x :=
    (le_iSup_of_le t (le_iSup_of_le ψ le_rfl))
  have heq := convolve_normalized_unitBump B t f x
  change convolve (dilate t.val ψ.val) f x = _ at heq
  rw [heq, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hB.le), ENNReal.ofReal_mul
    (inv_nonneg.mpr hB.le)] at ht
  calc
    _ = ENNReal.ofReal B * (ENNReal.ofReal B⁻¹ *
        ENNReal.ofReal ‖(((scaledBump t).normed volume) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) x‖) := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hB.le, mul_inv_cancel₀ hB.ne']
      simp
    _ ≤ ENNReal.ofReal B * grand N f x := by gcongr

/-- A fixed normalized bump is among the grand tests up to a constant.
The approximate identity theorem then gives almost everywhere domination. -/
lemma exists_ae_norm_le_grand {𝕜 : Type} [RCLike 𝕜] (d N : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ f : Euclidean d → 𝕜, Integrable f →
      ∀ᵐ x, ENNReal.ofReal ‖f x‖ ≤ ENNReal.ofReal B * grand N f x := by
  obtain ⟨B, hB, hψ⟩ := exists_test_normalizer N
    (unitBump_normed_coe_smooth (𝕜 := 𝕜) (d := d)) unitBump_normed_coe_support
  refine ⟨B, hB, ?_⟩
  intro f hf
  let t : ℕ → Scale := fun n => ⟨1 / ((n : ℝ) + 1), by positivity⟩
  have hlim : Tendsto (fun n => (scaledBump (d := d) (t n)).rOut) atTop (𝓝 0) := by
    simpa [scaledBump, t] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
  have hratio : ∀ᶠ n in atTop, (scaledBump (d := d) (t n)).rOut ≤ 2 * (scaledBump (d := d) (t n)).rIn := by
    apply Eventually.of_forall
    intro n
    dsimp [scaledBump]
    linarith
  filter_upwards [ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    hlim hratio hf.locallyIntegrable] with x hx
  apply le_of_tendsto' (ENNReal.continuous_ofReal.tendsto _ |>.comp hx.norm)
  intro n
  exact normed_bump_convolution_le_grand hB hψ (t n) f x
end ExpandedFA.PartIV.HardyLevel
namespace ExpandedFA.PartIV.HardyLevel
open ExpandedFA.Fourier HardyMaximalSpec

lemma norm_le_of_grand_le {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    {f : Euclidean d → 𝕜} {B T : ℝ} (hB : 0 ≤ B) (hT : 0 ≤ T)
    {x : Euclidean d}
    (hf : ENNReal.ofReal ‖f x‖ ≤ ENNReal.ofReal B * grand N f x)
    (hG : grand N f x ≤ ENNReal.ofReal T) : ‖f x‖ ≤ B * T := by
  have h : ENNReal.ofReal ‖f x‖ ≤ ENNReal.ofReal (B * T) := by
    rw [ENNReal.ofReal_mul hB]
    exact hf.trans (by gcongr)
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB hT)).mp h

lemma grand_nonlevel_bound {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    {f : Euclidean d → 𝕜} {B : ℝ} (hB : 0 ≤ B)
    (hdom : ∀ᵐ x, ENNReal.ofReal ‖f x‖ ≤ ENNReal.ofReal B * grand N f x)
    (k : ℤ) :
    ∀ᵐ x, coordinates x ∉ coordinateLevel N f k → ‖f x‖ ≤ B * threshold k := by
  filter_upwards [hdom] with x hx hout
  have hG : grand N f x ≤ ENNReal.ofReal (threshold k) := by
    simpa only [coordinateLevel, mem_preimage, coordinates, WithLp.toLp_ofLp,
      level, mem_ofPred_eq, not_lt] using hout
  exact norm_le_of_grand_le hB (zpow_nonneg (by norm_num) _) hx hG

lemma exists_grand_nonlevel_bound {𝕜 : Type} [RCLike 𝕜] (d N : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ f : Euclidean d → 𝕜, Integrable f → ∀ k : ℤ,
      ∀ᵐ x, coordinates x ∉ coordinateLevel N f k → ‖f x‖ ≤ B * threshold k := by
  obtain ⟨B, hB, hdom⟩ := exists_ae_norm_le_grand (𝕜 := 𝕜) d N
  exact ⟨B, hB, fun f hf k => grand_nonlevel_bound hB.le (hdom f hf) k⟩
end ExpandedFA.PartIV.HardyLevel


namespace ExpandedFA.PartIV.HardyLevel
open ExpandedFA.Fourier ExpandedFA.Distributions HardyMaximalSpec HardyWhitney

/-- Combining grand domination outside the level and bounded averages inside
it gives the actual good-function bound. -/
lemma good_bound_of_grand_and_average_bound
    {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    {Ω : TopologicalSpace.Opens (Domain d)}
    {c Cg : ℝ} {A : ℕ → ℝ} {M : ℕ} {W : Partition Ω}
    (hW : PartitionEstimates c Cg A M W)
    {f : Euclidean d → 𝕜} {B C : ℝ} (hB : 0 ≤ B) (hBC : B ≤ C)
    (hdom : ∀ᵐ x, ENNReal.ofReal ‖f x‖ ≤ ENNReal.ofReal B * grand N f x)
    (k : ℤ) (hΩ : (Ω : Set (Domain d)) = coordinateLevel N f k)
    (havg : ∀ Q : W.cubes, ‖average f W Q‖ ≤ C * threshold k) :
    ∀ᵐ x, ‖good f W x‖ ≤ C * threshold k := by
  apply good_bound_of_average_bound hW f havg
  filter_upwards [grand_nonlevel_bound hB hdom k] with x hx hout
  have hm : coordinates x ∉ coordinateLevel N f k := by simpa only [hΩ] using hout
  exact (hx hm).trans
    (mul_le_mul_of_nonneg_right hBC (zpow_nonneg (by norm_num) _))
end ExpandedFA.PartIV.HardyLevel


namespace ExpandedFA.PartIV.HardyLevel
open ExpandedFA.Distributions ExpandedFA.Fourier HardyWhitney HardyMaximalSpec
lemma bad_summable_integral_norm {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : TopologicalSpace.Opens (Domain d)} {c C : ℝ} {A : ℕ → ℝ} {M : ℕ} {W : Partition Ω}
    (hW : PartitionEstimates c C A M W) (hc : 0 < c)
    {f : Euclidean d → 𝕜} (hf : Integrable f) :
    Summable (fun Q : W.cubes => ∫ x, ‖bad f W Q x‖) := by
  have hsum := ENNReal.summable_toReal (bad_absolute_integral_sum_finite hW hc hf).ne
  have heq (Q : W.cubes) : (∫⁻ x, ENNReal.ofReal ‖bad f W Q x‖).toReal =
      ∫ x, ‖bad f W Q x‖ := by
    simpa only [ofReal_norm] using
      (integral_norm_eq_lintegral_enorm (bad_integrable hW hf Q).aestronglyMeasurable).symm
  simpa only [heq] using hsum
end ExpandedFA.PartIV.HardyLevel


namespace ExpandedFA.PartIV.HardyLevel.TestEstimates
open ExpandedFA.Fourier ExpandedFA.PartIV.HardyMaximalSpec
open ExpandedFA.Distributions ExpandedFA.PartIV.HardyWhitney

def recenter {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Euclidean d → 𝕜) (z : Euclidean d) (t a : ℝ) (x : Euclidean d) : 𝕜 :=
  a⁻¹ • η (z + (-t) • x)

lemma iteratedFDeriv_recenter {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η : Euclidean d → 𝕜) (hη : ContDiff ℝ ∞ η)
    (z x : Euclidean d) (t a : ℝ) (j : ℕ) :
    iteratedFDeriv ℝ j (recenter η z t a) x =
      a⁻¹ • ((-t)^j • iteratedFDeriv ℝ j η (z + (-t) • x)) := by
  have hg : ContDiff ℝ j (fun y => η (z + y)) :=
    hη.of_le (by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top)) |>.comp (by fun_prop)
  have hgs : ContDiff ℝ j (fun y => η (z + (-t) • y)) := hg.comp (by fun_prop)
  unfold recenter
  rw [iteratedFDeriv_const_smul_apply' hgs.contDiffAt]
  have hs := congrFun (iteratedFDeriv_comp_const_smul (-t) hg) x
  rw [hs, iteratedFDeriv_comp_add_left]

lemma convolution_recenter {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (η f : Euclidean d → 𝕜) (z : Euclidean d) {t : ℝ} (ht : 0 < t) (a : ℝ) :
    convolve (dilate t (recenter η z t a)) f z =
      ((t ^ d)⁻¹ * a⁻¹) • ∫ y, η y * f y := by
  unfold convolve
  rw [convolution_mul_swap]
  have hi : (fun y => dilate t (recenter η z t a) (z-y) * f y) =
      fun y => ((t ^ d)⁻¹ * a⁻¹) • (η y * f y) := by
    funext y
    have he : z + (-t) • (t⁻¹ • (z-y)) = y := by
      rw [smul_smul]
      have hcoef : -t * t⁻¹ = -(1 : ℝ) := by field_simp
      rw [hcoef, neg_one_smul]
      abel
    simp only [dilate, recenter, smul_mul_assoc]
    rw [he, smul_smul]
  rw [hi, integral_smul]

lemma pairing_le_of_recenter_test {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    (η f : Euclidean d → 𝕜) (z : Euclidean d) {t a B : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hB : 0 ≤ B)
    (hψ : IsTest N (recenter η z t a))
    (hz : grand N f z ≤ ENNReal.ofReal B) :
    ‖∫ y, η y * f y‖ ≤ a * t ^ d * B := by
  let ψ : Tests 𝕜 d N := ⟨recenter η z t a, hψ⟩
  have hg0 : ENNReal.ofReal ‖convolve (dilate t ψ.val) f z‖ ≤ grand N f z := by
    unfold grand
    exact le_iSup_of_le (⟨t, ht⟩ : Scale) (le_iSup_of_le ψ le_rfl)
  have hg := hg0.trans hz
  have hreal : ‖convolve (dilate t ψ.val) f z‖ ≤ B :=
    (ENNReal.ofReal_le_ofReal_iff hB).mp hg
  change ‖convolve (dilate t (recenter η z t a)) f z‖ ≤ B at hreal
  rw [convolution_recenter η f z ht a, norm_smul,
    Real.norm_eq_abs, abs_of_pos (mul_pos (inv_pos.mpr (pow_pos ht _)) (inv_pos.mpr ha))] at hreal
  have ht0 : t^d ≠ 0 := ne_of_gt (pow_pos ht _)
  have ha0 : a ≠ 0 := ne_of_gt ha
  calc
    ‖∫ y, η y * f y‖ = (a * t^d) * (((t^d)⁻¹ * a⁻¹) * ‖∫ y, η y * f y‖) := by field_simp
    _ ≤ (a * t^d) * B := mul_le_mul_of_nonneg_left hreal (by positivity)

lemma maximal_cube_outside_point {d : ℕ} {Ω : TopologicalSpace.Opens (Domain d)}
    (hne : (Ω : Set (Domain d))ᶜ.Nonempty)
    (Q : maximalCubes (Ω : Set (Domain d))) :
    ∃ z ∉ (Ω : Set (Domain d)), dist Q.val.center z ≤ 22 * Q.val.side := by
  obtain ⟨z, hz, heq⟩ := Ω.isOpen.isClosed_compl.exists_infDist_eq_dist hne Q.val.center
  refine ⟨z, hz, ?_⟩
  rw [← heq]
  exact (maximalCubes_distance _ Q.val Q.property Q.val.center Q.val.center_mem_star).2

lemma recenter_isTest_of_bound {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    (η : Euclidean d → 𝕜) (hη : ContDiff ℝ ∞ η)
    (z : Euclidean d) {t a : ℝ} (ht : 0 < t) (ha : 0 < a)
    (hs : tsupport η ⊆ Metric.ball z t)
    (hb : ∀ j ≤ N, ∀ y, ‖iteratedFDeriv ℝ j η y‖ ≤ a / t^j) :
    IsTest N (recenter η z t a) := by
  have hsm : ContDiff ℝ ∞ (recenter η z t a) := by
    unfold recenter
    exact (hη.comp (by fun_prop)).const_smul _
  refine ⟨hsm, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ tsupport (fun y => η (z + (-t) • y)) :=
      tsupport_smul_subset_right (fun _ => a⁻¹) (fun y => η (z + (-t) • y)) hx
    have hy : z + (-t) • x ∈ tsupport η :=
      tsupport_comp_subset_preimage (f := fun y => z + (-t) • y) η (by fun_prop) hx'
    have htiny := hs hy
    simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos ht] at htiny
    simp only [Metric.mem_ball, dist_zero_right]
    exact (mul_lt_mul_iff_right₀ ht).mp (by simpa only [mul_comm, mul_one] using htiny)
  · intro j hj b x
    unfold coordinatePartial
    have hunit : ‖fun i => basisVector (b i)‖ ≤ (1 : ℝ) := by
      rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
      intro i
      simp [basisVector, PiLp.norm_single]
    have hopp := (iteratedFDeriv ℝ j (recenter η z t a) x).unit_le_opNorm hunit
    apply hopp.trans
    rw [iteratedFDeriv_recenter η hη z x t a j, norm_smul, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha), Real.norm_eq_abs,
      abs_pow, abs_neg, abs_of_pos ht]
    have hraw := mul_le_mul_of_nonneg_left (hb j hj (z + (-t) • x))
      (show 0 ≤ a⁻¹ * t^j by positivity)
    calc
      a⁻¹ * (t^j * ‖iteratedFDeriv ℝ j η (z + (-t) • x)‖) =
          (a⁻¹ * t^j) * ‖iteratedFDeriv ℝ j η (z + (-t) • x)‖ := by ring
      _ ≤ (a⁻¹ * t^j) * (a / t^j) := hraw
      _ = 1 := by field_simp

abbrev coordinateEquiv (d : ℕ) : Euclidean d ≃L[ℝ] Domain d :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)

def transportWeight (𝕜 : Type) [RCLike 𝕜] {d : ℕ}
    (w : Domain d → ℝ) (x : Euclidean d) : 𝕜 := (w (coordinateEquiv d x) : 𝕜)

lemma norm_iteratedFDeriv_transportWeight {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (w : Domain d → ℝ) (hw : ContDiff ℝ ∞ w) (j : ℕ) (x : Euclidean d) :
    ‖iteratedFDeriv ℝ j (transportWeight 𝕜 w) x‖ ≤
      ‖iteratedFDeriv ℝ j w (coordinateEquiv d x)‖ * ‖(coordinateEquiv d).toContinuousLinearMap‖^j := by
  have hwj : ContDiff ℝ j w := hw.of_le (by exact_mod_cast (show (j : ℕ∞) ≤ ⊤ from le_top))
  have hc : ContDiff ℝ j (w ∘ coordinateEquiv d) := hwj.comp (coordinateEquiv d).contDiff
  change ‖iteratedFDeriv ℝ j ((RCLike.ofRealLI : ℝ →ₗᵢ[ℝ] 𝕜) ∘ (w ∘ coordinateEquiv d)) x‖ ≤ _
  rw [LinearIsometry.norm_iteratedFDeriv_comp_left _ hc.contDiffAt le_rfl]
  change ‖iteratedFDeriv ℝ j (w ∘ (coordinateEquiv d).toContinuousLinearMap) x‖ ≤ _
  rw [(coordinateEquiv d).toContinuousLinearMap.iteratedFDeriv_comp_right hwj x le_rfl]
  simpa using (iteratedFDeriv ℝ j w (coordinateEquiv d x)).norm_compContinuousLinearMap_le
    (fun _ : Fin j => (coordinateEquiv d).toContinuousLinearMap)

lemma transportWeight_contDiff {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (w : Domain d → ℝ) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (transportWeight 𝕜 w) := by
  change ContDiff ℝ ∞ ((RCLike.ofRealCLM (K := 𝕜)) ∘ (w ∘ coordinateEquiv d))
  exact (RCLike.ofRealCLM (K := 𝕜)).contDiff.comp (hw.comp (coordinateEquiv d).contDiff)

lemma transportWeight_support_ball {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Q : DyadicCube d) (w : Domain d → ℝ) (hs : tsupport w ⊆ Q.star)
    (z : Domain d) (hz : dist Q.center z ≤ 22 * Q.side) :
    tsupport (transportWeight 𝕜 w) ⊆
      Metric.ball ((coordinateEquiv d).symm z)
        ((24 * (‖(coordinateEquiv d).symm.toContinuousLinearMap‖ + 1)) * Q.side) := by
  intro x hx
  have hx' : x ∈ tsupport (w ∘ coordinateEquiv d) :=
    tsupport_comp_subset (g := fun r : ℝ => (r : 𝕜)) (by simp) _ hx
  have hy : coordinateEquiv d x ∈ tsupport w :=
    tsupport_comp_subset_preimage (f := coordinateEquiv d) w (coordinateEquiv d).continuous hx'
  have hsx : dist (coordinateEquiv d x) Q.center ≤ (9/8) * Q.side / 2 := hs hy
  have hdist : dist (coordinateEquiv d x) z ≤ 23 * Q.side := by
    have htri := dist_triangle (coordinateEquiv d x) Q.center z
    have hside := Q.side_pos
    linarith
  have heq : x - (coordinateEquiv d).symm z =
      (coordinateEquiv d).symm (coordinateEquiv d x-z) := by
    rw [map_sub, ContinuousLinearEquiv.symm_apply_apply]
  rw [Metric.mem_ball, dist_eq_norm, heq]
  calc
    ‖(coordinateEquiv d).symm (coordinateEquiv d x-z)‖ ≤
        ‖(coordinateEquiv d).symm.toContinuousLinearMap‖ * ‖coordinateEquiv d x-z‖ :=
      (coordinateEquiv d).symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖(coordinateEquiv d).symm.toContinuousLinearMap‖ * (23 * Q.side) :=
      mul_le_mul_of_nonneg_left hdist (norm_nonneg _)
    _ < (24 * (‖(coordinateEquiv d).symm.toContinuousLinearMap‖ + 1)) * Q.side := by
      have hside := Q.side_pos
      have hnorm := norm_nonneg (coordinateEquiv d).symm.toContinuousLinearMap
      nlinarith

def transportScale (d : ℕ) : ℝ :=
  24 * (‖(coordinateEquiv d).symm.toContinuousLinearMap‖ + 1)

def normalizer (d N : ℕ) (A : ℕ → ℝ) : ℝ :=
  1 + ∑ j ∈ Finset.range (N+1), A j *
    (transportScale d * ‖(coordinateEquiv d).toContinuousLinearMap‖)^j

lemma transportScale_pos (d : ℕ) : 0 < transportScale d := by
  unfold transportScale
  positivity

lemma normalizer_pos (d N : ℕ) (A : ℕ → ℝ) (hA : ∀ j, 0 < A j) :
    0 < normalizer d N A := by
  have hT := transportScale_pos d
  unfold normalizer
  have hs : 0 ≤ ∑ j ∈ Finset.range (N+1), A j *
      (transportScale d * ‖(coordinateEquiv d).toContinuousLinearMap‖)^j :=
    Finset.sum_nonneg fun j hj => mul_nonneg (hA j).le (by positivity)
  linarith

lemma normalizer_bound (d N : ℕ) (A : ℕ → ℝ) (hA : ∀ j, 0 < A j)
    (j : ℕ) (hj : j ≤ N) :
    A j * (transportScale d * ‖(coordinateEquiv d).toContinuousLinearMap‖)^j ≤ normalizer d N A := by
  have hT := transportScale_pos d
  have hh := Finset.single_le_sum
    (f := fun j => A j * (transportScale d * ‖(coordinateEquiv d).toContinuousLinearMap‖)^j)
    (fun j (_ : j ∈ Finset.range (N+1)) => mul_nonneg (hA j).le (by positivity))
    (show j ∈ Finset.range (N+1) by simp only [Finset.mem_range]; omega)
  unfold normalizer
  linarith

lemma scaled_derivative_transport_bound {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    (A : ℕ → ℝ) (hA : ∀ j, 0 < A j) (Q : DyadicCube d)
    (w : Domain d → ℝ) (hw : ContDiff ℝ ∞ w)
    (hb : ∀ j ≤ N, ∀ y, ‖iteratedFDeriv ℝ j w y‖ ≤ A j * Q.side ^ (-(j : ℤ))) :
    ∀ j ≤ N, ∀ x,
      ‖iteratedFDeriv ℝ j (transportWeight 𝕜 w) x‖ ≤
        normalizer d N A / (transportScale d * Q.side)^j := by
  intro j hj x
  have hT := transportScale_pos d
  have hl := Q.side_pos
  have hmax := normalizer_bound d N A hA j hj
  calc
    ‖iteratedFDeriv ℝ j (transportWeight 𝕜 w) x‖ ≤
      ‖iteratedFDeriv ℝ j w (coordinateEquiv d x)‖ * ‖(coordinateEquiv d).toContinuousLinearMap‖^j :=
      norm_iteratedFDeriv_transportWeight w hw j x
    _ ≤ (A j * Q.side ^ (-(j : ℤ))) * ‖(coordinateEquiv d).toContinuousLinearMap‖^j :=
      mul_le_mul_of_nonneg_right (hb j hj _) (by positivity)
    _ = (A j * (transportScale d * ‖(coordinateEquiv d).toContinuousLinearMap‖)^j) /
          (transportScale d * Q.side)^j := by
      rw [zpow_neg, zpow_natCast]
      field_simp
      ring
    _ ≤ normalizer d N A / (transportScale d * Q.side)^j :=
      div_le_div_of_nonneg_right hmax (by positivity)

def pairingConstant (d N : ℕ) (A : ℕ → ℝ) : ℝ :=
  normalizer d N A * (transportScale d)^d

lemma pairingConstant_pos (d N : ℕ) (A : ℕ → ℝ) (hA : ∀ j, 0 < A j) :
    0 < pairingConstant d N A := by
  exact mul_pos (normalizer_pos d N A hA) (pow_pos (transportScale_pos d) _)

lemma whitney_weight_pairing {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    (A : ℕ → ℝ) (hA : ∀ j, 0 < A j) (Q : DyadicCube d)
    (w : Domain d → ℝ) (hw : ContDiff ℝ ∞ w) (hs : tsupport w ⊆ Q.star)
    (hb : ∀ j ≤ N, ∀ y, ‖iteratedFDeriv ℝ j w y‖ ≤ A j * Q.side ^ (-(j : ℤ)))
    (f : Euclidean d → 𝕜) (z : Domain d)
    (hdist : dist Q.center z ≤ 22 * Q.side) {B : ℝ} (hB : 0 ≤ B)
    (hz : grand N f ((coordinateEquiv d).symm z) ≤ ENNReal.ofReal B) :
    ‖∫ y, transportWeight 𝕜 w y * f y‖ ≤ pairingConstant d N A * Q.side^d * B := by
  have ht : 0 < transportScale d * Q.side := mul_pos (transportScale_pos d) Q.side_pos
  have hψ := recenter_isTest_of_bound (transportWeight 𝕜 w)
    (transportWeight_contDiff w hw) ((coordinateEquiv d).symm z) ht
    (normalizer_pos d N A hA) (transportWeight_support_ball Q w hs z hdist)
    (scaled_derivative_transport_bound A hA Q w hw hb)
  have hp := pairing_le_of_recenter_test (transportWeight 𝕜 w) f
    ((coordinateEquiv d).symm z) ht (normalizer_pos d N A hA) hB hψ hz
  calc
    ‖∫ y, transportWeight 𝕜 w y * f y‖ ≤
        normalizer d N A * (transportScale d * Q.side)^d * B := hp
    _ = pairingConstant d N A * Q.side^d * B := by unfold pairingConstant; rw [mul_pow]; ring

lemma average_ratio_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Q : DyadicCube d) {c D B den : ℝ} (hc : 0 < c) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hden : c * Q.side^d ≤ den) (num : 𝕜) (hnum : ‖num‖ ≤ D * Q.side^d * B) :
    ‖den⁻¹ • num‖ ≤ (D/c) * B := by
  have hl : 0 < Q.side^d := pow_pos Q.side_pos _
  have hdp : 0 < den := (mul_pos hc hl).trans_le hden
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdp)]
  calc
    den⁻¹ * ‖num‖ ≤ den⁻¹ * (D * Q.side^d * B) :=
      mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr hdp.le)
    _ ≤ (c * Q.side^d)⁻¹ * (D * Q.side^d * B) :=
      mul_le_mul_of_nonneg_right (inv_anti₀ (mul_pos hc hl) hden) (by positivity)
    _ = (D/c) * B := by field_simp

def canonicalPartition {d : ℕ} (hd : 0 < d) (Ω : EligibleOpen d) : Partition Ω.val :=
  ⟨maximalCubes (Ω.val : Set (Domain d)), whitneyWeight hd Ω⟩

lemma canonical_partition_estimates (d : ℕ) (hd : 0 < d) :
    ∃ A : ℕ → ℝ, (∀ j, 0 < A j) ∧
      (∀ Ω : EligibleOpen d, PartitionEstimates (1 / ((30^d : ℕ) : ℝ)) 8 A (30^d)
        (canonicalPartition hd Ω)) ∧
      (∀ (Ω : EligibleOpen d) (Q : (canonicalPartition hd Ω).cubes) j x,
        ‖iteratedFDeriv ℝ j ((canonicalPartition hd Ω).weight Q) x‖ ≤
          A j * Q.val.side ^ (-(j : ℤ))) := by
  obtain ⟨A, hA, hbound⟩ := normalizedCutoff_derivative_bounds d
  refine ⟨A, hA, ?_, ?_⟩
  · intro Ω
    obtain ⟨hcover, hdisj, hinside, hlocal, hoverlap, hneighbor, _⟩ := maximalCubes_geometry hd Ω
    refine ⟨hcover, hdisj, hinside, hlocal, hoverlap, whitneyWeight_nonneg hd Ω,
      whitneyWeight_tsupport hd Ω, whitneyWeight_sum hd Ω, ?_, ?_, ?_⟩
    · intro Q
      exact test_integral_lower_bound_inv (whitneyWeight hd Ω Q) Q.val (30^d)
        (whitneyWeight_nonneg hd Ω Q) (whitneyWeight_lower hd Ω Q)
    · intro Q j a x
      exact (coordinate_derivative_le_operator _ a x).trans
        (hbound Ω.val _ (maximalCubes_geometry hd Ω) Q j x)
    · intro Q R h
      obtain ⟨hQR, hRQ⟩ := hneighbor Q R h
      constructor <;> nlinarith [Q.val.side_pos, R.val.side_pos]
  · intro Ω Q j x
    exact hbound Ω.val _ (maximalCubes_geometry hd Ω) Q j x

lemma canonical_nested {d : ℕ} (hd : 0 < d) (Ω Ω' : EligibleOpen d)
    (hΩ : (Ω'.val : Set (Domain d)) ⊆ Ω.val) :
    NestedEstimates 8 (30^d) (canonicalPartition hd Ω) (canonicalPartition hd Ω') :=
  maximalCubes_nested hd Ω Ω' hΩ

lemma average_le_of_operator_bounds {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    {Ω : TopologicalSpace.Opens (Domain d)} (W : Partition Ω)
    {c C : ℝ} {A : ℕ → ℝ} {M : ℕ} (hc : 0 < c) (hA : ∀ j, 0 < A j)
    (hW : PartitionEstimates c C A M W)
    (hcan : W.cubes ⊆ maximalCubes (Ω : Set (Domain d)))
    (hop : ∀ (Q : W.cubes) j x,
      ‖iteratedFDeriv ℝ j (W.weight Q) x‖ ≤ A j * Q.val.side ^ (-(j : ℤ)))
    (hne : (Ω : Set (Domain d))ᶜ.Nonempty)
    (f : Euclidean d → 𝕜) (k : ℤ)
    (hΩ : (Ω : Set (Domain d)) = coordinateLevel N f k) (Q : W.cubes) :
    ‖average f W Q‖ ≤ (pairingConstant d N A / c) * threshold k := by
  obtain ⟨z, hz, hdist⟩ := maximal_cube_outside_point hne ⟨Q.val, hcan Q.property⟩
  have hgz : grand N f ((coordinateEquiv d).symm z) ≤ ENNReal.ofReal (threshold k) := by
    have hn : ¬ ENNReal.ofReal (threshold k) < grand N f ((coordinateEquiv d).symm z) := by
      change ¬ ENNReal.ofReal (threshold k) < grand N f (WithLp.toLp 2 z)
      simpa only [hΩ, coordinateLevel, level, Set.mem_preimage, Set.mem_ofPred_eq] using hz
    exact le_of_not_gt hn
  have hθ : 0 < threshold k := zpow_pos (by norm_num) _
  have hsup := hW.2.2.2.2.2.2.1 Q
  have hp := whitney_weight_pairing A hA Q.val (W.weight Q) (W.weight Q).contDiff hsup
    (fun j _ x => hop Q j x) f z hdist hθ.le hgz
  have hden : c * Q.val.side^d ≤ ∫ x, weight W Q x := by
    have heq : (∫ x, weight W Q x) = ∫ y, W.weight Q y :=
      (PiLp.volume_preserving_ofLp (Fin d)).integral_comp
        (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).measurableEmbedding _
    rw [heq]
    simpa only [DyadicCube.volume_carrier_toReal] using (hW.2.2.2.2.2.2.2.2.1 Q).2
  have hp' : ‖∫ x, weight W Q x • f x‖ ≤ pairingConstant d N A * Q.val.side^d * threshold k := by
    change ‖∫ x, (weight W Q x : 𝕜) * f x‖ ≤ _ at hp
    simpa only [RCLike.real_smul_eq_coe_mul] using hp
  exact average_ratio_bound Q.val hc (pairingConstant_pos d N A hA).le hθ.le hden _ hp'

end ExpandedFA.PartIV.HardyLevel.TestEstimates


namespace ExpandedFA.PartIV.HardyLevel
open ExpandedFA.Distributions ExpandedFA.Fourier HardyWhitney HardyMaximalSpec
section MoreTwoLevels
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
  {Ω Ω' : TopologicalSpace.Opens (Domain d)}
  {c C c' C' : ℝ} {A A' : ℕ → ℝ} {M M' : ℕ}
  {W : Partition Ω} {W' : Partition Ω'}
lemma weighted_bad_coarse_finite_support
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c' C' A' M' W')
    {D : ℝ} {L : ℕ} (hN : NestedEstimates D L W W')
    (f : Euclidean d → 𝕜) (R : W'.cubes) :
    Function.HasFiniteSupport (fun Q : W.cubes =>
      (fun x => weight W Q x • bad f W' R x)) := by
  apply (hN.2 R).1.subset
  intro Q hQ
  by_contra hn
  apply hQ
  funext x
  by_cases hx : coordinates x ∈ Q.val.star
  · have hr : coordinates x ∉ R.val.star := fun hy => hn ⟨coordinates x, hy, hx⟩
    simp [bad, weight_zero_off_star hW' R hr]
  · simp [weight_zero_off_star hW Q hx]
lemma correction_coarse_finite_support
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c' C' A' M' W')
    {D : ℝ} {L : ℕ} (hN : NestedEstimates D L W W')
    (f : Euclidean d → 𝕜) (R : W'.cubes) :
    Function.HasFiniteSupport (fun Q : W.cubes => correction f W W' Q R) := by
  apply (hN.2 R).1.subset
  intro Q hQ
  by_contra hn
  exact hQ (correction_zero_of_no_inter hW hW' f Q R hn)
lemma weighted_bad_coarse_sum
    (hW : PartitionEstimates c C A M W)
    (hsub : (Ω' : Set (Domain d)) ⊆ Ω)
    (f : Euclidean d → 𝕜) (R : W'.cubes) (x : Euclidean d) :
    (∑' Q : W.cubes, weight W Q x • bad f W' R x) = bad f W' R x := by
  by_cases hx : coordinates x ∈ (Ω' : Set (Domain d))
  · rw [(summable_of_hasFiniteSupport (weight_finite_support hW x)).tsum_smul_const,
      weight_sum hW (hsub hx), one_smul]
  · have hz : bad f W' R x = 0 := by simp [bad, weight_zero_off R hx]
    simp [hz]
lemma correction_coarse_sum_zero
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c' C' A' M' W')
    (hc' : 0 < c') {D : ℝ} {L : ℕ} (hN : NestedEstimates D L W W')
    (hsub : (Ω' : Set (Domain d)) ⊆ Ω)
    {f : Euclidean d → 𝕜} (hf : Integrable f) (R : W'.cubes) :
    (∑' Q : W.cubes, correction f W W' Q R) = 0 := by
  have hfin := weighted_bad_coarse_finite_support hW hW' hN f R
  have hsum : Summable (fun Q : W.cubes => ∫ x, ‖weight W Q x • bad f W' R x‖) := by
    apply summable_of_hasFiniteSupport
    apply hfin.subset
    intro Q hQ hz
    apply hQ
    have hz' (x : Euclidean d) : weight W Q x • bad f W' R x = 0 := congrFun hz x
    simp only [hz', norm_zero, integral_zero]
  have hswap := integral_tsum_of_summable_integral_norm
    (fun Q => weighted_integrable hW (bad_integrable hW' hf R) Q) hsum
  simp only [correction, tsum_const_smul'']
  rw [hswap]
  simp_rw [weighted_bad_coarse_sum hW hsub f R]
  rw [bad_integral_zero hW' hc' hf R, smul_zero]
lemma correction_bracket_finite_support
    (hW' : PartitionEstimates c' C' A' M' W')
    (f : Euclidean d → 𝕜) (Q : W.cubes) (x : Euclidean d) :
    Function.HasFiniteSupport (fun R : W'.cubes =>
      weight W Q x • bad f W' R x - weight W' R x • correction f W W' Q R) := by
  apply (weight_finite_support hW' x).subset
  intro R hR hz
  exact hR (by simp [bad, hz])

lemma piece_eq_weighted_good_add_correction
    (hW' : PartitionEstimates c' C' A' M' W')
    (f : Euclidean d → 𝕜) (Q : W.cubes) (x : Euclidean d) :
    piece f W W' Q x = weight W Q x • (good f W' x - average f W Q) +
      ∑' R : W'.cubes, weight W' R x • correction f W W' Q R := by
  have hb : Summable (fun R : W'.cubes => weight W Q x • bad f W' R x) :=
    (summable_of_hasFiniteSupport (bad_finite_support hW' f x)).const_smul _
  have hc : Summable (fun R : W'.cubes => weight W' R x • correction f W W' Q R) := by
    apply summable_of_hasFiniteSupport
    apply (weight_finite_support hW' x).subset
    intro R hR hz
    exact hR (by simp [hz])
  rw [piece, hb.tsum_sub hc, tsum_const_smul'']
  simp only [bad, good, smul_sub]
  abel

lemma weighted_correction_sum_bound
    (hW' : PartitionEstimates c' C' A' M' W')
    (f : Euclidean d → 𝕜) {Bcorr : ℝ} (hBcorr : 0 ≤ Bcorr)
    (hcorr : ∀ (Q : W.cubes) (R : W'.cubes), ‖correction f W W' Q R‖ ≤ Bcorr)
    (Q : W.cubes) (x : Euclidean d) :
    ‖∑' R : W'.cubes, weight W' R x • correction f W W' Q R‖ ≤ Bcorr := by
  by_cases hx : coordinates x ∈ (Ω' : Set (Domain d))
  · have hs : Summable (fun R : W'.cubes => weight W' R x) :=
      summable_of_hasFiniteSupport (weight_finite_support hW' x)
    have hsum : HasSum (fun R : W'.cubes => weight W' R x * Bcorr) Bcorr := by
      simpa only [weight_sum hW' hx, one_mul] using hs.hasSum.mul_right Bcorr
    apply tsum_of_norm_bounded hsum
    intro R
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg hW' R x)]
    exact mul_le_mul_of_nonneg_left (hcorr Q R) (weight_nonneg hW' R x)
  · have hz (R : W'.cubes) : weight W' R x • correction f W W' Q R = 0 := by
      rw [weight_zero_off R hx, zero_smul]
    simpa only [hz, tsum_zero, norm_zero] using hBcorr

lemma piece_bound_of_bounds
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c' C' A' M' W')
    (f : Euclidean d → 𝕜) {Bgood Bavg Bcorr : ℝ} (hBcorr : 0 ≤ Bcorr)
    (hgood : ∀ᵐ x, ‖good f W' x‖ ≤ Bgood)
    (havg : ∀ Q : W.cubes, ‖average f W Q‖ ≤ Bavg)
    (hcorr : ∀ (Q : W.cubes) (R : W'.cubes), ‖correction f W W' Q R‖ ≤ Bcorr)
    (Q : W.cubes) : ∀ᵐ x, ‖piece f W W' Q x‖ ≤ Bgood + Bavg + Bcorr := by
  filter_upwards [hgood] with x hx
  rw [piece_eq_weighted_good_add_correction hW' f Q x]
  calc
    _ ≤ ‖weight W Q x • (good f W' x - average f W Q)‖ +
      ‖∑' R : W'.cubes, weight W' R x • correction f W W' Q R‖ := norm_add_le _ _
    _ ≤ ‖good f W' x - average f W Q‖ + Bcorr := by
      apply add_le_add _ (weighted_correction_sum_bound hW' f hBcorr hcorr Q x)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg hW Q x)]
      exact mul_le_of_le_one_left (norm_nonneg _) (weight_le_one hW Q x)
    _ ≤ _ := add_le_add ((norm_sub_le _ _).trans (add_le_add hx (havg Q))) (le_refl _)

lemma weighted_correction_integral_norm_le
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c' C' A' M' W')
    (hc' : 0 < c') {f : Euclidean d → 𝕜} (hf : Integrable f)
    (Q : W.cubes) (R : W'.cubes) :
    (∫ x, ‖weight W' R x • correction f W W' Q R‖) ≤
      ∫ x, ‖weight W Q x • bad f W' R x‖ := by
  have hm := weight_integral_pos hW' hc' R
  calc
    _ = (∫ x, weight W' R x) * ‖correction f W W' Q R‖ := by
      simp_rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg hW' R _)]
      exact integral_mul_const _ _
    _ = ‖∫ x, weight W Q x • bad f W' R x‖ := by
      rw [← Real.norm_of_nonneg hm.le, ← norm_smul, correction, smul_smul,
        mul_inv_cancel₀ hm.ne', one_smul]
    _ ≤ _ := norm_integral_le_integral_norm _

lemma correction_bracket_integral_norm_le
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c' C' A' M' W')
    (hc' : 0 < c') {f : Euclidean d → 𝕜} (hf : Integrable f)
    (Q : W.cubes) (R : W'.cubes) :
    (∫ x, ‖weight W Q x • bad f W' R x - weight W' R x • correction f W W' Q R‖) ≤
      2 * ∫ x, ‖bad f W' R x‖ := by
  have hi := weighted_integrable hW (bad_integrable hW' hf R) Q
  have hic := (weight_integrable R).smul_const (correction f W W' Q R)
  have hn : (∫ x, ‖weight W Q x • bad f W' R x‖) ≤ ∫ x, ‖bad f W' R x‖ := by
    apply integral_mono hi.norm (bad_integrable hW' hf R).norm
    intro x
    change ‖weight W Q x • bad f W' R x‖ ≤ ‖bad f W' R x‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg hW Q x)]
    exact mul_le_of_le_one_left (norm_nonneg _) (weight_le_one hW Q x)
  calc
    _ ≤ ∫ x, (‖weight W Q x • bad f W' R x‖ + ‖weight W' R x • correction f W W' Q R‖) :=
      integral_mono (hi.sub hic).norm (hi.norm.add hic.norm) (fun _ => norm_sub_le _ _)
    _ = (∫ x, ‖weight W Q x • bad f W' R x‖) +
        ∫ x, ‖weight W' R x • correction f W W' Q R‖ := integral_add hi.norm hic.norm
    _ ≤ (∫ x, ‖weight W Q x • bad f W' R x‖) +
        ∫ x, ‖weight W Q x • bad f W' R x‖ :=
      add_le_add (le_refl _) (weighted_correction_integral_norm_le hW hW' hc' hf Q R)
    _ ≤ _ := by linarith

lemma correction_bracket_summable_integral_norm
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c' C' A' M' W')
    (hc' : 0 < c') {f : Euclidean d → 𝕜} (hf : Integrable f)
    (hbad : Summable (fun R : W'.cubes => ∫ x, ‖bad f W' R x‖)) (Q : W.cubes) :
    Summable (fun R : W'.cubes => ∫ x, ‖weight W Q x • bad f W' R x -
      weight W' R x • correction f W W' Q R‖) := by
  exact Summable.of_nonneg_of_le
    (fun R => integral_nonneg (fun _ => norm_nonneg _))
    (fun R => correction_bracket_integral_norm_le hW hW' hc' hf Q R) (hbad.mul_left 2)

lemma norm_sum_integrable_of_summable_integral_norm {ι : Type*} [Countable ι]
    (F : ι → Euclidean d → 𝕜) (hi : ∀ i, Integrable (F i))
    (hs : Summable (fun i => ∫ x, ‖F i x‖))
    (hpt : ∀ x, Summable (fun i => ‖F i x‖)) :
    Integrable (fun x => ∑' i, ‖F i x‖) := by
  have hm : AEStronglyMeasurable (fun x => ∑' i, ‖F i x‖) :=
    AEStronglyMeasurable.tsum (fun i => (hi i).aestronglyMeasurable.norm)
  refine ⟨hm, (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
    (fun x => tsum_nonneg (fun i => norm_nonneg (F i x))))).mpr ?_⟩
  simp_rw [ENNReal.ofReal_tsum_of_nonneg (fun i => norm_nonneg (F i _)) (hpt _)]
  rw [lintegral_tsum (f := fun i x => ENNReal.ofReal ‖F i x‖) (fun i => ENNReal.measurable_ofReal.comp_aemeasurable
    (hi i).aestronglyMeasurable.norm.aemeasurable)]
  simp_rw [ofReal_norm, ← ofReal_integral_norm_eq_lintegral_enorm (hi _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg (fun _ => norm_nonneg _)) hs]
  exact ENNReal.ofReal_lt_top

lemma piece_integrable_of_summable_bad
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c' C' A' M' W')
    (hc' : 0 < c') {f : Euclidean d → 𝕜} (hf : Integrable f)
    (hbad : Summable (fun R : W'.cubes => ∫ x, ‖bad f W' R x‖)) (Q : W.cubes) :
    Integrable (piece f W W' Q) := by
  have hsum := correction_bracket_summable_integral_norm hW hW' hc' hf hbad Q
  have hpt (x : Euclidean d) : Summable (fun R : W'.cubes =>
      weight W Q x • bad f W' R x - weight W' R x • correction f W W' Q R) :=
    summable_of_hasFiniteSupport (correction_bracket_finite_support hW' f Q x)
  have hin := norm_sum_integrable_of_summable_integral_norm
    (fun R x => weight W Q x • bad f W' R x - weight W' R x • correction f W W' Q R)
    (fun R => correction_bracket_integrable hW hW' hf Q R) hsum (fun x => (hpt x).norm)
  have hi : Integrable (fun x => ∑' R : W'.cubes,
      (weight W Q x • bad f W' R x - weight W' R x • correction f W W' Q R)) := by
    exact hin.mono'
      (AEStronglyMeasurable.tsum (fun R =>
        (correction_bracket_integrable hW hW' hf Q R).aestronglyMeasurable))
      (Eventually.of_forall fun x => norm_tsum_le_tsum_norm (hpt x).norm)
  exact (bad_integrable hW hf Q).sub hi

lemma piece_integral_zero_of_summable_bad
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c' C' A' M' W')
    (hc : 0 < c) (hc' : 0 < c') {f : Euclidean d → 𝕜} (hf : Integrable f)
    (hbad : Summable (fun R : W'.cubes => ∫ x, ‖bad f W' R x‖)) (Q : W.cubes) :
    (∫ x, piece f W W' Q x) = 0 := by
  have hsum := correction_bracket_summable_integral_norm hW hW' hc' hf hbad Q
  have hswap := integral_tsum_of_summable_integral_norm
    (fun R => correction_bracket_integrable hW hW' hf Q R) hsum
  have hz : (∫ x, ∑' R : W'.cubes, (weight W Q x • bad f W' R x -
      weight W' R x • correction f W W' Q R)) = 0 := by
    rw [← hswap]
    simp only [correction_bracket_integral_zero hW hW' hc' hf, tsum_zero]
  have hi := (bad_integrable hW hf Q).sub
    (piece_integrable_of_summable_bad hW hW' hc' hf hbad Q)
  change Integrable (fun x => bad f W Q x - piece f W W' Q x) at hi
  simp only [piece, sub_sub_cancel] at hi
  change (∫ x, bad f W Q x - ∑' R : W'.cubes,
    (weight W Q x • bad f W' R x - weight W' R x • correction f W W' Q R)) = 0
  rw [integral_sub (bad_integrable hW hf Q) hi, bad_integral_zero hW hc hf Q, hz, sub_self]

lemma weighted_bad_double_finite_support
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c' C' A' M' W')
    (f : Euclidean d → 𝕜) (x : Euclidean d) :
    Function.HasFiniteSupport (fun p : W.cubes × W'.cubes => weight W p.1 x • bad f W' p.2 x) := by
  apply ((weight_finite_support hW x).prod (bad_finite_support hW' f x)).subset
  intro p hp
  constructor
  · intro hz
    exact hp (by simp [hz])
  · intro hz
    exact hp (by simp [hz])

lemma weighted_correction_double_finite_support
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c' C' A' M' W')
    {D : ℝ} {L : ℕ} (hN : NestedEstimates D L W W')
    (f : Euclidean d → 𝕜) (x : Euclidean d) :
    Function.HasFiniteSupport (fun p : W.cubes × W'.cubes =>
      weight W' p.2 x • correction f W W' p.1 p.2) := by
  have hsf := weight_finite_support hW' x
  have hs := hsf.biUnion (fun (R : W'.cubes) _ => (hN.2 R).1)
  apply (hs.prod hsf).subset
  intro p hp
  constructor
  · apply mem_iUnion.mpr
    refine ⟨p.2, mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · intro hz
      exact hp (by simp [hz])
    · by_contra hn
      exact hp (by simp [correction_zero_of_no_inter hW hW' f p.1 p.2 hn])
  · intro hz
    exact hp (by simp [hz])

lemma piece_sum_eq_good_sub
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c' C' A' M' W')
    (hc' : 0 < c') {D : ℝ} {L : ℕ} (hN : NestedEstimates D L W W')
    (hsub : (Ω' : Set (Domain d)) ⊆ Ω)
    {f : Euclidean d → 𝕜} (hf : Integrable f) (x : Euclidean d) :
    (∑' Q : W.cubes, piece f W W' Q x) = good f W' x - good f W x := by
  have hA : Summable (Function.uncurry (fun (Q : W.cubes) (R : W'.cubes) =>
      weight W Q x • bad f W' R x)) :=
    summable_of_hasFiniteSupport (weighted_bad_double_finite_support hW hW' f x)
  have hD : Summable (Function.uncurry (fun (Q : W.cubes) (R : W'.cubes) =>
      weight W' R x • correction f W W' Q R)) :=
    summable_of_hasFiniteSupport (weighted_correction_double_finite_support hW hW' hN f x)
  have hB : Summable (fun Q : W.cubes => bad f W Q x) :=
    summable_of_hasFiniteSupport (bad_finite_support hW f x)
  have hAr (Q : W.cubes) : Summable (fun R : W'.cubes => weight W Q x • bad f W' R x) :=
    hA.prod_factor Q
  have hDr (Q : W.cubes) : Summable (fun R : W'.cubes => weight W' R x • correction f W W' Q R) :=
    hD.prod_factor Q
  have hAs : Summable (fun Q : W.cubes => ∑' R : W'.cubes, weight W Q x • bad f W' R x) := hA.prod
  have hDs : Summable (fun Q : W.cubes => ∑' R : W'.cubes, weight W' R x • correction f W W' Q R) := hD.prod
  have hp (Q : W.cubes) : piece f W W' Q x = bad f W Q x -
      (∑' R : W'.cubes, weight W Q x • bad f W' R x) +
        ∑' R : W'.cubes, weight W' R x • correction f W W' Q R := by
    rw [piece, (hAr Q).tsum_sub (hDr Q)]
    abel
  simp_rw [hp]
  rw [(hB.sub hAs).tsum_add hDs, hB.tsum_sub hAs,
    ← hA.tsum_comm, ← hD.tsum_comm]
  simp_rw [weighted_bad_coarse_sum hW hsub f]
  have hz (R : W'.cubes) : (∑' Q : W.cubes,
      weight W' R x • correction f W W' Q R) = 0 := by
    rw [tsum_const_smul'', correction_coarse_sum_zero hW hW' hc' hN hsub hf R, smul_zero]
  simp only [hz, tsum_zero, add_zero, good]
  abel

end MoreTwoLevels
end ExpandedFA.PartIV.HardyLevel


namespace ExpandedFA.PartIV.HardyLevel
open ExpandedFA.Distributions ExpandedFA.Fourier HardyWhitney HardyMaximalSpec
lemma partition_estimates_mono {d : ℕ} {Ω : TopologicalSpace.Opens (Domain d)}
    {c C D : ℝ} {A : ℕ → ℝ} {M : ℕ} {W : Partition Ω}
    (hW : PartitionEstimates c C A M W) (hCD : C ≤ D) :
    PartitionEstimates c D A M W := by
  obtain ⟨hcover, hdisj, hinside, hlocal, hoverlap, hpos, hsupp, hsum, hint, hder, hneighbor⟩ := hW
  refine ⟨hcover, hdisj, hinside, hlocal, hoverlap, hpos, hsupp, hsum, hint, hder, ?_⟩
  intro Q R h
  obtain ⟨hQR, hRQ⟩ := hneighbor Q R h
  exact ⟨hQR.trans (mul_le_mul_of_nonneg_right hCD R.val.side_nonneg),
    hRQ.trans (mul_le_mul_of_nonneg_right hCD Q.val.side_nonneg)⟩

lemma nested_estimates_mono {d : ℕ} {Ω Ω' : TopologicalSpace.Opens (Domain d)}
    {C D : ℝ} {M : ℕ} {W : Partition Ω} {W' : Partition Ω'}
    (hW : NestedEstimates C M W W') (hCD : C ≤ D) : NestedEstimates D M W W' := by
  refine ⟨?_, hW.2⟩
  intro R Q h
  obtain ⟨hsize, hsub⟩ := hW.1 R Q h
  refine ⟨hsize.trans (mul_le_mul_of_nonneg_right hCD Q.val.side_nonneg), hsub.trans ?_⟩
  apply Metric.closedBall_subset_closedBall
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCD Q.val.side_nonneg) (by norm_num)
end ExpandedFA.PartIV.HardyLevel


namespace ExpandedFA.PartIV.HardyLevel
open ExpandedFA.Distributions ExpandedFA.Fourier HardyWhitney HardyMaximalSpec
section MoreTwoLevels
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
  {Ω Ω' : TopologicalSpace.Opens (Domain d)}
  {c C c' C' : ℝ} {A A' : ℕ → ℝ} {M M' : ℕ}
  {W : Partition Ω} {W' : Partition Ω'}
lemma correction_bracket_integral_norm_le_weighted
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c' C' A' M' W')
    (hc' : 0 < c') {f : Euclidean d → 𝕜} (hf : Integrable f)
    (Q : W.cubes) (R : W'.cubes) :
    (∫ x, ‖weight W Q x • bad f W' R x - weight W' R x • correction f W W' Q R‖) ≤
      2 * ∫ x, ‖weight W Q x • bad f W' R x‖ := by
  have hi := weighted_integrable hW (bad_integrable hW' hf R) Q
  have hic := (weight_integrable R).smul_const (correction f W W' Q R)
  calc
    _ ≤ ∫ x, (‖weight W Q x • bad f W' R x‖ + ‖weight W' R x • correction f W W' Q R‖) :=
      integral_mono (hi.sub hic).norm (hi.norm.add hic.norm) (fun _ => norm_sub_le _ _)
    _ = (∫ x, ‖weight W Q x • bad f W' R x‖) +
        ∫ x, ‖weight W' R x • correction f W W' Q R‖ := integral_add hi.norm hic.norm
    _ ≤ (∫ x, ‖weight W Q x • bad f W' R x‖) +
        ∫ x, ‖weight W Q x • bad f W' R x‖ :=
      add_le_add (le_refl _) (weighted_correction_integral_norm_le hW hW' hc' hf Q R)
    _ = _ := by ring

lemma weighted_bad_coarse_norm_sum
    (hW : PartitionEstimates c C A M W)
    (hsub : (Ω' : Set (Domain d)) ⊆ Ω)
    (f : Euclidean d → 𝕜) (R : W'.cubes) (x : Euclidean d) :
    (∑' Q : W.cubes, ‖weight W Q x • bad f W' R x‖) = ‖bad f W' R x‖ := by
  by_cases hx : coordinates x ∈ (Ω' : Set (Domain d))
  · have hw (Q : W.cubes) : ‖weight W Q x • bad f W' R x‖ = weight W Q x * ‖bad f W' R x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg hW Q x)]
    simp_rw [hw]
    rw [(summable_of_hasFiniteSupport (weight_finite_support hW x)).tsum_mul_right,
      weight_sum hW (hsub hx), one_mul]
  · have hz : bad f W' R x = 0 := by simp [bad, weight_zero_off R hx]
    simp [hz]

lemma weighted_bad_coarse_lintegral_sum
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c' C' A' M' W')
    (hsub : (Ω' : Set (Domain d)) ⊆ Ω)
    {f : Euclidean d → 𝕜} (hf : Integrable f) (R : W'.cubes) :
    (∑' Q : W.cubes, ∫⁻ x, ENNReal.ofReal ‖weight W Q x • bad f W' R x‖) =
      ∫⁻ x, ENNReal.ofReal ‖bad f W' R x‖ := by
  rw [← lintegral_tsum (f := fun Q x => ENNReal.ofReal ‖weight W Q x • bad f W' R x‖)
    (fun Q => ENNReal.measurable_ofReal.comp_aemeasurable
      (weighted_integrable hW (bad_integrable hW' hf R) Q).aestronglyMeasurable.norm.aemeasurable)]
  have hpt (x : Euclidean d) : Summable (fun Q : W.cubes => ‖weight W Q x • bad f W' R x‖) :=
    ((summable_of_hasFiniteSupport (weight_finite_support hW x)).smul_const (bad f W' R x)).norm
  simp_rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hpt _),
    weighted_bad_coarse_norm_sum hW hsub f R]

lemma correction_bracket_double_lintegral_le
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c' C' A' M' W')
    (hc' : 0 < c') (hsub : (Ω' : Set (Domain d)) ⊆ Ω)
    {f : Euclidean d → 𝕜} (hf : Integrable f) :
    (∑' Q : W.cubes, ∑' R : W'.cubes, ∫⁻ x,
      ENNReal.ofReal ‖weight W Q x • bad f W' R x - weight W' R x • correction f W W' Q R‖) ≤
      2 * ∑' R : W'.cubes, ∫⁻ x, ENNReal.ofReal ‖bad f W' R x‖ := by
  calc
    _ ≤ ∑' Q : W.cubes, ∑' R : W'.cubes, 2 *
        ∫⁻ x, ENNReal.ofReal ‖weight W Q x • bad f W' R x‖ := by
      apply ENNReal.tsum_le_tsum
      intro Q
      apply ENNReal.tsum_le_tsum
      intro R
      simp_rw [ofReal_norm, ← ofReal_integral_norm_eq_lintegral_enorm
        (correction_bracket_integrable hW hW' hf Q R),
        ← ofReal_integral_norm_eq_lintegral_enorm
          (weighted_integrable hW (bad_integrable hW' hf R) Q)]
      simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using
        ENNReal.ofReal_le_ofReal (correction_bracket_integral_norm_le_weighted hW hW' hc' hf Q R)
    _ = 2 * ∑' R : W'.cubes, ∑' Q : W.cubes,
        ∫⁻ x, ENNReal.ofReal ‖weight W Q x • bad f W' R x‖ := by
      simp_rw [ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_comm]
    _ = _ := by simp_rw [weighted_bad_coarse_lintegral_sum hW hW' hsub hf]

lemma piece_lintegral_le
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c' C' A' M' W')
    {f : Euclidean d → 𝕜} (hf : Integrable f) (Q : W.cubes) :
    (∫⁻ x, ENNReal.ofReal ‖piece f W W' Q x‖) ≤
      (∫⁻ x, ENNReal.ofReal ‖bad f W Q x‖) +
      ∑' R : W'.cubes, ∫⁻ x, ENNReal.ofReal
        ‖weight W Q x • bad f W' R x - weight W' R x • correction f W W' Q R‖ := by
  have hpt (x : Euclidean d) : Summable (fun R : W'.cubes =>
      weight W Q x • bad f W' R x - weight W' R x • correction f W W' Q R) :=
    summable_of_hasFiniteSupport (correction_bracket_finite_support hW' f Q x)
  calc
    _ ≤ ∫⁻ x, (ENNReal.ofReal ‖bad f W Q x‖ + ∑' R : W'.cubes,
        ENNReal.ofReal ‖weight W Q x • bad f W' R x - weight W' R x • correction f W W' Q R‖) := by
      apply lintegral_mono
      intro x
      calc
        _ ≤ ENNReal.ofReal (‖bad f W Q x‖ + ∑' R : W'.cubes,
            ‖weight W Q x • bad f W' R x - weight W' R x • correction f W W' Q R‖) := by
          apply ENNReal.ofReal_le_ofReal
          exact (norm_sub_le _ _).trans (add_le_add (le_refl _)
            (norm_tsum_le_tsum_norm (hpt x).norm))
        _ = _ := by
          rw [ENNReal.ofReal_add (norm_nonneg _) (tsum_nonneg (fun _ => norm_nonneg _)),
            ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hpt x).norm]
    _ = _ := by
      rw [lintegral_add_left' (f := fun x => ENNReal.ofReal ‖bad f W Q x‖)
        (ENNReal.measurable_ofReal.comp_aemeasurable
        (bad_integrable hW hf Q).aestronglyMeasurable.norm.aemeasurable),
        lintegral_tsum (f := fun R x => ENNReal.ofReal
          ‖weight W Q x • bad f W' R x - weight W' R x • correction f W W' Q R‖)
          (fun R => ENNReal.measurable_ofReal.comp_aemeasurable
            (correction_bracket_integrable hW hW' hf Q R).aestronglyMeasurable.norm.aemeasurable)]

lemma piece_absolute_integral_sum_le
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c' C' A' M' W')
    (hc' : 0 < c') (hsub : (Ω' : Set (Domain d)) ⊆ Ω)
    {f : Euclidean d → 𝕜} (hf : Integrable f) :
    (∑' Q : W.cubes, ∫⁻ x, ENNReal.ofReal ‖piece f W W' Q x‖) ≤
      (∑' Q : W.cubes, ∫⁻ x, ENNReal.ofReal ‖bad f W Q x‖) +
        2 * ∑' R : W'.cubes, ∫⁻ x, ENNReal.ofReal ‖bad f W' R x‖ := by
  calc
    _ ≤ ∑' Q : W.cubes, ((∫⁻ x, ENNReal.ofReal ‖bad f W Q x‖) +
        ∑' R : W'.cubes, ∫⁻ x, ENNReal.ofReal
          ‖weight W Q x • bad f W' R x - weight W' R x • correction f W W' Q R‖) :=
      ENNReal.tsum_le_tsum (piece_lintegral_le hW hW' hf)
    _ = _ := ENNReal.tsum_add
    _ ≤ _ := add_le_add (le_refl _) (correction_bracket_double_lintegral_le hW hW' hc' hsub hf)

lemma piece_absolute_integral_sum_finite
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c' C' A' M' W')
    (hc : 0 < c) (hc' : 0 < c') (hsub : (Ω' : Set (Domain d)) ⊆ Ω)
    {f : Euclidean d → 𝕜} (hf : Integrable f) :
    (∑' Q : W.cubes, ∫⁻ x, ENNReal.ofReal ‖piece f W W' Q x‖) < ⊤ := by
  apply lt_of_le_of_lt (piece_absolute_integral_sum_le hW hW' hc' hsub hf)
  exact ENNReal.add_lt_top.mpr ⟨bad_absolute_integral_sum_finite hW hc hf,
    ENNReal.mul_lt_top (by norm_num) (bad_absolute_integral_sum_finite hW' hc' hf)⟩

end MoreTwoLevels
end ExpandedFA.PartIV.HardyLevel


namespace ExpandedFA.PartIV.HardyLevel.TestEstimates
open ExpandedFA.Fourier ExpandedFA.Distributions HardyMaximalSpec HardyWhitney

/-- The canonical maximal-cube partition, extended by the actual empty
partition when the open set is empty. -/
def canonicalFinitePartition {d : ℕ} (hd : 0 < d)
    (Ω : TopologicalSpace.Opens (Domain d))
    (hfin : volume (Ω : Set (Domain d)) < ⊤) : Partition Ω := by
  classical
  exact if h : (Ω : Set (Domain d)).Nonempty then
    canonicalPartition hd ⟨Ω, h, hfin⟩ else emptyPartition Ω

lemma canonicalFinitePartition_cubes_subset {d : ℕ} (hd : 0 < d)
    (Ω : TopologicalSpace.Opens (Domain d))
    (hfin : volume (Ω : Set (Domain d)) < ⊤) :
    (canonicalFinitePartition hd Ω hfin).cubes ⊆ maximalCubes (Ω : Set (Domain d)) := by
  classical
  unfold canonicalFinitePartition
  split_ifs <;> simp [canonicalPartition, emptyPartition]

lemma canonicalFinitePartition_of_nonempty {d : ℕ} (hd : 0 < d)
    (Ω : TopologicalSpace.Opens (Domain d))
    (hfin : volume (Ω : Set (Domain d)) < ⊤)
    (hne : (Ω : Set (Domain d)).Nonempty) :
    canonicalFinitePartition hd Ω hfin = canonicalPartition hd ⟨Ω, hne, hfin⟩ := by
  simp only [canonicalFinitePartition, dite_eq_left hne]

lemma canonicalFinitePartition_distance {d : ℕ} (hd : 0 < d)
    (Ω : TopologicalSpace.Opens (Domain d))
    (hfin : volume (Ω : Set (Domain d)) < ⊤) :
    DistanceBounds (Ω : Set (Domain d)) (canonicalFinitePartition hd Ω hfin).cubes := by
  intro Q hQ x hx
  exact maximalCubes_distance _ Q
    (canonicalFinitePartition_cubes_subset hd Ω hfin hQ) x hx

lemma canonical_finite_partition_estimates (d : ℕ) (hd : 0 < d) :
    ∃ A : ℕ → ℝ, (∀ j, 0 < A j) ∧
      ∀ (Ω : TopologicalSpace.Opens (Domain d))
        (hfin : volume (Ω : Set (Domain d)) < ⊤),
        PartitionEstimates (1 / ((30^d : ℕ) : ℝ)) 8 A (30^d)
          (canonicalFinitePartition hd Ω hfin) ∧
        (∀ (Q : (canonicalFinitePartition hd Ω hfin).cubes) j x,
          ‖iteratedFDeriv ℝ j ((canonicalFinitePartition hd Ω hfin).weight Q) x‖ ≤
            A j * Q.val.side ^ (-(j : ℤ))) := by
  classical
  obtain ⟨A, hA, hp, hop⟩ := canonical_partition_estimates d hd
  refine ⟨A, hA, ?_⟩
  intro Ω hfin
  by_cases hne : (Ω : Set (Domain d)).Nonempty
  · have hw := canonicalFinitePartition_of_nonempty hd Ω hfin hne
    rw [hw]
    exact ⟨hp ⟨Ω, hne, hfin⟩, hop ⟨Ω, hne, hfin⟩⟩
  · have hw : canonicalFinitePartition hd Ω hfin = emptyPartition Ω := by
      simp only [canonicalFinitePartition, dite_eq_right hne]
    rw [hw]
    refine ⟨empty_partition_estimates (not_nonempty_iff_eq_empty.mp hne) _ _ _ _, ?_⟩
    intro Q
    exact False.elim Q.property

lemma canonical_finite_nested {d : ℕ} (hd : 0 < d)
    (Ω Ω' : TopologicalSpace.Opens (Domain d))
    (hfin : volume (Ω : Set (Domain d)) < ⊤)
    (hfin' : volume (Ω' : Set (Domain d)) < ⊤)
    (hΩ : (Ω' : Set (Domain d)) ⊆ Ω) :
    NestedEstimates 8 (30^d) (canonicalFinitePartition hd Ω hfin)
      (canonicalFinitePartition hd Ω' hfin') := by
  classical
  by_cases hf : (Ω' : Set (Domain d)).Nonempty
  · have hc : (Ω : Set (Domain d)).Nonempty := hf.mono hΩ
    simpa only [canonicalFinitePartition, dite_eq_left hf, dite_eq_left hc] using
      canonical_nested hd ⟨Ω, hc, hfin⟩ ⟨Ω', hf, hfin'⟩ hΩ
  · simp only [canonicalFinitePartition, dite_eq_right hf]
    exact nested_estimates_empty_fine 8 (30^d) _

lemma canonicalFinitePartition_empty {d : ℕ} (hd : 0 < d)
    (Ω : TopologicalSpace.Opens (Domain d))
    (hfin : volume (Ω : Set (Domain d)) < ⊤)
    (hempty : (Ω : Set (Domain d)) = ∅) :
    (canonicalFinitePartition hd Ω hfin).cubes = ∅ := by
  have hne : ¬ (Ω : Set (Domain d)).Nonempty := by simp [hempty]
  simp [canonicalFinitePartition, hne, emptyPartition]

end ExpandedFA.PartIV.HardyLevel.TestEstimates


namespace ExpandedFA.PartIV.HardyLevel.TestEstimates
open ExpandedFA.Fourier ExpandedFA.PartIV.HardyMaximalSpec
open ExpandedFA.Distributions ExpandedFA.PartIV.HardyWhitney

lemma neg_pow_le_mul_of_le {a b L : ℝ} (ha : 0 < a) (hb : 0 < b)
    (_hL : 0 ≤ L) (h : a ≤ L * b) (k : ℕ) :
    b ^ (-(k : ℤ)) ≤ L^k * a ^ (-(k : ℤ)) := by
  have hinv : b⁻¹ ≤ L * a⁻¹ := by
    simpa only [one_div, div_eq_mul_inv, one_mul] using
      (div_le_div_iff₀ hb ha).mpr (show 1 * a ≤ L * b by simpa using h)
  simp only [zpow_neg, zpow_natCast, ← inv_pow]
  calc
    (b⁻¹)^k ≤ (L * a⁻¹)^k := pow_le_pow_left₀ (inv_nonneg.mpr hb.le) hinv k
    _ = L^k * (a⁻¹)^k := mul_pow _ _ _

def productA (A : ℕ → ℝ) (j : ℕ) : ℝ :=
  1 + ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) * A i * A (j-i) * (8:ℝ)^(j-i)

lemma productA_pos (A : ℕ → ℝ) (hA : ∀ j, 0 < A j) (j : ℕ) : 0 < productA A j := by
  unfold productA
  have hs : 0 ≤ ∑ i ∈ Finset.range (j+1),
      (j.choose i : ℝ) * A i * A (j-i) * (8:ℝ)^(j-i) := by
    exact Finset.sum_nonneg fun i hi => by
      have hAi := hA i
      have hAj := hA (j-i)
      positivity
  linarith

lemma product_weight_derivative_bound {d : ℕ} (A : ℕ → ℝ) (hA : ∀ j, 0 < A j)
    (Q R : DyadicCube d) (hside : R.side ≤ 8 * Q.side)
    (u v : Domain d → ℝ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hbu : ∀ j x, ‖iteratedFDeriv ℝ j u x‖ ≤ A j * R.side ^ (-(j : ℤ)))
    (hbv : ∀ j x, ‖iteratedFDeriv ℝ j v x‖ ≤ A j * Q.side ^ (-(j : ℤ))) :
    ∀ j x, ‖iteratedFDeriv ℝ j (fun y => u y * v y) x‖ ≤
      productA A j * R.side ^ (-(j : ℤ)) := by
  intro j x
  have hscale (i : ℕ) :
      Q.side ^ (-(i : ℤ)) ≤ (8:ℝ)^i * R.side ^ (-(i : ℤ)) :=
    neg_pow_le_mul_of_le R.side_pos Q.side_pos (by norm_num) hside i
  have hv' (i : ℕ) : ‖iteratedFDeriv ℝ i v x‖ ≤ A i * ((8:ℝ)^i * R.side ^ (-(i : ℤ))) :=
    (hbv i x).trans (mul_le_mul_of_nonneg_left (hscale i) (hA i).le)
  have hterm (i : ℕ) (hi : i ∈ Finset.range (j+1)) :
      (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i u x‖ * ‖iteratedFDeriv ℝ (j-i) v x‖ ≤
        ((j.choose i : ℝ) * A i * A (j-i) * (8:ℝ)^(j-i)) * R.side ^ (-(j : ℤ)) := by
    have hij : i ≤ j := by simp only [Finset.mem_range] at hi; omega
    have hAi := hA i
    have hAj := hA (j-i)
    have hRi := zpow_pos R.side_pos (-(i : ℤ))
    calc
      (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i u x‖ * ‖iteratedFDeriv ℝ (j-i) v x‖ ≤
          (j.choose i : ℝ) * (A i * R.side ^ (-(i : ℤ))) *
            (A (j-i) * ((8:ℝ)^(j-i) * R.side ^ (-((j-i : ℕ) : ℤ)))) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hbu i x) (by positivity))
          (hv' (j-i)) (norm_nonneg _) (by positivity)
      _ = ((j.choose i : ℝ) * A i * A (j-i) * (8:ℝ)^(j-i)) * R.side ^ (-(j : ℤ)) := by
        simp only [zpow_neg, zpow_natCast, ← inv_pow]
        have he : (R.side⁻¹)^i * (R.side⁻¹)^(j-i) = (R.side⁻¹)^j := by
          rw [← pow_add, Nat.add_sub_of_le hij]
        calc
          _ = ((j.choose i : ℝ) * A i * A (j-i) * (8:ℝ)^(j-i)) *
              ((R.side⁻¹)^i * (R.side⁻¹)^(j-i)) := by ring
          _ = _ := by rw [he]
  calc
    ‖iteratedFDeriv ℝ j (fun y => u y * v y) x‖ ≤
        ∑ i ∈ Finset.range (j+1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i u x‖ *
          ‖iteratedFDeriv ℝ (j-i) v x‖ := norm_iteratedFDeriv_mul_le hu hv x (by simp)
    _ ≤ ∑ i ∈ Finset.range (j+1),
        ((j.choose i : ℝ) * A i * A (j-i) * (8:ℝ)^(j-i)) * R.side ^ (-(j : ℤ)) :=
      Finset.sum_le_sum hterm
    _ ≤ productA A j * R.side ^ (-(j : ℤ)) := by
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right _ (le_of_lt (zpow_pos R.side_pos _))
      unfold productA
      linarith

lemma product_weight_pairing {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    {Ω Ω' : TopologicalSpace.Opens (Domain d)} (W : Partition Ω) (W' : Partition Ω')
    {c' C' : ℝ} {A : ℕ → ℝ} {M' : ℕ} (hA : ∀ j, 0 < A j)
    (hW' : PartitionEstimates c' C' A M' W')
    (hcan' : W'.cubes ⊆ maximalCubes (Ω' : Set (Domain d)))
    (hop : ∀ (Q : W.cubes) j x,
      ‖iteratedFDeriv ℝ j (W.weight Q) x‖ ≤ A j * Q.val.side ^ (-(j : ℤ)))
    (hop' : ∀ (R : W'.cubes) j x,
      ‖iteratedFDeriv ℝ j (W'.weight R) x‖ ≤ A j * R.val.side ^ (-(j : ℤ)))
    (hne : (Ω' : Set (Domain d))ᶜ.Nonempty)
    (f : Euclidean d → 𝕜) (k : ℤ)
    (hΩ' : (Ω' : Set (Domain d)) = coordinateLevel N f (k+1))
    (Q : W.cubes) (R : W'.cubes) (hside : R.val.side ≤ 8 * Q.val.side) :
    ‖∫ x, weight W Q x • (weight W' R x • f x)‖ ≤
      pairingConstant d N (productA A) * R.val.side^d * threshold (k+1) := by
  obtain ⟨z, hz, hdist⟩ := maximal_cube_outside_point hne ⟨R.val, hcan' R.property⟩
  have hgz : grand N f ((coordinateEquiv d).symm z) ≤ ENNReal.ofReal (threshold (k+1)) := by
    have hn : ¬ ENNReal.ofReal (threshold (k+1)) < grand N f ((coordinateEquiv d).symm z) := by
      change ¬ ENNReal.ofReal (threshold (k+1)) < grand N f (WithLp.toLp 2 z)
      simpa only [hΩ', coordinateLevel, level, Set.mem_preimage, Set.mem_ofPred_eq] using hz
    exact le_of_not_gt hn
  have hθ : 0 < threshold (k+1) := zpow_pos (by norm_num) _
  have hs : tsupport (fun y => W'.weight R y * W.weight Q y) ⊆ R.val.star :=
    tsupport_mul_subset_left.trans (hW'.2.2.2.2.2.2.1 R)
  have hder := product_weight_derivative_bound A hA Q.val R.val hside
    (W'.weight R) (W.weight Q) (W'.weight R).contDiff (W.weight Q).contDiff
    (hop' R) (hop Q)
  have hp := whitney_weight_pairing (productA A) (productA_pos A hA) R.val
    (fun y => W'.weight R y * W.weight Q y) ((W'.weight R).contDiff.mul (W.weight Q).contDiff)
    hs (fun j _ y => hder j y) f z hdist hθ.le hgz
  have he : (fun x => weight W Q x • (weight W' R x • f x)) =
      fun x => transportWeight 𝕜 (fun y => W'.weight R y * W.weight Q y) x * f x := by
    funext x
    change weight W Q x • (weight W' R x • f x) =
      (((weight W' R x * weight W Q x : ℝ) : 𝕜) * f x)
    simp only [RCLike.real_smul_eq_coe_mul, map_mul]
    ring
  rwa [he]

lemma correction_le_of_operator_bounds {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    {Ω Ω' : TopologicalSpace.Opens (Domain d)} (W : Partition Ω) (W' : Partition Ω')
    {c C : ℝ} {A : ℕ → ℝ} {M : ℕ} (hc : 0 < c) (hA : ∀ j, 0 < A j)
    (hW : PartitionEstimates c C A M W) (hW' : PartitionEstimates c C A M W')
    (hcan' : W'.cubes ⊆ maximalCubes (Ω' : Set (Domain d)))
    (hop : ∀ (Q : W.cubes) j x,
      ‖iteratedFDeriv ℝ j (W.weight Q) x‖ ≤ A j * Q.val.side ^ (-(j : ℤ)))
    (hop' : ∀ (R : W'.cubes) j x,
      ‖iteratedFDeriv ℝ j (W'.weight R) x‖ ≤ A j * R.val.side ^ (-(j : ℤ)))
    (hne : (Ω' : Set (Domain d))ᶜ.Nonempty)
    (hnest : ∀ (R : W'.cubes) (Q : W.cubes), (R.val.star ∩ Q.val.star).Nonempty →
      R.val.side ≤ 8 * Q.val.side)
    (f : Euclidean d → 𝕜) (hf : Integrable f) (k : ℤ)
    (hΩ' : (Ω' : Set (Domain d)) = coordinateLevel N f (k+1))
    (Q : W.cubes) (R : W'.cubes) :
    ‖correction f W W' Q R‖ ≤
      (2 * (pairingConstant d N (productA A)/c + pairingConstant d N A/c)) * threshold k := by
  have hθ : 0 < threshold k := zpow_pos (by norm_num) _
  have hθ' : 0 < threshold (k+1) := zpow_pos (by norm_num) _
  have hconst : 0 ≤ 2 * (pairingConstant d N (productA A)/c + pairingConstant d N A/c) := by
    have hD := pairingConstant_pos d N (productA A) (productA_pos A hA)
    have hD' := pairingConstant_pos d N A hA
    positivity
  by_cases hinter : (R.val.star ∩ Q.val.star).Nonempty
  swap
  · rw [correction_zero_of_no_inter hW hW' f Q R hinter, norm_zero]
    exact mul_nonneg hconst hθ.le
  have hside := hnest R Q hinter
  let den : ℝ := ∫ x, weight W' R x
  let J : ℝ := ∫ x, weight W Q x * weight W' R x
  let I : 𝕜 := ∫ x, weight W Q x • (weight W' R x • f x)
  let ar : 𝕜 := average f W' R
  have hdenpos : 0 < den := weight_integral_pos hW' hc R
  have hprod : Integrable (fun x => weight W Q x * weight W' R x) := by
    simpa only [smul_eq_mul] using weighted_integrable hW (weight_integrable R) Q
  have hJnonneg : 0 ≤ J := integral_nonneg fun x =>
    mul_nonneg (weight_nonneg hW Q x) (weight_nonneg hW' R x)
  have hJle : J ≤ den := by
    exact integral_mono hprod (weight_integrable R) fun x =>
      by nlinarith [weight_nonneg hW' R x, weight_le_one hW Q x]
  have hI := product_weight_pairing W W' hA hW' hcan' hop hop' hne f k hΩ' Q R hside
  have har : ‖ar‖ ≤ (pairingConstant d N A/c) * threshold (k+1) :=
    average_le_of_operator_bounds W' hc hA hW' hcan' hop' hne f (k+1) hΩ' R
  have hdenlower : c * R.val.side^d ≤ den := by
    dsimp [den]
    rw [weight_integral_eq]
    simpa only [DyadicCube.volume_carrier_toReal] using (hW'.2.2.2.2.2.2.2.2.1 R).2
  have hIratio : ‖den⁻¹ • I‖ ≤ (pairingConstant d N (productA A)/c) * threshold (k+1) :=
    average_ratio_bound R.val hc (pairingConstant_pos d N (productA A) (productA_pos A hA)).le
      hθ'.le hdenlower I hI
  have hcoef0 : 0 ≤ den⁻¹ * J := mul_nonneg (inv_nonneg.mpr hdenpos.le) hJnonneg
  have hcoef1 : den⁻¹ * J ≤ 1 := by
    calc
      den⁻¹ * J ≤ den⁻¹ * den := mul_le_mul_of_nonneg_left hJle (inv_nonneg.mpr hdenpos.le)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hdenpos)
  have hsplit : correction f W W' Q R = den⁻¹ • I - (den⁻¹ * J) • ar := by
    have hi := weighted_integrable hW (weighted_integrable hW' hf R) Q
    have he : (fun x => weight W Q x • bad f W' R x) =
        fun x => weight W Q x • (weight W' R x • f x) -
          (weight W Q x * weight W' R x) • ar := by
      funext x
      dsimp [bad, ar]
      simp only [smul_sub, smul_smul]
    unfold correction
    rw [he, integral_sub hi (hprod.smul_const ar), integral_smul_const, smul_sub, smul_smul]
  have hbound : ‖correction f W W' Q R‖ ≤
      (pairingConstant d N (productA A)/c + pairingConstant d N A/c) * threshold (k+1) := by
    rw [hsplit]
    calc
      ‖den⁻¹ • I - (den⁻¹ * J) • ar‖ ≤ ‖den⁻¹ • I‖ + ‖(den⁻¹ * J) • ar‖ := norm_sub_le _ _
      _ ≤ (pairingConstant d N (productA A)/c) * threshold (k+1) + ‖ar‖ := by
        apply add_le_add hIratio
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef0]
        exact mul_le_of_le_one_left (norm_nonneg _) hcoef1
      _ ≤ (pairingConstant d N (productA A)/c + pairingConstant d N A/c) * threshold (k+1) := by
        nlinarith [har]
  have hstep : threshold (k+1) = 2 * threshold k := by
    unfold threshold
    rw [zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
    norm_num
    ring
  calc
    ‖correction f W W' Q R‖ ≤
        (pairingConstant d N (productA A)/c + pairingConstant d N A/c) * threshold (k+1) := hbound
    _ = _ := by rw [hstep]; ring

end ExpandedFA.PartIV.HardyLevel.TestEstimates


namespace ExpandedFA.PartIV.HardyLevel
open ExpandedFA.Distributions ExpandedFA.Fourier HardyWhitney HardyMaximalSpec

lemma assemble_level_decomposition {𝕜 : Type} [RCLike 𝕜] {d N : ℕ}
    {c : ℝ} {A : ℕ → ℝ} {M : ℕ} {U V : ℝ}
    (hc : 0 < c) (hA : ∀ j, 0 < A j) (hM : 0 < M)
    (hU : 0 ≤ U) (hV : 0 ≤ V)
    (hdom : ∃ B : ℝ, 0 < B ∧ ∀ f : Euclidean d → 𝕜, Integrable f →
      ∀ᵐ x, ENNReal.ofReal ‖f x‖ ≤ ENNReal.ofReal B * grand N f x)
    (hdata : ∀ f : Euclidean d → 𝕜, Integrable f → (∫⁻ x, grand N f x) < ⊤ →
      ∃ (Ω : ℤ → TopologicalSpace.Opens (Domain d)) (W : ∀ k, Partition (Ω k)),
        (∀ k, (Ω k : Set (Domain d)) = coordinateLevel N f k) ∧
        (∀ k, PartitionEstimates c 8 A M (W k)) ∧
        (∀ k, NestedEstimates 8 M (W k) (W (k + 1))) ∧
        (∀ k, (Ω k : Set (Domain d)) = ∅ → (W k).cubes = ∅) ∧
        (∀ k (Q : (W k).cubes), ‖average f (W k) Q‖ ≤ U * threshold k) ∧
        (∀ k (Q : (W k).cubes) (R : (W (k + 1)).cubes),
          ‖correction f (W k) (W (k + 1)) Q R‖ ≤ V * threshold k)) :
    ∃ (c C : ℝ) (A : ℕ → ℝ) (M : ℕ),
      0 < c ∧ 1 ≤ C ∧ (∀ j, 0 < A j) ∧ 0 < M ∧
      ∀ f : Euclidean d → 𝕜, Integrable f →
      (∫⁻ x, grand N f x) < ⊤ →
      ∃ (Ω : ℤ → TopologicalSpace.Opens (Domain d)) (W : ∀ k, Partition (Ω k)),
        (∀ k, (Ω k : Set (Domain d)) = coordinateLevel N f k) ∧
        (∀ k, PartitionEstimates c C A M (W k)) ∧
        (∀ k, NestedEstimates C M (W k) (W (k + 1))) ∧
        (∀ k, (Ω k : Set (Domain d)) = ∅ → (W k).cubes = ∅) ∧
        (∀ k, Integrable (good f (W k))) ∧
        (∀ k, ∀ᵐ x, ‖good f (W k) x‖ ≤ C * threshold k) ∧
        Tendsto (fun k : ℤ => ∫ x, ‖good f (W k) x - f x‖) atTop (𝓝 0) ∧
        (∀ φ : Schwartz 𝕜 d,
          Tendsto (fun k : ℤ => ∫ x, φ x * good f (W k) x) atBot (𝓝 0)) ∧
        (∀ (k : ℤ) (Q : (W k).cubes),
          Integrable (piece f (W k) (W (k + 1)) Q) ∧
          (∫ x, piece f (W k) (W (k + 1)) Q x) = 0 ∧
          (∀ᵐ x, x ∉ cubeRegion Q.val C → piece f (W k) (W (k + 1)) Q x = 0) ∧
          (∀ᵐ x, ‖piece f (W k) (W (k + 1)) Q x‖ ≤ C * threshold k)) ∧
        (∀ k,
          (∑' Q : (W k).cubes, ∫⁻ x,
            ENNReal.ofReal ‖piece f (W k) (W (k + 1)) Q x‖) < ⊤ ∧
          (∀ᵐ x, (∑' Q : (W k).cubes, piece f (W k) (W (k + 1)) Q x) =
            good f (W (k + 1)) x - good f (W k) x)) ∧
        (∑' k : ℤ, ∑' Q : (W k).cubes,
          ENNReal.ofReal (C * threshold k) * volume (cubeRegion Q.val 1)) ≤
            2 * ENNReal.ofReal C * ∫⁻ x, grand N f x := by
  obtain ⟨B, hB, hdom⟩ := hdom
  let H : ℝ := B + U
  let C : ℝ := 8 + 2 * H + U + V
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hBC : B ≤ H := by dsimp [H]; linarith
  have hUC : U ≤ H := by dsimp [H]; linarith
  have h8C : 8 ≤ C := by dsimp [C]; linarith
  have hHC : H ≤ C := by dsimp [C]; linarith
  have hC : 0 ≤ C := by linarith
  refine ⟨c, C, A, M, hc, by linarith, hA, hM, ?_⟩
  intro f hf hI
  obtain ⟨Ω, W, hΩ, hW0, hN0, he, havg, hcorr⟩ := hdata f hf hI
  have hW (k : ℤ) : PartitionEstimates c C A M (W k) :=
    partition_estimates_mono (hW0 k) h8C
  have hN (k : ℤ) : NestedEstimates C M (W k) (W (k + 1)) :=
    nested_estimates_mono (hN0 k) h8C
  have hsub (k : ℤ) : (Ω (k + 1) : Set (Domain d)) ⊆ Ω k := by
    rw [hΩ (k + 1), hΩ k]
    exact (coordinate_levels N f hf hI k).2.2
  have hgoodH (k : ℤ) : ∀ᵐ x, ‖good f (W k) x‖ ≤ H * threshold k := by
    apply good_bound_of_grand_and_average_bound (hW k) hB.le hBC (hdom f hf) k (hΩ k)
    intro Q
    exact (havg k Q).trans (mul_le_mul_of_nonneg_right hUC (threshold_pos k).le)
  have hgood (k : ℤ) : ∀ᵐ x, ‖good f (W k) x‖ ≤ C * threshold k := by
    filter_upwards [hgoodH k] with x hx
    exact hx.trans (mul_le_mul_of_nonneg_right hHC (threshold_pos k).le)
  refine ⟨Ω, W, hΩ, hW, hN, he, (fun k => good_integrable (hW k) hc hf), hgood,
    good_tendsto_L1_of_average_bound f hf hI Ω W hΩ hW U havg,
    (fun φ => pairing_tendsto_zero (fun k => good f (W k)) C hgood φ φ.integrable), ?_, ?_,
    coefficient_bound f hf Ω W hΩ hC hW⟩
  · intro k Q
    have hbad := bad_summable_integral_norm (hW (k + 1)) hc hf
    refine ⟨piece_integrable_of_summable_bad (hW k) (hW (k + 1)) hc hf hbad Q,
      piece_integral_zero_of_summable_bad (hW k) (hW (k + 1)) hc hc hf hbad Q,
      Eventually.of_forall (fun x hx => piece_zero_off_dilate (hW k) (hW (k + 1))
        (by linarith : 9 / 8 ≤ C) (hN k) f Q x hx), ?_⟩
    have hb := piece_bound_of_bounds (hW k) (hW (k + 1)) f
      (mul_nonneg hV (threshold_pos k).le) (hgoodH (k + 1)) (havg k) (hcorr k) Q
    filter_upwards [hb] with x hx
    have hs : threshold (k + 1) = 2 * threshold k := by
      simp [threshold, zpow_add₀, mul_comm]
    rw [hs] at hx
    exact hx.trans (by dsimp [C]; nlinarith [threshold_pos k])
  · intro k
    exact ⟨piece_absolute_integral_sum_finite (hW k) (hW (k + 1)) hc hc (hsub k) hf,
      Eventually.of_forall (piece_sum_eq_good_sub (hW k) (hW (k + 1)) hc (hN k) (hsub k) hf)⟩
end ExpandedFA.PartIV.HardyLevel


namespace ExpandedFA.PartIV.HardyLevel
open ExpandedFA.Distributions ExpandedFA.Fourier HardyWhitney HardyMaximalSpec TestEstimates

/-- The full Whitney localization of the differences of consecutive good
functions, with all integer levels and the actual grand maximal function. -/
theorem level_decomposition :
    Specs.ExpandedFA.PartIV.HardyLevelDecomposition.levelDecompositionType := by
  intro 𝕜 _ d N hd _hN
  obtain ⟨A, hA, hp⟩ := canonical_finite_partition_estimates d hd
  let c : ℝ := 1 / ((30 ^ d : ℕ) : ℝ)
  let U : ℝ := pairingConstant d N A / c
  let V : ℝ := 2 * (pairingConstant d N (productA A) / c + pairingConstant d N A / c)
  have hc : 0 < c := by dsimp [c]; positivity
  have hU : 0 ≤ U := (div_pos (pairingConstant_pos d N A hA) hc).le
  have hV : 0 ≤ V := by
    have hP := pairingConstant_pos d N (productA A) (productA_pos A hA)
    have hP' := pairingConstant_pos d N A hA
    dsimp [V]
    positivity
  refine assemble_level_decomposition (c := c) (A := A) (M := 30 ^ d) (U := U) (V := V)
    hc hA (by positivity) hU hV (exists_ae_norm_le_grand (𝕜 := 𝕜) d N) ?_
  intro f hf hI
  let Ω : ℤ → TopologicalSpace.Opens (Domain d) :=
    fun k => ⟨coordinateLevel N f k, (coordinate_levels N f hf hI k).1⟩
  have hfin (k : ℤ) : volume (Ω k : Set (Domain d)) < ⊤ :=
    (coordinate_levels N f hf hI k).2.1
  let W : ∀ k, Partition (Ω k) := fun k => canonicalFinitePartition hd (Ω k) (hfin k)
  have hW (k : ℤ) : PartitionEstimates c 8 A (30 ^ d) (W k) := (hp (Ω k) (hfin k)).1
  have hop (k : ℤ) : ∀ (Q : (W k).cubes) j x,
      ‖iteratedFDeriv ℝ j ((W k).weight Q) x‖ ≤ A j * Q.val.side ^ (-(j : ℤ)) :=
    (hp (Ω k) (hfin k)).2
  have hsub (k : ℤ) : (Ω (k + 1) : Set (Domain d)) ⊆ Ω k :=
    (coordinate_levels N f hf hI k).2.2
  have hnest (k : ℤ) : NestedEstimates 8 (30 ^ d) (W k) (W (k + 1)) :=
    canonical_finite_nested hd (Ω k) (Ω (k + 1)) (hfin k) (hfin (k + 1)) (hsub k)
  have hcan (k : ℤ) : (W k).cubes ⊆ maximalCubes (Ω k : Set (Domain d)) :=
    canonicalFinitePartition_cubes_subset hd (Ω k) (hfin k)
  have hne (k : ℤ) : (Ω k : Set (Domain d))ᶜ.Nonempty := complement_nonempty hd (hfin k)
  refine ⟨Ω, W, (fun _ => rfl), hW, hnest, ?_, ?_, ?_⟩
  · intro k he
    exact canonicalFinitePartition_empty hd (Ω k) (hfin k) he
  · intro k Q
    exact average_le_of_operator_bounds (W k) hc hA (hW k) (hcan k) (hop k) (hne k) f k rfl Q
  · intro k Q R
    exact correction_le_of_operator_bounds (W k) (W (k + 1)) hc hA (hW k) (hW (k + 1))
      (hcan (k + 1)) (hop k) (hop (k + 1)) (hne (k + 1))
      (fun R Q h => (hnest k).1 R Q h |>.1) f hf k rfl Q R

end ExpandedFA.PartIV.HardyLevel
