import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.CompactOpenMetric
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.CompactExhaustion
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith

open Set Filter
open scoped Topology NNReal

namespace D12Complex.Ch11.CompactOpenMetric

noncomputable def stageSup := compactStageSup
noncomputable def distance := compactOpenDistance

lemma stage_compact (Ω : Set ℂ) (hΩ : IsOpen Ω) (n : ℕ) :
    IsCompact (compactExhaustionStage Ω (n + 1)) :=
  CompactExhaustion.compact Ω hΩ (n + 1) (by omega)

lemma stageSup_eq_dist (Ω : Set ℂ) (hΩ : IsOpen Ω) (n : ℕ) (f g : C(Ω, ℂ)) :
    (compactStageSup Ω n f g : ℝ) =
      @dist C(compactExhaustionStage Ω (n + 1), ℂ)
        (by
          let := isCompact_iff_compactSpace.mp (stage_compact Ω hΩ n)
          infer_instance) (restrictToStage Ω n f) (restrictToStage Ω n g) := by
  let := isCompact_iff_compactSpace.mp (stage_compact Ω hΩ n)
  exact congrArg (fun x : ℝ≥0 => (x : ℝ))
    (ContinuousMap.nndist_eq_iSup (f := restrictToStage Ω n f)
      (g := restrictToStage Ω n g)).symm

theorem supremum : Specs.D12Complex.Ch11.CompactOpenMetric.supremum_type := by
  intro Ω hΩ n f g r hr
  let := isCompact_iff_compactSpace.mp (stage_compact Ω hΩ n)
  rw [stageSup_eq_dist Ω hΩ]
  simpa only [dist_eq_norm, restrictToStage, ContinuousMap.comp_apply, ContinuousMap.coe_mk] using
    (ContinuousMap.dist_le (f := restrictToStage Ω n f) (g := restrictToStage Ω n g) hr)

theorem emptySupremum : Specs.D12Complex.Ch11.CompactOpenMetric.emptySupremum_type := by
  intro Ω n f g h
  have : IsEmpty (compactExhaustionStage Ω (n + 1)) := by
    rw [h]
    infer_instance
  simp [compactStageSup]

lemma weight_pos (n : ℕ) : 0 < (1 / 2 : ℝ) ^ (n + 1) := by positivity

lemma summable_weights : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) := by
  simpa only [pow_succ] using
    (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_right (1 / 2)

lemma term_nonneg (Ω : Set ℂ) (f g : C(Ω, ℂ)) (n : ℕ) :
    0 ≤ (1 / 2 : ℝ) ^ (n + 1) * min 1 (compactStageSup Ω n f g : ℝ) :=
  mul_nonneg (weight_pos n).le (le_min zero_le_one (NNReal.coe_nonneg _))

lemma term_le_weight (Ω : Set ℂ) (f g : C(Ω, ℂ)) (n : ℕ) :
    (1 / 2 : ℝ) ^ (n + 1) * min 1 (compactStageSup Ω n f g : ℝ) ≤
      (1 / 2 : ℝ) ^ (n + 1) := by
  exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (weight_pos n).le).trans_eq (mul_one _)

theorem summable : Specs.D12Complex.Ch11.CompactOpenMetric.summable_type := by
  intro Ω f g
  exact summable_weights.of_nonneg_of_le (term_nonneg Ω f g) (term_le_weight Ω f g)

lemma stageSup_self (Ω : Set ℂ) (n : ℕ) (f : C(Ω, ℂ)) :
    compactStageSup Ω n f f = 0 := by
  simp only [compactStageSup, nndist_self]
  exact ciSup_bot

lemma stageSup_comm (Ω : Set ℂ) (n : ℕ) (f g : C(Ω, ℂ)) :
    compactStageSup Ω n f g = compactStageSup Ω n g f := by
  simp only [compactStageSup, nndist_comm]

lemma stageSup_triangle (Ω : Set ℂ) (hΩ : IsOpen Ω) (n : ℕ) (f g h : C(Ω, ℂ)) :
    (compactStageSup Ω n f h : ℝ) ≤
      (compactStageSup Ω n f g : ℝ) + (compactStageSup Ω n g h : ℝ) := by
  let := isCompact_iff_compactSpace.mp (stage_compact Ω hΩ n)
  simp only [stageSup_eq_dist Ω hΩ]
  exact dist_triangle _ _ _

lemma truncate_triangle {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : c ≤ a + b) :
    min 1 c ≤ min 1 a + min 1 b := by
  by_cases ha' : a ≤ 1
  · by_cases hb' : b ≤ 1
    · rw [min_eq_right ha', min_eq_right hb']
      exact (min_le_right _ _).trans hc
    · rw [min_eq_right ha', min_eq_left (le_of_not_ge hb')]
      exact (min_le_left _ _).trans (by linarith)
  · rw [min_eq_left (le_of_not_ge ha')]
    exact (min_le_left _ _).trans (le_add_of_nonneg_right (le_min zero_le_one hb))

lemma distance_self (Ω : Set ℂ) (f : C(Ω, ℂ)) : compactOpenDistance Ω f f = 0 := by
  simp [compactOpenDistance, stageSup_self]

lemma distance_comm (Ω : Set ℂ) (f g : C(Ω, ℂ)) :
    compactOpenDistance Ω f g = compactOpenDistance Ω g f := by
  simp only [compactOpenDistance, stageSup_comm Ω _ f g]

lemma distance_nonneg (Ω : Set ℂ) (f g : C(Ω, ℂ)) : 0 ≤ compactOpenDistance Ω f g :=
  tsum_nonneg (term_nonneg Ω f g)

lemma term_le_distance (Ω : Set ℂ) (f g : C(Ω, ℂ)) (n : ℕ) :
    (1 / 2 : ℝ) ^ (n + 1) * min 1 (compactStageSup Ω n f g : ℝ) ≤
      compactOpenDistance Ω f g :=
  (summable Ω f g).le_tsum n (fun j _ => term_nonneg Ω f g j)

lemma distance_triangle (Ω : Set ℂ) (hΩ : IsOpen Ω) (f g h : C(Ω, ℂ)) :
    compactOpenDistance Ω f h ≤ compactOpenDistance Ω f g + compactOpenDistance Ω g h := by
  unfold compactOpenDistance
  rw [← (summable Ω f g).tsum_add (summable Ω g h)]
  refine (summable Ω f h).tsum_le_tsum ?_ ((summable Ω f g).add (summable Ω g h))
  intro n
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left
    (truncate_triangle (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
      (stageSup_triangle Ω hΩ n f g h)) (weight_pos n).le

/-- Small metric distance controls the untruncated supremum on each fixed stage. -/
lemma stageSup_lt_of_distance_lt (Ω : Set ℂ) (f g : C(Ω, ℂ))
    (n : ℕ) {ε : ℝ} (_hε : 0 < ε)
    (h : compactOpenDistance Ω f g < (1 / 2 : ℝ) ^ (n + 1) * min 1 ε) :
    (compactStageSup Ω n f g : ℝ) < ε := by
  have hm : min 1 (compactStageSup Ω n f g : ℝ) < min 1 ε :=
    (mul_lt_mul_iff_right₀ (weight_pos n)).mp ((term_le_distance Ω f g n).trans_lt h)
  rcases (min_lt_iff.mp hm) with h1 | h2
  · exact False.elim ((not_lt_of_ge (min_le_left 1 ε)) h1)
  · exact h2.trans_le (min_le_right _ _)

lemma eq_of_distance_eq_zero (Ω : Set ℂ) (hΩ : IsOpen Ω) (f g : C(Ω, ℂ))
    (h : compactOpenDistance Ω f g = 0) : f = g := by
  ext z
  obtain ⟨j, hj, hz⟩ := CompactExhaustion.exists_stage_of_mem hΩ z.property
  have hz' := CompactExhaustion.stage_mono Ω hj (Nat.le_succ j) hz
  have hsup : (compactStageSup Ω j f g : ℝ) = 0 := by
    apply le_antisymm _ (NNReal.coe_nonneg _)
    apply le_of_forall_pos_lt_add
    intro ε hε
    simpa only [zero_add] using stageSup_lt_of_distance_lt Ω f g j hε
      (by rw [h]; exact mul_pos (weight_pos j) (lt_min zero_lt_one hε))
  have hn := (supremum Ω hΩ j f g 0 le_rfl).mp hsup.le ⟨z.val, hz'⟩
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))

/-- An actual metric structure with the specified series as its distance. -/
@[instance_reducible]
noncomputable def metricSpace (Ω : Set ℂ) (hΩ : IsOpen Ω) : MetricSpace C(Ω, ℂ) where
  dist := compactOpenDistance Ω
  dist_self := distance_self Ω
  dist_comm := distance_comm Ω
  dist_triangle := distance_triangle Ω hΩ
  eq_of_dist_eq_zero := eq_of_distance_eq_zero Ω hΩ _ _

theorem metric : Specs.D12Complex.Ch11.CompactOpenMetric.metric_type := by
  intro Ω hΩ
  exact ⟨metricSpace Ω hΩ, fun _ _ => rfl⟩

lemma stageWithin_compact (Ω : Set ℂ) (hΩ : IsOpen Ω) (n : ℕ) :
    IsCompact {z : Ω | z.val ∈ compactExhaustionStage Ω (n + 1)} := by
  let := isCompact_iff_compactSpace.mp (stage_compact Ω hΩ n)
  let inclusion : compactExhaustionStage Ω (n + 1) → Ω :=
    fun z => ⟨z.val, z.property.1⟩
  have hc : Continuous inclusion := continuous_subtype_val.subtype_mk _
  have he : Set.range inclusion = {z : Ω | z.val ∈ compactExhaustionStage Ω (n + 1)} := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact w.property
    · intro hz
      exact ⟨⟨z.val, hz⟩, rfl⟩
  rw [← he]
  exact isCompact_range hc

lemma compact_subset_stage (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (K : Set Ω) (hK : IsCompact K) :
    ∃ n : ℕ, ∀ z ∈ K, z.val ∈ compactExhaustionStage Ω (n + 1) := by
  obtain ⟨j, hj, hsub⟩ := CompactExhaustion.cofinal Ω hΩ
    (Subtype.val '' K) (hK.image continuous_subtype_val)
    (by rintro z ⟨w, _, rfl⟩; exact w.property)
  exact ⟨j, fun z hz => CompactExhaustion.stage_mono Ω hj (Nat.le_succ j)
    (hsub ⟨z, hz, rfl⟩)⟩

lemma tendsto_stageSup_iff (Ω : Set ℂ) (hΩ : IsOpen Ω) (n : ℕ)
    {ι : Type} (l : Filter ι) (F : ι → C(Ω, ℂ)) (f : C(Ω, ℂ)) :
    Tendsto (fun i => (compactStageSup Ω n (F i) f : ℝ)) l (𝓝 0) ↔
      TendstoUniformlyOn (fun i z => F i z) f l
        {z : Ω | z.val ∈ compactExhaustionStage Ω (n + 1)} := by
  let := isCompact_iff_compactSpace.mp (stage_compact Ω hΩ n)
  rw [Metric.tendsto_nhds, Metric.tendstoUniformlyOn_iff]
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)]
  constructor
  · intro h ε hε
    filter_upwards [h ε hε] with i hi z hz
    have hp := ContinuousMap.dist_apply_le_dist (f := restrictToStage Ω n (F i))
      (g := restrictToStage Ω n f) ⟨z.val, hz⟩
    rw [← stageSup_eq_dist Ω hΩ] at hp
    exact (dist_comm _ _).trans_le hp |>.trans_lt hi
  · intro h ε hε
    filter_upwards [h ε hε] with i hi
    rw [stageSup_eq_dist Ω hΩ]
    apply (ContinuousMap.dist_lt_iff hε).mpr
    intro z
    exact (dist_comm _ _).trans_lt (hi ⟨z.val, z.property.1⟩ z.property)

lemma tendsto_distance_iff_stages (Ω : Set ℂ) {ι : Type} (l : Filter ι)
    (F : ι → C(Ω, ℂ)) (f : C(Ω, ℂ)) :
    Tendsto (fun i => compactOpenDistance Ω (F i) f) l (𝓝 0) ↔
      ∀ n : ℕ, Tendsto (fun i => (compactStageSup Ω n (F i) f : ℝ)) l (𝓝 0) := by
  constructor
  · intro h n
    rw [Metric.tendsto_nhds] at h ⊢
    intro ε hε
    have hδ : 0 < (1 / 2 : ℝ) ^ (n + 1) * min 1 ε :=
      mul_pos (weight_pos n) (lt_min zero_lt_one hε)
    filter_upwards [h _ hδ] with i hi
    have hi' : compactOpenDistance Ω (F i) f < (1 / 2 : ℝ) ^ (n + 1) * min 1 ε := by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (distance_nonneg Ω (F i) f)] using hi
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)] using
      stageSup_lt_of_distance_lt Ω (F i) f n hε hi'
  · intro h
    have ht : ∀ n : ℕ, Tendsto
        (fun i => (1 / 2 : ℝ) ^ (n + 1) * min 1 (compactStageSup Ω n (F i) f : ℝ))
        l (𝓝 (0 : ℝ)) := by
      intro n
      simpa only [min_eq_right zero_le_one, mul_zero] using
        (tendsto_const_nhds (x := (1 / 2 : ℝ) ^ (n + 1))).mul
          ((tendsto_const_nhds (x := (1 : ℝ))).min (h n))
    have hb : ∀ᶠ i in l, ∀ n : ℕ,
        ‖(1 / 2 : ℝ) ^ (n + 1) * min 1 (compactStageSup Ω n (F i) f : ℝ)‖ ≤
          (1 / 2 : ℝ) ^ (n + 1) :=
      Eventually.of_forall fun i n => by
        rw [Real.norm_eq_abs, abs_of_nonneg (term_nonneg Ω (F i) f n)]
        exact term_le_weight Ω (F i) f n
    simpa only [compactOpenDistance, tsum_zero] using
      (tendsto_tsum_of_dominated_convergence summable_weights ht hb)

theorem convergence : Specs.D12Complex.Ch11.CompactOpenMetric.convergence_type := by
  intro Ω hΩ ι l F f
  rw [tendsto_distance_iff_stages]
  constructor
  · intro h K hK
    obtain ⟨n, hn⟩ := compact_subset_stage Ω hΩ K hK
    exact ((tendsto_stageSup_iff Ω hΩ n l F f).mp (h n)).mono hn
  · intro h n
    exact (tendsto_stageSup_iff Ω hΩ n l F f).mpr
      (h _ (stageWithin_compact Ω hΩ n))

theorem topology : Specs.D12Complex.Ch11.CompactOpenMetric.topology_type := by
  intro Ω hΩ ι l F f
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  exact (convergence Ω hΩ ι l F f).symm

theorem empty : Specs.D12Complex.Ch11.CompactOpenMetric.empty_type := by
  refine ⟨0, trivial, ?_⟩
  intro f _
  ext z
  exact False.elim z.property

end D12Complex.Ch11.CompactOpenMetric
