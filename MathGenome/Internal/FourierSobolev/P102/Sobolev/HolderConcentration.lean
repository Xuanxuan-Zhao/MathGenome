import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.HolderConcentration
import MathGenome.Internal.FourierSobolev.P102.Sobolev.ConcentrationScaling
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.UniformSpace.UniformApproximation

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff ENNReal NNReal Topology
namespace P102.Sobolev.EndpointNoncompactness
open P102.U4

namespace HolderConcentration

lemma rescale_at_scaled_point {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : Space d → 𝕜) (x₀ z : Space d) (a : ℝ) {r : ℝ} (hr : r ≠ 0) :
    rescale φ x₀ a r (x₀ + r • z) = r ^ a • φ z := by
  simp [rescale, smul_smul, hr]

/-- The endpoint Hölder quotient of a scaled pair is exactly independent of r. -/
lemma rescale_holder_quotient {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : Space d → 𝕜) (x₀ z w : Space d) (a : ℝ) {r : ℝ}
    (hr : 0 < r) (hzw : z ≠ w) :
    ‖rescale φ x₀ a r (x₀ + r • z) - rescale φ x₀ a r (x₀ + r • w)‖ =
      (‖φ z - φ w‖ / ‖z - w‖ ^ a) *
        ‖(x₀ + r • z) - (x₀ + r • w)‖ ^ a := by
  rw [rescale_at_scaled_point _ _ _ _ hr.ne', rescale_at_scaled_point _ _ _ _ hr.ne',
    ← smul_sub, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hr.le _)]
  have heq : (x₀ + r • z) - (x₀ + r • w) = r • (z - w) := by
    rw [smul_sub]
    abel
  rw [heq, norm_smul, Real.norm_of_nonneg hr.le,
    Real.mul_rpow hr.le (norm_nonneg _)]
  have hp : ‖z - w‖ ^ a ≠ 0 :=
    (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzw)) _).ne'
  field_simp

lemma rescale_eq_zero_of_lt_dist {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {φ : Space d → 𝕜} (hφ : tsupport φ ⊆ Metric.closedBall 0 1)
    (x₀ : Space d) (a : ℝ) {r : ℝ} (hr : 0 < r) {x : Space d}
    (hrx : r < ‖x - x₀‖) : rescale φ x₀ a r x = 0 := by
  have hnot : r⁻¹ • (x - x₀) ∉ tsupport φ := by
    intro hs
    have hb : r⁻¹ * ‖x - x₀‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hr.le)] using hφ hs
    have hle : ‖x - x₀‖ ≤ r := by
      calc
        ‖x - x₀‖ = r * (r⁻¹ * ‖x - x₀‖) := by field_simp
        _ ≤ r * 1 := mul_le_mul_of_nonneg_left hb hr.le
        _ = r := mul_one _
    exact (not_le_of_gt hrx) hle
  simp only [rescale, image_eq_zero_of_notMem_tsupport hnot, smul_zero]

/-- Away from the concentration point the family is eventually identically zero. -/
lemma rescale_tendsto_zero_off_center {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {φ : Space d → 𝕜} (hφ : tsupport φ ⊆ Metric.closedBall 0 1)
    (x₀ : Space d) (a : ℝ) {x : Space d} (hx : x ≠ x₀) :
    Tendsto (fun r => rescale φ x₀ a r x) (𝓝[>] 0) (𝓝 0) := by
  have hd : 0 < ‖x - x₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hevent : ∀ᶠ r in 𝓝[>] (0 : ℝ), rescale φ x₀ a r x = 0 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hd).filter_mono nhdsWithin_le_nhds] with r hr hrx
    exact rescale_eq_zero_of_lt_dist hφ x₀ a hr hrx
  exact tendsto_const_nhds.congr' (hevent.mono fun _ h => h.symm)

/-- In the supercritical range the amplitude goes to zero uniformly on the
whole Euclidean space, hence on any domain or its closure. -/
lemma rescale_tendsto_uniformly_zero {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {φ : Space d → 𝕜} (hφ : Continuous φ) (hcompact : HasCompactSupport φ)
    (x₀ : Space d) {a : ℝ} (ha : 0 < a) (S : Set (Space d)) :
    TendstoUniformlyOn (rescale φ x₀ a) 0 (𝓝[>] 0) S := by
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuous hφ
  have ht : Tendsto (fun r : ℝ => r ^ a * M) (𝓝[>] 0) (𝓝 0) := by
    have hid : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using (hid.rpow_const_nhds_zero ha).mul_const M
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [self_mem_nhdsWithin, ht.eventually_lt_const hε] with r hrpos hr x _hx
  have hb : ‖rescale φ x₀ a r x‖ ≤ r ^ a * M := by
    simp only [rescale, norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt hrpos) a)]
    exact mul_le_mul_of_nonneg_left (hM _) (Real.rpow_nonneg (le_of_lt hrpos) a)
  simpa only [Pi.zero_apply, dist_zero_left] using hb.trans_lt hr

/-- Uniform limits are uniquely determined pointwise. A positive endpoint
seminorm at every term therefore rules out convergence in the full Hölder norm
when the family already converges uniformly to zero. -/
theorem no_holder_subsequence_of_uniform_zero {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (F : ℕ → Space d → 𝕜) (S : Set (Space d)) (a : ℝ)
    (hzero : TendstoUniformlyOn F 0 atTop S)
    {c : ℝ} (hc : 0 < c)
    (hlower : ∀ n, ∃ x ∈ S, ∃ y ∈ S,
      x ≠ y ∧ c * ‖x - y‖ ^ a ≤ ‖F n x - F n y‖) :
    ∀ σ : ℕ → ℕ, StrictMono σ → ¬ ∃ g,
      HolderTendsto (fun n => F (σ n)) g S a := by
  intro σ hσ
  rintro ⟨g, hsup, hsemi⟩
  have hg (x : Space d) (hx : x ∈ S) : g x = 0 :=
    tendsto_nhds_unique (hsup.tendsto_at hx) ((hzero.tendsto_at hx).comp hσ.tendsto_atTop)
  obtain ⟨n, hn⟩ := (hsemi (c / 2) (half_pos hc)).exists
  obtain ⟨x, hx, y, hy, hxy, hlow⟩ := hlower (σ n)
  have hupp := hn x hx y hy
  rw [hg x hx, hg y hy, sub_zero, sub_zero] at hupp
  have hp : 0 < ‖x - y‖ ^ a := Real.rpow_pos_of_pos
    (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _
  nlinarith

/-- A fixed-height concentration has a discontinuous pointwise limit at its
centre. Uniform convergence of any subsequence would make that limit continuous. -/
theorem no_uniform_subsequence_of_fixed_height {X : Type*} [TopologicalSpace X]
    {E : Type*} [NormedAddCommGroup E] (F : ℕ → X → E) (S : Set X) (x₀ : X)
    (hx₀ : x₀ ∈ S) (hacc : x₀ ∈ closure (S \ {x₀}))
    (hcont : ∀ n, ContinuousOn (F n) S)
    (hzero : ∀ x ∈ S, x ≠ x₀ → Tendsto (fun n => F n x) atTop (𝓝 0))
    {c : E} (hc : c ≠ 0) (hcenter : ∀ n, F n x₀ = c) :
    ∀ σ : ℕ → ℕ, StrictMono σ → ¬ ∃ g,
      TendstoUniformlyOn (fun n => F (σ n)) g atTop S := by
  intro σ hσ
  rintro ⟨g, hg⟩
  have hgc : ContinuousOn g S :=
    hg.continuousOn (Frequently.of_forall fun n => hcont (σ n))
  have hgzero (x : X) (hx : x ∈ S \ {x₀}) : g x = 0 := by
    have hne : x ≠ x₀ := by simpa only [mem_singleton_iff] using hx.2
    exact tendsto_nhds_unique (hg.tendsto_at hx.1) ((hzero x hx.1 hne).comp hσ.tendsto_atTop)
  have hg0 : g x₀ = 0 :=
    ((hgc x₀ hx₀).mono sdiff_subset).eq_const_of_mem_closure hacc hgzero
  have hgc0 : g x₀ = c :=
    tendsto_nhds_unique (hg.tendsto_at hx₀) (by simpa only [hcenter] using tendsto_const_nhds)
  exact hc (hgc0.symm.trans hg0)

/-- Bounded smooth compactly supported functions belong to every Hölder class
with exponent in (0,1]. This holds globally, even for unbounded domains. -/
lemma smooth_compact_holder_bound {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f : Space d → 𝕜} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (S : Set (Space d)) : ∃ M : ℝ, IntegerEmbeddings.HolderNormBound f S a M := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hf (by simp)
  obtain ⟨A₀, hA⟩ := hc.exists_bound_of_continuous hf.continuous
  let A := max A₀ 0
  let B := max (K : ℝ) (2 * A)
  have hA0 : 0 ≤ A := le_max_right _ _
  have hb (x : Space d) : ‖f x‖ ≤ A := (hA x).trans (le_max_left _ _)
  have hB0 : 0 ≤ B := K.coe_nonneg.trans (le_max_left _ _)
  refine ⟨A + B, A, B, hA0, hB0, le_rfl, fun x _ => hb x, ?_⟩
  intro x _ y _
  by_cases hxy : x = y
  · simp [hxy, Real.zero_rpow ha.ne']
  have ht : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  by_cases hsmall : ‖x - y‖ ≤ 1
  · have hp : ‖x - y‖ ≤ ‖x - y‖ ^ a := by
      simpa using Real.rpow_le_rpow_of_exponent_ge ht hsmall ha1
    calc
      ‖f x - f y‖ ≤ (K : ℝ) * ‖x - y‖ := by
        simpa only [dist_eq_norm] using hK.dist_le_mul x y
      _ ≤ B * ‖x - y‖ ^ a :=
        mul_le_mul (le_max_left _ _) hp (norm_nonneg _) hB0
  · have hp : 1 ≤ ‖x - y‖ ^ a := Real.one_le_rpow (le_of_not_ge hsmall) ha.le
    calc
      ‖f x - f y‖ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
      _ ≤ 2 * A := by linarith [hb x, hb y]
      _ ≤ B * ‖x - y‖ ^ a := by
        calc
          _ ≤ B := le_max_right _ _
          _ = B * 1 := (mul_one _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hp hB0

lemma scales_tendsto_positive {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (scales ρ) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.mpr ⟨scales_tendsto ρ,
    Filter.Eventually.of_forall (scales_pos hρ)⟩

/-- The normalized bump drops from one to zero along a unit coordinate vector.
Both scaled points are interior, and their endpoint quotient is exactly one. -/
lemma family_holder_lower {d : ℕ} (hd : 0 < d) {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {p : ℝ≥0} [Fact (1 ≤ (p : ℝ≥0∞))]
    (D : ConcentrationFamily 𝕜 Ω p) (a : ℝ) {r : ℝ}
    (hr : 0 < r) (hrρ : r < D.radius) :
    ∃ x ∈ (Ω : Set (Space d)), ∃ y ∈ (Ω : Set (Space d)),
      x ≠ y ∧ 1 * ‖x - y‖ ^ a ≤
        ‖rescale D.bump D.center a r x - rescale D.bump D.center a r y‖ := by
  let i : Fin d := ⟨0, hd⟩
  let w := coordinateVector d i
  have hw : ‖w‖ = 1 := (EuclideanSpace.basisFun (Fin d) ℝ).norm_eq_one i
  have hw0 : w ≠ 0 := by intro h; simp [h] at hw
  have hout : w ∉ tsupport D.bump := by
    intro h
    have := D.support h
    simp only [Metric.mem_ball, dist_zero_right, hw, lt_self_iff_false] at this
  have hv : D.bump w = 0 := image_eq_zero_of_notMem_tsupport hout
  have hy : D.center + r • w ∈ (Ω : Set (Space d)) := by
    apply D.ball_subset
    simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
      norm_smul, Real.norm_of_nonneg hr.le, hw, mul_one] using hrρ
  have hne : D.center + r • (0 : Space d) ≠ D.center + r • w := by
    intro h
    have hz : r • (0 : Space d) = r • w := add_left_cancel h
    exact hw0 ((smul_right_injective _ hr.ne' hz).symm)
  refine ⟨D.center + r • (0 : Space d), by simpa using D.center_mem,
    D.center + r • w, hy, hne, ?_⟩
  have hquot := rescale_holder_quotient D.bump D.center 0 w a hr (Ne.symm hw0)
  simpa only [D.value_zero, hv, sub_zero, norm_one, zero_sub, norm_neg,
    hw, Real.one_rpow, div_one] using hquot.ge

end HolderConcentration

open HolderConcentration

/-- Supercritical endpoint failure on every nonempty open set. -/
theorem supercritical_concentration : HolderExpected.Supercritical := by
  intro d hd 𝕜 _ Ω hΩ p hp hdp _
  obtain ⟨D⟩ := concentration_family d hd 𝕜 Ω hΩ p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hp)
  have hdpr : (d : ℝ) < p := by exact_mod_cast hdp
  have ha : 0 < 1 - (d : ℝ) / p := sub_pos.mpr ((div_lt_one hp0).mpr hdpr)
  have ha1 : 1 - (d : ℝ) / p ≤ 1 := sub_le_self _ (div_nonneg (Nat.cast_nonneg _) hp0.le)
  let S := closure (Ω : Set (Space d))
  have hu : TendstoUniformlyOn (rescale D.bump D.center (1 - (d : ℝ) / p)) 0
      (𝓝[>] 0) S :=
    rescale_tendsto_uniformly_zero D.smooth.continuous D.compact D.center ha S
  refine ⟨D, ?_, hu, ⟨1, zero_lt_one, ?_⟩, ?_⟩
  · intro r hr _
    exact smooth_compact_holder_bound (rescale_smooth D.smooth D.center _ r)
      (rescale_compact D.compact D.center _ hr.ne') ha ha1 S
  · intro r hr hrρ
    exact family_holder_lower hd D _ hr hrρ
  · have huseq : TendstoUniformlyOn
        (fun n => rescale D.bump D.center (1 - (d : ℝ) / p) (scales D.radius n))
        0 atTop S := fun u hu' =>
      (scales_tendsto_positive D.radius_pos).eventually (hu u hu')
    apply no_holder_subsequence_of_uniform_zero
      (fun n => rescale D.bump D.center (1 - (d : ℝ) / p) (scales D.radius n))
      S (1 - (d : ℝ) / p) huseq zero_lt_one
    intro n
    obtain ⟨x, hx, y, hy, hxy, hl⟩ :=
      family_holder_lower hd D (1 - (d : ℝ) / p)
        (scales_pos D.radius_pos n) (scales_lt D.radius_pos n)
    exact ⟨x, subset_closure hx, y, subset_closure hy, hxy, hl⟩

/-- Fixed-height endpoint failure in dimension one. -/
theorem dimension_one_concentration : HolderExpected.DimensionOne := by
  intro 𝕜 _ Ω hΩ
  let : Fact (1 ≤ ((1 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
  obtain ⟨D⟩ := concentration_family 1 (by omega) 𝕜 Ω hΩ 1 le_rfl
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · intro r hr hrρ
    simpa only [Nat.cast_one, NNReal.coe_one, div_one, sub_self] using
      D.representative r hr hrρ
  · intro r _
    simp [rescale_center, D.value_zero]
  · intro x hx
    exact rescale_tendsto_zero_off_center
      (D.support.trans Metric.ball_subset_closedBall) D.center 0 hx
  · let S := closure (Ω : Set (Space 1))
    have hacc : D.center ∈ closure (S \ {D.center}) := by
      apply mem_closure_iff_nhdsWithin_neBot.mpr
      rw [sdiff_eq, nhdsWithin_inter_of_mem]
      · infer_instance
      · exact mem_nhdsWithin_of_mem_nhds (mem_of_superset
          (Ω.isOpen.mem_nhds D.center_mem) subset_closure)
    apply no_uniform_subsequence_of_fixed_height
      (fun n => rescale D.bump D.center 0 (scales D.radius n)) S D.center
      (subset_closure D.center_mem) hacc (c := (1 : 𝕜))
    · intro n
      exact (rescale_smooth D.smooth D.center 0 _).continuous.continuousOn
    · intro x _ hx
      exact (rescale_tendsto_zero_off_center
        (D.support.trans Metric.ball_subset_closedBall) D.center 0 hx).comp
          (scales_tendsto_positive D.radius_pos)
    · exact one_ne_zero
    · intro n
      simp [rescale_center, D.value_zero]

/-- In particular, both failures hold for the bounded Lipschitz open sets of
Rellich's theorem, without a connectedness assumption. -/
theorem holder_concentration_lipschitz : HolderExpected.Lipschitz := by
  constructor
  · intro m e Ω _hΩ hΩ 𝕜 _ p hp hdp _
    exact supercritical_concentration (m + 1) (by omega) 𝕜 Ω hΩ p hp hdp
  · intro e Ω _hΩ hΩ 𝕜 _
    exact dimension_one_concentration 𝕜 Ω hΩ

end P102.Sobolev.EndpointNoncompactness
