import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.SubcriticalConcentration
import MathGenome.Internal.FourierSobolev.P102.Sobolev.ConcentrationScaling
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff ENNReal NNReal Topology
namespace P102.Sobolev.EndpointNoncompactness
open P102.U4

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

lemma rescale_tendsto_zero_ae {d : ℕ} (hd : 0 < d)
    {𝕜 : Type} [RCLike 𝕜] {φ : Space d → 𝕜}
    (hφ : tsupport φ ⊆ Metric.closedBall 0 1) (x₀ : Space d) (a : ℝ)
    (Ω : Opens (Space d)) :
    ∀ᵐ x ∂volume.restrict (Ω : Set (Space d)),
      Tendsto (fun r => rescale φ x₀ a r x) (𝓝[>] 0) (𝓝 0) := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hne : ∀ᵐ x : Space d ∂volume, x ≠ x₀ := by
    rw [ae_iff]
    simp
  filter_upwards [ae_restrict_of_ae hne] with x hx
  exact rescale_tendsto_zero_off_center hφ x₀ a hx

/-- Lp convergence has an a.e. convergent subsubsequence. Together with a.e.
vanishing this excludes every subsequence with a positive fixed norm.
No finiteness assumption on the measure is used. -/
theorem no_lp_subsequence_of_ae_zero {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {q : ℝ≥0∞} (hq : q ≠ 0)
    (F : ℕ → α → E)
    (hzero : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0))
    {c : ℝ≥0∞} (hc : c ≠ 0) (hnorm : ∀ n, eLpNorm (F n) q μ = c) :
    ∀ σ : ℕ → ℕ, StrictMono σ → ∀ g : α → E,
      ¬ Tendsto (fun n => eLpNorm (F (σ n) - g) q μ) atTop (𝓝 0) := by
  intro σ hσ g hconv
  obtain ⟨τ, hτ, hτconv⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm hq hconv).exists_seq_tendsto_ae
  have hg : g =ᵐ[μ] 0 := by
    filter_upwards [hzero, hτconv] with x hx htx
    exact tendsto_nhds_unique htx ((hx.comp hσ.tendsto_atTop).comp hτ.tendsto_atTop)
  have hconst (n : ℕ) : eLpNorm (F (σ n) - g) q μ = c := by
    rw [← hnorm (σ n)]
    apply eLpNorm_congr_ae
    filter_upwards [hg] with x hx
    simp only [Pi.sub_apply, hx, Pi.zero_apply, sub_zero]
  have : c = 0 := tendsto_nhds_unique tendsto_const_nhds (by simpa only [hconst] using hconv)
  exact hc this


theorem lp_representative_bridge : SubcriticalExpected.LpBridge := by
  intro α E _ _ μ q _ F V hV g
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  have heq : (fun n => eLpNorm ((V n : α → E) - (g : α → E)) q μ) =
      (fun n => eLpNorm (F n - (g : α → E)) q μ) := by
    funext n
    exact eLpNorm_congr_ae ((hV n).sub Filter.EventuallyEq.rfl)
  rw [heq]


/-- The same smooth representatives, bundled in the actual quotient normed space. -/
lemma lp_sequence_noncompact_of_representatives {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {q : ℝ≥0∞} (hq : 1 ≤ q)
    (F : ℕ → Space d → 𝕜) (hF : ∀ n, MemLp (F n) q (volume.restrict (Ω : Set (Space d))))
    {c : ℝ} (hc : 0 ≤ c)
    (hnorm : ∀ n, eLpNorm (F n) q (volume.restrict (Ω : Set (Space d))) = ENNReal.ofReal c)
    (hno : NoLpSubsequence F Ω q) : LpSequenceNoncompact F Ω q c := by
  let : Fact (1 ≤ q) := ⟨hq⟩
  let V : ℕ → Lp 𝕜 q (volume.restrict (Ω : Set (Space d))) := fun n => (hF n).toLp (F n)
  have hV (n : ℕ) : (V n : Space d → 𝕜) =ᵐ[volume.restrict (Ω : Set (Space d))] F n :=
    (hF n).coeFn_toLp
  refine ⟨hq, V, hV, ?_, ?_⟩
  · intro n
    rw [Lp.norm_toLp, hnorm n, ENNReal.toReal_ofReal hc]
  · intro σ hσ g hconv
    apply hno σ hσ
    refine ⟨g, Lp.memLp g, ?_⟩
    exact (lp_representative_bridge (fun n => F (σ n)) (fun n => V (σ n))
      (fun n => hV (σ n)) g).mp hconv

/-- Subcritical concentration on every nonempty open set, including p=1.
The construction is local and uses no boundary or finite-volume hypothesis. -/
theorem subcritical_concentration : SubcriticalExpected.OpenSet := by
  intro d 𝕜 _ Ω hΩ p hp hpd _
  have hd : 0 < d := by
    have : (0 : ℝ≥0) < d := lt_of_lt_of_le zero_lt_one (hp.trans hpd.le)
    exact_mod_cast this
  have hq1 : 1 ≤ (criticalExponent d p : ℝ≥0∞) := by
    exact_mod_cast one_le_criticalExponent hp hpd
  have hq0 : (criticalExponent d p : ℝ≥0∞) ≠ 0 := ne_of_gt (zero_lt_one.trans_le hq1)
  obtain ⟨D⟩ := concentration_family d hd 𝕜 Ω hΩ p hp
  let f := rescale D.bump D.center (1 - (d : ℝ) / p)
  let c := (eLpNorm D.bump (criticalExponent d p) volume).toReal
  have hc : 0 < c := bump_lpNorm_pos D.smooth.continuous D.compact D.value_zero hq0
  have hfixed (r : ℝ) (hr : 0 < r) (hrρ : r < D.radius) :
      MemLp (f r) (criticalExponent d p) (volume.restrict (Ω : Set (Space d))) ∧
      eLpNorm (f r) (criticalExponent d p) (volume.restrict (Ω : Set (Space d))) =
        ENNReal.ofReal c := by
    have hm := (family_scalar_scaling D r hr hrρ (criticalExponent d p)).1
    refine ⟨hm, ?_⟩
    have he : (eLpNorm (f r) (criticalExponent d p)
        (volume.restrict (Ω : Set (Space d)))).toReal = c := by
      rw [eLpNorm_restrict_of_support Ω (D.support_rescale r hr hrρ)]
      exact rescale_critical_lpNorm hp hpd D.bump D.smooth.continuous D.center hr
    exact (ENNReal.ofReal_toReal hm.eLpNorm_ne_top).symm.trans (congrArg ENNReal.ofReal he)
  have hae : ∀ᵐ x ∂volume.restrict (Ω : Set (Space d)),
      Tendsto (fun r => f r x) (𝓝[>] 0) (𝓝 0) :=
    rescale_tendsto_zero_ae hd (D.support.trans Metric.ball_subset_closedBall)
      D.center _ Ω
  have hs : Tendsto (scales D.radius) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨scales_tendsto _,
      Filter.Eventually.of_forall (scales_pos D.radius_pos)⟩
  let F := fun n => f (scales D.radius n)
  have hF (n : ℕ) := hfixed (scales D.radius n)
    (scales_pos D.radius_pos n) (scales_lt D.radius_pos n)
  have hzero : ∀ᵐ x ∂volume.restrict (Ω : Set (Space d)),
      Tendsto (fun n => F n x) atTop (𝓝 0) := by
    filter_upwards [hae] with x hx
    exact hx.comp hs
  have hno : NoLpSubsequence F Ω (criticalExponent d p) := by
    intro σ hσ
    rintro ⟨g, _hg, hconv⟩
    exact no_lp_subsequence_of_ae_zero hq0 F hzero
      (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) (fun n => (hF n).2) σ hσ g hconv
  refine ⟨D, c, hc, hfixed, hae, hno, ?_⟩
  exact lp_sequence_noncompact_of_representatives hq1 F (fun n => (hF n).1)
    hc.le (fun n => (hF n).2) hno

/-- In particular the endpoint inclusion fails to be compact on every
nonempty bounded Lipschitz open set of the source theorem. -/
theorem subcritical_concentration_lipschitz : SubcriticalExpected.Lipschitz := by
  intro m e Ω _hL hΩ 𝕜 _ p hp hpd _
  exact subcritical_concentration (m + 1) 𝕜 Ω hΩ p hp hpd

end P102.Sobolev.EndpointNoncompactness
