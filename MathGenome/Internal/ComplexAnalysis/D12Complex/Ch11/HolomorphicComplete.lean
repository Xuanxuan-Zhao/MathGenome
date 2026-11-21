import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.HolomorphicComplete
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.CompactOpenMetric
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.HolomorphicLimits

noncomputable section
open Set Filter
open scoped Topology

namespace D12Complex.Ch11.HolomorphicComplete

@[simp] lemma extendFromOpen_apply (Ω : Set ℂ) (f : Ω → ℂ) (z : Ω) :
    extendFromOpen Ω f z = f z := by
  simp [extendFromOpen, z.property]

theorem restriction : Specs.D12Complex.Ch11.HolomorphicComplete.restriction_type := by
  intro Ω f hf
  let g : C(Ω, ℂ) := ⟨fun z => f z,
    continuous_iff_continuousAt.mpr fun z =>
      (hf.2 z z.property).continuousAt.comp continuous_subtype_val.continuousAt⟩
  have hg : HolomorphicOn Ω (extendFromOpen Ω g) := by
    refine ⟨hf.1, fun z hz => ?_⟩
    apply (hf.2 z hz).congr_of_eventuallyEq
    filter_upwards [hf.1.mem_nhds hz] with w hw
    simp [extendFromOpen, hw, g]
  exact ⟨⟨g, hg⟩, fun _ => rfl⟩

/-- Metric Cauchyness controls the values uniformly on any compact subset. -/
lemma uniformCauchy_on_compact (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (F : ℕ → C(Ω, ℂ))
    (hF : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      compactOpenDistance Ω (F m) (F n) < ε)
    (K : Set ℂ) (hK : IsCompact K) (hsub : K ⊆ Ω) :
    UniformCauchySeqOn (fun n => extendFromOpen Ω (F n)) atTop K := by
  obtain ⟨j, hj, hstage⟩ := CompactExhaustion.cofinal Ω hΩ K hK hsub
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  have hδ : 0 < (1 / 2 : ℝ) ^ (j + 1) * min 1 ε :=
    mul_pos (CompactOpenMetric.weight_pos j) (lt_min zero_lt_one hε)
  obtain ⟨N, hN⟩ := hF _ hδ
  refine ⟨N, fun m hm n hn z hz => ?_⟩
  have hs := CompactOpenMetric.stageSup_lt_of_distance_lt Ω (F m) (F n) j hε
    (hN m hm n hn)
  have hzstage := CompactExhaustion.stage_mono Ω hj (Nat.le_succ j) (hstage hz)
  have hb := (CompactOpenMetric.supremum Ω hΩ j (F m) (F n)
    (compactStageSup Ω j (F m) (F n)) (NNReal.coe_nonneg _)).mp le_rfl
      ⟨z, hzstage⟩
  simpa [extendFromOpen, hsub hz, dist_eq_norm] using hb.trans_lt hs

theorem cauchy_limit : Specs.D12Complex.Ch11.HolomorphicComplete.cauchy_limit_type := by
  classical
  intro Ω hΩ F hF
  let G : ℕ → ℂ → ℂ := fun n => extendFromOpen Ω (F n).val
  have hpoint : ∀ z : Ω, ∃ w : ℂ, Tendsto (fun n => G n z) atTop (𝓝 w) := by
    intro z
    have hc := uniformCauchy_on_compact Ω hΩ (fun n => (F n).val) hF
      {z.val} (isCompact_singleton) (singleton_subset_iff.mpr z.property)
    exact cauchySeq_tendsto_of_complete (hc.cauchySeq (mem_singleton z.val))
  let f : ℂ → ℂ := extendFromOpen Ω (fun z => (hpoint z).choose)
  have hlimpoint : ∀ z ∈ Ω, Tendsto (fun n => G n z) atTop (𝓝 (f z)) := by
    intro z hz
    simpa only [f, extendFromOpen, dite_eq_left hz] using (hpoint ⟨z, hz⟩).choose_spec
  have hlim : TendstoLocallyUniformlyOn G f atTop Ω := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mpr
    intro K hsub hK
    exact UniformCauchySeqOn.tendstoUniformlyOn_of_tendsto
      (uniformCauchy_on_compact Ω hΩ (fun n => (F n).val) hF K hK hsub)
      (fun z hz => hlimpoint z (hsub hz))
  have hhol : HolomorphicOn Ω f :=
    D12Complex.HolomorphicLimits.holomorphic_limit Ω G f hΩ (fun n => (F n).property) hlim
  let g : C(Ω, ℂ) := ⟨fun z => f z,
    continuous_iff_continuousAt.mpr fun z =>
      (hhol.2 z z.property).continuousAt.comp continuous_subtype_val.continuousAt⟩
  have hgeq : extendFromOpen Ω g = f := by
    funext z
    by_cases hz : z ∈ Ω
    · simp [extendFromOpen, hz, g]
    · simp [extendFromOpen, hz, f]
  let hg : HolomorphicSpace Ω := ⟨g, hgeq.symm ▸ hhol⟩
  have hcompact : ∀ K : Set Ω, IsCompact K →
      TendstoUniformlyOn (fun n z => (F n).val z) hg.val atTop K := by
    intro K hK
    have hu := (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mp hlim
      (Subtype.val '' K) (by rintro _ ⟨z, _, rfl⟩; exact z.property)
      (hK.image continuous_subtype_val)
    have hc := (hu.comp (Subtype.val : Ω → ℂ)).mono
      (show K ⊆ Subtype.val ⁻¹' (Subtype.val '' K) from fun z hz => ⟨z, hz, rfl⟩)
    exact hc.congr (Eventually.of_forall fun n z hz => extendFromOpen_apply Ω (F n).val z)
  exact ⟨hg, (CompactOpenMetric.convergence Ω hΩ ℕ atTop
    (fun n => (F n).val) g).mpr hcompact, hcompact⟩

/-- The induced metric restricts exactly the already established series metric. -/
@[instance_reducible] def metricSpace (Ω : Set ℂ) (hΩ : IsOpen Ω) :
    MetricSpace (HolomorphicSpace Ω) :=
  @MetricSpace.induced _ _ Subtype.val (by intro f g h; exact Subtype.ext h)
    (CompactOpenMetric.metricSpace Ω hΩ)

theorem complete : Specs.D12Complex.Ch11.HolomorphicComplete.complete_type := by
  intro Ω hΩ
  let := metricSpace Ω hΩ
  refine ⟨metricSpace Ω hΩ, fun _ _ => rfl, ?_⟩
  apply Metric.complete_of_cauchySeq_tendsto
  intro F hF
  obtain ⟨f, hlim, _⟩ := cauchy_limit Ω hΩ F (Metric.cauchySeq_iff.mp hF)
  refine ⟨f, ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he := (Metric.tendsto_nhds.mp hlim) ε hε
  filter_upwards [he] with n hn
  change compactOpenDistance Ω (F n).val f.val < ε
  exact lt_of_le_of_lt (le_abs_self _) (by simpa [Real.dist_eq] using hn)

end D12Complex.Ch11.HolomorphicComplete
