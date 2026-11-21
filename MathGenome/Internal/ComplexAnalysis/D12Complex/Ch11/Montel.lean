import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.Montel
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.HolomorphicCompactness
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.HolomorphicComplete
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section
open Set Filter Metric
open scoped Topology

namespace D12Complex.Ch11.Montel

/-- A sequence with ever larger values on a fixed compact set cannot have
a finite locally uniform subsequential limit. -/
lemma locallyBounded_of_finiteNormal (Ω : Set ℂ) (𝓕 : Set (ℂ → ℂ))
    (hΩ : IsOpen Ω) (hn : FiniteNormal Ω 𝓕) :
    HolomorphicCompactness.LocallyBounded Ω 𝓕 := by
  classical
  by_contra hb
  simp only [HolomorphicCompactness.LocallyBounded] at hb
  push Not at hb
  obtain ⟨K, hK, hKΩ, hb⟩ := hb
  have hbad (n : ℕ) : ∃ f ∈ 𝓕, ∃ z ∈ K, (n : ℝ) < ‖f z‖ :=
    hb n (Nat.cast_nonneg n)
  choose F hF z hz hlarge using hbad
  obtain ⟨φ, f, hφ, hf, hlim⟩ := hn F hF
  have hu := (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mp hlim K hKΩ hK
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (show ContinuousOn f K from
      fun w hw => (hf.2 w (hKΩ hw)).continuousAt.continuousWithinAt)
  have he := (Metric.tendstoUniformlyOn_iff.mp hu) 1 zero_lt_one
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  obtain ⟨n, hn⟩ := exists_nat_gt (M + 1)
  let k := max N n
  have hk := hN k (le_max_left _ _) (z (φ k)) (hz (φ k))
  have hv : ‖F (φ k) (z (φ k))‖ < M + 1 := by
    have ht := norm_le_norm_add_norm_sub (f (z (φ k))) (F (φ k) (z (φ k)))
    have hm := hM (z (φ k)) (hz (φ k))
    rw [dist_eq_norm, norm_sub_rev] at hk
    rw [norm_sub_rev] at ht
    linarith
  have hnφ : (n : ℝ) ≤ (φ k : ℝ) := by
    exact_mod_cast (le_max_right N n).trans (hφ.id_le k)
  have hl := hlarge (φ k)
  linarith

theorem locallyBounded_iff_finiteNormal :
    Specs.D12Complex.Ch11.Montel.locallyBounded_iff_finiteNormal_type := by
  intro Ω 𝓕 hΩ hhol
  exact ⟨fun hb => HolomorphicCompactness.subsequence_holomorphic_limit Ω 𝓕 hΩ hhol hb,
    locallyBounded_of_finiteNormal Ω 𝓕 hΩ⟩

/-- In a metric space, sequential relative compactness implies compactness
of the closure. Approximation errors tend to zero along every subsequence. -/
lemma isCompact_closure_of_subsequences {X : Type*} [MetricSpace X]
    (s : Set X)
    (h : ∀ F : ℕ → X, (∀ n, F n ∈ s) →
      ∃ f : X, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (F ∘ φ) atTop (𝓝 f)) :
    IsCompact (closure s) := by
  classical
  apply IsSeqCompact.isCompact
  intro F hF
  have ha (n : ℕ) : ∃ g ∈ s, dist (F n) g < 1 / ((n : ℝ) + 1) :=
    Metric.mem_closure_iff.mp (hF n) _ (by positivity)
  choose G hG hd using ha
  obtain ⟨f, φ, hφ, hlim⟩ := h G hG
  have hdist : Tendsto (fun n => dist (G n) (F n)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) (fun n => by simpa only [dist_comm] using (hd n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have ht : Tendsto (F ∘ φ) atTop (𝓝 f) :=
    hlim.congr_dist (hdist.comp hφ.tendsto_atTop)
  exact ⟨f, isClosed_closure.mem_of_tendsto ht (Eventually.of_forall fun n => hF (φ n)),
    φ, hφ, ht⟩

/-- The precise metric on Hol(Ω) has the already established compact-open
convergence. This bridge works for every metric with that distance. -/
lemma tendsto_iff_locallyUniform (Ω : Set ℂ) (hΩ : IsOpen Ω)
    [m : MetricSpace (HolomorphicSpace Ω)]
    (hm : ∀ f g : HolomorphicSpace Ω,
      dist f g = compactOpenDistance Ω f.val g.val)
    (G : ℕ → HolomorphicSpace Ω) (g : HolomorphicSpace Ω) :
    Tendsto G atTop (𝓝 g) ↔
      TendstoLocallyUniformlyOn (fun n => extendFromOpen Ω (G n).val)
        (extendFromOpen Ω g.val) atTop Ω := by
  let : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  rw [tendsto_iff_dist_tendsto_zero]
  simp_rw [hm]
  rw [← CompactOpenMetric.topology Ω hΩ ℕ atTop (fun n => (G n).val) g.val,
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly,
    tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  simp only [Function.comp_def, HolomorphicComplete.extendFromOpen_apply]

/-- Restricting functions in a finite normal family gives convergent
subsequences in the exact metric on Hol(Ω). -/
lemma subsequences_of_finiteNormal (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (𝓕 : Set (ℂ → ℂ)) (hn : FiniteNormal Ω 𝓕)
    [m : MetricSpace (HolomorphicSpace Ω)]
    (hm : ∀ f g : HolomorphicSpace Ω,
      dist f g = compactOpenDistance Ω f.val g.val)
    (G : ℕ → HolomorphicSpace Ω) (hG : ∀ n, G n ∈ restrictedFamily Ω 𝓕) :
    ∃ g : HolomorphicSpace Ω, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (G ∘ φ) atTop (𝓝 g) := by
  classical
  choose F hF hGF using hG
  obtain ⟨φ, f, hφ, hf, hlim⟩ := hn F hF
  obtain ⟨g, hg⟩ := HolomorphicComplete.restriction Ω f hf
  refine ⟨g, φ, hφ, (tendsto_iff_locallyUniform Ω hΩ hm (G ∘ φ) g).mpr ?_⟩
  exact (hlim.congr (fun n z hz => by
    simpa only [Function.comp_apply, extendFromOpen, dite_eq_left hz] using
      (hGF (φ n) ⟨z, hz⟩).symm)).congr_right (fun z hz => by
        simpa only [extendFromOpen, dite_eq_left hz] using (hg ⟨z, hz⟩).symm)

/-- Conversely, compactness of the closure produces ordinary locally
uniform convergence after restriction and extension of representatives. -/
lemma finiteNormal_of_compactClosure (Ω : Set ℂ) (𝓕 : Set (ℂ → ℂ))
    (hΩ : IsOpen Ω) (hhol : ∀ f ∈ 𝓕, HolomorphicOn Ω f)
    (hc : CompactClosure Ω 𝓕) : FiniteNormal Ω 𝓕 := by
  classical
  obtain ⟨m, hm, hc⟩ := hc
  let := m
  intro F hF
  choose G hG using fun n => HolomorphicComplete.restriction Ω (F n) (hhol _ (hF n))
  have hmem (n : ℕ) : G n ∈ restrictedFamily Ω 𝓕 := ⟨F n, hF n, hG n⟩
  obtain ⟨g, _, φ, hφ, hlim⟩ := hc.tendsto_subseq (fun n => subset_closure (hmem n))
  refine ⟨φ, extendFromOpen Ω g.val, hφ, g.property, ?_⟩
  exact ((tendsto_iff_locallyUniform Ω hΩ hm (G ∘ φ) g).mp hlim).congr
    (fun n z hz => by
      simpa only [Function.comp_apply, extendFromOpen, dite_eq_left hz] using
        hG (φ n) ⟨z, hz⟩)

theorem locallyBounded_iff_compactClosure :
    Specs.D12Complex.Ch11.Montel.locallyBounded_iff_compactClosure_type := by
  intro Ω 𝓕 hΩ hhol
  constructor
  · intro hb
    let := HolomorphicComplete.metricSpace Ω hΩ
    have hn : FiniteNormal Ω 𝓕 :=
      (locallyBounded_iff_finiteNormal Ω 𝓕 hΩ hhol).mp hb
    exact ⟨HolomorphicComplete.metricSpace Ω hΩ, fun _ _ => rfl,
      isCompact_closure_of_subsequences (restrictedFamily Ω 𝓕)
        (subsequences_of_finiteNormal Ω hΩ 𝓕 hn (fun _ _ => rfl))⟩
  · intro hc
    exact locallyBounded_of_finiteNormal Ω 𝓕 hΩ
      (finiteNormal_of_compactClosure Ω 𝓕 hΩ hhol hc)

theorem finiteNormal_iff_compactClosure :
    Specs.D12Complex.Ch11.Montel.finiteNormal_iff_compactClosure_type := by
  intro Ω 𝓕 hΩ hhol
  exact (locallyBounded_iff_finiteNormal Ω 𝓕 hΩ hhol).symm.trans
    (locallyBounded_iff_compactClosure Ω 𝓕 hΩ hhol)

end D12Complex.Ch11.Montel
