import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.GreenRegularBoundary
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.CanonicalGreen
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.BarrierSqueeze

/-! We use the dual Perron construction. Every minorant for the boundary
values `-log ‖ξ-a‖` is at most `-log ‖z-a‖` off the pole, by the
subharmonic maximum principle on the punctured domain. Its envelope gives
a positive Green competitor. Leastness and the reverse Perron comparison
identify it with the canonical Green function. Thus barrier attainment is
applied to an actual Perron envelope, never assumed for an exhaustion limit. -/
noncomputable section
open Set Metric Filter InnerProductSpace
open scoped Topology

namespace D12Complex

def canonicalGreenZeroExtension : Set ℂ → ℂ → ℂ → ℝ :=
  Specs.D12Complex.Ch14.GreenRegularBoundary.canonicalGreenZeroExtension_value

end D12Complex

namespace D12Complex.GreenRegularBoundary

/-- The logarithmic singularity is an upper comparison for every member of
the dual Perron class, including near irregular boundary points. -/
lemma dual_class_le {Ω : Set ℂ} {a : ℂ} {u : ℂ → ℝ}
    (hΩ : IsDomain Ω) (hΩb : Bornology.IsBounded Ω) (ha : a ∈ Ω)
    (hu : u ∈ perronClass Ω (fun ξ => -Real.log ‖ξ - a‖)) :
    ∀ z ∈ Ω \ {a}, u z + Real.log ‖z - a‖ ≤ 0 := by
  have hU : IsOpen (Ω \ {a}) := hΩ.2.1.sdiff isClosed_singleton
  have hs := SubharmonicOperations.subharmonicOn_add (Ω \ {a}) u
    (fun z => Real.log ‖z - a‖)
    (HarmonicReplacementPasting.subharmonicOn_mono hu.1 hU (fun _ hz => hz.1))
    (SubharmonicOperations.harmonicOn_subharmonicOn _ _
      (RegularGreen.harmonic_log_distance Ω a hΩ.2.1))
  apply SubharmonicMaximum.subharmonic_boundary_maximum _ _ 0
    (hΩb.subset (fun _ hz => hz.1)) hs
  intro ξ hξ ε hε
  have hev : ∀ᶠ z in 𝓝[Ω \ {a}] ξ, u z + Real.log ‖z - a‖ ≤ 0 + ε := by
    rcases RegularGreen.frontier_punctured_subset hΩ.2.1 a hξ with hξF | hξa
    · have hξa : ξ ≠ a := by rintro rfl; exact (hΩ.2.1.frontier_eq ▸ hξF).2 ha
      obtain ⟨δ, hδ, hd⟩ := hu.2 ξ hξF (ε / 2) (half_pos hε)
      have hlog := (RegularGreen.continuousAt_log_distance (a := a) hξa).tendsto
      have hlog' := (hlog.eventually (gt_mem_nhds (show
        Real.log ‖ξ - a‖ < Real.log ‖ξ - a‖ + ε / 2 by linarith))).filter_mono
        (show 𝓝[Ω \ {a}] ξ ≤ 𝓝 ξ from nhdsWithin_le_nhds)
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds ξ hδ), hlog']
        with z hz hzδ hzlog
      have ht := hd z hz.1 hzδ
      linarith
    · have heqa : ξ = a := hξa
      subst ξ
      have hc := (hu.1.2.1 a ha).continuousAt (hΩ.2.1.mem_nhds ha)
      have h1 := (hc.tendsto.eventually (gt_mem_nhds (show u a < u a + 1 by linarith))).filter_mono (show 𝓝[Ω \ {a}] a ≤ 𝓝 a from nhdsWithin_le_nhds)
      have h2 := ((HarmonicRemovable.tendsto_log_norm a).eventually
        (eventually_le_atBot (ε - (u a + 1)))).filter_mono
        (nhdsWithin_mono a (show Ω \ {a} ⊆ {a}ᶜ from fun _ hz => hz.2))
      filter_upwards [h1, h2] with z hz1 hz2
      linarith
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhdsWithin_iff.mp hev
  exact ⟨δ, hδ, fun z hz hdist => hd ⟨hdist, hz⟩⟩

/-- A harmonic correction always produces the prescribed normalized pole. -/
lemma normalized_pole_of_correction {Ω : Set ℂ} {a : ℂ} {H : ℂ → ℝ}
    (hΩ : IsOpen Ω) (ha : a ∈ Ω) (hH : HarmonicOn Ω H) :
    HasNormalizedLogPole Ω a (fun z => H z - Real.log ‖z - a‖) := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ a ha
  exact ⟨r, hr, hsub, H, HarmonicRemovable.harmonicOn_mono hH isOpen_ball hsub,
    fun z _ => by ring⟩

lemma correction_pole_tendsto {Ω : Set ℂ} {a : ℂ} {H : ℂ → ℝ}
    (hΩ : IsOpen Ω) (ha : a ∈ Ω) (hH : HarmonicOn Ω H) :
    Tendsto (fun z => H z - Real.log ‖z - a‖) (𝓝[≠] a) atTop := by
  have hc := (hH.2.1.continuousOn a ha).continuousAt (hΩ.mem_nhds ha)
  apply Filter.tendsto_atTop.mpr
  intro M
  have h1 := (hc.tendsto.mono_left (show 𝓝[≠] a ≤ 𝓝 a from nhdsWithin_le_nhds)).eventually
    (lt_mem_nhds (show H a - 1 < H a by linarith))
  have h2 := (HarmonicRemovable.tendsto_log_norm a).eventually
    (eventually_le_atBot (H a - 1 - M))
  filter_upwards [h1, h2] with z hz1 hz2
  linarith

/-- The dual Perron envelope is an independently constructed positive Green
function; no boundary value of the canonical function enters this construction. -/
lemma dual_perron_positive {Ω : Set ℂ} {a : ℂ}
    (hΩ : IsDomain Ω) (hΩb : Bornology.IsBounded Ω) (ha : a ∈ Ω) :
    IsPositiveGreen Ω a (fun z =>
      -perronEnvelope Ω (fun ξ => -Real.log ‖ξ - a‖) z - Real.log ‖z - a‖) := by
  let P := perronEnvelope Ω (fun ξ => -Real.log ‖ξ - a‖)
  have hp := PerronEnvelope.perron_envelope Ω (fun ξ => -Real.log ‖ξ - a‖)
    hΩ hΩb (RegularGreen.log_boundary_continuous hΩ.2.1 ha).neg
  have hH : HarmonicOn Ω (fun z => -P z) :=
    (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hΩ.2.1).mpr
      (((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hΩ.2.1).mp hp.2.2.2).neg)
  have hhar := HarmonicRemovable.harmonicOn_sub
    (HarmonicRemovable.harmonicOn_mono hH (hΩ.2.1.sdiff isClosed_singleton)
      (fun _ hz => hz.1)) (RegularGreen.harmonic_log_distance Ω a hΩ.2.1)
  have hn : ∀ z ∈ Ω \ {a}, 0 ≤ -P z - Real.log ‖z - a‖ := by
    intro z hz
    have hle : P z ≤ -Real.log ‖z - a‖ := by
      apply csSup_le (hp.2.1 z hz.1).1
      rintro _ ⟨u, hu, rfl⟩
      linarith [dual_class_le hΩ hΩb ha hu z hz]
    linarith
  exact ⟨hhar, normalized_pole_of_correction hΩ.2.1 ha hH,
    RegularGreen.green_pos hΩ ha hhar hn (correction_pole_tendsto hΩ.2.1 ha hH)⟩

/-- Exact dual Perron formula on any bounded domain, whether regular or not. -/
lemma canonical_eq_dual_perron {Ω : Set ℂ} {a : ℂ}
    (hΩ : IsDomain Ω) (hΩb : Bornology.IsBounded Ω) (ha : a ∈ Ω) :
    EqOn (canonicalGreen Ω a) (fun z =>
      -perronEnvelope Ω (fun ξ => -Real.log ‖ξ - a‖) z - Real.log ‖z - a‖)
      (Ω \ {a}) := by
  have hc := CanonicalGreen.canonical_green Ω a hΩ hΩb ha
  change IsLeastPositiveGreen Ω a (canonicalGreen Ω a) at hc
  obtain ⟨H, hH, heq⟩ := CanonicalGreen.harmonic_correction hΩ.2.1 hc.1.1 hc.1.2.1
  have hclass : (fun z => -H z) ∈ perronClass Ω (fun ξ => -Real.log ‖ξ - a‖) := by
    refine ⟨SubharmonicOperations.harmonicOn_subharmonicOn _ _
      ((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hΩ.2.1).mpr
        (((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hΩ.2.1).mp hH).neg)), ?_⟩
    intro ξ hξ ε hε
    have hξa : ξ ≠ a := by rintro rfl; exact (hΩ.2.1.frontier_eq ▸ hξ).2 ha
    have ht := (RegularGreen.continuousAt_log_distance (a := a) hξa).neg.tendsto
    have hev : ∀ᶠ z in 𝓝[Ω] ξ, -H z ≤ -Real.log ‖ξ - a‖ + ε := by
      have ht' := (ht.eventually (gt_mem_nhds (show
        -Real.log ‖ξ - a‖ < -Real.log ‖ξ - a‖ + ε by linarith))).filter_mono (show 𝓝[Ω] ξ ≤ 𝓝 ξ from nhdsWithin_le_nhds)
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (isOpen_ne.mem_nhds hξa), ht'] with z hz hza hzlog
      have hh := heq ⟨hz, hza⟩
      have hpos := hc.1.2.2 z ⟨hz, hza⟩
      dsimp only at hh
      change -Real.log ‖z - a‖ < -Real.log ‖ξ - a‖ + ε at hzlog
      linarith
    obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhdsWithin_iff.mp hev
    exact ⟨δ, hδ, fun z hz hdist => hd ⟨hdist, hz⟩⟩
  have hp := PerronEnvelope.perron_envelope Ω (fun ξ => -Real.log ‖ξ - a‖)
    hΩ hΩb (RegularGreen.log_boundary_continuous hΩ.2.1 ha).neg
  intro z hz
  have hupper := hc.2 _ (dual_perron_positive hΩ hΩb ha) z hz
  have hlower := PerronEnvelope.le_envelope (hp.2.1 z hz.1).2 hclass
  have hh := heq hz
  dsimp only at hh
  exact le_antisymm hupper (by linarith)

theorem regular_point_limit :
    Specs.D12Complex.Ch14.GreenRegularBoundary.regular_point_limit_type := by
  intro Ω a ξ hΩ hΩb ha hreg
  change Tendsto (canonicalGreen Ω a) (𝓝[Ω] ξ) (𝓝 0)
  have hξa : ξ ≠ a := by rintro rfl; exact (hΩ.2.1.frontier_eq ▸ hreg.1).2 ha
  have ht := (BarrierSqueeze.barrier_squeeze Ω (fun η => -Real.log ‖η - a‖) ξ
    hΩ hΩb (RegularGreen.log_boundary_continuous hΩ.2.1 ha).neg hreg).neg.sub
    ((RegularGreen.continuousAt_log_distance (a := a) hξa).tendsto.mono_left
      (show 𝓝[Ω] ξ ≤ 𝓝 ξ from nhdsWithin_le_nhds))
  have he : (fun z => -perronEnvelope Ω (fun η => -Real.log ‖η - a‖) z -
      Real.log ‖z - a‖) =ᶠ[𝓝[Ω] ξ] canonicalGreen Ω a := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_ne.mem_nhds hξa)] with z hz hza
    exact (canonical_eq_dual_perron hΩ hΩb ha ⟨hz, hza⟩).symm
  simpa only [neg_neg, sub_self] using ht.congr' he

theorem regular_domain_identification :
    Specs.D12Complex.Ch14.GreenRegularBoundary.regular_domain_identification_type := by
  intro Ω a hΩ hΩb ha hreg z hz
  change canonicalGreen Ω a z = regularGreen Ω a z
  have hlog := RegularGreen.log_boundary_continuous hΩ.2.1 ha
  have hn := RegularDirichlet.perronEnvelope_linear Ω
    (fun ξ => Real.log ‖ξ - a‖) (fun ξ => Real.log ‖ξ - a‖) (-1) 0
    hΩ hΩb hreg hlog hlog hz.1
  have hn' : perronEnvelope Ω (fun ξ => -Real.log ‖ξ - a‖) z =
      -perronEnvelope Ω (fun ξ => Real.log ‖ξ - a‖) z := by
    simpa only [neg_one_mul, zero_mul, add_zero] using hn
  have he := canonical_eq_dual_perron hΩ hΩb ha hz
  dsimp only at he
  rw [hn', neg_neg] at he
  simpa only [regularGreen, RegularDirichlet.perronSolution_eq_envelope hz.1] using he

theorem zero_extension :
    Specs.D12Complex.Ch14.GreenRegularBoundary.zero_extension_type := by
  intro Ω a hΩ hΩb ha hreg
  have hg := (RegularGreen.regular_green Ω a hΩ hΩb hreg ha).1
  change IsZeroBoundaryGreen Ω a (regularGreen Ω a) at hg
  have he : EqOn (canonicalGreenZeroExtension Ω a) (regularGreen Ω a)
      (closure Ω \ {a}) := by
    intro z hz
    by_cases hzΩ : z ∈ Ω
    · simpa only [canonicalGreenZeroExtension,
        Specs.D12Complex.Ch14.GreenRegularBoundary.canonicalGreenZeroExtension_value,
        ite_eq_left hzΩ, canonicalGreen, regularGreen, perronSolution,
        Specs.D12Complex.Ch14.RegularGreen.regularGreen_value,
        Specs.D12Complex.Ch14.RegularDirichlet.perronSolution_value] using
        regular_domain_identification Ω a hΩ hΩb ha hreg ⟨hzΩ, hz.2⟩
    · have hzF : z ∈ frontier Ω := by rw [hΩ.2.1.frontier_eq]; exact ⟨hz.1, hzΩ⟩
      simpa only [canonicalGreenZeroExtension,
        Specs.D12Complex.Ch14.GreenRegularBoundary.canonicalGreenZeroExtension_value,
        ite_eq_right hzΩ] using (hg.2.2.2 hzF).symm
  have hnew : IsZeroBoundaryGreen Ω a (canonicalGreenZeroExtension Ω a) := by
    refine ⟨HarmonicReplacementPasting.harmonicOn_congr hg.1
      (fun z hz => (he ⟨subset_closure hz.1, hz.2⟩).symm), ?_,
      hg.2.2.1.congr he, ?_⟩
    · obtain ⟨r, hr, hsub, H, hH, hEq⟩ := hg.2.1
      refine ⟨r, hr, hsub, H, hH, fun z hz => ?_⟩
      change H z = canonicalGreenZeroExtension Ω a z + Real.log ‖z - a‖
      rw [he ⟨subset_closure (hsub hz.1), hz.2⟩]
      exact hEq hz
    · intro ξ hξ
      rw [he ⟨frontier_subset_closure hξ, ?_⟩]
      · exact hg.2.2.2 hξ
      · rintro rfl
        exact (hΩ.2.1.frontier_eq ▸ hξ).2 ha
  exact ⟨hnew, he, fun g hg' z hz =>
    (RegularGreen.regular_green_unique Ω a hΩ hΩb hreg ha g hg' hz).trans (he hz).symm⟩

end D12Complex.GreenRegularBoundary
