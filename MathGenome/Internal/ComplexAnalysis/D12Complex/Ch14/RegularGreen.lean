import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.RegularGreen
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.RegularDirichlet
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.HarmonicRemovable

noncomputable section
open Set Metric Filter InnerProductSpace
open scoped Topology

namespace D12Complex

/-- The regular Dirichlet correction of the logarithmic fundamental solution. -/
def regularGreen (Ω : Set ℂ) (a z : ℂ) : ℝ :=
  perronSolution Ω (fun ξ => Real.log ‖ξ - a‖) z - Real.log ‖z - a‖

end D12Complex

namespace D12Complex.RegularGreen

/-- Exports of the canonical predicates shared with independent downstream Specs. -/
abbrev HasNormalizedLogPole : Specs.D12Complex.Ch14.RegularGreen.HasNormalizedLogPole_type :=
  _root_.D12Complex.HasNormalizedLogPole

abbrev IsZeroBoundaryGreen : Specs.D12Complex.Ch14.RegularGreen.IsZeroBoundaryGreen_type :=
  _root_.D12Complex.IsZeroBoundaryGreen

lemma continuousAt_log_distance {a z : ℂ} (hz : z ≠ a) :
    ContinuousAt (fun w => Real.log ‖w - a‖) z :=
  (continuous_id.sub continuous_const).norm.continuousAt.log
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz))

lemma log_boundary_continuous {Ω : Set ℂ} {a : ℂ} (hΩ : IsOpen Ω) (ha : a ∈ Ω) :
    ContinuousOn (fun ξ => Real.log ‖ξ - a‖) (frontier Ω) := by
  intro ξ hξ
  apply (continuousAt_log_distance (a := a) ?_).continuousWithinAt
  rintro rfl
  exact (hΩ.frontier_eq ▸ hξ).2 ha

lemma correction_solution {Ω : Set ℂ} {a : ℂ} (hΩ : IsDomain Ω)
    (hΩb : Bornology.IsBounded Ω) (hreg : ∀ ξ ∈ frontier Ω, RegularBoundaryPoint Ω ξ)
    (ha : a ∈ Ω) :
    IsDirichletSolution Ω (fun ξ => Real.log ‖ξ - a‖)
      (perronSolution Ω (fun ξ => Real.log ‖ξ - a‖)) :=
  RegularDirichlet.perronSolution_isSolution hΩ hΩb hreg
    (log_boundary_continuous hΩ.2.1 ha)

lemma harmonic_log_distance (Ω : Set ℂ) (a : ℂ) (hΩ : IsOpen Ω) :
    HarmonicOn (Ω \ {a}) (fun z => Real.log ‖z - a‖) := by
  apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _
    (hΩ.sdiff isClosed_singleton)).mpr
  intro z hz
  exact HarmonicRemovable.harmonicAt_log_norm a z hz.2

lemma construction_properties {Ω : Set ℂ} {a : ℂ} (hΩ : IsDomain Ω)
    (hΩb : Bornology.IsBounded Ω) (hreg : ∀ ξ ∈ frontier Ω, RegularBoundaryPoint Ω ξ)
    (ha : a ∈ Ω) : IsZeroBoundaryGreen Ω a (regularGreen Ω a) := by
  have hs := correction_solution hΩ hΩb hreg ha
  have hh := HarmonicRemovable.harmonicOn_mono (V := Ω \ {a}) hs.1
    (hΩ.2.1.sdiff isClosed_singleton) (fun _ hz => hz.1)
  refine ⟨HarmonicRemovable.harmonicOn_sub hh
    (harmonic_log_distance Ω a hΩ.2.1), ?_, ?_, ?_⟩
  · obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hΩ.2.1 a ha
    refine ⟨r, hr, hsub, perronSolution Ω (fun ξ => Real.log ‖ξ - a‖),
      HarmonicRemovable.harmonicOn_mono hs.1 isOpen_ball hsub, ?_⟩
    intro z _
    simp [regularGreen]
  · exact (hs.2.1.mono (fun _ hz => hz.1)).sub
      (fun z hz => (continuousAt_log_distance hz.2).continuousWithinAt)
  · intro ξ hξ
    simp only [regularGreen, hs.2.2 hξ, sub_self]

/-- The harmonic correction is finite at the pole, whereas log distance
 tends to minus infinity. -/
lemma tendsto_green_pole {Ω : Set ℂ} {a : ℂ} (hΩ : IsDomain Ω)
    (hΩb : Bornology.IsBounded Ω) (hreg : ∀ ξ ∈ frontier Ω, RegularBoundaryPoint Ω ξ)
    (ha : a ∈ Ω) : Tendsto (regularGreen Ω a) (𝓝[≠] a) atTop := by
  have hs := correction_solution hΩ hΩb hreg ha
  have hc := (hs.1.2.1.continuousOn a ha).continuousAt (hΩ.2.1.mem_nhds ha)
  apply Filter.tendsto_atTop.mpr
  intro M
  have h1 := (hc.tendsto.mono_left (show 𝓝[≠] a ≤ 𝓝 a from nhdsWithin_le_nhds)).eventually
    (lt_mem_nhds (show perronSolution Ω (fun ξ => Real.log ‖ξ - a‖) a - 1 <
      perronSolution Ω (fun ξ => Real.log ‖ξ - a‖) a by linarith))
  have h2 := (HarmonicRemovable.tendsto_log_norm a).eventually
    (eventually_le_atBot (perronSolution Ω (fun ξ => Real.log ‖ξ - a‖) a - 1 - M))
  filter_upwards [h1, h2] with z hz1 hz2
  dsimp [regularGreen]
  linarith


lemma frontier_punctured_subset {Ω : Set ℂ} (hΩ : IsOpen Ω) (a : ℂ) :
    frontier (Ω \ {a}) ⊆ frontier Ω ∪ {a} := by
  intro ξ hξ
  by_cases hξa : ξ = a
  · exact Or.inr hξa
  · left
    rw [hΩ.frontier_eq]
    refine ⟨closure_mono (fun z hz => hz.1) (frontier_subset_closure hξ), ?_⟩
    intro hξΩ
    exact ((hΩ.sdiff isClosed_singleton).frontier_eq ▸ hξ).2 ⟨hξΩ, hξa⟩

lemma boundary_tendsto {Ω : Set ℂ} {a : ℂ} {g : ℂ → ℝ} (hΩ : IsOpen Ω)
    (ha : a ∈ Ω) (hg : IsZeroBoundaryGreen Ω a g) {ξ : ℂ} (hξ : ξ ∈ frontier Ω) :
    Tendsto g (𝓝[Ω] ξ) (𝓝 0) := by
  have hξa : ξ ≠ a := by rintro rfl; exact (hΩ.frontier_eq ▸ hξ).2 ha
  have hc : ContinuousWithinAt g (closure Ω) ξ :=
    continuousWithinAt_sdiff_singleton.mp (hg.2.2.1 ξ ⟨frontier_subset_closure hξ, hξa⟩)
  simpa only [hg.2.2.2 hξ] using (hc.mono subset_closure).tendsto

lemma green_nonneg {Ω : Set ℂ} {a : ℂ} {g : ℂ → ℝ} (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (ha : a ∈ Ω) (hg : IsZeroBoundaryGreen Ω a g)
    (hp : Tendsto g (𝓝[≠] a) atTop) : ∀ z ∈ Ω \ {a}, 0 ≤ g z := by
  apply BoundaryMaximum.harmonic_boundary_minimum _ _ 0
    (hΩb.subset (fun _ hz => hz.1)) hg.1
  intro ξ hξ ε hε
  have hev : ∀ᶠ z in 𝓝[Ω \ {a}] ξ, -ε ≤ g z := by
    rcases frontier_punctured_subset hΩ a hξ with hξ | hξa
    · have ht := (boundary_tendsto hΩ ha hg hξ).mono_left
        (nhdsWithin_mono _ (show Ω \ {a} ⊆ Ω from fun _ hz => hz.1))
      exact (ht.eventually (lt_mem_nhds (show -ε < (0 : ℝ) by linarith))).mono
        (fun _ hz => hz.le)
    · have heqa : ξ = a := hξa
      subst ξ
      exact (hp.eventually (eventually_ge_atTop (-ε))).filter_mono
        (nhdsWithin_mono a (show Ω \ {a} ⊆ {a}ᶜ from fun _ hz => hz.2))
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhdsWithin_iff.mp hev
  exact ⟨δ, hδ, fun z hz hdist => by simpa using hd ⟨hdist, hz⟩⟩

/-- Strong positivity uses connectedness of the original domain. The zero
set cannot accumulate at the pole, and is both open and relatively closed.
This avoids imposing any extra topological hypothesis on a punctured domain. -/
lemma green_pos {Ω : Set ℂ} {a : ℂ} {g : ℂ → ℝ} (hΩ : IsDomain Ω)
    (ha : a ∈ Ω) (hh : HarmonicOn (Ω \ {a}) g)
    (hn : ∀ z ∈ Ω \ {a}, 0 ≤ g z) (hp : Tendsto g (𝓝[≠] a) atTop) :
    ∀ z ∈ Ω \ {a}, 0 < g z := by
  let V : Set ℂ := {z | z ∈ Ω \ {a} ∧ g z = 0}
  let W : Set ℂ := Ω \ V
  have hVo : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have hm := MeanValueStrongPrinciple.harmonic_local_circle_mean _ _ hh
    obtain ⟨ρ, hρ, hsub, heq⟩ := MeanValueStrongPrinciple.maximum_locally_constant
      hh.2.1.continuousOn.neg (BoundaryMaximum.localCircleMeanProperty_neg hm) hz.1
      (fun w hw => by dsimp; rw [hz.2]; simpa using hn w hw)
    apply Filter.mem_of_superset (ball_mem_nhds z hρ)
    intro w hw
    refine ⟨hsub hw, ?_⟩
    have he := heq w hw
    change -g w = -g z at he
    rw [hz.2] at he
    linarith
  have hWo : IsOpen W := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    by_cases hza : z = a
    · subst z
      have hev := eventually_nhdsWithin_iff.mp (hp.eventually (eventually_gt_atTop 0))
      filter_upwards [hΩ.2.1.mem_nhds ha, hev] with w hw hpos
      refine ⟨hw, ?_⟩
      intro hwV
      have := hpos hwV.1.2
      rw [hwV.2] at this
      exact lt_irrefl _ this
    · have hzu : z ∈ Ω \ {a} := ⟨hz.1, hza⟩
      have hgz : g z ≠ 0 := fun he => hz.2 ⟨hzu, he⟩
      have hc := (hh.2.1.continuousOn z hzu).continuousAt (hh.1.mem_nhds hzu)
      have hev := hc.tendsto.eventually (isOpen_ne.mem_nhds hgz)
      filter_upwards [hΩ.2.1.mem_nhds hz.1, hev] with w hw hgw
      exact ⟨hw, fun hwV => hgw hwV.2⟩
  intro z hz
  apply lt_of_le_of_ne (hn z hz)
  intro he
  have hzV : z ∈ V := ⟨hz, he.symm⟩
  have hsub := hΩ.2.2.subset_left_of_subset_union hVo hWo
    (disjoint_left.mpr (fun _ hv hw => hw.2 hv))
    (show Ω ⊆ V ∪ W from fun w hw => by
      by_cases hwV : w ∈ V
      · exact Or.inl hwV
      · exact Or.inr ⟨hw, hwV⟩)
    (show (Ω ∩ V).Nonempty from ⟨z, hz.1, hzV⟩)
  exact (hsub ha).1.2 rfl

/-- A local normalized pole patches to a global harmonic correction. Closure
continuity is proved separately at the interior pole and at other points. -/
lemma correction_of_green {Ω : Set ℂ} {a : ℂ} {g : ℂ → ℝ} (hΩ : IsOpen Ω)
    (ha : a ∈ Ω) (hg : IsZeroBoundaryGreen Ω a g) :
    ∃ H : ℂ → ℝ, IsDirichletSolution Ω (fun ξ => Real.log ‖ξ - a‖) H ∧
      EqOn H (fun z => g z + Real.log ‖z - a‖) (closure Ω \ {a}) := by
  classical
  obtain ⟨r, hr, hsub, h, hh, heq⟩ := hg.2.1
  let H : ℂ → ℝ := fun z => if z = a then h a else g z + Real.log ‖z - a‖
  have Heq {z : ℂ} (hz : z ≠ a) : H z = g z + Real.log ‖z - a‖ := by simp [H, hz]
  have hsum : HarmonicOn (Ω \ {a}) (fun z => g z + Real.log ‖z - a‖) := by
    apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hg.1.1).mpr
    exact ((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hg.1.1).mp hg.1).add
      ((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hg.1.1).mp
        (harmonic_log_distance Ω a hΩ))
  have hH : HarmonicOn Ω H := by
    apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hΩ).mpr
    intro z hz
    by_cases hza : z = a
    · subst z
      apply (harmonicAt_congr_nhds (f₁ := h) (f₂ := H) ?_).mp
        (((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ isOpen_ball).mp hh)
          a (mem_ball_self hr))
      filter_upwards [ball_mem_nhds a hr] with w hw
      by_cases hwa : w = a
      · simp [H, hwa]
      · exact (heq ⟨hw, hwa⟩).trans (Heq hwa).symm
    · apply (harmonicAt_congr_nhds (f₁ := fun w => g w + Real.log ‖w - a‖)
        (f₂ := H) ?_).mp
        (((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hg.1.1).mp hsum)
          z ⟨hz, hza⟩)
      filter_upwards [isOpen_ne.mem_nhds hza] with w hw
      exact (Heq hw).symm
  have hHc : ContinuousOn H (closure Ω) := by
    intro z hz
    by_cases hza : z = a
    · subst z
      exact ((hH.2.1.continuousOn a ha).continuousAt (hΩ.mem_nhds ha)).continuousWithinAt
    · have hc : ContinuousWithinAt g (closure Ω) z :=
        continuousWithinAt_sdiff_singleton.mp (hg.2.2.1 z ⟨hz, hza⟩)
      apply (hc.add (continuousAt_log_distance hza).continuousWithinAt).congr_of_eventuallyEq
        ?_ (Heq hza)
      filter_upwards [nhdsWithin_le_nhds (isOpen_ne.mem_nhds hza)] with w hw
      exact Heq hw
  refine ⟨H, ⟨hH, hHc, ?_⟩, fun z hz => Heq hz.2⟩
  intro ξ hξ
  have hξa : ξ ≠ a := by rintro rfl; exact (hΩ.frontier_eq ▸ hξ).2 ha
  rw [Heq hξa, hg.2.2.2 hξ, zero_add]

theorem regular_green : Specs.D12Complex.Ch14.RegularGreen.regular_green_type := by
  intro Ω a hΩ hΩb hreg ha
  have hg := construction_properties hΩ hΩb hreg ha
  have hp := tendsto_green_pole hΩ hΩb hreg ha
  exact ⟨hg, green_pos hΩ ha hg.1 (green_nonneg hΩ.2.1 hΩb ha hg hp) hp,
    fun ξ hξ => boundary_tendsto hΩ.2.1 ha hg hξ⟩

theorem regular_green_unique :
    Specs.D12Complex.Ch14.RegularGreen.regular_green_unique_type := by
  intro Ω a hΩ hΩb hreg ha g hg
  obtain ⟨H, hH, heq⟩ := correction_of_green hΩ.2.1 ha hg
  have he := RegularDirichlet.solution_unique hΩb hH (correction_solution hΩ hΩb hreg ha)
  intro z hz
  have hh := he (show z ∈ closure Ω from hz.1)
  rw [heq hz] at hh
  change g z = perronSolution Ω (fun ξ => Real.log ‖ξ - a‖) z - Real.log ‖z - a‖
  linarith

end D12Complex.RegularGreen
