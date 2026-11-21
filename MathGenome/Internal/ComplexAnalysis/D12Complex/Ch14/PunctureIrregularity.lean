import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.PunctureIrregularity
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.BarrierSqueeze
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.HarmonicRemovable
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
open Set Metric Filter
open scoped Topology

namespace D12Complex.PunctureIrregularity

/-- The unit disk with its center removed. -/
def puncturedDisk : Set ℂ := ball 0 1 \ {0}

/-- Boundary data equal to one at the isolated puncture and zero on the circle. -/
def punctureDatum (z : ℂ) : ℝ := if z = 0 then 1 else 0

lemma disk_open : IsOpen puncturedDisk := isOpen_ball.sdiff isClosed_singleton
lemma disk_bounded : Bornology.IsBounded puncturedDisk :=
  isBounded_ball.subset sdiff_subset

lemma disk_closure : closure puncturedDisk = closedBall 0 1 := by
  apply Subset.antisymm
  · exact (closure_mono sdiff_subset).trans_eq (closure_ball (0 : ℂ) (by norm_num))
  · rw [← closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]
    apply closure_minimal
    · exact (dense_compl_singleton (0 : ℂ)).open_subset_closure_inter isOpen_ball
    · exact isClosed_closure

lemma disk_frontier : frontier puncturedDisk = {0} ∪ sphere 0 1 := by
  rw [disk_open.frontier_eq, disk_closure]
  ext z
  simp only [puncturedDisk, Set.mem_sdiff, mem_closedBall, mem_ball, mem_singleton_iff,
    mem_union, mem_sphere]
  constructor
  · rintro ⟨hz, hn⟩
    by_cases he : z = 0
    · exact Or.inl he
    · exact Or.inr (le_antisymm hz (le_of_not_gt (fun h => hn ⟨h, he⟩)))
  · rintro (rfl | hz)
    · simp
    · exact ⟨hz.le, fun h => (ne_of_lt h.1) hz⟩

lemma disk_domain : IsDomain puncturedDisk := by
  let e := Homeomorph.unitBall (E := ℂ)
  let f : ℂ → ℂ := fun z => (e z : ℂ)
  have hf : Continuous f := continuous_subtype_val.comp e.continuous
  have hf0 : f 0 = 0 := Homeomorph.coe_unitBall_apply_zero
  have him : f '' ({0}ᶜ : Set ℂ) = puncturedDisk := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨(e w).property, ?_⟩
      intro he
      have : e w = e 0 := Subtype.ext (he.trans hf0.symm)
      exact hw (e.injective this)
    · intro hz
      obtain ⟨w, hw⟩ := e.surjective ⟨z, hz.1⟩
      refine ⟨w, ?_, congrArg Subtype.val hw⟩
      intro he
      subst w
      exact hz.2 ((congrArg Subtype.val hw).symm.trans hf0)
  have hc := (isConnected_compl_singleton_of_one_lt_rank
    (by simp : 1 < Module.rank ℝ ℂ) (0 : ℂ)).image f hf.continuousOn
  rw [him] at hc
  exact ⟨hc.nonempty, disk_open, hc.isPreconnected⟩

theorem punctured_disk_geometry :
    IsDomain puncturedDisk ∧ Bornology.IsBounded puncturedDisk ∧
      closure puncturedDisk = closedBall 0 1 ∧
      frontier puncturedDisk = {0} ∪ sphere 0 1 :=
  ⟨disk_domain, disk_bounded, disk_closure, disk_frontier⟩

lemma datum_nonneg (z : ℂ) : 0 ≤ punctureDatum z := by
  unfold punctureDatum
  split_ifs <;> norm_num

lemma datum_le_one (z : ℂ) : punctureDatum z ≤ 1 := by
  unfold punctureDatum
  split_ifs <;> norm_num

lemma datum_sphere {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) : punctureDatum z = 0 := by
  have hn : z ≠ 0 := by intro he; simpa [he] using hz
  simp [punctureDatum, hn]

lemma datum_continuous : ContinuousOn punctureDatum (frontier puncturedDisk) := by
  rw [disk_frontier]
  intro ξ hξ
  rcases hξ with hξ | hξ
  · have he : ξ = 0 := hξ
    subst ξ
    apply Metric.continuousWithinAt_iff.mpr
    intro ε hε
    refine ⟨1, zero_lt_one, fun z hz hd => ?_⟩
    have hz0 : z = 0 := by
      rcases hz with hz | hz
      · exact hz
      · have hh : dist z 0 = 1 := hz
        linarith
    simp [hz0, hε]
  · have hn : ξ ≠ 0 := by intro he; simpa [he] using hξ
    have he : punctureDatum =ᶠ[𝓝 ξ] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hn] with z hz
      simp [punctureDatum, show z ≠ 0 from hz]
    exact ((continuousAt_const.congr he.symm).continuousWithinAt)

theorem puncture_datum_continuous :
    ContinuousOn punctureDatum (frontier puncturedDisk) ∧ punctureDatum 0 = 1 ∧
      ∀ z ∈ sphere (0 : ℂ) 1, punctureDatum z = 0 :=
  ⟨datum_continuous, by simp [punctureDatum], fun _ hz => datum_sphere hz⟩

/-- The logarithmic perturbation removes the isolated boundary constraint.
Every class member is bounded above by one before this argument is used. -/
lemma class_nonpositive {u : ℂ → ℝ}
    (hu : u ∈ perronClass puncturedDisk punctureDatum) :
    ∀ z ∈ puncturedDisk, u z ≤ 0 := by
  have hM : ∀ z ∈ puncturedDisk, u z ≤ 1 :=
    PerronEnvelope.class_upper_bound disk_bounded hu (fun ξ _ => datum_le_one ξ)
  have hpert (ε : ℝ) (hε : 0 < ε) :
      ∀ z ∈ puncturedDisk, u z + ε * Real.log ‖z‖ ≤ 0 := by
    let f : ℂ → ℝ := fun z => u z + ε * Real.log ‖z‖
    have hh : HarmonicOn puncturedDisk (fun z => -ε * Real.log ‖z‖) := by
      apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ disk_open).mpr
      intro z hz
      convert (HarmonicRemovable.harmonicAt_log_norm 0 z hz.2).const_smul (c := -ε) using 1
      ext w
      simp [smul_eq_mul]
    have hs : SubharmonicOn puncturedDisk f := by
      convert SubharmonicMaximum.subharmonic_sub_harmonic _ _ _ hu.1 hh using 1
      ext z
      dsimp [f]
      ring
    have hb : BoundaryLimsupLE puncturedDisk f 0 := by
      intro ξ hξ τ hτ
      rw [disk_frontier] at hξ
      rcases hξ with hξ | hξ
      · have he : ξ = 0 := hξ
        subst ξ
        have hl : ∀ᶠ z in 𝓝[puncturedDisk] (0 : ℂ),
            Real.log ‖z‖ ≤ -1 / ε := by
          have ht := (HarmonicRemovable.tendsto_log_norm (0 : ℂ)).eventually
            (eventually_le_atBot (-1 / ε))
          have hl' := (nhdsWithin_mono 0 (show puncturedDisk ⊆ {0}ᶜ from
            fun _ hz => hz.2)) ht
          filter_upwards [hl'] with z hz
          simpa only [sub_zero] using hz
        have hevent : ∀ᶠ z in 𝓝[puncturedDisk] (0 : ℂ), f z ≤ 0 + τ := by
          filter_upwards [hl, self_mem_nhdsWithin] with z hz hzu
          have hm := hM z hzu
          have heq : ε * (-1 / ε) = -1 := by field_simp
          have hmul := mul_le_mul_of_nonneg_left hz hε.le
          dsimp [f]
          linarith
        obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhdsWithin_iff.mp hevent
        exact ⟨δ, hδ, fun z hz ht => hd ⟨ht, hz⟩⟩
      · have hfξ : ξ ∈ frontier puncturedDisk := by rw [disk_frontier]; exact Or.inr hξ
        obtain ⟨δ, hδ, hd⟩ := hu.2 ξ hfξ τ hτ
        refine ⟨δ, hδ, fun z hz ht => ?_⟩
        have hb := hd z hz ht
        rw [datum_sphere hξ] at hb
        have hn : ‖z‖ < 1 := by simpa using hz.1
        have hl : Real.log ‖z‖ ≤ 0 := Real.log_nonpos (norm_nonneg z) hn.le
        have hm := mul_nonpos_of_nonneg_of_nonpos hε.le hl
        dsimp [f]
        linarith
    exact SubharmonicMaximum.subharmonic_boundary_maximum _ f 0 disk_bounded hs hb
  intro z hz
  have ht : Tendsto (fun ε : ℝ => u z + ε * Real.log ‖z‖)
      (𝓝[>] 0) (𝓝 (u z)) := by
    have hc : ContinuousAt (fun ε : ℝ => u z + ε * Real.log ‖z‖) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hpert ε hε z hz

lemma zero_mem_class : (fun _ => (0 : ℝ)) ∈ perronClass puncturedDisk punctureDatum :=
  PerronEnvelope.class_const disk_open (fun ξ _ => datum_nonneg ξ)

theorem puncture_perron_zero :
    ∀ z ∈ puncturedDisk, perronEnvelope puncturedDisk punctureDatum z = 0 := by
  intro z hz
  have hb : BddAbove ((fun u : ℂ → ℝ => u z) '' perronClass puncturedDisk punctureDatum) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨u, hu, rfl⟩
    exact class_nonpositive hu z hz
  apply le_antisymm
  · apply csSup_le (s := ((fun u : ℂ → ℝ => u z) ''
      perronClass puncturedDisk punctureDatum)) ⟨0, (fun _ => 0), zero_mem_class, rfl⟩
    rintro _ ⟨u, hu, rfl⟩
    exact class_nonpositive hu z hz
  · exact PerronEnvelope.le_envelope hb zero_mem_class

lemma zero_frontier : (0 : ℂ) ∈ frontier puncturedDisk := by
  rw [disk_frontier]
  exact Or.inl rfl

lemma zero_closure : (0 : ℂ) ∈ closure puncturedDisk :=
  frontier_subset_closure zero_frontier

lemma approach_neBot : NeBot (𝓝[puncturedDisk] (0 : ℂ)) :=
  mem_closure_iff_nhdsWithin_neBot.mp zero_closure

/-- A hypothetical continuous harmonic solution is itself a Perron minorant.
The preceding comparison already contradicts continuity at the puncture. -/
theorem no_dirichlet_solution :
    ¬ ∃ u : ℂ → ℝ, ContinuousOn u (closure puncturedDisk) ∧
      HarmonicOn puncturedDisk u ∧ EqOn u punctureDatum (frontier puncturedDisk) := by
  rintro ⟨u, hc, hh, heq⟩
  have hu : u ∈ perronClass puncturedDisk punctureDatum := by
    refine ⟨SubharmonicOperations.harmonicOn_subharmonicOn _ _ hh, ?_⟩
    intro ξ hξ ε hε
    obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.mp
      (hc ξ (frontier_subset_closure hξ)) ε hε
    refine ⟨δ, hδ, fun z hz ht => ?_⟩
    have hdist := hd (subset_closure hz) ht
    rw [Real.dist_eq] at hdist
    have := (abs_lt.mp hdist).2
    rw [heq hξ] at this
    linarith
  haveI := approach_neBot
  have ht : Tendsto u (𝓝[puncturedDisk] (0 : ℂ)) (𝓝 (u 0)) :=
    (hc 0 zero_closure).mono subset_closure
  have hle : u 0 ≤ 0 := le_of_tendsto ht (by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact class_nonpositive hu z hz)
  have hv : u 0 = 1 := by simpa [punctureDatum] using heq zero_frontier
  linarith

theorem puncture_boundary_failure :
    ¬ Tendsto (perronEnvelope puncturedDisk punctureDatum)
      (𝓝[puncturedDisk] 0) (𝓝 (punctureDatum 0)) := by
  intro ht
  haveI := approach_neBot
  have ht0 : Tendsto (perronEnvelope puncturedDisk punctureDatum)
      (𝓝[puncturedDisk] (0 : ℂ)) (𝓝 (0 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (puncture_perron_zero z hz).symm
  have := tendsto_nhds_unique ht ht0
  simpa [punctureDatum] using this

theorem puncture_no_barrier :
    (¬ ∃ r : ℝ, ∃ b : ℂ → ℝ, PositiveLocalBarrier puncturedDisk 0 r b) ∧
      ¬ RegularBoundaryPoint puncturedDisk 0 := by
  have hn : ¬ RegularBoundaryPoint puncturedDisk 0 := by
    intro hreg
    exact puncture_boundary_failure (BarrierSqueeze.barrier_squeeze _ _ _
      disk_domain disk_bounded datum_continuous hreg)
  exact ⟨fun ⟨r, b, hb⟩ => hn ⟨zero_frontier, r, b, hb⟩, hn⟩

end D12Complex.PunctureIrregularity
