import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.HarmonicRemovable
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.DiskDirichlet
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.BoundaryMaximum
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

noncomputable section
open Set Metric Complex Filter InnerProductSpace
open scoped Topology

namespace D12Complex.HarmonicRemovable

lemma isOpen_puncturedBall (a : ℂ) (R : ℝ) : IsOpen (ball a R \ {a}) :=
  isOpen_ball.sdiff isClosed_singleton

lemma harmonicAt_log_norm (a z : ℂ) (hz : z ≠ a) :
    HarmonicAt (fun w => Real.log ‖w - a‖) z := by
  exact (analyticAt_id.sub analyticAt_const).harmonicAt_log_norm (sub_ne_zero.mpr hz)

theorem log_norm_harmonic :
    Specs.D12Complex.Ch13.HarmonicRemovable.log_norm_harmonic_type := by
  intro a R _
  apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _
    (isOpen_puncturedBall a R)).mpr
  intro z hz
  exact harmonicAt_log_norm a z hz.2

lemma tendsto_log_norm (a : ℂ) :
    Tendsto (fun z => Real.log ‖z - a‖) (𝓝[≠] a) atBot := by
  exact Real.tendsto_log_nhdsGT_zero.comp (tendsto_norm_sub_self_nhdsNE a)

theorem log_norm_no_continuous_extension :
    Specs.D12Complex.Ch13.HarmonicRemovable.log_norm_no_continuous_extension_type := by
  intro a R hR
  rintro ⟨v, hv, heq⟩
  have hevent : v =ᶠ[𝓝[≠] a] (fun z => Real.log ‖z - a‖) := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds a hR), self_mem_nhdsWithin]
      with z hz hza
    exact heq ⟨hz, hza⟩
  exact not_tendsto_nhds_of_tendsto_atBot (tendsto_log_norm a) (v a)
    ((hv.tendsto.mono_left nhdsWithin_le_nhds).congr' hevent)

theorem log_norm_no_harmonic_extension :
    Specs.D12Complex.Ch13.HarmonicRemovable.log_norm_no_harmonic_extension_type := by
  intro a R hR
  rintro ⟨v, hv, heq⟩
  exact log_norm_no_continuous_extension a R hR
    ⟨v, (hv.2.1.continuousOn a (mem_ball_self hR)).continuousAt
      (isOpen_ball.mem_nhds (mem_ball_self hR)), heq⟩

lemma extension_unique {a : ℂ} {R : ℝ} {u v w : ℂ → ℝ} (hR : 0 < R)
    (hv : HarmonicOn (ball a R) v) (hw : HarmonicOn (ball a R) w)
    (hev : EqOn v u (ball a R \ {a})) (hew : EqOn w u (ball a R \ {a})) :
    EqOn w v (ball a R) := by
  intro z hz
  by_cases hza : z = a
  · subst z
    have he : w =ᶠ[𝓝[≠] a] v := by
      filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds a hR), self_mem_nhdsWithin]
        with z hz hza
      exact (hew ⟨hz, hza⟩).trans (hev ⟨hz, hza⟩).symm
    have hc (f : ℂ → ℝ) (hf : HarmonicOn (ball a R) f) : ContinuousAt f a :=
      (hf.2.1.continuousOn a (mem_ball_self hR)).continuousAt
        (ball_mem_nhds a hR)
    exact tendsto_nhds_unique ((hc w hw).tendsto.mono_left nhdsWithin_le_nhds)
      (((hc v hv).tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm)
  · exact (hew ⟨hz, hza⟩).trans (hev ⟨hz, hza⟩).symm

/-- The only possible boundary points are the center and the outer circle. -/
lemma frontier_puncturedBall_subset (a : ℂ) (r : ℝ) :
    frontier (ball a r \ {a}) ⊆ {a} ∪ sphere a r := by
  intro ξ hξ
  by_cases hξa : ξ = a
  · exact Or.inl hξa
  · right
    have hcl : ξ ∈ closedBall a r :=
      (closure_minimal (fun z hz => mem_closedBall.mpr (mem_ball.mp hz.1).le)
        isClosed_closedBall) (frontier_subset_closure hξ)
    have hn : ξ ∉ ball a r \ {a} := by
      rw [(isOpen_puncturedBall a r).frontier_eq] at hξ
      exact hξ.2
    have hnr : ¬ dist ξ a < r := fun h => hn ⟨h, hξa⟩
    exact mem_sphere.mpr (le_antisymm hcl (le_of_not_gt hnr))

/-- A bounded-above harmonic function with nonpositive outer-circle values
is nonpositive even when no value is prescribed at the puncture. -/
lemma bounded_punctured_boundary_maximum {a : ℂ} {r : ℝ} {w : ℂ → ℝ}
    (hh : HarmonicOn (ball a r \ {a}) w)
    (hc : ContinuousOn w (closedBall a r \ {a}))
    (hb : ∀ ξ ∈ sphere a r, w ξ ≤ 0)
    (M : ℝ) (hM : ∀ z ∈ ball a r \ {a}, w z ≤ M) :
    ∀ z ∈ ball a r \ {a}, w z ≤ 0 := by
  have hpert (ε : ℝ) (hε : 0 < ε) :
      ∀ z ∈ ball a r \ {a}, w z + ε * (Real.log ‖z - a‖ - Real.log r) ≤ 0 := by
    let f : ℂ → ℝ := fun z => w z + ε * (Real.log ‖z - a‖ - Real.log r)
    have hf : HarmonicOn (ball a r \ {a}) f := by
      apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hh.1).mpr
      have hw := (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hh.1).mp hh
      intro z hz
      exact (hw z hz).add (((harmonicAt_log_norm a z hz.2).sub
        (harmonicAt_const (Real.log r))).const_smul (c := ε))
    have hbf : BoundaryLimsupLE (ball a r \ {a}) f 0 := by
      intro ξ hξ τ hτ
      have hevent : ∀ᶠ z in 𝓝[ball a r \ {a}] ξ, f z ≤ τ := by
        rcases frontier_puncturedBall_subset a r hξ with hξa | hξr
        · have heqa : ξ = a := hξa
          subst ξ
          have hl := (tendsto_log_norm a).eventually
            (eventually_le_atBot (Real.log r - M / ε))
          have hl' := (nhdsWithin_mono a (show ball a r \ {a} ⊆ {a}ᶜ from
            fun _ hz => hz.2)) hl
          filter_upwards [hl', self_mem_nhdsWithin] with z hz hzu
          have hm := hM z hzu
          have hmε : ε * (M / ε) = M := by field_simp
          dsimp [f]
          nlinarith
        · have hξne : ξ ≠ a := by
            intro he
            subst ξ
            have hr : r = 0 := by simpa using hξr.symm
            have hnone : ball a r \ {a} = ∅ := by simp [hr]
            simp [hnone] at hξ
          have hlog : ContinuousAt (fun z : ℂ => Real.log ‖z - a‖) ξ :=
            ((continuous_id.sub continuous_const).norm.continuousAt).log
              (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hξne))
          have hfw : ContinuousWithinAt f (ball a r \ {a}) ξ :=
            ((hc ξ ⟨sphere_subset_closedBall hξr, hξne⟩).mono
              (fun _ hz => ⟨ball_subset_closedBall hz.1, hz.2⟩)).add
              ((continuousWithinAt_const.mul
                (hlog.continuousWithinAt.sub continuousWithinAt_const)))
          have hfξ : f ξ = w ξ := by
            have hnorm : ‖ξ - a‖ = r := by simpa [dist_eq_norm] using hξr
            simp [f, hnorm]
          have hl := hfw.tendsto.eventually (gt_mem_nhds
            (show f ξ < τ from by rw [hfξ]; linarith [hb ξ hξr]))
          exact hl.mono (fun _ hz => hz.le)
      obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hevent
      exact ⟨δ, hδ, fun z hz hd => by simpa using hsub ⟨hd, hz⟩⟩
    exact BoundaryMaximum.harmonic_boundary_maximum _ f 0
      (isBounded_ball.subset (fun _ hz => hz.1)) hf hbf
  intro z hz
  have hlim : Tendsto (fun ε : ℝ => w z + ε * (Real.log ‖z - a‖ - Real.log r))
      (𝓝[>] 0) (𝓝 (w z)) := by
    have h : ContinuousAt (fun ε : ℝ => w z + ε *
        (Real.log ‖z - a‖ - Real.log r)) 0 := by fun_prop
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hpert ε hε z hz

lemma harmonicOn_mono {U V : Set ℂ} {u : ℂ → ℝ} (hu : HarmonicOn U u)
    (hV : IsOpen V) (hVU : V ⊆ U) : HarmonicOn V u :=
  (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hV).mpr
    (((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hu.1).mp hu).mono hVU)

lemma harmonicOn_sub {U : Set ℂ} {u v : ℂ → ℝ} (hu : HarmonicOn U u)
    (hv : HarmonicOn U v) : HarmonicOn U (fun z => u z - v z) :=
  (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hu.1).mpr
    (((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hu.1).mp hu).sub
      ((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hv.1).mp hv))

lemma harmonicOn_congr {U : Set ℂ} {u v : ℂ → ℝ} (hu : HarmonicOn U u)
    (heq : EqOn u v U) : HarmonicOn U v := by
  apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hu.1).mpr
  have hh := (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hu.1).mp hu
  intro z hz
  refine (harmonicAt_congr_nhds (f₁ := u) (f₂ := v) ?_).mp (hh z hz)
  filter_upwards [hu.1.mem_nhds hz] with w hw
  exact heq hw

/-- Solve on an interior circle, so no boundary data at the original disk's
outer radius are assumed. Translation uses the proved holomorphic composition law. -/
lemma inner_disk_solution {a : ℂ} {R r : ℝ} {u : ℂ → ℝ}
    (hu : HarmonicOn (ball a R \ {a}) u) (hr : 0 < r) (hrR : r < R) :
    ∃ v : ℂ → ℝ, ContinuousOn v (closedBall a r) ∧
      HarmonicOn (ball a r) v ∧ EqOn v u (sphere a r) := by
  let φ : ℂ → ℝ := fun z => u (a + z)
  have hφ : ContinuousOn φ (sphere 0 r) := by
    apply hu.2.1.continuousOn.comp (continuous_const.add continuous_id).continuousOn
    intro z hz
    have hn : ‖z‖ = r := by simpa using hz
    constructor
    · simpa [dist_eq_norm, hn] using hrR
    · have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; exact hr.ne')
      simpa using hz0
  let p : ℂ → ℝ := DiskDirichlet.closedPoissonIntegral r φ
  have hp := DiskDirichlet.closedPoissonIntegral_solution r φ hr hφ
  change ContinuousOn p (closedBall 0 r) ∧ HarmonicOn (ball 0 r) p ∧
    EqOn p φ (sphere 0 r) ∧ _ at hp
  let v : ℂ → ℝ := fun z => p (z - a)
  have hmap : MapsTo (fun z : ℂ => z - a) (closedBall a r) (closedBall 0 r) := by
    intro z hz
    simpa [dist_eq_norm] using hz
  have hc : ContinuousOn v (closedBall a r) :=
    hp.1.comp (continuous_id.sub continuous_const).continuousOn hmap
  have hv : HarmonicOn (ball a r) v := by
    apply HarmonicFoundation.harmonicOn_comp_holomorphic (ball 0 r) (ball a r)
      p (fun z => z - a) hp.2.1
      ⟨isOpen_ball, fun z _ => differentiableAt_id.sub_const a⟩
    intro z hz
    simpa [dist_eq_norm] using hz
  refine ⟨v, hc, hv, fun z hz => ?_⟩
  have hs : z - a ∈ sphere (0 : ℂ) r := by simpa [dist_eq_norm] using hz
  simpa [v, φ] using hp.2.2.1 hs

/-- A bounded punctured function agrees with the interior-circle solution. -/
lemma bounded_inner_extension {a : ℂ} {R r : ℝ} {u : ℂ → ℝ}
    (hu : HarmonicOn (ball a R \ {a}) u) (hr : 0 < r) (hrR : r < R)
    (M : ℝ) (hM : ∀ z ∈ ball a R \ {a}, |u z| ≤ M) :
    ∃ v : ℂ → ℝ, HarmonicOn (ball a r) v ∧ EqOn v u (ball a r \ {a}) := by
  obtain ⟨v, hc, hv, heq⟩ := inner_disk_solution hu hr hrR
  obtain ⟨N, hN⟩ := (isCompact_closedBall a r).exists_bound_of_continuousOn hc
  have hsub : ball a r \ {a} ⊆ ball a R \ {a} := by
    intro z hz
    exact ⟨(mem_ball.mp hz.1).trans hrR, hz.2⟩
  have hsubc : closedBall a r \ {a} ⊆ ball a R \ {a} := by
    intro z hz
    exact ⟨lt_of_le_of_lt hz.1 hrR, hz.2⟩
  have hu' := harmonicOn_mono hu (isOpen_puncturedBall a r) hsub
  have hv' := harmonicOn_mono hv (isOpen_puncturedBall a r) (fun _ hz => hz.1)
  have hcv : ContinuousOn v (closedBall a r \ {a}) := hc.mono (fun _ hz => hz.1)
  have hcu : ContinuousOn u (closedBall a r \ {a}) := hu.2.1.continuousOn.mono hsubc
  have hup := bounded_punctured_boundary_maximum (harmonicOn_sub hu' hv')
    (hcu.sub hcv) (fun ξ hξ => by rw [heq hξ]; simp) (M + N) (by
      intro z hz
      have h1 := (le_abs_self (u z)).trans (hM z (hsub hz))
      have h2 : |v z| ≤ N := by simpa [Real.norm_eq_abs] using hN z (ball_subset_closedBall hz.1)
      linarith [neg_abs_le (v z)])
  have hdown := bounded_punctured_boundary_maximum (harmonicOn_sub hv' hu')
    (hcv.sub hcu) (fun ξ hξ => by rw [heq hξ]; simp) (M + N) (by
      intro z hz
      have h1 := hM z (hsub hz)
      have h2 : |v z| ≤ N := by simpa [Real.norm_eq_abs] using hN z (ball_subset_closedBall hz.1)
      linarith [le_abs_self (v z), neg_abs_le (u z)])
  exact ⟨v, hv, fun z hz => le_antisymm (by linarith [hdown z hz])
    (by linarith [hup z hz])⟩

/-- A local extension changes only the missing value, so it patches to the
entire original disk. Harmonicity is checked in actual neighborhoods. -/
lemma patch_extension {a : ℂ} {R r : ℝ} {u v : ℂ → ℝ} (hr : 0 < r)
    (hu : HarmonicOn (ball a R \ {a}) u) (hv : HarmonicOn (ball a r) v)
    (heq : EqOn v u (ball a r \ {a})) :
    ∃ w : ℂ → ℝ, HarmonicOn (ball a R) w ∧ EqOn w u (ball a R \ {a}) := by
  let w : ℂ → ℝ := fun z => if z = a then v a else u z
  have hw : HarmonicOn (ball a R) w := by
    apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ isOpen_ball).mpr
    have hu' := (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hu.1).mp hu
    have hv' := (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ hv.1).mp hv
    intro z hz
    by_cases hza : z = a
    · subst z
      apply (harmonicAt_congr_nhds (f₁ := v) (f₂ := w) ?_).mp
        (hv' a (mem_ball_self hr))
      filter_upwards [ball_mem_nhds a hr] with z hzr
      by_cases hza : z = a
      · simp [w, hza]
      · simp only [w, ite_eq_right hza]
        exact heq ⟨hzr, hza⟩
    · apply (harmonicAt_congr_nhds (f₁ := u) (f₂ := w) ?_).mp
        (hu' z ⟨hz, hza⟩)
      filter_upwards [hu.1.mem_nhds (show z ∈ ball a R \ {a} from ⟨hz, hza⟩)]
        with y hy
      simp only [w, ite_eq_right (show y ≠ a from hy.2)]
  exact ⟨w, hw, fun z hz => by simp only [w, ite_eq_right (show z ≠ a from hz.2)]⟩

theorem bounded_harmonic_removable :
    Specs.D12Complex.Ch13.HarmonicRemovable.bounded_harmonic_removable_type := by
  intro a R u hR hu hbound
  obtain ⟨M, hM⟩ := hbound
  obtain ⟨v, hv, heq⟩ := bounded_inner_extension hu (half_pos hR) (by linarith) M hM
  obtain ⟨w, hw, hew⟩ := patch_extension (half_pos hR) hu hv heq
  exact ⟨w, hw, hew, fun v' hv' hev' => extension_unique hR hw hv' hew hev'⟩

theorem locally_bounded_harmonic_removable :
    Specs.D12Complex.Ch13.HarmonicRemovable.locally_bounded_harmonic_removable_type := by
  intro a R u hR hu hbound
  obtain ⟨r, hr, hrR, M, hM⟩ := hbound
  have hu' : HarmonicOn (ball a r \ {a}) u :=
    harmonicOn_mono hu (isOpen_puncturedBall a r) (fun z hz =>
      ⟨lt_of_lt_of_le hz.1 hrR, hz.2⟩)
  obtain ⟨v, hv, heq, _⟩ := bounded_harmonic_removable a r u hr hu' ⟨M, hM⟩
  obtain ⟨w, hw, hew⟩ := patch_extension hr hu hv heq
  exact ⟨w, hw, hew, fun v' hv' hev' => extension_unique hR hw hv' hew hev'⟩

end D12Complex.HarmonicRemovable
