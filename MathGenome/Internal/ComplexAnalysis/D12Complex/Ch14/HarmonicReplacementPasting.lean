import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.HarmonicReplacementPasting
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.SubharmonicMaximum
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.SubharmonicOperations
import Mathlib.Topology.Piecewise

noncomputable section
open Set Metric
open scoped Topology

namespace D12Complex.HarmonicReplacementPasting

abbrev harmonicReplacement := D12Complex.harmonicReplacement
abbrev subharmonicPaste := D12Complex.subharmonicPaste

lemma subharmonicOn_mono {U V : Set ℂ} {u : ℂ → ℝ}
    (hu : SubharmonicOn U u) (hV : IsOpen V) (hVU : V ⊆ U) :
    SubharmonicOn V u :=
  ⟨hV, hu.2.1.mono hVU, fun a R hR hs => hu.2.2 a R hR (hs.trans hVU)⟩

lemma harmonicOn_mono {U V : Set ℂ} {h : ℂ → ℝ}
    (hh : HarmonicOn U h) (hV : IsOpen V) (hVU : V ⊆ U) : HarmonicOn V h :=
  ⟨hV, hh.2.1.mono hVU, fun z hz => hh.2.2 z (hVU hz)⟩

lemma subharmonicOn_congr {U : Set ℂ} {u v : ℂ → ℝ}
    (hu : SubharmonicOn U u) (he : EqOn u v U) : SubharmonicOn U v := by
  apply SubharmonicDefinition.harmonicComparisonOn_subharmonicOn
  have hcomp := (SubharmonicDefinition.subharmonicOn_iff_harmonicComparisonOn U u).mp hu
  refine ⟨hu.1, hu.2.1.congr he.symm, ?_⟩
  intro a R hR hs h hc hh hb z hz
  rw [← he (hs hz)]
  exact hcomp.2.2 a R hR hs h hc hh
    (fun w hw => (he (hs (sphere_subset_closedBall hw))).trans_le (hb w hw)) z hz

/-- Continuity on a closed containing set turns pointwise boundary bounds
into boundary upper limits. In particular, the boundary need not be smooth. -/
lemma boundaryLimsupLE_of_continuousOn {V C : Set ℂ} {f : ℂ → ℝ}
    (hC : IsClosed C) (hVC : V ⊆ C) (hc : ContinuousOn f C)
    (hb : ∀ ξ ∈ frontier V, f ξ ≤ 0) : BoundaryLimsupLE V f 0 := by
  intro ξ hξ ε hε
  have hξC : ξ ∈ C := (closure_minimal hVC hC) (frontier_subset_closure hξ)
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.mp (hc ξ hξC) ε hε
  refine ⟨δ, hδ, fun z hz hdist => ?_⟩
  have hf := hd (hVC hz) hdist
  have := (abs_lt.mp (show |f z - f ξ| < ε by simpa [Real.dist_eq] using hf)).2
  linarith [hb ξ hξ]

/-- The continuous assembled function already controls the interface limits.
This slightly stronger form is useful for harmonic replacement. -/
lemma subharmonic_paste_of_continuous (U W : Set ℂ) (u v : ℂ → ℝ)
    (hu : SubharmonicOn U u) (hv : SubharmonicOn W v) (hWU : W ⊆ U)
    (hc : ContinuousOn (subharmonicPaste W u v) U) :
    SubharmonicOn U (subharmonicPaste W u v) := by
  let p := subharmonicPaste W u v
  have hup : ∀ z, u z ≤ p z := by
    intro z
    simp only [p, subharmonicPaste, D12Complex.subharmonicPaste]
    split_ifs <;> simp
  have hpW : SubharmonicOn W p := by
    have hm := SubharmonicOperations.subharmonicOn_max W u v
      (subharmonicOn_mono hu hv.1 hWU) hv
    apply subharmonicOn_congr hm
    intro z hz
    simp [p, subharmonicPaste, D12Complex.subharmonicPaste, hz]
  apply SubharmonicDefinition.harmonicComparisonOn_subharmonicOn
  refine ⟨hu.1, hc, ?_⟩
  intro a R hR hsub h hh hharm hb
  have huh : ∀ z ∈ closedBall a R, u z ≤ h z :=
    ((SubharmonicDefinition.subharmonicOn_iff_harmonicComparisonOn U u).mp hu).2.2
      a R hR hsub h hh hharm (fun z hz => (hup z).trans (hb z hz))
  let V := W ∩ ball a R
  have hVo : IsOpen V := hv.1.inter isOpen_ball
  have hVC : V ⊆ closedBall a R := fun _ hz => ball_subset_closedBall hz.2
  have hfront : ∀ ξ ∈ frontier V, p ξ ≤ h ξ := by
    intro ξ hξ
    have hξC : ξ ∈ closedBall a R :=
      (closure_minimal hVC isClosed_closedBall) (frontier_subset_closure hξ)
    by_cases hξW : ξ ∈ W
    · have hn : ξ ∉ ball a R := by
        intro hi
        rw [hVo.frontier_eq] at hξ
        exact hξ.2 ⟨hξW, hi⟩
      have hs : ξ ∈ sphere a R := le_antisymm hξC (le_of_not_gt hn)
      exact hb ξ hs
    · simpa [p, subharmonicPaste, D12Complex.subharmonicPaste, hξW] using huh ξ hξC
  have hlim : BoundaryLimsupLE V (fun z => p z - h z) 0 :=
    boundaryLimsupLE_of_continuousOn isClosed_closedBall hVC
      ((hc.mono hsub).sub hh) (fun ξ hξ => sub_nonpos.mpr (hfront ξ hξ))
  have hcompare : ∀ z ∈ V, p z ≤ h z :=
    SubharmonicMaximum.subharmonic_harmonic_comparison V p h
      ((isBounded_closedBall (x := a) (r := R)).subset hVC)
      (subharmonicOn_mono hpW hVo inter_subset_left)
      (harmonicOn_mono hharm hVo inter_subset_right) hlim
  intro z hz
  by_cases hi : z ∈ ball a R
  · by_cases hW : z ∈ W
    · exact hcompare z ⟨hW, hi⟩
    · simpa [p, subharmonicPaste, D12Complex.subharmonicPaste, hW] using huh z hz
  · exact hb z (le_antisymm hz (le_of_not_gt hi))

theorem subharmonic_pasting :
    Specs.D12Complex.Ch14.HarmonicReplacementPasting.subharmonic_pasting_type := by
  intro U W u v hu hv hWU _hinterface hc
  exact subharmonic_paste_of_continuous U W u v hu hv hWU hc

/-- Harmonicity is local, so equality on the open set transports the actual
C² and Laplacian definition without assigning derivatives outside the set. -/
lemma harmonicOn_congr {U : Set ℂ} {u v : ℂ → ℝ}
    (hu : HarmonicOn U u) (he : EqOn u v U) : HarmonicOn U v := by
  apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd U v hu.1).mpr
  have hn := (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd U u hu.1).mp hu
  intro z hz
  apply (InnerProductSpace.harmonicAt_congr_nhds _).mp (hn z hz)
  filter_upwards [hu.1.mem_nhds hz] with w hw
  exact he hw

lemma harmonicReplacement_continuous {U : Set ℂ} {u : ℂ → ℝ} {a : ℂ} {R : ℝ}
    (hu : SubharmonicOn U u) (hR : 0 < R) (hsub : closedBall a R ⊆ U) :
    ContinuousOn (harmonicReplacement a R u) U := by
  classical
  obtain ⟨hc, _hh, he⟩ := SubharmonicDefinition.diskPoissonExtension_solution a R u hR
    (hu.2.1.mono (sphere_subset_closedBall.trans hsub))
  change ContinuousOn (fun z => if z ∈ ball a R then diskPoissonExtension a R u z else u z) U
  apply ContinuousOn.if
  · intro z hz
    exact he (frontier_ball_subset_sphere hz.2)
  · exact hc.mono (fun z hz => closure_ball_subset_closedBall hz.2)
  · exact hu.2.1.mono inter_subset_left

lemma le_harmonicReplacement {U : Set ℂ} {u : ℂ → ℝ} {a : ℂ} {R : ℝ}
    (hu : SubharmonicOn U u) (hR : 0 < R) (hsub : closedBall a R ⊆ U) :
    ∀ z ∈ U, u z ≤ harmonicReplacement a R u z := by
  intro z _hz
  unfold harmonicReplacement D12Complex.harmonicReplacement
  split_ifs with hi
  · exact hu.2.2 a R hR hsub z (ball_subset_closedBall hi)
  · exact le_rfl

theorem harmonicReplacement_properties :
    Specs.D12Complex.Ch14.HarmonicReplacementPasting.harmonicReplacement_properties_type := by
  intro U u a R hu hR hsub
  obtain ⟨hcH, hhH, hbH⟩ := SubharmonicDefinition.diskPoissonExtension_solution a R u hR
    (hu.2.1.mono (sphere_subset_closedBall.trans hsub))
  have hc := harmonicReplacement_continuous hu hR hsub
  have hle := le_harmonicReplacement hu hR hsub
  have he : EqOn (diskPoissonExtension a R u) (harmonicReplacement a R u) (ball a R) := by
    intro z hz
    simp [harmonicReplacement, D12Complex.harmonicReplacement, hz]
  have hp : EqOn (subharmonicPaste (ball a R) u (diskPoissonExtension a R u))
      (harmonicReplacement a R u) U := by
    intro z _hz
    by_cases hi : z ∈ ball a R
    · simp [subharmonicPaste, D12Complex.subharmonicPaste,
        harmonicReplacement, D12Complex.harmonicReplacement, hi,
        max_eq_right (hu.2.2 a R hR hsub z (ball_subset_closedBall hi))]
    · simp [subharmonicPaste, D12Complex.subharmonicPaste,
        harmonicReplacement, D12Complex.harmonicReplacement, hi]
  have hsp := subharmonic_paste_of_continuous U (ball a R) u (diskPoissonExtension a R u)
    hu (SubharmonicOperations.harmonicOn_subharmonicOn _ _ hhH)
    (ball_subset_closedBall.trans hsub) (hc.congr hp)
  exact ⟨hc, subharmonicOn_congr hsp hp, harmonicOn_congr hhH he, hle⟩

/-- Boundary comparison proves order preservation of the genuine Poisson
solutions, including their prescribed circle values. -/
lemma diskPoissonExtension_mono (a : ℂ) (R : ℝ) (u v : ℂ → ℝ) (hR : 0 < R)
    (hu : ContinuousOn u (sphere a R)) (hv : ContinuousOn v (sphere a R))
    (huv : ∀ z ∈ sphere a R, u z ≤ v z) :
    ∀ z ∈ closedBall a R, diskPoissonExtension a R u z ≤ diskPoissonExtension a R v z := by
  obtain ⟨hcu, hhu, hbu⟩ := SubharmonicDefinition.diskPoissonExtension_solution a R u hR hu
  obtain ⟨hcv, hhv, hbv⟩ := SubharmonicDefinition.diskPoissonExtension_solution a R v hR hv
  have hb : ∀ z ∈ sphere a R, diskPoissonExtension a R u z ≤ diskPoissonExtension a R v z := by
    intro z hz
    rw [hbu hz, hbv hz]
    exact huv z hz
  have hlim : BoundaryLimsupLE (ball a R)
      (fun z => diskPoissonExtension a R u z - diskPoissonExtension a R v z) 0 :=
    boundaryLimsupLE_of_continuousOn isClosed_closedBall ball_subset_closedBall
      (hcu.sub hcv) (fun z hz => sub_nonpos.mpr (hb z (frontier_ball_subset_sphere hz)))
  have hi := SubharmonicMaximum.subharmonic_harmonic_comparison (ball a R)
    (diskPoissonExtension a R u) (diskPoissonExtension a R v)
    isBounded_ball (SubharmonicOperations.harmonicOn_subharmonicOn _ _ hhu) hhv hlim
  intro z hz
  by_cases hzB : z ∈ ball a R
  · exact hi z hzB
  · exact hb z (le_antisymm hz (le_of_not_gt hzB))

theorem harmonicReplacement_monotone :
    Specs.D12Complex.Ch14.HarmonicReplacementPasting.harmonicReplacement_monotone_type := by
  intro U u v a R hu hv hR hsub huv z hz
  have hs := sphere_subset_closedBall.trans hsub
  have hP := diskPoissonExtension_mono a R u v hR (hu.2.1.mono hs) (hv.2.1.mono hs)
    (fun w hw => huv w (hs hw))
  unfold D12Complex.harmonicReplacement
  split_ifs with hi
  · exact hP z (ball_subset_closedBall hi)
  · exact huv z hz

end D12Complex.HarmonicReplacementPasting
