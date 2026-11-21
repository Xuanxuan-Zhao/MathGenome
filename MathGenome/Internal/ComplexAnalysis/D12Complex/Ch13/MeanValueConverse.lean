import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.MeanValueConverse
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.DiskDirichlet
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.BoundaryMaximum

noncomputable section
open Set Metric Complex Filter InnerProductSpace
open scoped Topology

namespace D12Complex.MeanValueConverse

/-- Restriction shrinks each mean radius separately. -/
lemma localCircleMeanProperty_restrict {U V : Set ℂ} {u : ℂ → ℝ}
    (hm : LocalCircleMeanProperty U u) (hV : IsOpen V) (hVU : V ⊆ U) :
    LocalCircleMeanProperty V u := by
  intro a ha
  obtain ⟨ρ, hρ, _, hmean⟩ := hm a (hVU ha)
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV a ha
  refine ⟨min ρ (δ / 2), lt_min hρ (half_pos hδ), ?_, ?_⟩
  · exact (closedBall_subset_ball (lt_of_le_of_lt (min_le_right _ _) (by linarith))).trans hδV
  · intro r hr hrr
    exact hmean r hr (hrr.trans_le (min_le_left _ _))

/-- Subtraction preserves local means under the continuity needed for
integrability on the small circles. -/
lemma localCircleMeanProperty_sub {U : Set ℂ} {u v : ℂ → ℝ}
    (hc : ContinuousOn u U) (hd : ContinuousOn v U)
    (hm : LocalCircleMeanProperty U u) (hn : LocalCircleMeanProperty U v) :
    LocalCircleMeanProperty U (fun z => u z - v z) := by
  intro a ha
  obtain ⟨ρ, hρ, hρU, hmean⟩ := hm a ha
  obtain ⟨δ, hδ, hδU, hmean'⟩ := hn a ha
  refine ⟨min ρ δ, lt_min hρ hδ,
    (closedBall_subset_closedBall (min_le_left _ _)).trans hρU, ?_⟩
  intro r hr hrr
  have hrρ := hrr.trans_le (min_le_left ρ δ)
  have hrδ := hrr.trans_le (min_le_right ρ δ)
  have hsU : sphere a r ⊆ U :=
    (sphere_subset_closedBall.trans (closedBall_subset_closedBall hrρ.le)).trans hρU
  rw [Real.circleAverage_fun_sub ((hc.mono hsU).circleIntegrable hr.le)
    ((hd.mono hsU).circleIntegrable hr.le), hmean r hr hrρ, hmean' r hr hrδ]

/-- A continuous closed-disk function vanishing on the circle satisfies the
boundary upper-limit condition used by the continuous mean maximum principle. -/
lemma boundaryLimsupLE_zero_of_eqOn_sphere {a : ℂ} {R : ℝ} {w : ℂ → ℝ}
    (hR : 0 < R) (hc : ContinuousOn w (closedBall a R))
    (hb : ∀ ξ ∈ sphere a R, w ξ = 0) : BoundaryLimsupLE (ball a R) w 0 := by
  intro ξ hξ ε hε
  have hs : ξ ∈ sphere a R := by simpa [frontier_ball a hR.ne'] using hξ
  obtain ⟨δ, hδ, hbound⟩ := Metric.continuousWithinAt_iff.mp
    (hc ξ (sphere_subset_closedBall hs)) ε hε
  refine ⟨δ, hδ, fun z hz hd => ?_⟩
  have he := hbound (ball_subset_closedBall hz) hd
  rw [Real.dist_eq, hb ξ hs, sub_zero] at he
  simpa using (le_abs_self (w z)).trans he.le

/-- Comparison with a harmonic function needs only local means of the
continuous function; its radii need not be uniform across the disk. -/
lemma eqOn_of_boundary_eq {a : ℂ} {R : ℝ} {u v : ℂ → ℝ}
    (hR : 0 < R) (hc : ContinuousOn u (closedBall a R))
    (hd : ContinuousOn v (closedBall a R))
    (hm : LocalCircleMeanProperty (ball a R) u)
    (hv : HarmonicOn (ball a R) v) (hb : EqOn u v (sphere a R)) :
    EqOn u v (ball a R) := by
  have hwc := hc.sub hd
  have hwm := localCircleMeanProperty_sub (hc.mono ball_subset_closedBall)
    (hd.mono ball_subset_closedBall) hm
    (MeanValueStrongPrinciple.harmonic_local_circle_mean _ _ hv)
  have hwb : ∀ ξ ∈ sphere a R, u ξ - v ξ = 0 := fun ξ hξ => sub_eq_zero.mpr (hb hξ)
  have hupper := BoundaryMaximum.continuous_mean_boundary_maximum (ball a R)
    (fun z => u z - v z) 0 isOpen_ball (isBounded_ball)
    (hwc.mono ball_subset_closedBall) hwm
    (boundaryLimsupLE_zero_of_eqOn_sphere hR hwc hwb)
  have hnegc : ContinuousOn (fun z => -(u z - v z)) (closedBall a R) := hwc.neg
  have hlower := BoundaryMaximum.continuous_mean_boundary_maximum (ball a R)
    (fun z => -(u z - v z)) 0 isOpen_ball (isBounded_ball)
    (hnegc.mono ball_subset_closedBall)
    (BoundaryMaximum.localCircleMeanProperty_neg hwm)
    (boundaryLimsupLE_zero_of_eqOn_sphere hR hnegc (fun ξ hξ => by rw [hwb ξ hξ, neg_zero]))
  intro z hz
  have := hupper z hz
  have := hlower z hz
  linarith

theorem continuous_local_circle_mean_harmonic :
    Specs.D12Complex.Ch13.MeanValueConverse.continuous_local_circle_mean_harmonic_type := by
  intro U u hU hc hm
  apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd U u hU).mpr
  intro a ha
  obtain ⟨ρ, hρ, hsub, _⟩ := hm a ha
  let φ : ℂ → ℝ := fun z => u (z + a)
  have hφ : ContinuousOn φ (sphere 0 ρ) := by
    apply (hc.mono hsub).comp (continuous_id.add continuous_const).continuousOn
    intro z hz
    simpa [mem_closedBall, dist_eq_norm] using (sphere_subset_closedBall hz)
  let h := DiskDirichlet.closedPoissonIntegral ρ φ
  obtain ⟨hhc, hhh, hhb, _⟩ := DiskDirichlet.closedPoissonIntegral_solution ρ φ hρ hφ
  change ContinuousOn h (closedBall 0 ρ) at hhc
  change HarmonicOn (ball 0 ρ) h at hhh
  change EqOn h φ (sphere 0 ρ) at hhb
  let v : ℂ → ℝ := fun z => h (z - a)
  have hmaps : MapsTo (fun z : ℂ => z - a) (ball a ρ) (ball 0 ρ) := by
    intro z hz
    simpa [mem_ball, dist_eq_norm] using hz
  have hvc : ContinuousOn v (closedBall a ρ) := by
    apply hhc.comp (continuous_id.sub continuous_const).continuousOn
    intro z hz
    simpa [mem_closedBall, dist_eq_norm] using hz
  have hv : HarmonicOn (ball a ρ) v :=
    HarmonicFoundation.harmonicOn_comp_holomorphic _ _ h (fun z => z - a) hhh
      ⟨isOpen_ball, fun z _ => differentiableAt_id.sub_const a⟩ hmaps
  have hb : EqOn u v (sphere a ρ) := by
    intro z hz
    have hz' : z - a ∈ sphere (0 : ℂ) ρ := by simpa [mem_sphere, dist_eq_norm] using hz
    simpa [v, φ] using (hhb hz').symm
  have heq : EqOn u v (ball a ρ) := eqOn_of_boundary_eq hρ (hc.mono hsub) hvc
    (localCircleMeanProperty_restrict hm isOpen_ball (ball_subset_closedBall.trans hsub)) hv hb
  have hevent : u =ᶠ[𝓝 a] v := Filter.mem_of_superset (ball_mem_nhds a hρ) heq
  exact (harmonicAt_congr_nhds hevent).mpr
    (((HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ isOpen_ball).mp hv)
      a (mem_ball_self hρ))

end D12Complex.MeanValueConverse
