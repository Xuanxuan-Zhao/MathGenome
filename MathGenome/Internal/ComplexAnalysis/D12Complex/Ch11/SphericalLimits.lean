import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.SphericalLimits
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.ChordalMetric
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch11.HolomorphicLimits
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.ScalarSphereBridge
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.UniformApproximation
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Filter Metric
open scoped Topology

namespace D12Complex.SphericalLimits

namespace Definitions
abbrev SphericalLocallyUniformOn := D12Complex.SphericalLimits.SphericalLocallyUniformOn
end Definitions

open private coordinate_open coordinate_continuousAt coordinate_exists
  from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SphereHolomorphic

/-- A compact buffer inside the chart absorbs all sufficiently late images. -/
lemma compact_buffer {X Y : Type*} [TopologicalSpace X] [MetricSpace Y] [CompactSpace Y]
    {f : ℕ → X → Y} {F : X → Y} {K : Set X} {U : Set Y}
    (hK : IsCompact K) (hF : ContinuousOn F K) (hU : IsOpen U)
    (himage : MapsTo F K U) (hlim : TendstoUniformlyOn f F atTop K) :
    ∃ C : Set Y, IsCompact C ∧ C ⊆ U ∧ MapsTo F K C ∧
      ∀ᶠ n in atTop, MapsTo (f n) K C := by
  obtain ⟨δ, hδ, hsub⟩ := (hK.image_of_continuousOn hF).exists_cthickening_subset_open
    hU (by rintro _ ⟨z, hz, rfl⟩; exact himage hz)
  refine ⟨cthickening δ (F '' K), isClosed_cthickening.isCompact, hsub, ?_, ?_⟩
  · intro z hz
    exact self_subset_cthickening (F '' K) (mem_image_of_mem F hz)
  · filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim δ hδ] with n hn z hz
    exact mem_cthickening_of_dist_le (f n z) (F z) δ (F '' K)
      (mem_image_of_mem F hz) (by simpa only [dist_comm] using (hn z hz).le)

lemma uniform_chart_convergence {X Y : Type*} [TopologicalSpace X]
    [MetricSpace Y] [CompactSpace Y] {f : ℕ → X → Y} {F : X → Y}
    {K : Set X} {U : Set Y} {g : Y → ℂ}
    (hK : IsCompact K) (hF : ContinuousOn F K) (hU : IsOpen U)
    (himage : MapsTo F K U) (hg : ContinuousOn g U)
    (hlim : TendstoUniformlyOn f F atTop K) :
    (∃ M : ℝ, 0 < M ∧ (∀ z ∈ K, ‖g (F z)‖ ≤ M) ∧
      ∀ᶠ n in atTop, ∀ z ∈ K, f n z ∈ U ∧ ‖g (f n z)‖ ≤ M) ∧
      TendstoUniformlyOn (fun n z => g (f n z)) (fun z => g (F z)) atTop K := by
  obtain ⟨C, hC, hCU, hFC, hfC⟩ := compact_buffer hK hF hU himage hlim
  have hgc := hg.mono hCU
  obtain ⟨M, hM, hbound⟩ := (hC.image_of_continuousOn hgc).isBounded.exists_pos_norm_le
  refine ⟨⟨M, hM, ?_, ?_⟩, ?_⟩
  · intro z hz
    exact hbound _ (mem_image_of_mem g (hFC hz))
  · filter_upwards [hfC] with n hn z hz
    exact ⟨hCU (hn hz), hbound _ (mem_image_of_mem g (hn hz))⟩
  · exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
      ((hC.uniformContinuousOn_of_continuous hgc).comp_tendstoLocallyUniformlyOn
        hlim.tendstoLocallyUniformlyOn hFC hfC)

/-- The chosen metric has definitionally the already fixed sphere topology. -/
@[instance_reducible] private def sphereMetric : MetricSpace RiemannSphere :=
  (Classical.choose Chordal.chordal_metric).replaceTopology
    (Classical.choose_spec Chordal.chordal_metric).1.symm

local instance : MetricSpace RiemannSphere := sphereMetric
local instance : CompactSpace RiemannSphere := sphere_compact

private lemma dist_chordal (p q : RiemannSphere) : dist p q = Chordal.chordal p q :=
  (Classical.choose_spec Chordal.chordal_metric).2.1 p q

lemma spherical_tendstoLocallyUniformlyOn {Ω : Set ℂ}
    {f : ℕ → ℂ → RiemannSphere} {F : ℂ → RiemannSphere}
    (hΩ : IsOpen Ω) (hlim : SphericalLocallyUniformOn f F Ω) :
    TendstoLocallyUniformlyOn f F atTop Ω := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hΩ).mpr
  intro K hKΩ hK
  apply Metric.tendstoUniformlyOn_iff.mpr
  simpa only [dist_chordal] using hlim K hK hKΩ

lemma limit_continuousOn {Ω : Set ℂ}
    {f : ℕ → ℂ → RiemannSphere} {F : ℂ → RiemannSphere}
    (hΩ : IsOpen Ω) (hf : ∀ n, PlaneSphereHolomorphicOn Ω (f n))
    (hlim : SphericalLocallyUniformOn f F Ω) : ContinuousOn F Ω := by
  exact (spherical_tendstoLocallyUniformlyOn hΩ hlim).continuousOn
    (Frequently.of_forall fun n => planeSphereHolomorphicOn_continuousOn Ω (f n) (hf n))

theorem chart_compact_convergence :
    Specs.D12Complex.Ch11.SphericalLimits.chart_compact_convergence_type := by
  intro Ω f F hΩ hf hlim c K hK hKΩ himage
  apply uniform_chart_convergence hK ((limit_continuousOn hΩ hf hlim).mono hKΩ)
    (coordinate_open c) himage
  · intro p hp
    exact (coordinate_continuousAt c p hp).continuousWithinAt
  · exact Metric.tendstoUniformlyOn_iff.mpr (by
      simpa only [dist_chordal] using hlim K hK hKΩ)

theorem chart_neighborhood_convergence :
    Specs.D12Complex.Ch11.SphericalLimits.chart_neighborhood_convergence_type := by
  intro Ω f F hΩ hf hlim a ha c hc
  have hFa : ContinuousAt F a :=
    ((limit_continuousOn hΩ hf hlim) a ha).continuousAt (hΩ.mem_nhds ha)
  have hnhds : Ω ∩ F ⁻¹' (sphereCoordinate c).source ∈ 𝓝 a :=
    inter_mem (hΩ.mem_nhds ha) (hFa ((coordinate_open c).mem_nhds hc))
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.mp hnhds
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hclosed : closedBall a r ⊆ Ω ∩ F ⁻¹' (sphereCoordinate c).source :=
    (closedBall_subset_ball (half_lt_self hR)).trans hsub
  have hKΩ : closedBall a r ⊆ Ω := fun _ hz => (hclosed hz).1
  have himage : MapsTo F (closedBall a r) (sphereCoordinate c).source :=
    fun _ hz => (hclosed hz).2
  obtain ⟨⟨M, hM, hbound, hevent⟩, hord⟩ :=
    chart_compact_convergence Ω f F hΩ hf hlim c (closedBall a r)
      (isCompact_closedBall a r) hKΩ himage
  refine ⟨r, hr, hKΩ, himage, ⟨M, hM, hbound, ?_⟩, hord⟩
  filter_upwards [hevent] with n hn
  refine ⟨⟨isOpen_ball, ?_⟩, hn⟩
  intro z hz
  exact ((planeSphereHolomorphicAt_iff_chart (f n) z c
    (hn z (ball_subset_closedBall hz)).1).mp
      ((hf n).2 z (hKΩ (ball_subset_closedBall hz)))).2.differentiableAt

theorem sphere_holomorphic_limit :
    Specs.D12Complex.Ch11.SphericalLimits.sphere_holomorphic_limit_type := by
  intro Ω f F hΩ hf hlim
  have hcont := limit_continuousOn hΩ hf hlim
  refine ⟨hΩ, fun a ha => ?_⟩
  have hFa : ContinuousAt F a := (hcont a ha).continuousAt (hΩ.mem_nhds ha)
  obtain ⟨c, hc⟩ := coordinate_exists (F a)
  obtain ⟨r, hr, _, _, ⟨_, _, _, hevent⟩, hord⟩ :=
    chart_neighborhood_convergence Ω f F hΩ hf hlim a ha c hc
  have hdiff : ∀ᶠ n in atTop,
      DifferentiableOn ℂ (fun z => sphereCoordinate c (f n z)) (ball a r) := by
    filter_upwards [hevent] with n hn z hz
    exact (hn.1.2 z hz).differentiableWithinAt
  have hd := (hord.tendstoLocallyUniformlyOn.mono ball_subset_closedBall).differentiableOn
    hdiff isOpen_ball
  refine ⟨hFa, c, hc, ball a r, mem_ball_self hr, isOpen_ball, ?_⟩
  intro z hz
  exact hd.differentiableAt (isOpen_ball.mem_nhds hz)

theorem scalar_meromorphic_limit :
    Specs.D12Complex.Ch11.SphericalLimits.scalar_meromorphic_limit_type := by
  intro Ω f F hΩ hf hlim
  have hF := sphere_holomorphic_limit Ω f F hΩ.2.1
    (fun n => scalarMeromorphic_planeSphereHolomorphic (hf n)) hlim
  exact ⟨hF, (plane_scalar_sphere_bridge Ω F hΩ).mp hF⟩

end D12Complex.SphericalLimits
