import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C12.InfinitesimalFluxAndCirculation
import MathGenome.Internal.MultivariableAnalysis.D04.C12.ClassicalIntegralCalibrations
import MathGenome.Internal.MultivariableAnalysis.D04.C12.ClassicalSurfaceStokes
import MathGenome.Internal.MultivariableAnalysis.D04.C12.PlanarDiskIntegralBridge
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Set Filter Topology
open scoped RealInnerProductSpace BigOperators ContDiff
namespace D04.LocalDensities
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C11.EuclideanVectorOperators.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C12.ClassicalRegularDomains.Model
open Specs.D04.C12.GaussDivergenceTheorem.Model

open Specs.D04.C12.InfinitesimalFluxAndCirculation

lemma region_constant {n : ℕ} {S : Set (E n)} (hS : Jordan S) (c : ℝ) :
    RegionIntegrable (fun _ : S => c) ∧
      regionIntegral (fun _ : S => c) = c * volume S := by
  simpa only [mul_one, D04.JordanRegions.regionIntegral_one] using
    D04.SlicingAndMoments.region_smul (D04.JordanRegions.jordan_bounded hS)
      (fun _ : S => (1 : ℝ)) (D04.LinearVolume.region_one_integrable hS) c

lemma average_error_bound {n : ℕ} {S : Set (E n)} (hS : Jordan S)
    (hv : 0 < volume S) (g : S → ℝ) (hg : RegionIntegrable g)
    (c M : ℝ) (hM : 0 ≤ M) (hbound : ∀ y, |g y-c| ≤ M) :
    |regionIntegral g / volume S - c| ≤ M := by
  have hc := region_constant hS c
  have hd := D04.SlicingAndMoments.region_sub (D04.JordanRegions.jordan_bounded hS)
    g (fun _ => c) hg hc.1
  have hb := D04.JordanRegions.scalar_uniform_bound hS (fun y => g y-c) hd.1 M hM hbound
  rw [hd.2] at hb
  change |regionIntegral g - regionIntegral (fun _ : S => c)| ≤ M * volume S at hb
  rw [hc.2] at hb
  have he : regionIntegral g / volume S - c =
      (regionIntegral g-c*volume S)/volume S := by field_simp
  rw [he, abs_div, abs_of_pos hv]
  exact (div_le_iff₀ hv).mpr hb

theorem shrinking_average : shrinking_averageType := by
  intro n g x S hg hS
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hgδ⟩ := Metric.continuousAt_iff.mp hg (ε/2) (by positivity)
  have hr : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < δ :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)
  filter_upwards [hS, hr] with r hSr hr
  obtain ⟨hj, hv, hi, hs⟩ := hSr
  rw [Real.dist_eq]
  apply lt_of_le_of_lt (average_error_bound hj hv _ hi (g x) (ε/2) (by positivity) ?_)
    (by linarith)
  intro y
  exact le_of_lt (by
    rw [← Real.dist_eq]
    exact hgδ ((Metric.mem_closedBall.mp (hs y.property)).trans_lt hr))


private def ballDefining {n : ℕ} (x : E n) (r : ℝ) (y : E n) : ℝ :=
  ‖y-x‖^2-r^2

private lemma ballDefining_derivative {n : ℕ} (x : E n) (r : ℝ) (y : E n) :
    HasFDerivAt (ballDefining x r) ((2 : ℝ) • innerSL ℝ (y-x)) y := by
  convert (((hasStrictFDerivAt_norm_sq (y-x)).hasFDerivAt.comp y
    ((hasFDerivAt_id y).sub_const x)).sub_const (r^2)) using 1
  all_goals first | rfl | simp [two_smul]

private lemma ball_defining {d : ℕ} (x : E (d+1)) (r : ℝ) (hr : 0 < r) :
    IsDefiningFunction (Metric.ball x r) univ (ballDefining x r) := by
  refine ⟨isOpen_univ, ?_, ?_, ?_, ?_⟩
  · exact ((((contDiff_id.sub contDiff_const).norm_sq ℝ).sub contDiff_const)).contDiffOn
  · intro y _
    simp only [Metric.mem_ball, dist_eq_norm, ballDefining]
    constructor <;> intro h <;> nlinarith [norm_nonneg (y-x)]
  · intro y _
    rw [frontier_ball _ hr.ne']
    change dist y x = r ↔ ‖y-x‖^2-r^2=0
    rw [dist_eq_norm]
    constructor <;> intro h <;> nlinarith [norm_nonneg (y-x)]
  · intro y _ hy he
    have hv := congrArg (fun A : E (d+1) →L[ℝ] ℝ => A (y-x)) he
    rw [(ballDefining_derivative x r y).fderiv] at hv
    simp only [smul_apply, innerSL_apply_apply,
      smul_eq_mul, zero_apply, real_inner_self_eq_norm_sq] at hv
    dsimp [ballDefining] at hy
    nlinarith

lemma ball_regular {d : ℕ} (x : E (d+1)) (r : ℝ) (hr : 0 < r) :
    IsClassicalRegularDomain (Metric.ball x r) := by
  exact ⟨by omega, Metric.isBounded_ball, Metric.isOpen_ball,
    fun p hp => ⟨univ, ballDefining x r, mem_univ p, ball_defining x r hr⟩⟩

private lemma ball_gradient {n : ℕ} (x : E n) (r : ℝ) (y : E n) :
    Specs.D04.C02.DerivativeBridge.Model.scalarGradient (ballDefining x r) y =
      (2 : ℝ) • (y-x) := by
  apply ext_inner_right ℝ
  intro v
  have he := D04.scalarGradient_represents (ballDefining x r) y v
  exact he.symm.trans (by
    change fderiv ℝ (ballDefining x r) y v = _
    rw [(ballDefining_derivative x r y).fderiv]
    simp [real_inner_smul_left, inner_sub_left])

lemma ball_normal {d : ℕ} (x : E (d+1)) (r : ℝ) (hr : 0 < r)
    (y : frontier (Metric.ball x r)) :
    outwardNormal (ball_regular x r hr) y = r⁻¹ • (y.val-x) := by
  rw [D04.ClassicalRegularDomains.outwardNormal_formula
    (ball_regular x r hr) y (ball_defining x r hr) (mem_univ _)]
  change ‖Specs.D04.C02.DerivativeBridge.Model.scalarGradient (ballDefining x r) y‖⁻¹ •
    Specs.D04.C02.DerivativeBridge.Model.scalarGradient (ballDefining x r) y = _
  rw [ball_gradient, norm_smul]
  have hy : ‖(y : E (d+1))-x‖ = r := by
    have hy : (y : E (d+1)) ∈ Metric.sphere x r := by
      simpa only [frontier_ball _ hr.ne'] using y.property
    simpa only [Metric.mem_sphere, dist_eq_norm] using hy
  rw [hy]
  norm_num
  rw [smul_smul]
  congr 1
  field_simp

lemma open_volume_pos {n : ℕ} {S : Set (E n)} (hS : Jordan S)
    (hopen : IsOpen S) (hne : S.Nonempty) : 0 < volume S := by
  by_contra hn
  have hv : volume S = 0 := le_antisymm (le_of_not_gt hn) (D04.JordanRegions.volume_nonneg hS)
  have hz := D04.NullCovers.contentZero_null (D04.JordanRegions.zero_volume_contentZero hS hv)
  have hm := D04.NullPreservation.coordinate_volume_zero_of_null hz
  have ho : IsOpen (WithLp.ofLp '' S) := (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).isOpenMap S hopen
  exact ho.measure_ne_zero MeasureTheory.volume (hne.image _) hm

lemma small_closedBalls {n : ℕ} {U : Set (E n)} (hU : IsOpen U)
    {x : E n} (hx : x ∈ U) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), Metric.closedBall x r ⊆ U := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hU x hx
  have hr : ∀ᶠ r in 𝓝[>] (0 : ℝ), r < δ :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)
  filter_upwards [hr] with r hr y hy
  apply hsub
  exact Metric.mem_ball.mpr ((Metric.mem_closedBall.mp hy).trans_lt hr)

theorem local_flux : local_fluxType := by
  intro d U F x hU hx hF
  let flux : ℝ → ℝ := fun r => regionIntegral (fun y : Metric.ball x r => divergence F y)
  have hsmall := small_closedBalls hU hx
  have hflux (r : ℝ) (hr : 0 < r) (hsub : Metric.closedBall x r ⊆ U) :
      Jordan (Metric.ball x r) ∧ 0 < volume (Metric.ball x r) ∧
      RegionIntegrable (fun y : Metric.ball x r => divergence F y) ∧
      HasDensityIntegral (d := d)
        (normalFlux F (fun y : frontier (Metric.ball x r) => r⁻¹ • (y.val-x)))
        (flux r) := by
    have hD := ball_regular x r hr
    have hj := (D04.RegularDomainGeometry.jordan_domain_and_closure hD).1
    have hv := open_volume_pos hj Metric.isOpen_ball ⟨x, Metric.mem_ball_self hr⟩
    have hcl : closure (Metric.ball x r) ⊆ U := by
      rw [closure_ball x hr.ne']
      exact hsub
    obtain ⟨hi, hgauss⟩ := D04.Gauss.gauss hD U F hU hcl hF
    have hnormal : outwardNormal hD =
        (fun y : frontier (Metric.ball x r) => r⁻¹ • (y.val-x)) :=
      funext (ball_normal x r hr)
    rw [hnormal] at hgauss
    exact ⟨hj, hv, hi, hgauss⟩
  refine ⟨flux, ?_, hsmall, ?_⟩
  · intro r hr hsub
    obtain ⟨hj,hv,hi,hflux⟩ := hflux r hr hsub
    exact ⟨hj,hv,hflux⟩
  · apply shrinking_average (divergence F) x (fun r => Metric.ball x r)
    · exact (D04.Gauss.divergence_continuousOn U F hU hF).continuousAt (hU.mem_nhds hx)
    · filter_upwards [hsmall, self_mem_nhdsWithin] with r hsub hr
      obtain ⟨hj,hv,hi,hflux⟩ := hflux r hr hsub
      exact ⟨hj,hv,hi,Metric.ball_subset_closedBall⟩


/-- The analytic part of circulation: averages of curl in any isometrically
parametrized plane converge to the normal component at the center. This uses
the actual Darboux disk integrals and the proved pi*r^2 calibration. -/
lemma planar_curl_average (U : Set (E 3)) (F : E 3 → E 3) (x N : E 3)
    (A : E 2 →ₗᵢ[ℝ] E 3) (hU : IsOpen U) (hx : x ∈ U) (hF : CrOn 1 U F) :
    Tendsto (fun r => regionIntegral
      (fun u : Specs.D04.C12.ClassicalIntegralCalibrations.Model.diskParameters r =>
        inner ℝ (curl F (x + A u)) N) / (Real.pi * r^2))
      (𝓝[>] 0) (𝓝 (inner ℝ (curl F x) N)) := by
  let S := Specs.D04.C12.ClassicalIntegralCalibrations.Model.diskParameters
  let g : E 2 → ℝ := fun u => inner ℝ (curl F (x+A u)) N
  have hcont : ContinuousOn (curl F) U := D04.ClassicalSurfaceStokes.curl_continuousOn U hU F hF
  have hg : ContinuousAt g 0 := by
    have hc : ContinuousAt (fun u : E 2 => x+A u) 0 := continuousAt_const.add A.continuous.continuousAt
    have hfc : ContinuousAt (curl F) (x+A 0) := by
      simpa only [map_zero, add_zero] using hcont.continuousAt (hU.mem_nhds hx)
    have hf : ContinuousAt (fun u : E 2 => curl F (x+A u)) 0 :=
      ContinuousAt.comp (f := fun u : E 2 => x+A u) (g := curl F) hfc hc
    simpa only [map_zero, add_zero] using hf.inner continuousAt_const
  have hsmall := small_closedBalls hU hx
  have hS (r : ℝ) (hr : 0 < r) : S r = Metric.closedBall (0 : E 2) r := by
    ext u
    change u 0^2+u 1^2 ≤ r^2 ↔ dist u 0 ≤ r
    rw [dist_zero_right, D04.norm_coordinates]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    rw [Real.sqrt_le_iff]
    simp only [hr.le, true_and]
    rfl
  have hi (r : ℝ) (hr : 0 < r) (hsub : Metric.closedBall x r ⊆ U) :
      RegionIntegrable (fun u : S r => g u) := by
    have hj := (D04.Calibrations.disk_volume r hr).1
    have hc : Continuous (fun u : closure (S r) => g u) := by
      apply Continuous.inner _ continuous_const
      apply hcont.comp_continuous (continuous_const.add (A.continuous.comp continuous_subtype_val))
      intro u
      apply hsub
      have hu : ‖(u : E 2)‖ ≤ r := by
        have hu : (u : E 2) ∈ Metric.closedBall 0 r := by
          simpa only [hS r hr, Metric.isClosed_closedBall.closure_eq] using u.property
        simpa only [Metric.mem_closedBall, dist_zero_right] using hu
      change ‖x + A (u : E 2) - x‖ ≤ r
      simpa only [add_sub_cancel_left, A.norm_map] using hu
    exact D04.JordanRegions.integrable_continuous_on_closure (by norm_num) hj _ hc
  have hav := shrinking_average g 0 S hg (by
    filter_upwards [hsmall, self_mem_nhdsWithin] with r hsub hr
    obtain ⟨hj,hv⟩ := D04.Calibrations.disk_volume r hr
    exact ⟨hj, hv.symm ▸ (mul_pos Real.pi_pos (sq_pos_of_pos hr)), hi r hr hsub,
      (hS r hr).subset⟩)
  have heq : (fun r => regionIntegral (fun u : S r => g u) / volume (S r)) =ᶠ[𝓝[>] 0]
      (fun r => regionIntegral (fun u : S r => g u) / (Real.pi*r^2)) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [(D04.Calibrations.disk_volume r hr).2]
  simpa only [g, map_zero, add_zero] using hav.congr' heq



/-- Assemble the geometric and unsigned integration theorems for the same
affine isometry, uniformly over all positive radii. -/
theorem disk_geometry : disk_geometryType := by
  intro x N hN
  obtain ⟨A, _, _, hA⟩ := D04.PlanarDiskGeometry.disk_geometry x N hN
  refine ⟨A, ?_⟩
  intro r hr
  obtain ⟨himage, hcompact, hM, hboundary, normal, hnormal⟩ := hA r hr
  refine ⟨himage, hM, (D04.compact_iff_isCompact _).mp hcompact,
    hboundary, normal, hnormal, ?_⟩
  intro g hg
  exact (D04.PlanarDiskIntegralBridge.disk_integral x N hN A
    (fun s hs => (hA s hs).1) r hr g hg).2.2

/-- Boundary work and orientation come from surface Stokes, while the
unsigned parameter formula identifies the value with the shrinking average. -/
theorem circulation_from_geometry : circulation_from_geometryType := by
  intro geometry U F x N hU hx hF hN
  obtain ⟨A,hA⟩ := geometry x N hN
  let circulation : ℝ → ℝ := fun r => regionIntegral
    (fun u : Specs.D04.C12.ClassicalIntegralCalibrations.Model.diskParameters r =>
      inner ℝ (curl F (x+A u)) N)
  refine ⟨circulation, ?_, small_closedBalls hU hx,
    planar_curl_average U F x N A hU hx hF⟩
  intro r hr hsub
  obtain ⟨himage,hM,hcompact,hboundary,normal,hnormal,hparameter⟩ := hA r hr
  have hDU : Specs.D04.C12.InfinitesimalFluxAndCirculation.Model.planarDisk x N r ⊆ U :=
    fun y hy => hsub hy.2
  have hg : ContinuousOn (fun y => inner ℝ (curl F y) N)
      (Specs.D04.C12.InfinitesimalFluxAndCirculation.Model.planarDisk x N r) :=
    ((D04.ClassicalSurfaceStokes.curl_continuousOn U hU F hF).mono hDU).inner continuousOn_const
  have hvalue := hparameter (fun y => inner ℝ (curl F y) N) hg
  obtain ⟨o,hcompat,hstokes⟩ := D04.ClassicalSurfaceStokes.surface_stokes hM hcompact normal
  obtain ⟨bO,hout,hpositive,hwork⟩ := hstokes U F hU hDU hF
  have hflux : Specs.D04.C10.SurfaceAssembly.Model.surfaceFlux normal
      (fun y => curl F y) = circulation r := by
    change Specs.D04.C10.SurfaceAssembly.Model.surfaceIntegral _
      (fun y => inner ℝ (curl F y) (normal.toFun y)) = _
    simp only [hnormal]
    exact hvalue
  refine ⟨hM,hcompact,hboundary,?_,hvalue.symm,by positivity⟩
  refine ⟨normal,o,bO,hnormal,hcompat,hout,?_⟩
  exact (congrArg
    (fun I : ℝ => Specs.D04.C12.ClassicalSurfaceStokes.Model.HasBoundaryWorkIntegral bO F I)
    hflux).mp hwork

/-- The circulation density for every center and every unit normal, with
the induced boundary orientation and the positive disk-area normalization. -/
theorem local_circulation : local_circulationType :=
  circulation_from_geometry disk_geometry

end D04.LocalDensities
