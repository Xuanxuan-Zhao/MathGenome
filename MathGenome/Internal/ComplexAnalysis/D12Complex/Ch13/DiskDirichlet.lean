import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.DiskDirichlet
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.PoissonHarmonic
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Tactic.Abel
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Complex Metric Real Filter Set InnerProductSpace
open scoped Topology

namespace D12Complex.DiskDirichlet
open PoissonHarmonic

def closedPoissonIntegral (R : ℝ) (φ : ℂ → ℝ) (z : ℂ) : ℝ :=
  if ‖z‖ < R then poissonIntegral R φ z else φ z

lemma closedPoissonIntegral_eq_interior {R : ℝ} (φ : ℂ → ℝ) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) : closedPoissonIntegral R φ z = poissonIntegral R φ z := by
  simp only [closedPoissonIntegral, ite_eq_left (show ‖z‖ < R by simpa using hz)]

lemma closedPoissonIntegral_eq_boundary {R : ℝ} (φ : ℂ → ℝ) {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) R) : closedPoissonIntegral R φ z = φ z := by
  have hn : ‖z‖ = R := by simpa using hz
  simp [closedPoissonIntegral, hn]

theorem harmonic_poisson_representation :
    Specs.D12Complex.Ch13.DiskDirichlet.harmonic_poisson_representation_type := by
  intro U u a R hu hR hsub z hz
  have hh := (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd U u hu.1).mp hu
  have h := (hh.mono hsub).circleAverage_poissonKernel_smul hz
  rw [← h]
  simp only [circleAverage_def, smul_eq_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only [Pi.mul_apply]
  rw [poissonKernel_def]
  rw [show ‖circleMap a R t - a‖ = R by simp [abs_of_pos hR]]
  congr 2
  congr 1
  abel_nf

lemma dirichlet_representation {R : ℝ} {u : ℂ → ℝ} (_hR : 0 < R)
    (hc : ContinuousOn u (closedBall 0 R)) (hu : HarmonicOn (ball 0 R) u)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) : poissonIntegral R u z = u z := by
  have hh := (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ isOpen_ball).mp hu
  rw [poissonIntegral_eq_circleAverage]
  exact (HarmonicContOnCl.mk_ball hh hc).circleAverage_poissonKernel_smul hz

theorem disk_dirichlet_unique :
    Specs.D12Complex.Ch13.DiskDirichlet.disk_dirichlet_unique_type := by
  intro R φ u hR _ hc hu hb z hz
  change u z = closedPoissonIntegral R φ z
  by_cases hzi : z ∈ ball (0 : ℂ) R
  · rw [closedPoissonIntegral_eq_interior φ hzi, ← dirichlet_representation hR hc hu hzi]
    rw [poissonIntegral_eq_circleAverage, poissonIntegral_eq_circleAverage]
    apply circleAverage_congr_sphere
    intro ζ hζ
    have hζ' : ζ ∈ sphere (0 : ℂ) R := by simpa [abs_of_pos hR] using hζ
    change poissonKernel 0 z ζ * u ζ = poissonKernel 0 z ζ * φ ζ
    rw [hb hζ']
  · have hzs : z ∈ sphere (0 : ℂ) R := by
      simp only [mem_ball, mem_closedBall, mem_sphere] at *
      exact le_antisymm hz (le_of_not_gt hzi)
    rw [closedPoissonIntegral_eq_boundary φ hzs]
    exact hb hzs

lemma kernel_continuousOn {R : ℝ} (_hR : 0 < R) {z : ℂ} (hz : ‖z‖ < R) :
    ContinuousOn (kernel R z) (sphere (0 : ℂ) R) := by
  apply continuousOn_const.div ((continuous_id.sub continuous_const).norm.pow 2).continuousOn
  intro ζ hζ
  apply pow_ne_zero
  apply norm_ne_zero_iff.mpr
  intro he
  change ζ - z = 0 at he
  have heq : ζ = z := sub_eq_zero.mp he
  have hnorm : ‖ζ‖ = R := by simpa using hζ
  rw [heq] at hnorm
  exact hz.ne hnorm

lemma average_kernel {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ < R) :
    circleAverage (kernel R z) 0 R = 1 := kernel_normalized R hR z hz

/-- A pointwise near/far estimate avoids using discontinuous cutoff functions
in the boundary-limit proof. -/
lemma boundary_error_bound {R : ℝ} {φ : ℂ → ℝ} (hR : 0 < R)
    (hφ : ContinuousOn φ (sphere 0 R)) {ξ : ℂ}
    {ε δ M : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hnear : ∀ ζ ∈ sphere (0 : ℂ) R, dist ζ ξ < δ → |φ ζ - φ ξ| ≤ ε)
    (hbound : ∀ ζ ∈ sphere (0 : ℂ) R, |φ ζ - φ ξ| ≤ M)
    {z : ℂ} (hz : ‖z‖ < R) (hzξ : dist z ξ < δ / 2) :
    |poissonIntegral R φ z - φ ξ| ≤
      ε + (M / (δ / 2) ^ 2) * (R ^ 2 - ‖z‖ ^ 2) := by
  have hk := kernel_continuousOn hR hz
  have hfi : CircleIntegrable (fun ζ => kernel R z ζ * (φ ζ - φ ξ)) 0 R :=
    (hk.mul (hφ.sub continuousOn_const)).circleIntegrable hR.le
  have hav : poissonIntegral R φ z - φ ξ =
      circleAverage (fun ζ => kernel R z ζ * (φ ζ - φ ξ)) 0 R := by
    calc
      _ = circleAverage (fun ζ => kernel R z ζ * φ ζ) 0 R -
          circleAverage (fun ζ => (φ ξ) * kernel R z ζ) 0 R := by
        rw [show circleAverage (fun ζ => φ ξ * kernel R z ζ) 0 R = φ ξ by
          simpa [smul_eq_mul, average_kernel hR hz] using
            (circleAverage_fun_smul (a := φ ξ) (f := kernel R z) (c := 0) (R := R))]
        rfl
      _ = _ := by
        rw [← circleAverage_fun_sub (f₁ := fun ζ => kernel R z ζ * φ ζ)
          (f₂ := fun ζ => φ ξ * kernel R z ζ)
          ((hk.mul hφ).circleIntegrable hR.le)
          ((continuousOn_const.mul hk).circleIntegrable hR.le)]
        congr 1
        ext ζ
        ring
  rw [hav]
  apply abs_circleAverage_le_circleAverage_abs.trans
  have hn : 0 ≤ R ^ 2 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hd2 : 0 < (δ / 2) ^ 2 := sq_pos_of_pos (by linarith)
  have hCi : CircleIntegrable (fun ζ => ε * kernel R z ζ +
      (M / (δ / 2) ^ 2) * (R ^ 2 - ‖z‖ ^ 2)) 0 R :=
    ((continuousOn_const.mul hk).add continuousOn_const).circleIntegrable hR.le
  calc
    circleAverage |fun ζ => kernel R z ζ * (φ ζ - φ ξ)| 0 R ≤
        circleAverage (fun ζ => ε * kernel R z ζ +
          (M / (δ / 2) ^ 2) * (R ^ 2 - ‖z‖ ^ 2)) 0 R := by
      apply circleAverage_mono hfi.abs hCi
      intro ζ hζ
      have hζ' : ζ ∈ sphere (0 : ℂ) R := by simpa [abs_of_pos hR] using hζ
      have hnζ : ‖ζ‖ = R := by simpa using hζ'
      have hkp : 0 ≤ kernel R z ζ := (kernel_positive R hR z ζ hz hnζ).le
      change |kernel R z ζ * (φ ζ - φ ξ)| ≤ _
      rw [abs_mul, abs_of_nonneg hkp]
      by_cases hclose : dist ζ ξ < δ
      · have hb := mul_le_mul_of_nonneg_left (hnear ζ hζ' hclose) hkp
        have hnon : 0 ≤ (M / (δ / 2) ^ 2) * (R ^ 2 - ‖z‖ ^ 2) :=
          mul_nonneg (div_nonneg hM hd2.le) hn
        nlinarith
      · have hdist : δ / 2 ≤ ‖ζ - z‖ := by
          have ht := dist_triangle ζ z ξ
          have hfar : δ ≤ dist ζ ξ := le_of_not_gt hclose
          have hdist' : δ / 2 ≤ dist ζ z := by linarith
          simpa only [dist_eq_norm] using hdist'
        have hsq : (δ / 2) ^ 2 ≤ ‖ζ - z‖ ^ 2 := by nlinarith [norm_nonneg (ζ - z)]
        have hkbound : kernel R z ζ * |φ ζ - φ ξ| ≤
            (M / (δ / 2) ^ 2) * (R ^ 2 - ‖z‖ ^ 2) := by
          calc
            _ ≤ kernel R z ζ * M := mul_le_mul_of_nonneg_left (hbound ζ hζ') hkp
            _ = M * ((R ^ 2 - ‖z‖ ^ 2) / ‖ζ - z‖ ^ 2) := by unfold kernel; ring
            _ ≤ M * ((R ^ 2 - ‖z‖ ^ 2) / (δ / 2) ^ 2) := by
              gcongr
            _ = _ := by ring
        exact hkbound.trans (le_add_of_nonneg_left (mul_nonneg hε hkp))
    _ = _ := by
      rw [circleAverage_fun_add (f₁ := fun ζ => ε * kernel R z ζ)
        (f₂ := fun _ : ℂ => (M / (δ / 2) ^ 2) * (R ^ 2 - ‖z‖ ^ 2))
        ((continuousOn_const.mul hk).circleIntegrable hR.le)
        (circleIntegrable_const _ _ _), circleAverage_const]
      have he : circleAverage (fun ζ => ε * kernel R z ζ) 0 R = ε := by
        simpa [smul_eq_mul, average_kernel hR hz] using
          (circleAverage_fun_smul (a := ε) (f := kernel R z) (c := 0) (R := R))
      rw [he]

theorem poissonIntegral_boundary_limit :
    Specs.D12Complex.Ch13.DiskDirichlet.poissonIntegral_boundary_limit_type := by
  intro R φ hR hφ ξ hξ
  change Tendsto (poissonIntegral R φ) (𝓝[ball 0 R] ξ) (𝓝 (φ ξ))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hnear⟩ := (Metric.continuousWithinAt_iff.mp (hφ ξ hξ)) (ε / 2) (by linarith)
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) R).exists_bound_of_continuousOn
    (hφ.sub (continuousOn_const (c := φ ξ)))
  let C := max M 0 / (δ / 2) ^ 2
  have hlim : Tendsto (fun z : ℂ => C * (R ^ 2 - ‖z‖ ^ 2)) (𝓝 ξ) (𝓝 0) := by
    have hnξ : ‖ξ‖ = R := by simpa using hξ
    convert (continuous_const.mul (continuous_const.sub (continuous_norm.pow 2))).continuousAt.tendsto (x := ξ) using 1
    simp [hnξ]
  have hevent := hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hevent,
    nhdsWithin_le_nhds (ball_mem_nhds ξ (show 0 < δ / 2 by linarith))]
    with z hz he hzξ
  have hbound := boundary_error_bound hR hφ (ξ := ξ) (ε := ε / 2)
    (by linarith) hδ (le_max_right M 0)
    (fun ζ hζ hd => (by simpa [Real.dist_eq] using hnear hζ hd : |φ ζ - φ ξ| < ε / 2).le)
    (fun ζ hζ => (by simpa [Real.norm_eq_abs] using hM ζ hζ : |φ ζ - φ ξ| ≤ M).trans (le_max_left _ _))
    (show ‖z‖ < R by simpa using hz) (show dist z ξ < δ / 2 from hzξ)
  rw [Real.dist_eq]
  change |poissonIntegral R φ z - φ ξ| < ε
  linarith

lemma closedPoissonIntegral_harmonic {R : ℝ} {φ : ℂ → ℝ}
    (hR : 0 < R) (hφ : ContinuousOn φ (sphere 0 R)) :
    HarmonicOn (ball 0 R) (closedPoissonIntegral R φ) := by
  apply (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ isOpen_ball).mpr
  have hp := (HarmonicFoundation.harmonicOn_iff_harmonicOnNhd _ _ isOpen_ball).mp
    (poissonIntegral_harmonic R φ hR hφ)
  intro z hz
  have heq : poissonIntegral R φ =ᶠ[𝓝 z] closedPoissonIntegral R φ := by
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact (closedPoissonIntegral_eq_interior φ hw).symm
  exact (harmonicAt_congr_nhds heq).mp (hp z hz)

theorem closedPoissonIntegral_solution :
    Specs.D12Complex.Ch13.DiskDirichlet.closedPoissonIntegral_solution_type := by
  intro R φ hR hφ
  change ContinuousOn (closedPoissonIntegral R φ) (closedBall 0 R) ∧
    HarmonicOn (ball 0 R) (closedPoissonIntegral R φ) ∧
    EqOn (closedPoissonIntegral R φ) φ (sphere 0 R) ∧
    EqOn (closedPoissonIntegral R φ) (poissonIntegral R φ) (ball 0 R)
  have hh := closedPoissonIntegral_harmonic hR hφ
  refine ⟨?_, hh, (fun _ hz => closedPoissonIntegral_eq_boundary φ hz),
    (fun _ hz => closedPoissonIntegral_eq_interior φ hz)⟩
  intro z hz
  by_cases hi : z ∈ ball (0 : ℂ) R
  · exact ((hh.2.1.continuousOn z hi).continuousAt (isOpen_ball.mem_nhds hi)).continuousWithinAt
  · have hs : z ∈ sphere (0 : ℂ) R := by
      simp only [mem_ball, mem_closedBall, mem_sphere] at *
      exact le_antisymm hz (le_of_not_gt hi)
    rw [← ball_union_sphere]
    apply ContinuousWithinAt.union
    · change Tendsto (closedPoissonIntegral R φ) (𝓝[ball 0 R] z)
        (𝓝 (closedPoissonIntegral R φ z))
      rw [closedPoissonIntegral_eq_boundary φ hs]
      have heq : poissonIntegral R φ =ᶠ[𝓝[ball 0 R] z] closedPoissonIntegral R φ := by
        filter_upwards [self_mem_nhdsWithin] with w hw
        exact (closedPoissonIntegral_eq_interior φ hw).symm
      exact (poissonIntegral_boundary_limit R φ hR hφ z hs).congr' heq
    · exact (hφ z hs).congr (fun _ hw => closedPoissonIntegral_eq_boundary φ hw)
        (closedPoissonIntegral_eq_boundary φ hs)

end D12Complex.DiskDirichlet
