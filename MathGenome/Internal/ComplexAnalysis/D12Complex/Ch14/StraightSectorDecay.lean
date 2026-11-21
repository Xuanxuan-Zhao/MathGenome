import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.StraightSectorDecay
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch14.SectorPowerChart
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.HarmonicReflection
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch13.LocalConjugateRegularity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith

noncomputable section
open Set Metric Filter
open scoped Topology

namespace D12Complex.StraightSectorDecay

lemma norm_gradient_eq (u : ℂ → ℝ) (z : ℂ) :
    ‖gradient u z‖ = ‖fderiv ℝ u z‖ := by
  exact (InnerProductSpace.toDual ℝ ℂ).symm.norm_map _

/-- A zero of a C¹ function has linear vanishing and bounded real gradient. -/
lemma linear_bounds_of_contDiffOn (U : Set ℂ) (u : ℂ → ℝ) (c : ℂ)
    (hU : IsOpen U) (hu : ContDiffOn ℝ 1 u U) (hc : c ∈ U) (hzero : u c = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧ ball c r ⊆ U ∧
      ∀ z ∈ ball c r, |u z| ≤ C * ‖z-c‖ ∧ ‖gradient u z‖ ≤ C := by
  let C := ‖fderiv ℝ u c‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hcont : ContinuousAt (fun z => ‖fderiv ℝ u z‖) c :=
    ((hu.continuousOn_fderiv_of_isOpen hU (by simp)) c hc).continuousAt
      (hU.mem_nhds hc) |>.norm
  have hb : ∀ᶠ z in 𝓝 c, ‖fderiv ℝ u z‖ < C :=
    hcont.eventually (gt_mem_nhds (by dsimp [C]; linarith))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem (hU.mem_nhds hc) hb)
  have hsubU : ball c r ⊆ U := fun z hz => (hsub hz).1
  have hbound : ∀ z ∈ ball c r, ‖fderiv ℝ u z‖ ≤ C :=
    fun z hz => (hsub hz).2.le
  refine ⟨C, hC, r, hr, hsubU, fun z hz => ⟨?_, ?_⟩⟩
  · have hm := (convex_ball c r).norm_image_sub_le_of_norm_fderiv_le
      (fun w hw => ((hu w (hsubU hw)).contDiffAt
        (hU.mem_nhds (hsubU hw))).differentiableAt (by simp))
      hbound (mem_ball_self hr) hz
    simpa [hzero, Real.norm_eq_abs] using hm
  · rw [norm_gradient_eq]
    exact hbound z hz

/-- Odd reflection only needs continuity on the open diameter, even at its center. -/
lemma halfDisk_decay (R : ℝ) (u : ℂ → ℝ) (hR : 0 < R)
    (hu : HarmonicOn {z : ℂ | ‖z‖ < R ∧ 0 < z.im} u)
    (hcont : ContinuousOn u {z : ℂ | ‖z‖ < R ∧ 0 ≤ z.im})
    (hzero : ∀ z : ℂ, ‖z‖ < R → z.im = 0 → u z = 0) :
    ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      ∀ z : ℂ, ‖z‖ < r → 0 < z.im →
        |u z| ≤ C * ‖z‖ ∧ ‖gradient u z‖ ≤ C := by
  let v := HarmonicReflection.oddReflection u
  have hv : HarmonicOn (ball 0 R) v :=
    HarmonicReflection.harmonic_oddReflection R u hR hu hcont hzero
  obtain ⟨C, hC, r, hr, hsub, hb⟩ := linear_bounds_of_contDiffOn (ball 0 R) v 0
    isOpen_ball (hv.2.1.of_le (by norm_num)) (mem_ball_self hR)
    (HarmonicReflection.oddReflection_of_zero u (by simp))
  refine ⟨C, hC, min r R, lt_min hr hR, min_le_right _ _, ?_⟩
  intro z hz hi
  have he : v =ᶠ[𝓝 z] u := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hi]
      with w hw
    exact HarmonicReflection.oddReflection_of_pos u hw
  have h := hb z (by simpa using lt_of_lt_of_le hz (min_le_left r R))
  rw [he.eq_of_nhds, he.gradient_eq] at h
  simpa using h

/-- Straight-sector corner decay, with no regularity assumed at the vertex. -/
theorem sector_decay : Specs.D12Complex.Ch14.StraightSectorDecay.sector_decay_type := by
  intro θ R u hθ hθ' hR hu hcont hzero
  let α := Real.pi / θ
  let β := θ / Real.pi
  have hα : 0 < α := div_pos Real.pi_pos hθ
  have hβ : 0 < β := div_pos hθ Real.pi_pos
  have hβα : β * α = 1 := by dsimp [α, β]; field_simp
  let T := R ^ α
  have hT : 0 < T := Real.rpow_pos_of_pos hR _
  let v : ℂ → ℝ := u ∘ SectorPowerChart.Q θ
  obtain ⟨hP, hQ, hPm, hQm, hQP, _⟩ :=
    SectorPowerChart.biholomorphic θ R hθ hθ' hR
  have hv : HarmonicOn {w : ℂ | ‖w‖ < T ∧ 0 < w.im} v :=
    HarmonicFoundation.harmonicOn_comp_holomorphic _ _ u _ hu hQ hQm
  have hvc : ContinuousOn v {w : ℂ | ‖w‖ < T ∧ 0 ≤ w.im} :=
    hcont.comp (SectorPowerChart.inverse_continuous θ R hθ hθ' hR)
      (SectorPowerChart.inverse_mapsTo_closure θ R hθ hθ' hR)
  have hvzero : ∀ w : ℂ, ‖w‖ < T → w.im = 0 → v w = 0 := by
    intro w hw hi
    apply hzero
    exact ⟨SectorPowerChart.diameter_frontier θ R hθ hθ' hR w hi hw,
      (SectorPowerChart.inverse_mapsTo_closure θ R hθ hθ' hR ⟨hw, hi.ge⟩).2⟩
  obtain ⟨C, hC, s, hs, hsT, hb⟩ := halfDisk_decay T v hT hv hvc hvzero
  let r := min R (s ^ β)
  have hr : 0 < r := lt_min hR (Real.rpow_pos_of_pos hs _)
  let K := max C (C * α) + 1
  have hK : 0 < K := by dsimp [K]; linarith [le_max_left C (C*α)]
  have hCK : C ≤ K := by dsimp [K]; linarith [le_max_left C (C*α)]
  have hCaK : C * α ≤ K := by dsimp [K]; linarith [le_max_right C (C*α)]
  refine ⟨K, hK, r, hr, min_le_left _ _, ?_⟩
  intro z hz hzr
  have hzR : z ∈ CircularExhaustion.sector θ ∩ ball 0 R :=
    ⟨hz, by simpa using lt_of_lt_of_le hzr (min_le_left R (s^β))⟩
  have hw := hPm hzR
  have hn : ‖SectorPowerChart.P θ z‖ < s := by
    rw [SectorPowerChart.power_norm θ hθ]
    have h := Real.rpow_lt_rpow (norm_nonneg z)
      (lt_of_lt_of_le hzr (min_le_right R (s^β))) hα
    rwa [← Real.rpow_mul hs.le, hβα, Real.rpow_one] at h
  have he : v ∘ SectorPowerChart.P θ =ᶠ[𝓝 z] u := by
    filter_upwards [hu.1.mem_nhds hzR] with y hy
    change u (SectorPowerChart.Q θ (SectorPowerChart.P θ y)) = u y
    rw [hQP hy]
  have hvd : DifferentiableAt ℝ v (SectorPowerChart.P θ z) :=
    ((hv.2.1 _ hw).contDiffAt (hv.1.mem_nhds hw)).differentiableAt (by norm_num)
  have hPd : DifferentiableAt ℝ (SectorPowerChart.P θ) z :=
    (hP.2 z hzR).restrictScalars ℝ
  have hbz := hb (SectorPowerChart.P θ z) hn hw.2
  constructor
  · calc
      |u z| = |v (SectorPowerChart.P θ z)| := congrArg abs he.eq_of_nhds.symm
      _ ≤ C * ‖SectorPowerChart.P θ z‖ := hbz.1
      _ = C * ‖z‖ ^ α := by rw [SectorPowerChart.power_norm θ hθ]
      _ ≤ K * ‖z‖ ^ α := mul_le_mul_of_nonneg_right hCK (Real.rpow_nonneg (norm_nonneg _) _)
  · have hB : ‖fderiv ℝ v (SectorPowerChart.P θ z)‖ ≤ C := by
      simpa only [norm_gradient_eq] using hbz.2
    calc
      ‖gradient u z‖ = ‖fderiv ℝ u z‖ := norm_gradient_eq _ _
      _ = ‖(fderiv ℝ v (SectorPowerChart.P θ z)).comp
          (fderiv ℝ (SectorPowerChart.P θ) z)‖ := by
        rw [← he.fderiv_eq, fderiv_comp z hvd hPd]
      _ ≤ ‖fderiv ℝ v (SectorPowerChart.P θ z)‖ *
          ‖fderiv ℝ (SectorPowerChart.P θ) z‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * ‖fderiv ℝ (SectorPowerChart.P θ) z‖ :=
        mul_le_mul_of_nonneg_right hB (norm_nonneg _)
      _ = (C * α) * ‖z‖ ^ (α - 1) := by
        rw [SectorPowerChart.differential_norm θ hθ hθ' z hz]
        exact (mul_assoc _ _ _).symm
      _ ≤ K * ‖z‖ ^ (α - 1) :=
        mul_le_mul_of_nonneg_right hCaK (Real.rpow_nonneg (norm_nonneg _) _)

end D12Complex.StraightSectorDecay
