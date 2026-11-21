import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.WeakStrongAnalyticity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07UniformBoundedness
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
Weak and strong analyticity. The first step applies uniform boundedness to
point evaluations of the vector difference quotients on the dual. Each scalar
quotient extends continuously across its center and is bounded on a compact
disk. This proves norm continuity without assuming it. Scalar Cauchy formulas
then give the vector Cauchy formula by separation; differentiation of the
Cauchy integral gives norm holomorphy and hence a norm power series.
-/

namespace ExpandedFA.BanachAlgebra.WeakStrongAnalyticity

open Set Metric Filter Complex
open scoped Topology

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X]
  {U : Set ℂ} {f : ℂ → X}

/-- Weak holomorphy implies norm continuity, even without completeness of `X`. -/
theorem continuousOn_of_dual_differentiableOn (hU : IsOpen U)
    (hf : ∀ ℓ : X →L[ℂ] ℂ, DifferentiableOn ℂ (ℓ ∘ f) U) :
    ContinuousOn f U := by
  intro a ha
  obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds ha)
  let T : closedBall a R → (X →L[ℂ] ℂ) →L[ℂ] ℂ :=
    fun z => NormedSpace.inclusionInDoubleDual ℂ X (slope f a z)
  have hpoint : ∀ ℓ : X →L[ℂ] ℂ, ∃ C : ℝ, ∀ z, ‖T z ℓ‖ ≤ C := by
    intro ℓ
    have hc : ContinuousOn (dslope (ℓ ∘ f) a) (closedBall a R) :=
      (continuousOn_dslope (closedBall_mem_nhds a hR)).mpr
        ⟨((hf ℓ).continuousOn).mono hRU,
          (hf ℓ a ha).differentiableAt (hU.mem_nhds ha)⟩
    obtain ⟨C, hC⟩ := (isCompact_closedBall a R).exists_bound_of_continuousOn hc
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : (z : ℂ) = a
    · simp [T, hz]
    · have he : T z ℓ = dslope (ℓ ∘ f) a z := by
        rw [dslope_of_ne _ hz]
        exact (ℓ.toLinearMap.slope_comp f a z).symm
      rw [he]
      exact (hC z z.property).trans (le_max_left _ _)
  obtain ⟨C, hC, hCT⟩ :=
    ExpandedFA.P1.C07UniformBoundedness.uniform_boundedness ℂ
      (X →L[ℂ] ℂ) ℂ (closedBall a R) T hpoint
  have hbound (z : ℂ) (hz : z ∈ closedBall a R) :
      ‖f z - f a‖ ≤ ‖z - a‖ * C := by
    have hs : ‖slope f a z‖ ≤ C := by
      rw [← (NormedSpace.inclusionInDoubleDualLi ℂ).norm_map (slope f a z)]
      exact hCT ⟨z, hz⟩
    calc
      ‖f z - f a‖ = ‖(z - a) • slope f a z‖ := by simp only [sub_smul_slope, vsub_eq_sub]
      _ = ‖z - a‖ * ‖slope f a z‖ := norm_smul _ _
      _ ≤ ‖z - a‖ * C := mul_le_mul_of_nonneg_left hs (norm_nonneg _)
  have hcont : ContinuousAt f a := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨min R (ε / (C + 1)), lt_min hR (div_pos hε (by linarith)), ?_⟩
    intro z hz
    have hzR : z ∈ closedBall a R := (lt_min_iff.mp hz).1.le
    have hzε : ‖z - a‖ < ε / (C + 1) := by
      simpa [dist_eq_norm] using (lt_min_iff.mp hz).2
    calc
      dist (f z) (f a) = ‖f z - f a‖ := dist_eq_norm _ _
      _ ≤ ‖z - a‖ * C := hbound z hzR
      _ ≤ ‖z - a‖ * (C + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _ < ε := (lt_div_iff₀ (by linarith : 0 < C + 1)).mp hzε
  exact hcont.continuousWithinAt

/-- Continuous linear functionals commute with a circle integral. -/
theorem dual_circleIntegral [CompleteSpace X] (ℓ : X →L[ℂ] ℂ)
    {g : ℂ → X} {c : ℂ} {R : ℝ} (hg : CircleIntegrable g c R) :
    ℓ (∮ z in C(c, R), g z) = ∮ z in C(c, R), ℓ (g z) := by
  simp only [circleIntegral]
  rw [← ℓ.intervalIntegral_comp_comm hg.out]
  simp only [map_smul]

/-- Scalar Cauchy formulas determine the vector Cauchy formula by separation. -/
theorem circleIntegral_eq_of_dual_differentiableOn [CompleteSpace X]
    (hU : IsOpen U)
    (hf : ∀ ℓ : X →L[ℂ] ℂ, DifferentiableOn ℂ (ℓ ∘ f) U)
    {c w : ℂ} {R : ℝ} (hR : 0 < R) (hRU : closedBall c R ⊆ U)
    (hw : w ∈ ball c R) :
    (∮ z in C(c, R), (z - w)⁻¹ • f z) = (2 * Real.pi * I : ℂ) • f w := by
  have hfi : CircleIntegrable f c R :=
    ((continuousOn_of_dual_differentiableOn hU hf).mono
      (sphere_subset_closedBall.trans hRU)).circleIntegrable hR.le
  have hws : w ∉ sphere c |R| := by
    simpa only [mem_sphere, abs_of_pos hR] using ne_of_lt (mem_ball.mp hw)
  have hki : CircleIntegrable (fun z => (z - w)⁻¹ • f z) c R := by
    simpa only [zpow_neg_one] using hfi.sub_zpow_smul (-1) hws
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro ℓ
  rw [dual_circleIntegral ℓ hki, map_smul]
  simp only [map_smul]
  exact ((hf ℓ).mono hRU).circleIntegral_sub_inv_smul hw

/-- Weak holomorphy on an arbitrary open set implies norm holomorphy. -/
theorem differentiableOn_of_dual_differentiableOn [CompleteSpace X]
    (hU : IsOpen U)
    (hf : ∀ ℓ : X →L[ℂ] ℂ, DifferentiableOn ℂ (ℓ ∘ f) U) :
    DifferentiableOn ℂ f U := by
  intro a ha
  obtain ⟨R, hR, hRU⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds ha)
  have hfi : CircleIntegrable f a R :=
    ((continuousOn_of_dual_differentiableOn hU hf).mono
      (sphere_subset_closedBall.trans hRU)).circleIntegrable hR.le
  have has : a ∉ sphere a |R| := by
    simpa only [mem_sphere, dist_self, abs_of_pos hR] using hR.ne
  have hd := (hasDerivAt_circleIntegral_sub_inv_smul hfi has).const_smul
    (2 * Real.pi * I : ℂ)⁻¹
  have he : f =ᶠ[𝓝 a]
      (fun w => (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(a, R), (z - w)⁻¹ • f z) := by
    filter_upwards [ball_mem_nhds a hR] with w hw
    rw [circleIntegral_eq_of_dual_differentiableOn hU hf hR hRU hw]
    have hk : (2 * Real.pi * I : ℂ) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
    exact (inv_smul_smul₀ hk (f w)).symm
  exact (hd.congr_of_eventuallyEq he).differentiableAt.differentiableWithinAt

/-- The full weak/strong analyticity equivalence, with no initial norm regularity. -/
theorem weak_strong_analyticity : Spec.AnalyticityEquivalence.{u} := by
  intro X _ _ _ U f hU
  constructor
  · intro hf ℓ a ha
    exact (ℓ.analyticAt (f a)).comp (hf a ha)
  · intro hf
    exact (differentiableOn_of_dual_differentiableOn hU
      (fun ℓ => (hf ℓ).differentiableOn)).analyticOnNhd hU

end ExpandedFA.BanachAlgebra.WeakStrongAnalyticity
