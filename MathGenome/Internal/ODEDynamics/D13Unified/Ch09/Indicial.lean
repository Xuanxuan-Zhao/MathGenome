import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch09.Indicial

/-! Indicial polynomial and fixed-branch complex powers (paper.tex 9.3).
The canonical objects in Specs are shared with all subsequent chapter 9 goals.
The solution and independence predicates retain the branch's domain. -/

noncomputable section

namespace D13Unified.Ch09.Indicial

open Specs.D13Unified.Ch09.Indicial

abbrev RegularSingularEquation := Equation
abbrev SlitLogBranch := LogBranch

def taylorCoefficient : taylorCoefficientType := taylorCoefficientValue

def pZero : pZeroType := pZeroValue

def qZero : qZeroType := qZeroValue

def indicialPolynomial : indicialPolynomialType := indicialPolynomialValue

def indicial : indicialType := indicialValue

def slitDisc : slitDiscType := slitDiscValue

def power : powerType := @powerValue

def IsSolution : solutionType := solutionValue

def IndependentOn : independentType := @independentValue

private theorem baseDisc_simplyConnected (R : ℝ) (hR : 0 < R) :
    IsSimplyConnected (Metric.ball (0 : ℂ) R ∩ Complex.slitPlane) := by
  have hc : (↑(R / 2) : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    simp only [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos (half_pos hR)]
    exact half_lt_self hR
  have hs := ((convex_ball (0 : ℂ) R).starConvex hc).inter
    (Complex.starConvex_ofReal_slitPlane (half_pos hR))
  have hn : (Metric.ball (0 : ℂ) R ∩ Complex.slitPlane).Nonempty :=
    ⟨↑(R / 2), hc, Complex.ofReal_mem_slitPlane.mpr (half_pos hR)⟩
  exact @SimplyConnectedSpace.ofContractible _ _ (hs.contractibleSpace hn)

private theorem rotation_norm (angle : ℝ) (z : ℂ) : ‖rotation angle z‖ = ‖z‖ := by
  simp [rotation, Complex.norm_exp]

private theorem slitDisc_open (R angle : ℝ) : IsOpen (slitDiscValue R angle) :=
  (rotation angle).isOpenMap _ (Metric.isOpen_ball.inter Complex.isOpen_slitPlane)

private theorem slitDisc_subset (R angle : ℝ) :
    slitDiscValue R angle ⊆ Metric.ball 0 R := by
  rintro z ⟨w, hw, rfl⟩
  simpa only [Metric.mem_ball, dist_zero_right, rotation_norm] using hw.1

private theorem slitDisc_ne_zero (R angle : ℝ) :
    ∀ z ∈ slitDiscValue R angle, z ≠ 0 := by
  rintro z ⟨w, hw, rfl⟩
  change Complex.exp _ * w ≠ 0
  exact mul_ne_zero (Complex.exp_ne_zero _) (Complex.slitPlane_ne_zero hw.2)

private theorem rotated_mem_slitPlane {R angle : ℝ} {z : ℂ}
    (hz : z ∈ slitDiscValue R angle) : (rotation angle).symm z ∈ Complex.slitPlane := by
  rcases hz with ⟨w, hw, rfl⟩
  simpa using hw.2

/-- Explicitly construct a branch on every rotated slit disc. The selection of
this example does not constrain the `LogBranch` parameter of later results. -/
private def principalBranch (R angle : ℝ) : LogBranch R where
  angle := angle
  log := principalBranchExpected angle
  holomorphic := by
    intro z hz
    apply DifferentiableWithinAt.add (differentiableWithinAt_const _)
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.clog _ (rotated_mem_slitPlane hz)
    change DifferentiableAt ℂ (fun z : ℂ => _ * z) z
    exact (differentiableAt_const _).mul differentiableAt_id
  exp_log := by
    intro z hz
    change Complex.exp ((angle : ℂ) * Complex.I + Complex.log ((rotation angle).symm z)) = z
    rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero
      (rotated_mem_slitPlane hz))]
    exact (rotation angle).apply_symm_apply z

/-- All defining identities and the genuine topology of the chosen domain. -/
theorem setup : setupType := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E
    simp [pZeroValue, qZeroValue, taylorCoefficientValue, iteratedDeriv_zero]
  · intro E r
    simp [indicialPolynomialValue, indicialValue]
  · intro R angle hR
    refine ⟨slitDisc_open R angle, ?_, slitDisc_subset R angle, slitDisc_ne_zero R angle⟩
    exact (rotation angle).isSimplyConnected_image.mpr (baseDisc_simplyConnected R hR)
  · intro R b r
    constructor
    · exact Complex.differentiable_exp.comp_differentiableOn (b.holomorphic.const_mul r)
    · intro z _hz
      exact Complex.exp_ne_zero _

/-- Taylor's theorem on the original whole disc, including its center. -/
theorem coefficientExpansion : coefficientExpansionType := by
  intro E z hz
  constructor
  · convert Complex.hasSum_taylorSeries_on_ball E.p_holomorphic hz using 1
    funext n
    simp only [taylorCoefficientValue, sub_zero, smul_eq_mul]
    ring
  · convert Complex.hasSum_taylorSeries_on_ball E.q_holomorphic hz using 1
    funext n
    simp only [taylorCoefficientValue, sub_zero, smul_eq_mul]
    ring

theorem branchExists : branchExistsType := by
  intro R angle
  exact ⟨principalBranch R angle, rfl, rfl⟩

end D13Unified.Ch09.Indicial
