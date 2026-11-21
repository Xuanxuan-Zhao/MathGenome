import MathGenome.Internal.MultivariableAnalysis.D04.C03.CrossedPartials
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.MixedPartialExample
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Filter Topology Asymptotics
namespace D04

def mixedPartialExample : Specs.D04.C03.MixedPartialExample.mixedPartialExampleType :=
  Specs.D04.C03.MixedPartialExample.mixedPartialExampleValue

theorem mixedPartialExample_zero : mixedPartialExample 0 = 0 := by
  simp [mixedPartialExample, Specs.D04.C03.MixedPartialExample.mixedPartialExampleValue,
    Specs.D04.C03.MixedPartialExample.Model.mixedPartialExample]

private theorem example_formula (z : E 2) : mixedPartialExample z =
    z 0 * z 1 * (z 0 ^ 2 - z 1 ^ 2) / (z 0 ^ 2 + z 1 ^ 2) := rfl

private theorem norm_sq_plane (z : E 2) : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

private theorem denominator_pos (z : E 2) (hz : z ≠ 0) : 0 < z 0 ^ 2 + z 1 ^ 2 := by
  rw [← norm_sq_plane]
  exact sq_pos_of_pos (norm_pos_iff.mpr hz)

private theorem abs_ratio_le_one (x y : ℝ) : |(x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2)| ≤ 1 := by
  by_cases h : x ^ 2 + y ^ 2 = 0
  · simp [h]
  · have hp : 0 < x ^ 2 + y ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    rw [abs_div, abs_of_pos hp, div_le_one hp, abs_le]
    constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]

theorem mixedPartialExample_bound (z : E 2) :
    |mixedPartialExample z| ≤ |z 0 * z 1| ∧ |z 0 * z 1| ≤ ‖z‖ ^ 2 / 2 := by
  constructor
  · rw [example_formula, mul_div_assoc, abs_mul]
    simpa using mul_le_mul_of_nonneg_left (abs_ratio_le_one (z 0) (z 1)) (abs_nonneg (z 0 * z 1))
  · rw [norm_sq_plane, abs_le]
    constructor <;> nlinarith [sq_nonneg (z 0 - z 1), sq_nonneg (z 0 + z 1)]

private theorem hasFDerivAt_example_zero : HasFDerivAt mixedPartialExample (0 : E 2 →L[ℝ] ℝ) 0 := by
  rw [hasFDerivAt_iff_isLittleO]
  apply isLittleO_iff.mpr
  intro c hc
  filter_upwards [Metric.ball_mem_nhds (0 : E 2) hc] with z hz
  simp only [mixedPartialExample_zero, sub_zero, zero_apply]
  have hz' : ‖z‖ < c := by simpa [Metric.mem_ball, dist_eq_norm] using hz
  rw [Real.norm_eq_abs]
  calc
    |mixedPartialExample z| ≤ ‖z‖ ^ 2 / 2 := (mixedPartialExample_bound z).1.trans (mixedPartialExample_bound z).2
    _ ≤ c * ‖z‖ := by nlinarith [norm_nonneg z]

theorem mixedPartialExample_derivative_zero :
    HasTotalDerivative univ mixedPartialExample 0 0 ∧ totalDerivative mixedPartialExample 0 = 0 := by
  have h := (hasTotalDerivative_iff_hasFDerivAt univ mixedPartialExample 0 0
    isOpen_univ (mem_univ _)).mpr hasFDerivAt_example_zero
  exact ⟨h, totalDerivative_eq univ mixedPartialExample 0 0 h⟩

/-- The two rational coefficients, extended by zero at the origin. -/
private def exampleDx (z : E 2) : ℝ :=
  z 1 * (z 0 ^ 4 + 4 * z 0 ^ 2 * z 1 ^ 2 - z 1 ^ 4) / (z 0 ^ 2 + z 1 ^ 2) ^ 2
private def exampleDy (z : E 2) : ℝ :=
  z 0 * (z 0 ^ 4 - 4 * z 0 ^ 2 * z 1 ^ 2 - z 1 ^ 4) / (z 0 ^ 2 + z 1 ^ 2) ^ 2
private def exampleDifferential (z : E 2) : E 2 →L[ℝ] ℝ :=
  exampleDx z • PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0 +
  exampleDy z • PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1

private theorem exampleDifferential_apply (z h : E 2) :
    exampleDifferential z h = exampleDx z * h 0 + exampleDy z * h 1 := by
  rfl

private theorem example_hasFDerivAt (z : E 2) :
    HasFDerivAt mixedPartialExample (exampleDifferential z) z := by
  by_cases hz : z = 0
  · subst z
    simpa [exampleDifferential, exampleDx, exampleDy] using hasFDerivAt_example_zero
  · have hden : z 0 ^ 2 + z 1 ^ 2 ≠ 0 := ne_of_gt (denominator_pos z hz)
    have hx := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 z (0 : Fin 2)
    have hy := PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 z (1 : Fin 2)
    have hi := (hasFDerivAt_inv hden).comp z ((hx.pow 2).add (hy.pow 2))
    have h := ((hx.mul hy).mul ((hx.pow 2).sub (hy.pow 2))).mul hi
    convert h using 1
    · funext v
      exact div_eq_mul_inv _ _
    · ext v
      simp [exampleDifferential_apply, exampleDx, exampleDy,
        PiLp.proj_apply, smul_eq_mul,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
      field_simp [hden]
      ring

private theorem coefficient_ratio_bound (x y : ℝ) :
    |(x ^ 4 + 4 * x ^ 2 * y ^ 2 - y ^ 4) / (x ^ 2 + y ^ 2) ^ 2| ≤ 3 ∧
    |(x ^ 4 - 4 * x ^ 2 * y ^ 2 - y ^ 4) / (x ^ 2 + y ^ 2) ^ 2| ≤ 3 := by
  by_cases h : x ^ 2 + y ^ 2 = 0
  · simp [h]
  · have hp : 0 < (x ^ 2 + y ^ 2) ^ 2 := sq_pos_of_ne_zero h
    have hxy : 0 ≤ x ^ 2 * y ^ 2 := mul_nonneg (sq_nonneg x) (sq_nonneg y)
    constructor <;> rw [abs_le] <;> constructor
    all_goals first
      | rw [le_div_iff₀ hp]; nlinarith [sq_nonneg (x ^ 2), sq_nonneg (y ^ 2)]
      | rw [div_le_iff₀ hp]; nlinarith [sq_nonneg (x ^ 2), sq_nonneg (y ^ 2)]

private theorem exampleDx_bound (z : E 2) : |exampleDx z| ≤ 3 * |z 1| := by
  rw [exampleDx, mul_div_assoc, abs_mul, mul_comm 3]
  exact mul_le_mul_of_nonneg_left (coefficient_ratio_bound (z 0) (z 1)).1 (abs_nonneg _)

private theorem exampleDy_bound (z : E 2) : |exampleDy z| ≤ 3 * |z 0| := by
  rw [exampleDy, mul_div_assoc, abs_mul, mul_comm 3]
  exact mul_le_mul_of_nonneg_left (coefficient_ratio_bound (z 0) (z 1)).2 (abs_nonneg _)

private theorem exampleDx_continuous : Continuous exampleDx := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst z
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    refine ⟨ε / 3, by positivity, ?_⟩
    intro w hw
    rw [dist_eq_norm, show exampleDx 0 = 0 by simp [exampleDx], sub_zero, Real.norm_eq_abs]
    have hw' : ‖w‖ < ε / 3 := by simpa [dist_eq_norm] using hw
    have hc : |w 1| ≤ ‖w‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le w 1
    exact (exampleDx_bound w).trans_lt (by nlinarith)
  · have hx := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).continuousAt (x := z)
    have hy := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).continuousAt (x := z)
    exact (hy.mul (((hx.pow 4).add ((continuousAt_const.mul (hx.pow 2)).mul (hy.pow 2))).sub
      (hy.pow 4))).div (((hx.pow 2).add (hy.pow 2)).pow 2)
        (pow_ne_zero 2 (ne_of_gt (denominator_pos z hz)))

private theorem exampleDy_continuous : Continuous exampleDy := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst z
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    refine ⟨ε / 3, by positivity, ?_⟩
    intro w hw
    rw [dist_eq_norm, show exampleDy 0 = 0 by simp [exampleDy], sub_zero, Real.norm_eq_abs]
    have hw' : ‖w‖ < ε / 3 := by simpa [dist_eq_norm] using hw
    have hc : |w 0| ≤ ‖w‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le w 0
    exact (exampleDy_bound w).trans_lt (by nlinarith)
  · have hx := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).continuousAt (x := z)
    have hy := (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).continuousAt (x := z)
    exact (hx.mul (((hx.pow 4).sub ((continuousAt_const.mul (hx.pow 2)).mul (hy.pow 2))).sub
      (hy.pow 4))).div (((hx.pow 2).add (hy.pow 2)).pow 2)
        (pow_ne_zero 2 (ne_of_gt (denominator_pos z hz)))

private theorem example_fderiv (z : E 2) :
    totalDerivative mixedPartialExample z = exampleDifferential z :=
  (example_hasFDerivAt z).fderiv

theorem mixedPartialExample_c1 : CrOn 1 univ mixedPartialExample := by
  change TotalDifferentiableOn univ mixedPartialExample ∧ ContinuousOn (totalDerivative mixedPartialExample) univ
  constructor
  · intro z _
    exact ⟨exampleDifferential z, (hasTotalDerivative_iff_hasFDerivAt univ _ _ z isOpen_univ
      (mem_univ _)).mpr (example_hasFDerivAt z)⟩
  · have h : Continuous exampleDifferential :=
      (exampleDx_continuous.smul continuous_const).add (exampleDy_continuous.smul continuous_const)
    rw [show totalDerivative mixedPartialExample = exampleDifferential from funext example_fderiv]
    exact h.continuousOn

private theorem example_partial_eq (z : E 2) (i : Fin 2) :
    scalarPartialDerivative mixedPartialExample z i = exampleDifferential z (standardBasis 2 i) := by
  exact scalarPartialDerivative_eq univ mixedPartialExample z (exampleDifferential z)
    ((hasTotalDerivative_iff_hasFDerivAt univ _ _ z isOpen_univ (mem_univ _)).mpr (example_hasFDerivAt z)) i

private theorem example_partial_x (z : E 2) :
    scalarPartialDerivative mixedPartialExample z 0 = exampleDx z := by
  rw [example_partial_eq, exampleDifferential_apply]
  simp [standardBasis_apply]
private theorem example_partial_y (z : E 2) :
    scalarPartialDerivative mixedPartialExample z 1 = exampleDy z := by
  rw [example_partial_eq, exampleDifferential_apply]
  simp [standardBasis_apply]

theorem mixedPartialExample_partials_continuous (i : Fin 2) :
    Continuous (fun z => scalarPartialDerivative mixedPartialExample z i) := by
  fin_cases i
  · convert exampleDx_continuous using 1
    funext z
    exact example_partial_x z
  · convert exampleDy_continuous using 1
    funext z
    exact example_partial_y z

private theorem example_hasPartial (z : E 2) (i : Fin 2) :
    HasDirectionalDerivative mixedPartialExample z (standardBasis 2 i)
      (scalarPartialDerivative mixedPartialExample z i) := by
  rw [example_partial_eq]
  exact totalDerivative_hasDirectionalDerivative univ mixedPartialExample z (standardBasis 2 i)
    (exampleDifferential z) ((hasTotalDerivative_iff_hasFDerivAt univ _ _ z isOpen_univ
      (mem_univ _)).mpr (example_hasFDerivAt z))

private theorem exampleDx_axis (y : ℝ) : exampleDx (y • standardBasis 2 1) = -y := by
  simp [exampleDx, PiLp.smul_apply, standardBasis_apply]
  by_cases h : y = 0
  · simp [h]
  · field_simp [h]

private theorem exampleDy_axis (x : ℝ) : exampleDy (x • standardBasis 2 0) = x := by
  simp [exampleDy, PiLp.smul_apply, standardBasis_apply]
  by_cases h : x = 0
  · simp [h]
  · field_simp [h]

theorem mixedPartialExample_axis_partials :
    (∀ y : ℝ, HasDirectionalDerivative mixedPartialExample
      (y • standardBasis 2 1) (standardBasis 2 0) (-y) ∧
      scalarPartialDerivative mixedPartialExample (y • standardBasis 2 1) 0 = -y) ∧
    (∀ x : ℝ, HasDirectionalDerivative mixedPartialExample
      (x • standardBasis 2 0) (standardBasis 2 1) x ∧
      scalarPartialDerivative mixedPartialExample (x • standardBasis 2 0) 1 = x) := by
  constructor
  · intro y
    have he : scalarPartialDerivative mixedPartialExample (y • standardBasis 2 1) 0 = -y := by
      rw [example_partial_x, exampleDx_axis]
    exact ⟨by simpa only [he] using example_hasPartial (y • standardBasis 2 1) 0, he⟩
  · intro x
    have he : scalarPartialDerivative mixedPartialExample (x • standardBasis 2 0) 1 = x := by
      rw [example_partial_y, exampleDy_axis]
    exact ⟨by simpa only [he] using example_hasPartial (x • standardBasis 2 0) 1, he⟩

theorem mixedPartialExample_mixed_partials :
    HasDirectionalDerivative (fun z => scalarPartialDerivative mixedPartialExample z 0)
        0 (standardBasis 2 1) (-1) ∧
    HasDirectionalDerivative (fun z => scalarPartialDerivative mixedPartialExample z 1)
        0 (standardBasis 2 0) 1 ∧
    scalarPartialDerivative (fun z => scalarPartialDerivative mixedPartialExample z 0) 0 1 = -1 ∧
    scalarPartialDerivative (fun z => scalarPartialDerivative mixedPartialExample z 1) 0 0 = 1 := by
  have hx : HasDirectionalDerivative (fun z => scalarPartialDerivative mixedPartialExample z 0)
      0 (standardBasis 2 1) (-1) := by
    apply (hasDirectionalDerivative_iff_hasDerivAt _ _ _ _).mpr
    have he : (fun t : ℝ => scalarPartialDerivative mixedPartialExample
        (0 + t • standardBasis 2 1) 0) = fun t => -t := by
      funext t
      simpa using (mixedPartialExample_axis_partials.1 t).2
    rw [he]
    exact (hasDerivAt_id (0 : ℝ)).neg
  have hy : HasDirectionalDerivative (fun z => scalarPartialDerivative mixedPartialExample z 1)
      0 (standardBasis 2 0) 1 := by
    apply (hasDirectionalDerivative_iff_hasDerivAt _ _ _ _).mpr
    have he : (fun t : ℝ => scalarPartialDerivative mixedPartialExample
        (0 + t • standardBasis 2 0) 1) = fun t => t := by
      funext t
      simpa using (mixedPartialExample_axis_partials.2 t).2
    rw [he]
    exact hasDerivAt_id (0 : ℝ)
  exact ⟨hx, hy, directionalDerivative_eq _ _ _ _ hx, directionalDerivative_eq _ _ _ _ hy⟩

open private crossed_directional_derivatives from MathGenome.Internal.MultivariableAnalysis.D04.C03.CrossedPartials

/-- The pointwise theorem's total differentiability hypothesis fails, despite
continuous first partials and existence of both crossed partials. -/
theorem mixedPartialExample_not_all_partials_differentiable :
    ¬ ∀ i : Fin 2, TotalDifferentiableAt univ
      (fun z => scalarPartialDerivative mixedPartialExample z i) 0 := by
  intro h
  obtain ⟨A, hA⟩ := h 0
  obtain ⟨B, hB⟩ := h 1
  have he := crossed_directional_derivatives mixedPartialExample
    (fun z => scalarPartialDerivative mixedPartialExample z 0)
    (fun z => scalarPartialDerivative mixedPartialExample z 1) A B 0
    (standardBasis 2 0) (standardBasis 2 1)
    (by simp [standardBasis]) (by simp [standardBasis])
    (Eventually.of_forall (fun z => ⟨example_hasPartial z 0, example_hasPartial z 1⟩))
    ((hasTotalDerivative_iff_hasFDerivAt univ _ _ 0 isOpen_univ (mem_univ _)).mp hA)
    ((hasTotalDerivative_iff_hasFDerivAt univ _ _ 0 isOpen_univ (mem_univ _)).mp hB)
  have hx := totalDerivative_directionalDerivative univ
    (fun z => scalarPartialDerivative mixedPartialExample z 0) 0 (standardBasis 2 1) A hA
  have hy := totalDerivative_directionalDerivative univ
    (fun z => scalarPartialDerivative mixedPartialExample z 1) 0 (standardBasis 2 0) B hB
  change scalarPartialDerivative (fun z => scalarPartialDerivative mixedPartialExample z 0) 0 1 = _ at hx
  change scalarPartialDerivative (fun z => scalarPartialDerivative mixedPartialExample z 1) 0 0 = _ at hy
  rw [mixedPartialExample_mixed_partials.2.2.1] at hx
  rw [mixedPartialExample_mixed_partials.2.2.2] at hy
  linarith

/-- Differentiating evaluation of D¹f would differentiate each scalar partial. -/
theorem mixedPartialExample_not_twice_differentiable :
    ¬ TimesDifferentiableAt 2 univ mixedPartialExample 0 := by
  intro hf
  apply mixedPartialExample_not_all_partials_differentiable
  intro i
  let ev : Differential (E 2) ℝ 1 →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ _ _ (fun _ => standardBasis 2 i)
  have hev : DifferentiableAt ℝ (fun z => higherDifferential 1 mixedPartialExample z
      (fun _ => standardBasis 2 i)) 0 :=
    ev.differentiableAt.comp 0 (timesDifferentiableAt_hasFDerivAt 1 univ mixedPartialExample 0 hf).differentiableAt
  apply (totalDifferentiableAt_iff_differentiableAt univ _ 0 isOpen_univ (mem_univ _)).mpr
  have he : (fun z => scalarPartialDerivative mixedPartialExample z i) =
      (fun z => higherDifferential 1 mixedPartialExample z (fun _ => standardBasis 2 i)) := by
    funext z
    change _ = iteratedFDeriv ℝ 1 mixedPartialExample z (fun _ => standardBasis 2 i)
    rw [iteratedFDeriv_one_apply, example_partial_eq, ← example_fderiv]
    rfl
  rw [he]
  exact hev

end D04
