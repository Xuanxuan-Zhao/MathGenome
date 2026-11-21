import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch18.Gaussian
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch18.GammaEulerLimit
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch18.Wallis
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch18.GammaDefinition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! The Gamma value is obtained from Euler's one-variable limit and Wallis,
not from a library Gaussian evaluation. The one-dimensional power-substitution
API is used for integrability and for the value on the positive half-line.
Continuous proper integrals are identified with the upstream Darboux integral
before passing to the two independent improper endpoint limits.
-/
noncomputable section
namespace SingleVariableAnalysis.Gaussian
open Filter Set MeasureTheory
open scoped Topology BigOperators
open Riemann Riemann.Improper
namespace G
export Specs.SingleVariableAnalysis.Ch18.Gaussian
  (gaussianKernelType gaussianKernelValue gammaHalf properTruncations squareSubstitution
    positiveHalf negativeHalf wholeLine absoluteConvergence gammaGaussianRelation)
end G

abbrev gaussianKernel : G.gaussianKernelType := G.gaussianKernelValue

def halfProduct (n : ℕ) : ℝ :=
  ∏ j ∈ Finset.range (n + 1), (1 / 2 + (j : ℝ))

theorem halfProduct_positive (n : ℕ) : 0 < halfProduct n := by
  apply Finset.prod_pos
  intro j _
  positivity

theorem halfProduct_coefficient (n : ℕ) :
    halfProduct n = (2 * (n : ℝ) + 1) * Wallis.wallisCoefficient n *
      (n.factorial : ℝ) / 2 := by
  induction n with
  | zero =>
    norm_num [halfProduct, Wallis.wallisCoefficient,
      Specs.SingleVariableAnalysis.Ch18.WallisRecurrence.coefficientValue]
  | succ n ih =>
    have hp : halfProduct (n + 1) = halfProduct n * (1 / 2 + ((n + 1 : ℕ) : ℝ)) :=
      Finset.prod_range_succ _ _
    rw [hp, ih, Nat.factorial_succ]
    push_cast
    have hc := Wallis.wallisCoefficient_step n
    linear_combination -(2 * (n : ℝ) + 3) * (n.factorial : ℝ) / 4 * hc

theorem gamma_half : G.gammaHalf := by
  have hEuler := (SpecialIntegrals.gamma_euler_limit (1 / 2) (by norm_num)).2
  have hnum : Tendsto (fun n : ℕ => (2 * (n : ℝ)) / (2 * n + 1)) atTop (𝓝 1) := by
    simpa [add_comm] using
      tendsto_add_mul_div_add_mul_atTop_nhds (0 : ℝ) 1 2 (d := 2) (by norm_num)
  have hden := Wallis.wallis_coefficient_limit
  change Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * Wallis.wallisCoefficient n)
    atTop (𝓝 (1 / Real.sqrt Real.pi)) at hden
  have h := hnum.div hden (by positivity : 1 / Real.sqrt Real.pi ≠ 0)
  have he : ∀ᶠ n : ℕ in atTop,
      (n.factorial : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) / halfProduct n =
        (2 * (n : ℝ) / (2 * n + 1)) /
          (Real.sqrt (n : ℝ) * Wallis.wallisCoefficient n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    rw [← Real.sqrt_eq_rpow, halfProduct_coefficient]
    have hs := Real.sq_sqrt (Nat.cast_nonneg n)
    have hc := (Wallis.wallisCoefficient_positive n).ne'
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    have hs0 : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
    have h2 : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    nlinarith
  have hv : (1 : ℝ) / (1 / Real.sqrt Real.pi) = Real.sqrt Real.pi := by simp
  rw [hv] at h
  have h' := h.congr' (Filter.EventuallyEq.symm he)
  exact tendsto_nhds_unique hEuler h'

theorem gaussian_continuous : Continuous gaussianKernel := by
  change Continuous (fun x : ℝ => Real.exp (-(x ^ 2)))
  fun_prop

theorem gaussian_positive (x : ℝ) : 0 < gaussianKernel x := Real.exp_pos _

theorem gaussian_even (x : ℝ) : gaussianKernel (-x) = gaussianKernel x := by
  simp [gaussianKernel, G.gaussianKernelValue]

/-- The continuous case of the Darboux/interval-integral bridge, on arbitrary
real compact intervals. It follows from the upstream Darboux Newton–Leibniz
theorem applied to the continuous function's interval-integral primitive. -/
theorem continuous_darboux {f : ℝ → ℝ} (hf : Continuous f)
    {a b : ℝ} (hab : a ≤ b) :
    ∃ h : RealIntegrable f a b, realIntegral f h = ∫ x in a..b, f x := by
  obtain ⟨h, hh⟩ := PTest.integral_of_continuous_derivative hab hf.continuousOn
    (F := fun y => ∫ x in a..y, f x) (fun y _ =>
      intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable _ _)
        hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt)
  exact ⟨h, by simpa using hh⟩

theorem gaussian_proper_truncations : G.properTruncations := by
  intro a b hab
  exact continuous_darboux gaussian_continuous hab

/-- Cancellation of the Jacobian on the positive branch of the square map. -/
theorem gamma_square_kernel (x : ℝ) (hx : 0 < x) :
    gammaKernel (1 / 2) (x ^ 2) * (2 * x) = 2 * gaussianKernel x := by
  have hp : (x ^ 2) ^ (1 / 2 - 1 : ℝ) = x⁻¹ := by
    rw [← Real.rpow_two, ← Real.rpow_mul hx.le]
    norm_num [Real.rpow_neg_one]
  change ((x ^ 2) ^ (1 / 2 - 1 : ℝ) * Real.exp (-(x ^ 2))) * (2 * x) = _
  rw [hp]
  change (x⁻¹ * Real.exp (-(x ^ 2))) * (2 * x) = 2 * Real.exp (-(x ^ 2))
  field_simp

theorem gaussian_square_substitution : G.squareSubstitution := by
  intro a b ha hab
  have hb := ha.trans_le hab
  have hab2 : a ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ ha.le hab 2
  obtain ⟨hg, hgv⟩ := positive_continuous_darboux
    (gammaKernel_continuousAt (1 / 2)) (sq_pos_of_pos ha) hab2
  obtain ⟨hf, hfv⟩ := gaussian_proper_truncations a b hab
  change realIntegral gaussianKernel hf = ∫ x in a..b, gaussianKernel x at hfv
  refine ⟨hg, hf, ?_⟩
  change realIntegral (gammaKernel (1 / 2)) hg = 2 * realIntegral gaussianKernel hf
  rw [hgv, hfv]
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (a := a) (b := b) (f := fun x : ℝ => x ^ 2) (f' := fun x => 2 * x)
    (g := gammaKernel (1 / 2))
    (fun x _ => by simpa using (hasDerivAt_pow 2 x))
    (by fun_prop) (show ContinuousOn (gammaKernel (1 / 2))
      ((fun x : ℝ => x ^ 2) '' uIcc a b) from by
        rintro _ ⟨x, hx, rfl⟩
        rw [uIcc_of_le hab] at hx
        exact (gammaKernel_continuousAt _ _ (sq_pos_of_pos (ha.trans_le hx.1))).continuousWithinAt)
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hab] at hx
  exact gamma_square_kernel x (ha.trans_le hx.1)

/-- Integrability comes from the positive Gamma integral under t = x².
Only a one-dimensional substitution is used. -/
theorem gaussian_integrable_positive : IntegrableOn gaussianKernel (Ioi 0) := by
  have h := (integrableOn_Ioi_comp_rpow_iff' (gammaKernel (1 / 2))
    (by norm_num : (2 : ℝ) ≠ 0)).mpr (gammaKernel_integrable (by norm_num : (0 : ℝ) < 1 / 2))
  simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
    Real.rpow_two, smul_eq_mul] at h
  apply h.congr_fun _ measurableSet_Ioi
  intro x hx
  have he := gamma_square_kernel x hx
  nlinarith

theorem gaussian_positive_measure_value :
    (∫ x in Ioi (0 : ℝ), gaussianKernel x) = Real.sqrt Real.pi / 2 := by
  have hγ : (∫ t in Ioi (0 : ℝ), gammaKernel (1 / 2) t) =
      gammaIntegral (1 / 2) (by norm_num) := by
    have hγval : gammaIntegral (1 / 2) (by norm_num) = Real.Gamma (1 / 2) :=
      gamma_eq_realGamma (1 / 2) (by norm_num)
    rw [hγval, Real.Gamma_eq_integral (by norm_num)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    exact mul_comm _ _
  have hs := integral_comp_rpow_Ioi_of_pos (g := gammaKernel (1 / 2))
    (by norm_num : (0 : ℝ) < 2)
  simp only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
    Real.rpow_two, smul_eq_mul] at hs
  have hv : (∫ x in Ioi (0 : ℝ), 2 * gaussianKernel x) =
      gammaIntegral (1 / 2) (by norm_num) := by
    rw [← hγ, ← hs]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simpa only [mul_comm] using (gamma_square_kernel x hx).symm
  rw [integral_const_mul] at hv
  have hhalf := gamma_half
  change gammaIntegral (1 / 2) (by norm_num) = Real.sqrt Real.pi at hhalf
  linarith

theorem gaussian_positive_half : G.positiveHalf := by
  change RightHasIntegral .real gaussianKernel 0 ⊤ (Real.sqrt Real.pi / 2 : ℝ)
  have hr : RightRegular .real gaussianKernel 0 ⊤ :=
    ⟨WithTop.coe_lt_top _, fun t => (gaussian_proper_truncations 0 t.val t.property.1.le).choose⟩
  apply PTest.right_has_of_tendsto (H := fun t : ℝ => ∫ x in 0..t, gaussianKernel x) hr
    (fun t => (gaussian_proper_truncations 0 t.val t.property.1.le).choose_spec)
  rw [← gaussian_positive_measure_value]
  exact intervalIntegral_tendsto_integral_Ioi 0 gaussian_integrable_positive tendsto_id

theorem gaussian_negative_half : G.negativeHalf := by
  change LeftHasIntegral .real gaussianKernel ⊥ 0 (Real.sqrt Real.pi / 2 : ℝ)
  have hpos : RightHasIntegral .real gaussianKernel 0 ⊤ (Real.sqrt Real.pi / 2 : ℝ) :=
    gaussian_positive_half
  obtain ⟨hr, hlim⟩ := hpos
  have hl : LeftRegular .real gaussianKernel ⊥ 0 :=
    ⟨WithBot.bot_lt_coe _, fun t => (gaussian_proper_truncations t.val 0 t.property.2.le).choose⟩
  refine ⟨hl, fun ε hε => ?_⟩
  obtain ⟨r, hrε⟩ := hlim ε hε
  refine ⟨⟨-r.val, WithBot.bot_lt_coe _, neg_neg_of_pos r.property.1⟩, fun t ht => ?_⟩
  let nt : RightIndex 0 ⊤ :=
    ⟨-t.val, neg_pos.mpr t.property.2, WithTop.coe_lt_top _⟩
  have hnt : r.val < nt.val := by dsimp [nt] at *; linarith
  have he := hrε nt hnt
  have hp : (LeftTruncation .real gaussianKernel ⊥ 0 hl t : ℝ) =
      RightTruncation .real gaussianKernel 0 ⊤ hr nt := by
    change realIntegral gaussianKernel (hl.2 t) = realIntegral gaussianKernel (hr.2 nt)
    have hleft : realIntegral gaussianKernel (hl.2 t) =
        ∫ x in t.val..0, gaussianKernel x :=
      (gaussian_proper_truncations t.val 0 t.property.2.le).choose_spec
    have hright : realIntegral gaussianKernel (hr.2 nt) =
        ∫ x in 0..nt.val, gaussianKernel x :=
      (gaussian_proper_truncations 0 nt.val nt.property.1.le).choose_spec
    rw [hleft, hright]
    have hn := intervalIntegral.integral_comp_neg (f := gaussianKernel) (a := t.val) (b := 0)
    simpa only [gaussian_even, neg_zero] using hn
  change dist (LeftTruncation .real gaussianKernel ⊥ 0 hl t : ℝ) _ < ε
  rw [hp]
  exact he

theorem gaussian_whole_line : G.wholeLine := by
  refine ⟨?_, ⟨0, WithBot.bot_lt_coe _, WithTop.coe_lt_top _⟩,
    Real.sqrt Real.pi / 2, Real.sqrt Real.pi / 2,
    gaussian_negative_half, gaussian_positive_half, ?_⟩
  · intro a b _ hab _
    exact (gaussian_proper_truncations a b hab).choose
  · change (Real.sqrt Real.pi : ℝ) = Real.sqrt Real.pi / 2 + Real.sqrt Real.pi / 2
    ring

theorem gaussian_absolute_convergence : G.absoluteConvergence := by
  have he : (fun x : ℝ => |gaussianKernel x|) = gaussianKernel :=
    funext (fun x => abs_of_pos (gaussian_positive x))
  change HasIntegral .real ((fun x : ℝ => |gaussianKernel x|) : ℝ → ℝ) ⊥ ⊤ _
  rw [he]
  exact gaussian_whole_line

theorem gamma_gaussian_relation : G.gammaGaussianRelation := by
  intro L hL
  have he := right_unique .real gaussianKernel 0 ⊤ L (Real.sqrt Real.pi / 2)
    hL gaussian_positive_half
  rw [he]
  have hhalf := gamma_half
  change gammaIntegral (1 / 2) (by norm_num) = Real.sqrt Real.pi at hhalf
  change gammaIntegral (1 / 2) (by norm_num) = _
  rw [hhalf]
  change (Real.sqrt Real.pi : ℝ) = 2 * (Real.sqrt Real.pi / 2)
  ring

end SingleVariableAnalysis.Gaussian
