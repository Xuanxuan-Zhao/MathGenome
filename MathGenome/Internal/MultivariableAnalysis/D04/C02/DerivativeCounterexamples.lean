import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeBridge
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeCounterexamples
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! The four counterexamples of d04:02:counterexamples, in the shared Euclidean
space. Homogeneity computes the derivatives of v. For w, restriction to any
fixed line is a rational function with zero derivative; the parabola instead
keeps its normalized remainder bounded below. The final example uses a
sequence with reciprocal an even multiple of pi. -/
noncomputable section
open Set Filter Topology
namespace D04.DerivativeExamples

def point : Specs.D04.C02.DerivativeCounterexamples.pointType := Specs.D04.C02.DerivativeCounterexamples.pointValue
def u : Specs.D04.C02.DerivativeCounterexamples.uType := Specs.D04.C02.DerivativeCounterexamples.uValue
def v : Specs.D04.C02.DerivativeCounterexamples.vType := Specs.D04.C02.DerivativeCounterexamples.vValue
def w : Specs.D04.C02.DerivativeCounterexamples.wType := Specs.D04.C02.DerivativeCounterexamples.wValue
def z : Specs.D04.C02.DerivativeCounterexamples.zType := Specs.D04.C02.DerivativeCounterexamples.zValue

@[simp] theorem point_apply_zero (x y : ℝ) : point x y 0 = x := rfl
@[simp] theorem point_apply_one (x y : ℝ) : point x y 1 = y := rfl
@[simp] theorem point_zero : point 0 0 = 0 := by ext i; fin_cases i <;> rfl

theorem point_coordinates (p : E 2) : point (p 0) (p 1) = p := by
  ext i; fin_cases i <;> rfl

theorem point_add (a b c d : ℝ) : point (a+c) (b+d) = point a b + point c d := by
  ext i; fin_cases i <;> rfl

@[simp] theorem u_formula (p : E 2) : u p = p 0 * p 1 / (p 0 ^ 2 + p 1 ^ 2) := rfl
@[simp] theorem v_formula (p : E 2) : v p = p 0 ^ 3 / (p 0 ^ 2 + p 1 ^ 2) := rfl
@[simp] theorem w_formula (p : E 2) : w p = p 0 ^ 3 * p 1 / (p 0 ^ 4 + p 1 ^ 2) := rfl
@[simp] theorem z_formula (x : ℝ) : z x = x ^ 2 * Real.sin x⁻¹ := rfl

@[simp] theorem u_zero : u 0 = 0 := by simp
@[simp] theorem v_zero : v 0 = 0 := by simp
@[simp] theorem w_zero : w 0 = 0 := by simp
@[simp] theorem z_zero : z 0 = 0 := by simp

theorem origin_values : Specs.D04.C02.DerivativeCounterexamples.origin_valuesType := ⟨u_zero, v_zero, w_zero, z_zero⟩

theorem denominator_pos {p : E 2} (hp : p ≠ 0) : 0 < p 0 ^ 2 + p 1 ^ 2 := by
  have h : p 0 ≠ 0 ∨ p 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hp
    rw [← point_coordinates p, h.1, h.2, point_zero]
  rcases h with h | h
  · positivity
  · positivity

theorem u_partials : Specs.D04.C02.DerivativeCounterexamples.u_partialsType := by
  change ∀ j : Fin 2, HasDirectionalDerivative u 0 (standardBasis 2 j) 0
  intro j
  apply (hasDirectionalDerivative_iff_hasDerivAt _ _ _ _).mpr
  have he : (fun t : ℝ => u (0 + t • standardBasis 2 j)) = fun _ => 0 := by
    funext t
    fin_cases j <;> simp [standardBasis_apply]
  rw [he]
  exact hasDerivAt_const 0 0

theorem u_diagonal : Specs.D04.C02.DerivativeCounterexamples.u_diagonalType := by
  intro x hx
  change x * x / (x ^ 2 + x ^ 2) = 1 / 2
  have hd : x ^ 2 + x ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem continuous_point {X : Type*} [TopologicalSpace X] {a b : X → ℝ}
    (ha : Continuous a) (hb : Continuous b) : Continuous (fun t => point (a t) (b t)) := by
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi fun i => by fin_cases i; exact ha; exact hb

theorem u_discontinuous : ¬ ContinuousAt u 0 := by
  intro h
  have hp : Tendsto (fun t : ℝ => point t t) (𝓝 0) (𝓝 (0 : E 2)) := by
    simpa using (continuous_point continuous_id continuous_id).tendsto (0 : ℝ)
  have ht : Tendsto (fun t : ℝ => u (point t t)) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [Function.comp_def, u_zero] using
      (h.tendsto.comp hp).mono_left nhdsWithin_le_nhds
  have he : (fun t : ℝ => u (point t t)) =ᶠ[𝓝[≠] 0] fun _ => 1 / 2 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact u_diagonal t ht
  have hc : Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) (𝓝[≠] 0) (𝓝 0) :=
    ht.congr' he
  have := tendsto_nhds_unique hc tendsto_const_nhds
  norm_num at this

theorem v_bound : ∀ p : E 2, |v p| ≤ ‖p‖ := by
  intro p
  by_cases hp : p = 0
  · subst p; simp
  have hd := denominator_pos hp
  calc
    |v p| = |p 0| ^ 3 / (p 0 ^ 2 + p 1 ^ 2) := by
      simp [abs_div, abs_of_pos hd]
    _ ≤ |p 0| := by
      apply (div_le_iff₀ hd).mpr
      have he : |p 0| ^ 3 = |p 0| * p 0 ^ 2 := by rw [← sq_abs (p 0)]; ring
      rw [he]
      nlinarith [mul_nonneg (abs_nonneg (p 0)) (sq_nonneg (p 1))]
    _ ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p 0

theorem v_continuous : Continuous v := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p = 0
  · subst p
    change Tendsto v (𝓝 (0 : E 2)) (𝓝 (v 0))
    rw [v_zero]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Real.norm_eq_abs]
    exact squeeze_zero (fun _ => abs_nonneg _) v_bound
      (by simpa using (continuous_norm.continuousAt (x := (0 : E 2))).tendsto)
  · change ContinuousAt (fun p : E 2 => p 0 ^ 3 / (p 0 ^ 2 + p 1 ^ 2)) p
    exact ((PiLp.continuous_apply 2 _ 0).continuousAt.pow 3).div
      (((PiLp.continuous_apply 2 _ 0).continuousAt.pow 2).add
        ((PiLp.continuous_apply 2 _ 1).continuousAt.pow 2)) (ne_of_gt (denominator_pos hp))

theorem v_smul (t : ℝ) (d : E 2) : v (t • d) = t * v d := by
  by_cases ht : t = 0
  · subst t; simp
  by_cases hd : d = 0
  · subst d; simp
  have hp : (t * d 0) ^ 2 + (t * d 1) ^ 2 = t ^ 2 * (d 0 ^ 2 + d 1 ^ 2) := by ring
  simp only [v_formula, PiLp.smul_apply, smul_eq_mul, hp]
  field_simp

theorem v_directions (d : E 2) : HasDirectionalDerivative v 0 d (v d) := by
  apply (hasDirectionalDerivative_iff_hasDerivAt _ _ _ _).mpr
  have he : (fun t : ℝ => v (0 + t • d)) = fun t => t * v d := by
    funext t; simp only [zero_add, v_smul]
  rw [he]
  simpa using (hasDerivAt_id (0 : ℝ)).mul_const (v d)

theorem v_nonlinear : v (point 1 0) = 1 ∧ v (point 0 1) = 0 ∧
    v (point 1 1) = 1 / 2 ∧ v (point 1 1) ≠ v (point 1 0) + v (point 0 1) := by
  norm_num

theorem v_not_differentiable : ¬ TotalDifferentiableAt univ v 0 := by
  rintro ⟨A, hA⟩
  have he (d : E 2) : A d = v d := by
    have h := totalDerivative_hasDirectionalDerivative univ v 0 d A hA
    exact ((hasDirectionalDerivative_iff_hasDerivAt _ _ _ _).mp h).unique
      ((hasDirectionalDerivative_iff_hasDerivAt _ _ _ _).mp (v_directions d))
  have hl := A.map_add (point 1 0) (point 0 1)
  rw [he, he, he] at hl
  have hp : point 1 0 + point 0 1 = point 1 1 := by
    rw [← point_add]; norm_num
  rw [hp] at hl
  exact v_nonlinear.2.2.2 hl

theorem w_bound (p : E 2) : |w p| ≤ |p 0| / 2 := by
  by_cases hx : p 0 = 0
  · simp [hx]
  have hd : 0 < p 0 ^ 4 + p 1 ^ 2 := by positivity
  rw [w_formula, abs_div, abs_mul, abs_pow, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  have he : |p 0| ^ 3 = |p 0| * p 0 ^ 2 := by rw [← sq_abs (p 0)]; ring
  rw [he]
  have h := mul_nonneg (abs_nonneg (p 0)) (sq_nonneg (p 0 ^ 2 - |p 1|))
  rw [← sq_abs (p 1)]
  nlinarith only [h]

theorem w_continuous : Continuous w := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p = 0
  · subst p
    change Tendsto w (𝓝 (0 : E 2)) (𝓝 (w 0))
    rw [w_zero]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Real.norm_eq_abs]
    apply squeeze_zero (fun _ => abs_nonneg _) w_bound
    simpa using (((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 0).abs.div_const 2).tendsto
      (0 : E 2))
  · have hd : 0 < p 0 ^ 4 + p 1 ^ 2 := by
      have h := denominator_pos hp
      rcases lt_or_eq_of_le (sq_nonneg (p 1)) with hy | hy
      · positivity
      · have hx : p 0 ≠ 0 := by intro hx; simp [hx, ← hy] at h
        positivity
    change ContinuousAt (fun p : E 2 => p 0 ^ 3 * p 1 / (p 0 ^ 4 + p 1 ^ 2)) p
    exact (((PiLp.continuous_apply 2 _ 0).continuousAt.pow 3).mul
      (PiLp.continuous_apply 2 _ 1).continuousAt).div
      (((PiLp.continuous_apply 2 _ 0).continuousAt.pow 4).add
        ((PiLp.continuous_apply 2 _ 1).continuousAt.pow 2)) (ne_of_gt hd)

theorem w_line (t : ℝ) (d : E 2) :
    w (t • d) = t ^ 2 * d 0 ^ 3 * d 1 / (t ^ 2 * d 0 ^ 4 + d 1 ^ 2) := by
  by_cases ht : t = 0
  · subst t; simp
  simp only [w_formula, PiLp.smul_apply, smul_eq_mul]
  have hp : (t * d 0) ^ 4 + (t * d 1) ^ 2 =
      t ^ 2 * (t ^ 2 * d 0 ^ 4 + d 1 ^ 2) := by ring
  rw [hp]
  field_simp

theorem w_directions (d : E 2) : HasDirectionalDerivative w 0 d 0 := by
  apply (hasDirectionalDerivative_iff_hasDerivAt _ _ _ _).mpr
  by_cases hb : d 1 = 0
  · have he : (fun t : ℝ => w (0 + t • d)) = fun _ => 0 := by
      funext t; simp [hb]
    rw [he]; exact hasDerivAt_const 0 0
  · have he : (fun t : ℝ => w (0 + t • d)) =
        fun t => t ^ 2 * d 0 ^ 3 * d 1 / (t ^ 2 * d 0 ^ 4 + d 1 ^ 2) := by
      funext t; simp only [zero_add, w_line]
    rw [he]
    convert ((((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (d 0 ^ 3)).mul_const (d 1)).div
      ((((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (d 0 ^ 4)).add_const (d 1 ^ 2))
      (by simpa using pow_ne_zero 2 hb) using 1 <;> first | rfl | simp

theorem w_parabola (x : ℝ) : w (point x (x ^ 2)) = x / 2 := by
  by_cases hx : x = 0
  · subst x; simp
  simp only [w_formula, point_apply_zero, point_apply_one]
  have hd : x ^ 4 + (x ^ 2) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem norm_point_sq (x y : ℝ) : ‖point x y‖ ^ 2 = x ^ 2 + y ^ 2 := by
  rw [norm_coordinates]
  simp only [Fin.sum_univ_two, point_apply_zero, point_apply_one]
  exact Real.sq_sqrt (by positivity)

theorem w_ratio_lower {x : ℝ} (hx : x ≠ 0) (hb : |x| < 1) :
    1 / 4 ≤ |w (point x (x ^ 2))| / ‖point x (x ^ 2)‖ := by
  have hp : point x (x ^ 2) ≠ 0 := by intro h; apply hx; simpa using congrArg (fun p : E 2 => p 0) h
  have hn : 0 < ‖point x (x ^ 2)‖ := norm_pos_iff.mpr hp
  have hsq := norm_point_sq x (x ^ 2)
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
  have hn2 : ‖point x (x ^ 2)‖ ≤ 2 * |x| := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * |x|)).mp
    nlinarith [sq_abs x, mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx2)]
  rw [w_parabola, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (le_div_iff₀ hn).mpr
  linarith

theorem w_ratio_not_tendsto :
    ¬ Tendsto (fun x : ℝ => |w (point x (x ^ 2))| / ‖point x (x ^ 2)‖)
      (𝓝[≠] 0) (𝓝 0) := by
  intro h
  have he : ∀ᶠ x : ℝ in 𝓝[≠] 0,
      1 / 4 ≤ |w (point x (x ^ 2))| / ‖point x (x ^ 2)‖ := by
    have hb : ∀ᶠ x : ℝ in 𝓝[≠] 0, |x| < 1 :=
      (continuous_abs.continuousAt.eventually (gt_mem_nhds (by norm_num : |(0 : ℝ)| < 1))).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hb] with x hx hb
    exact w_ratio_lower hx hb
  have hh : (1 / 4 : ℝ) ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds h he
  norm_num at hh

/-- The signed ratio also fails the required zero limit. -/
theorem w_signed_ratio_not_tendsto :
    ¬ Tendsto (fun x : ℝ => w (point x (x ^ 2)) / ‖point x (x ^ 2)‖)
      (𝓝[≠] 0) (𝓝 0) := by
  intro h
  apply w_ratio_not_tendsto
  simpa only [abs_zero, abs_div, abs_norm] using h.abs

theorem w_not_differentiable : ¬ TotalDifferentiableAt univ w 0 := by
  rintro ⟨A, hA⟩
  have hzero : A = 0 := by
    ext d
    have h := totalDerivative_hasDirectionalDerivative univ w 0 d A hA
    exact ((hasDirectionalDerivative_iff_hasDerivAt _ _ _ _).mp h).unique
      ((hasDirectionalDerivative_iff_hasDerivAt _ _ _ _).mp (w_directions d))
  have hf := (hasTotalDerivative_iff_hasFDerivAt univ w A 0 isOpen_univ (mem_univ _)).mp hA
  rw [hzero, hasFDerivAt_iff_tendsto] at hf
  have hp : Tendsto (fun t : ℝ => point t (t ^ 2)) (𝓝 0) (𝓝 (0 : E 2)) := by
    simpa using (continuous_point continuous_id (continuous_id.pow 2)).tendsto (0 : ℝ)
  apply w_ratio_not_tendsto
  simpa only [Function.comp_def, sub_zero, w_zero, zero_apply,
    Real.norm_eq_abs, div_eq_mul_inv, mul_comm] using
    (hf.comp hp).mono_left nhdsWithin_le_nhds

theorem z_derivative_zero : HasDerivAt z 0 0 := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have he : (fun t : ℝ => t⁻¹ • (z (0 + t) - z 0)) =
      fun t => t * Real.sin t⁻¹ := by
    funext t
    by_cases ht : t = 0
    · subst t; simp
    · simp [z_formula, smul_eq_mul]
      field_simp
  rw [he]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [Real.norm_eq_abs]
  apply squeeze_zero (fun _ => abs_nonneg _) (fun t => ?_)
    (by simpa using (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

theorem z_derivative_off_zero (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt z (2 * x * Real.sin x⁻¹ - Real.cos x⁻¹) x := by
  convert ((hasDerivAt_id x).pow 2).mul
    ((Real.hasDerivAt_sin x⁻¹).comp x (hasDerivAt_inv hx)) using 1
  · rfl
  · simp only [id_eq, Pi.pow_apply, Function.comp_apply]
    field_simp; ring

theorem z_differentiable : Differentiable ℝ z := by
  intro x
  by_cases hx : x = 0
  · subst x; exact z_derivative_zero.differentiableAt
  · exact (z_derivative_off_zero x hx).differentiableAt

theorem z_derivative_discontinuous : ¬ ContinuousAt (deriv z) 0 := by
  intro hc
  let seq : ℕ → ℝ := fun n => ((n + 1 : ℕ) * (2 * Real.pi))⁻¹
  have hs : Tendsto seq atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have hi := tendsto_inv_atTop_zero.comp ht
    simpa [seq, mul_inv_rev, Nat.cast_add, Nat.cast_one, mul_comm] using
      hi.mul_const (2 * Real.pi)⁻¹
  have hv (n : ℕ) : deriv z (seq n) = -1 := by
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hp : 2 * Real.pi ≠ 0 := by positivity
    rw [(z_derivative_off_zero _ (inv_ne_zero (mul_ne_zero hn hp))).deriv]
    simp only [inv_inv, Real.cos_nat_mul_two_pi]
    have he : ((n + 1 : ℕ) : ℝ) * (2 * Real.pi) = ((2 * (n+1) : ℕ) : ℝ) * Real.pi := by
      push_cast; ring
    rw [he, Real.sin_nat_mul_pi]
    ring
  have ht : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (𝓝 0) := by
    have := hc.tendsto.comp hs
    simpa only [Function.comp_def, hv, z_derivative_zero.deriv] using this
  have hh := tendsto_nhds_unique ht tendsto_const_nhds
  norm_num at hh

end D04.DerivativeExamples
