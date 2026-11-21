import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.HouseholderReflector
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

noncomputable section
open scoped BigOperators
open Matrix
namespace NumAnalysis206.HouseholderReflector
open NumAnalysis206.MatrixDefinitions
open NumAnalysis206.HouseholderDefinitions

abbrev signPlus : Specs.NumAnalysis206.HouseholderReflector.signPlus_type :=
  NumAnalysis206.HouseholderDefinitions.signPlus
abbrev firstVector : Specs.NumAnalysis206.HouseholderReflector.firstVector_type :=
  NumAnalysis206.HouseholderDefinitions.firstVector
abbrev alpha : Specs.NumAnalysis206.HouseholderReflector.alpha_type :=
  @NumAnalysis206.HouseholderDefinitions.alpha
abbrev direction : Specs.NumAnalysis206.HouseholderReflector.direction_type :=
  @NumAnalysis206.HouseholderDefinitions.direction
abbrev reflector : Specs.NumAnalysis206.HouseholderReflector.reflector_type :=
  @NumAnalysis206.HouseholderDefinitions.reflector
abbrev step : Specs.NumAnalysis206.HouseholderReflector.step_type :=
  @NumAnalysis206.HouseholderDefinitions.step

lemma firstVector_apply {d : ℕ} [NeZero d] (i : Fin d) :
    firstVector d i = if i = 0 then 1 else 0 := by
  simp [firstVector, HouseholderDefinitions.firstVector, PiLp.single_apply]

lemma norm_sq_dot {d : ℕ} (x : Vec ℝ d) : ‖x‖ ^ 2 = ⇑x ⬝ᵥ ⇑x := by
  simpa [dotProduct, pow_two] using EuclideanSpace.real_norm_sq_eq x

lemma abs_direction_first {d : ℕ} [NeZero d] (x : Vec ℝ d) :
    |direction x 0| = |x 0| + ‖x‖ := by
  simp only [direction, HouseholderDefinitions.direction, PiLp.sub_apply, PiLp.smul_apply,
    firstVector_apply, ite_true, smul_eq_mul, mul_one]
  unfold HouseholderDefinitions.alpha HouseholderDefinitions.signPlus
  split_ifs with h
  · simp only [neg_mul, one_mul, sub_neg_eq_add]
    rw [abs_of_nonneg h, abs_of_nonneg (add_nonneg h (norm_nonneg x))]
  · rw [abs_of_neg (lt_of_not_ge h), abs_of_nonpos (by linarith [norm_nonneg x])]
    ring

lemma direction_ne_zero {d : ℕ} [NeZero d] (x : Vec ℝ d) (hx : x ≠ 0) :
    direction x ≠ 0 := by
  intro hv
  have h := abs_direction_first x
  rw [hv] at h
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  simp only [PiLp.zero_apply, abs_zero] at h
  linarith [abs_nonneg (x 0)]

lemma alpha_sq {d : ℕ} [NeZero d] (x : Vec ℝ d) :
    alpha x ^ 2 = ‖x‖ ^ 2 := by
  unfold alpha HouseholderDefinitions.alpha HouseholderDefinitions.signPlus
  split_ifs <;> ring

lemma dot_first {d : ℕ} [NeZero d] (x : Vec ℝ d) :
    ⇑x ⬝ᵥ ⇑(firstVector d) = x 0 := by
  simp [firstVector, HouseholderDefinitions.firstVector, PiLp.single_apply, dotProduct]

lemma first_dot {d : ℕ} [NeZero d] (x : Vec ℝ d) :
    ⇑(firstVector d) ⬝ᵥ ⇑x = x 0 := by
  rw [dotProduct_comm, dot_first]

lemma first_dot_first (d : ℕ) [NeZero d] :
    ⇑(firstVector d) ⬝ᵥ ⇑(firstVector d) = 1 := by
  rw [dot_first, firstVector_apply]
  simp

lemma direction_dot {d : ℕ} [NeZero d] (x : Vec ℝ d) :
    ⇑(direction x) ⬝ᵥ ⇑(direction x) = 2 * (⇑(direction x) ⬝ᵥ ⇑x) := by
  change (⇑x - alpha x • ⇑(firstVector d)) ⬝ᵥ
    (⇑x - alpha x • ⇑(firstVector d)) =
      2 * ((⇑x - alpha x • ⇑(firstVector d)) ⬝ᵥ ⇑x)
  rw [dotProduct_sub, sub_dotProduct, sub_dotProduct, dotProduct_smul,
    dotProduct_smul, smul_dotProduct, smul_dotProduct, dot_first, first_dot,
    first_dot_first, ← norm_sq_dot]
  simp only [smul_eq_mul]
  nlinarith [alpha_sq x]

lemma dot_self_ne_zero {d : ℕ} (v : Vec ℝ d) (hv : v ≠ 0) :
    ⇑v ⬝ᵥ ⇑v ≠ 0 := by
  rw [← norm_sq_dot]
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)

lemma reflector_orthogonal {d : ℕ} (v : Vec ℝ d) (hv : v ≠ 0) :
    (reflector v).conjTranspose * reflector v = 1 := by
  let P := Matrix.vecMulVec (⇑v) (⇑v)
  let s := ⇑v ⬝ᵥ ⇑v
  have hs : s ≠ 0 := dot_self_ne_zero v hv
  have hp : P * P = s • P := by
    simp only [P, s, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
  have ht : P.conjTranspose = P := by
    ext i j
    simp [P, Matrix.conjTranspose_apply, Matrix.vecMulVec_apply, mul_comm]
  change (1 - (2 / s) • P).conjTranspose * (1 - (2 / s) • P) = 1
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, ht]
  simp only [star_trivial, mul_sub, sub_mul, one_mul, mul_one,
    Matrix.smul_mul, Matrix.mul_smul, hp, smul_smul]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

lemma reflector_maps {d : ℕ} [NeZero d] (x : Vec ℝ d) (hx : x ≠ 0) :
    reflector (direction x) *ᵥ ⇑x = ⇑(alpha x • firstVector d) := by
  have hs := dot_self_ne_zero (direction x) (direction_ne_zero x hx)
  have hd := direction_dot x
  have hc : (2 / (⇑(direction x) ⬝ᵥ ⇑(direction x))) *
      (⇑(direction x) ⬝ᵥ ⇑x) = 1 := by
    rw [div_mul_eq_mul_div]
    exact (div_eq_one_iff_eq hs).mpr hd.symm
  ext i
  simp only [reflector, HouseholderDefinitions.reflector, Matrix.sub_mulVec,
    Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  have hci := congrArg (fun a : ℝ => a * direction x i) hc
  change x i - (2 / (⇑(direction x) ⬝ᵥ ⇑(direction x))) *
      (direction x i * (⇑(direction x) ⬝ᵥ ⇑x)) = _
  rw [show (2 / (⇑(direction x) ⬝ᵥ ⇑(direction x))) *
      (direction x i * (⇑(direction x) ⬝ᵥ ⇑x)) = direction x i by nlinarith [hci]]
  change x i - (x i - alpha x * firstVector d i) = alpha x * firstVector d i
  ring

theorem householder : Specs.NumAnalysis206.HouseholderReflector.householder := by
  intro d _ x hx
  exact ⟨abs_direction_first x, direction_ne_zero x hx,
    reflector_orthogonal _ (direction_ne_zero x hx), reflector_maps x hx⟩

theorem step_zero : Specs.NumAnalysis206.HouseholderReflector.step_zero := by
  intro d _
  simp [HouseholderDefinitions.step]

theorem step_nonzero : Specs.NumAnalysis206.HouseholderReflector.step_nonzero := by
  intro d _ x hx
  simp [HouseholderDefinitions.step, hx]

end NumAnalysis206.HouseholderReflector
