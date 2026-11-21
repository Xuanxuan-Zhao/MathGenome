import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch04.Derivative
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Modulus
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Differentiating an absolute value

K03.04.modulus, paper.tex:757–767. Derivatives of complex-valued functions
use real increments. At a nonzero value, differentiate the squared norm and
then its nonnegative square root. At a zero, a differentiable norm has derivative
zero by its minimum property. The little-o definition and norm invariance then
give derivative zero for the original function, and also prove the converse.
-/

namespace SingleVariableAnalysis

open scoped Topology

theorem abs_derivative_positive (a : ℝ) (ha : 0 < a) :
    HasRealIncrementDerivative (fun x : ℝ => |x|) 1 a :=
  (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mpr (hasDerivAt_abs_pos ha)

theorem abs_derivative_negative (a : ℝ) (ha : a < 0) :
    HasRealIncrementDerivative (fun x : ℝ => |x|) (-1) a :=
  (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mpr (hasDerivAt_abs_neg ha)

theorem abs_not_differentiable_zero :
    ¬ ∃ L : ℝ, HasRealIncrementDerivative (fun x : ℝ => |x|) L 0 := by
  rintro ⟨L, hL⟩
  exact not_differentiableAt_abs_zero
    ((hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mp hL).differentiableAt

theorem complex_modulus_hasDerivAt_nonzero (f : ℝ → ℂ) (L : ℂ) (a : ℝ)
    (hf : HasDerivAt f L a) (ha : f a ≠ 0) :
    HasDerivAt (fun x => ‖f x‖) ((star (f a) * L).re / ‖f a‖) a := by
  have hs := hf.norm_sq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr ha))
  simpa only [Real.sqrt_sq (norm_nonneg _), Complex.inner, mul_comm L,
    RCLike.star_def, mul_div_mul_left _ _ (two_ne_zero : (2 : ℝ) ≠ 0)] using hs

/-- At a zero, taking norms preserves the assertion that the derivative is zero. -/
theorem complex_modulus_hasDerivAt_zero_iff (f : ℝ → ℂ) (a : ℝ) (ha : f a = 0) :
    HasDerivAt (fun x => ‖f x‖) 0 a ↔ HasDerivAt f 0 a := by
  simp only [hasDerivAt_iff_isLittleO, ha, norm_zero, sub_zero, smul_zero]
  exact Asymptotics.isLittleO_norm_left

theorem modulus_derivative_nonzero (f : ℝ → ℂ) (L : ℂ) (a : ℝ)
    (hf : HasRealIncrementDerivative f L a) (ha : f a ≠ 0) :
    HasRealIncrementDerivative (fun x => ‖f x‖) ((star (f a) * L).re / ‖f a‖) a := by
  apply (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mpr
  exact complex_modulus_hasDerivAt_nonzero f L a
    ((hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mp hf) ha

theorem modulus_deriv_nonzero (f : ℝ → ℂ) (a : ℝ)
    (hf : DifferentiableAt ℝ f a) (ha : f a ≠ 0) :
    deriv (fun x => ‖f x‖) a = (star (f a) * deriv f a).re / ‖f a‖ :=
  (complex_modulus_hasDerivAt_nonzero f _ a hf.hasDerivAt ha).deriv

theorem modulus_differentiable_zero_iff (f : ℝ → ℂ) (L : ℂ) (a : ℝ)
    (hf : HasRealIncrementDerivative f L a) (ha : f a = 0) :
    DifferentiableAt ℝ (fun x => ‖f x‖) a ↔ L = 0 := by
  have hd := (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mp hf
  constructor
  · intro hn
    have hmin : IsLocalMin (fun x => ‖f x‖) a := by
      apply Filter.Eventually.of_forall
      intro x
      simp only [ha, norm_zero]
      exact norm_nonneg _
    have hz : HasDerivAt (fun x => ‖f x‖) 0 a := by
      simpa only [hmin.deriv_eq_zero] using hn.hasDerivAt
    exact hd.unique ((complex_modulus_hasDerivAt_zero_iff f a ha).mp hz)
  · intro hL
    subst L
    exact ((complex_modulus_hasDerivAt_zero_iff f a ha).mpr hd).differentiableAt

theorem modulus_derivative_zero (f : ℝ → ℂ) (a : ℝ)
    (hf : HasRealIncrementDerivative f 0 a) (ha : f a = 0) :
    HasRealIncrementDerivative (fun x => ‖f x‖) 0 a := by
  apply (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mpr
  exact (complex_modulus_hasDerivAt_zero_iff f a ha).mpr
    ((hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mp hf)

theorem within_modulus_derivative_nonzero (f : ℝ → ℂ) (L : ℂ) (I : Set ℝ) (a : ℝ)
    (hI : a ∈ interior I) (hf : HasRealIncrementDerivativeWithin f L I a)
    (ha : f a ≠ 0) :
    HasRealIncrementDerivativeWithin (fun x => ‖f x‖)
      ((star (f a) * L).re / ‖f a‖) I a := by
  apply (withinDerivative_interior_iff _ _ I a hI).mpr
  exact complex_modulus_hasDerivAt_nonzero f L a
    ((withinDerivative_interior_iff _ _ I a hI).mp hf) ha

theorem within_modulus_differentiable_zero_iff (f : ℝ → ℂ) (L : ℂ)
    (I : Set ℝ) (a : ℝ) (hI : a ∈ interior I)
    (hf : HasRealIncrementDerivativeWithin f L I a) (ha : f a = 0) :
    (∃ M : ℝ, HasRealIncrementDerivativeWithin (fun x => ‖f x‖) M I a) ↔ L = 0 := by
  have hd : HasRealIncrementDerivative f L a :=
    (hasRealIncrementDerivative_iff_hasDerivAt _ _ _).mpr
      ((withinDerivative_interior_iff _ _ I a hI).mp hf)
  rw [← modulus_differentiable_zero_iff f L a hd ha]
  constructor
  · rintro ⟨M, hM⟩
    exact ((withinDerivative_interior_iff _ _ I a hI).mp hM).differentiableAt
  · intro hn
    exact ⟨deriv (fun x => ‖f x‖) a,
      (withinDerivative_interior_iff _ _ I a hI).mpr hn.hasDerivAt⟩

theorem within_modulus_derivative_zero (f : ℝ → ℂ) (I : Set ℝ) (a : ℝ)
    (hI : a ∈ interior I) (hf : HasRealIncrementDerivativeWithin f 0 I a)
    (ha : f a = 0) :
    HasRealIncrementDerivativeWithin (fun x => ‖f x‖) 0 I a := by
  apply (withinDerivative_interior_iff _ _ I a hI).mpr
  exact (complex_modulus_hasDerivAt_zero_iff f a ha).mpr
    ((withinDerivative_interior_iff _ _ I a hI).mp hf)

end SingleVariableAnalysis
