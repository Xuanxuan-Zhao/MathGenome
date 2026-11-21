import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.Scalar

/-!
# Canonical real and complex scalar foundation

The real field, its order, finite sums and products, sets, natural induction and
metric notions are the standard library objects. `Scalar` selects only `ℝ` or
`ℂ`; inequalities below are between real quantities. Derivatives in subsequent
modules have real input, and finite scalar limits take values in these types.
Complex metric completeness and other analytic consequences remain later goals.
-/

namespace SingleVariableAnalysis

open scoped BigOperators ComplexConjugate

/-- The scalar scope in the manuscript, using the canonical library types. -/
abbrev Scalar : ScalarKind → Type
  | .real => ℝ
  | .complex => ℂ

/-- Identify a complex number with its real and imaginary coordinates. -/
abbrev complexCoordinates : ℂ ≃ ℝ × ℝ := Complex.equivRealProd

/-- The manuscript's complex absolute value is the canonical complex norm. -/
noncomputable abbrev modulus (z : ℂ) : ℝ := ‖z‖

theorem real_leastUpperBound (A : Set ℝ) (hne : A.Nonempty) (hbd : BddAbove A) :
    ∃ b : ℝ, IsLUB A b :=
  ⟨sSup A, isLUB_csSup hne hbd⟩

theorem complex_pair_decomposition (z : ℂ) :
    (z.re : ℂ) + (z.im : ℂ) * Complex.I = z :=
  Complex.re_add_im z

theorem complex_pair_addition (z w : ℂ) :
    ((z + w).re, (z + w).im) = (z.re + w.re, z.im + w.im) := rfl

theorem complex_pair_multiplication (z w : ℂ) :
    ((z * w).re, (z * w).im) =
      (z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re) := rfl

theorem complex_pair_conjugation (z : ℂ) :
    ((conj z).re, (conj z).im) = (z.re, -z.im) := rfl

theorem complex_modulus_formula (z : ℂ) :
    ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) :=
  Complex.norm_eq_sqrt_sq_add_sq z

theorem real_norm_formula (x : ℝ) : ‖x‖ = |x| := Real.norm_eq_abs x

/-- Finite real Cauchy–Schwarz, including empty and zero sums. Mathlib proves
this by finite ordered-ring algebra, with a separate zero-sum case. -/
theorem real_cauchySchwarz {ι : Type*} (s : Finset ι) (u v : ι → ℝ) :
    (∑ j ∈ s, u j * v j) ^ 2 ≤ (∑ j ∈ s, u j ^ 2) * (∑ j ∈ s, v j ^ 2) :=
  Finset.sum_mul_sq_le_sq_mul_sq s u v

/-- Bound the norm of the complex sum by the sum of products of moduli, then
apply real finite Cauchy–Schwarz. No division or nonzero hypothesis is needed. -/
theorem complex_cauchySchwarz {ι : Type*} (s : Finset ι) (u v : ι → ℂ) :
    ‖∑ j ∈ s, conj (u j) * v j‖ ^ 2 ≤
      (∑ j ∈ s, ‖u j‖ ^ 2) * (∑ j ∈ s, ‖v j‖ ^ 2) := by
  have h : ‖∑ j ∈ s, conj (u j) * v j‖ ≤ ∑ j ∈ s, ‖u j‖ * ‖v j‖ := by
    simpa only [Complex.norm_mul, Complex.norm_conj] using
      norm_sum_le s (fun j => conj (u j) * v j)
  calc
    ‖∑ j ∈ s, conj (u j) * v j‖ ^ 2 ≤ (∑ j ∈ s, ‖u j‖ * ‖v j‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h 2
    _ ≤ (∑ j ∈ s, ‖u j‖ ^ 2) * (∑ j ∈ s, ‖v j‖ ^ 2) :=
      real_cauchySchwarz s (fun j => ‖u j‖) (fun j => ‖v j‖)

theorem complex_triangle (z w : ℂ) : ‖z + w‖ ≤ ‖z‖ + ‖w‖ := norm_add_le z w

theorem complex_modulus_multiplicative (z w : ℂ) : ‖z * w‖ = ‖z‖ * ‖w‖ :=
  Complex.norm_mul z w

theorem complex_conjugation_modulus (z : ℂ) : ‖conj z‖ = ‖z‖ := Complex.norm_conj z

theorem complex_distance_formula (z w : ℂ) :
    dist z w = Real.sqrt ((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) :=
  Complex.dist_eq_re_im z w

end SingleVariableAnalysis
