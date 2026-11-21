import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.Exponential

/-! Independent full statements for the trigonometric part of D12.02.03,
paper.tex:376–397. Canonical Mathlib functions are identified with the
paper's E formulas. Quotient functions are considered only on the indicated
open nonzero-denominator domains; totalized values elsewhere assert nothing
about a holomorphic extension. Simplicity means nonzero complex derivative. -/

noncomputable section

namespace D12Complex
/-- Hyperbolic cotangent; its natural domain is {z | Complex.sinh z ≠ 0}. -/
def coth (z : ℂ) : ℂ := Complex.cosh z / Complex.sinh z
end D12Complex

namespace Specs.D12Complex.Ch02.Trigonometric
open _root_.D12Complex

def coth_type := ℂ → ℂ
def coth_value : coth_type := fun z => Complex.cosh z / Complex.sinh z

def sin_eq_E_type : Prop :=
  ∀ z : ℂ, Complex.sin z = (E (Complex.I * z) - E (-Complex.I * z)) / (2 * Complex.I)

def cos_eq_E_type : Prop :=
  ∀ z : ℂ, Complex.cos z = (E (Complex.I * z) + E (-Complex.I * z)) / 2

def sinh_eq_E_type : Prop :=
  ∀ z : ℂ, Complex.sinh z = (E (z) - E (-z)) / 2

def cosh_eq_E_type : Prop :=
  ∀ z : ℂ, Complex.cosh z = (E (z) + E (-z)) / 2

def hasDerivAt_sin_type : Prop :=
  ∀ z : ℂ, HasDerivAt Complex.sin (Complex.cos z) z

def holomorphicOn_sin_type : Prop :=
  HolomorphicOn Set.univ Complex.sin

def sin_neg_type : Prop :=
  ∀ z : ℂ, Complex.sin (-z) = -Complex.sin z

def hasDerivAt_cos_type : Prop :=
  ∀ z : ℂ, HasDerivAt Complex.cos (-Complex.sin z) z

def holomorphicOn_cos_type : Prop :=
  HolomorphicOn Set.univ Complex.cos

def cos_neg_type : Prop :=
  ∀ z : ℂ, Complex.cos (-z) = Complex.cos z

def hasDerivAt_sinh_type : Prop :=
  ∀ z : ℂ, HasDerivAt Complex.sinh (Complex.cosh z) z

def holomorphicOn_sinh_type : Prop :=
  HolomorphicOn Set.univ Complex.sinh

def sinh_neg_type : Prop :=
  ∀ z : ℂ, Complex.sinh (-z) = -Complex.sinh z

def hasDerivAt_cosh_type : Prop :=
  ∀ z : ℂ, HasDerivAt Complex.cosh (Complex.sinh z) z

def holomorphicOn_cosh_type : Prop :=
  HolomorphicOn Set.univ Complex.cosh

def cosh_neg_type : Prop :=
  ∀ z : ℂ, Complex.cosh (-z) = Complex.cosh z

def sin_add_type : Prop :=
  ∀ z w : ℂ, Complex.sin (z + w) = Complex.sin z * Complex.cos w + Complex.cos z * Complex.sin w

def sin_sub_type : Prop :=
  ∀ z w : ℂ, Complex.sin (z - w) = Complex.sin z * Complex.cos w - Complex.cos z * Complex.sin w

def cos_add_type : Prop :=
  ∀ z w : ℂ, Complex.cos (z + w) = Complex.cos z * Complex.cos w - Complex.sin z * Complex.sin w

def cos_sub_type : Prop :=
  ∀ z w : ℂ, Complex.cos (z - w) = Complex.cos z * Complex.cos w + Complex.sin z * Complex.sin w

def sinh_add_type : Prop :=
  ∀ z w : ℂ, Complex.sinh (z + w) = Complex.sinh z * Complex.cosh w + Complex.cosh z * Complex.sinh w

def sinh_sub_type : Prop :=
  ∀ z w : ℂ, Complex.sinh (z - w) = Complex.sinh z * Complex.cosh w - Complex.cosh z * Complex.sinh w

def cosh_add_type : Prop :=
  ∀ z w : ℂ, Complex.cosh (z + w) = Complex.cosh z * Complex.cosh w + Complex.sinh z * Complex.sinh w

def cosh_sub_type : Prop :=
  ∀ z w : ℂ, Complex.cosh (z - w) = Complex.cosh z * Complex.cosh w - Complex.sinh z * Complex.sinh w

def sin_sq_add_cos_sq_type : Prop :=
  ∀ z : ℂ, Complex.sin z ^ 2 + Complex.cos z ^ 2 = 1

def cosh_sq_sub_sinh_sq_type : Prop :=
  ∀ z : ℂ, Complex.cosh z ^ 2 - Complex.sinh z ^ 2 = 1

def sin_mul_I_type : Prop :=
  ∀ z : ℂ, Complex.sin (z * Complex.I) = Complex.sinh z * Complex.I

def cos_mul_I_type : Prop :=
  ∀ z : ℂ, Complex.cos (z * Complex.I) = Complex.cosh z

def sinh_mul_I_type : Prop :=
  ∀ z : ℂ, Complex.sinh (z * Complex.I) = Complex.sin z * Complex.I

def cosh_mul_I_type : Prop :=
  ∀ z : ℂ, Complex.cosh (z * Complex.I) = Complex.cos z

def sin_eq_zero_iff_type : Prop :=
  ∀ z : ℂ, Complex.sin z = 0 ↔ ∃ k : ℤ, z = (k : ℂ) * (Real.pi : ℂ)

def cos_eq_zero_iff_type : Prop :=
  ∀ z : ℂ, Complex.cos z = 0 ↔ ∃ k : ℤ, z = (Real.pi : ℂ) / 2 + (k : ℂ) * (Real.pi : ℂ)

def sin_zeros_simple_type : Prop :=
  ∀ z : ℂ, Complex.sin z = 0 → deriv Complex.sin z ≠ 0

def cos_zeros_simple_type : Prop :=
  ∀ z : ℂ, Complex.cos z = 0 → deriv Complex.cos z ≠ 0

def sin_periodic_iff_type : Prop :=
  ∀ p : ℂ, Function.Periodic Complex.sin p ↔ ∃ k : ℤ, p = (k : ℂ) * (2 * (Real.pi : ℂ))

def cos_periodic_iff_type : Prop :=
  ∀ p : ℂ, Function.Periodic Complex.cos p ↔ ∃ k : ℤ, p = (k : ℂ) * (2 * (Real.pi : ℂ))

def sinh_periodic_iff_type : Prop :=
  ∀ p : ℂ, Function.Periodic Complex.sinh p ↔ ∃ k : ℤ, p = (k : ℂ) * (2 * (Real.pi : ℂ)) * Complex.I

def cosh_periodic_iff_type : Prop :=
  ∀ p : ℂ, Function.Periodic Complex.cosh p ↔ ∃ k : ℤ, p = (k : ℂ) * (2 * (Real.pi : ℂ)) * Complex.I

def tan_eq_quotient_type : Prop :=
  ∀ z : ℂ, Complex.tan z = Complex.sin z / Complex.cos z

def hasDerivAt_tan_type : Prop :=
  ∀ z : ℂ, Complex.cos z ≠ 0 → HasDerivAt Complex.tan (1 / Complex.cos z ^ 2) z

def holomorphicOn_tan_type : Prop :=
  HolomorphicOn {z : ℂ | Complex.cos z ≠ 0} Complex.tan

def cot_eq_quotient_type : Prop :=
  ∀ z : ℂ, Complex.cot z = Complex.cos z / Complex.sin z

def hasDerivAt_cot_type : Prop :=
  ∀ z : ℂ, Complex.sin z ≠ 0 → HasDerivAt Complex.cot (-1 / Complex.sin z ^ 2) z

def holomorphicOn_cot_type : Prop :=
  HolomorphicOn {z : ℂ | Complex.sin z ≠ 0} Complex.cot

def tanh_eq_quotient_type : Prop :=
  ∀ z : ℂ, Complex.tanh z = Complex.sinh z / Complex.cosh z

def hasDerivAt_tanh_type : Prop :=
  ∀ z : ℂ, Complex.cosh z ≠ 0 → HasDerivAt Complex.tanh (1 / Complex.cosh z ^ 2) z

def holomorphicOn_tanh_type : Prop :=
  HolomorphicOn {z : ℂ | Complex.cosh z ≠ 0} Complex.tanh

def coth_eq_quotient_type : Prop :=
  ∀ z : ℂ, coth z = Complex.cosh z / Complex.sinh z

def hasDerivAt_coth_type : Prop :=
  ∀ z : ℂ, Complex.sinh z ≠ 0 → HasDerivAt coth (-1 / Complex.sinh z ^ 2) z

def holomorphicOn_coth_type : Prop :=
  HolomorphicOn {z : ℂ | Complex.sinh z ≠ 0} coth

end Specs.D12Complex.Ch02.Trigonometric
