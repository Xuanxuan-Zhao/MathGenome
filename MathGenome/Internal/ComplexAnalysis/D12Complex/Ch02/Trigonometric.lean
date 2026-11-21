import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch02.Trigonometric
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch02.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.LinearCombination

/-!
The canonical trigonometric functions satisfy the exact E-based formulas.
The period converses are global: evaluate a sine period at π/2, or a cosine
period at zero, and use the complete complex criterion cos p = 1.
Imaginary substitution transports both directions to sinh and cosh.
The Pythagorean identities give nonzero derivatives at zeros and simplify
all four quotient-rule numerators. No nonzero-denominator condition is
omitted from a quotient derivative or its open holomorphy domain.
-/

noncomputable section

namespace D12Complex.Trigonometric

abbrev coth : Specs.D12Complex.Ch02.Trigonometric.coth_type := _root_.D12Complex.coth

theorem sin_eq_E : Specs.D12Complex.Ch02.Trigonometric.sin_eq_E_type := by
  intro z
  rw [Exponential.E_eq_exp]
  rw [Complex.sin]
  simp only [mul_comm Complex.I z, neg_mul]
  apply (eq_div_iff (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) Complex.I_ne_zero)).mpr
  simp only [div_mul_eq_mul_div, mul_assoc]
  ring_nf
  simp

theorem cos_eq_E : Specs.D12Complex.Ch02.Trigonometric.cos_eq_E_type := by
  intro z
  rw [Exponential.E_eq_exp]
  simp only [Complex.cos, mul_comm Complex.I z, neg_mul]

theorem sinh_eq_E : Specs.D12Complex.Ch02.Trigonometric.sinh_eq_E_type := by
  intro z
  rw [Exponential.E_eq_exp]
  rfl

theorem cosh_eq_E : Specs.D12Complex.Ch02.Trigonometric.cosh_eq_E_type := by
  intro z
  rw [Exponential.E_eq_exp]
  rfl

theorem hasDerivAt_sin : Specs.D12Complex.Ch02.Trigonometric.hasDerivAt_sin_type := by
  exact Complex.hasDerivAt_sin

theorem holomorphicOn_sin : Specs.D12Complex.Ch02.Trigonometric.holomorphicOn_sin_type := by
  exact ⟨isOpen_univ, fun z _ => (hasDerivAt_sin z).differentiableAt⟩

theorem sin_neg : Specs.D12Complex.Ch02.Trigonometric.sin_neg_type := by
  exact Complex.sin_neg

theorem hasDerivAt_cos : Specs.D12Complex.Ch02.Trigonometric.hasDerivAt_cos_type := by
  exact Complex.hasDerivAt_cos

theorem holomorphicOn_cos : Specs.D12Complex.Ch02.Trigonometric.holomorphicOn_cos_type := by
  exact ⟨isOpen_univ, fun z _ => (hasDerivAt_cos z).differentiableAt⟩

theorem cos_neg : Specs.D12Complex.Ch02.Trigonometric.cos_neg_type := by
  exact Complex.cos_neg

theorem hasDerivAt_sinh : Specs.D12Complex.Ch02.Trigonometric.hasDerivAt_sinh_type := by
  exact Complex.hasDerivAt_sinh

theorem holomorphicOn_sinh : Specs.D12Complex.Ch02.Trigonometric.holomorphicOn_sinh_type := by
  exact ⟨isOpen_univ, fun z _ => (hasDerivAt_sinh z).differentiableAt⟩

theorem sinh_neg : Specs.D12Complex.Ch02.Trigonometric.sinh_neg_type := by
  exact Complex.sinh_neg

theorem hasDerivAt_cosh : Specs.D12Complex.Ch02.Trigonometric.hasDerivAt_cosh_type := by
  exact Complex.hasDerivAt_cosh

theorem holomorphicOn_cosh : Specs.D12Complex.Ch02.Trigonometric.holomorphicOn_cosh_type := by
  exact ⟨isOpen_univ, fun z _ => (hasDerivAt_cosh z).differentiableAt⟩

theorem cosh_neg : Specs.D12Complex.Ch02.Trigonometric.cosh_neg_type := by
  exact Complex.cosh_neg

theorem sin_add : Specs.D12Complex.Ch02.Trigonometric.sin_add_type := by
  exact Complex.sin_add

theorem sin_sub : Specs.D12Complex.Ch02.Trigonometric.sin_sub_type := by
  exact Complex.sin_sub

theorem cos_add : Specs.D12Complex.Ch02.Trigonometric.cos_add_type := by
  exact Complex.cos_add

theorem cos_sub : Specs.D12Complex.Ch02.Trigonometric.cos_sub_type := by
  exact Complex.cos_sub

theorem sinh_add : Specs.D12Complex.Ch02.Trigonometric.sinh_add_type := by
  exact Complex.sinh_add

theorem sinh_sub : Specs.D12Complex.Ch02.Trigonometric.sinh_sub_type := by
  exact Complex.sinh_sub

theorem cosh_add : Specs.D12Complex.Ch02.Trigonometric.cosh_add_type := by
  exact Complex.cosh_add

theorem cosh_sub : Specs.D12Complex.Ch02.Trigonometric.cosh_sub_type := by
  exact Complex.cosh_sub

theorem sin_sq_add_cos_sq : Specs.D12Complex.Ch02.Trigonometric.sin_sq_add_cos_sq_type := by
  exact Complex.sin_sq_add_cos_sq

theorem cosh_sq_sub_sinh_sq : Specs.D12Complex.Ch02.Trigonometric.cosh_sq_sub_sinh_sq_type := by
  exact Complex.cosh_sq_sub_sinh_sq

theorem sin_mul_I : Specs.D12Complex.Ch02.Trigonometric.sin_mul_I_type := by
  exact Complex.sin_mul_I

theorem cos_mul_I : Specs.D12Complex.Ch02.Trigonometric.cos_mul_I_type := by
  exact Complex.cos_mul_I

theorem sinh_mul_I : Specs.D12Complex.Ch02.Trigonometric.sinh_mul_I_type := by
  exact Complex.sinh_mul_I

theorem cosh_mul_I : Specs.D12Complex.Ch02.Trigonometric.cosh_mul_I_type := by
  exact Complex.cosh_mul_I

theorem sin_eq_zero_iff : Specs.D12Complex.Ch02.Trigonometric.sin_eq_zero_iff_type := by
  intro z
  exact Complex.sin_eq_zero_iff

theorem cos_eq_zero_iff : Specs.D12Complex.Ch02.Trigonometric.cos_eq_zero_iff_type := by
  intro z
  rw [Complex.cos_eq_zero_iff]
  exact exists_congr fun k => by
    rw [show (2 * (k : ℂ) + 1) * (Real.pi : ℂ) / 2 =
      (Real.pi : ℂ) / 2 + (k : ℂ) * (Real.pi : ℂ) by ring]

theorem sin_zeros_simple : Specs.D12Complex.Ch02.Trigonometric.sin_zeros_simple_type := by
  intro z hz
  rw [(hasDerivAt_sin z).deriv]
  intro ho
  have h := Complex.sin_sq_add_cos_sq z
  simp [hz, ho] at h

theorem cos_zeros_simple : Specs.D12Complex.Ch02.Trigonometric.cos_zeros_simple_type := by
  intro z hz
  rw [(hasDerivAt_cos z).deriv]
  rw [neg_ne_zero]
  intro ho
  have h := Complex.sin_sq_add_cos_sq z
  simp [hz, ho] at h

theorem sin_periodic_iff : Specs.D12Complex.Ch02.Trigonometric.sin_periodic_iff_type := by
  intro p
  constructor
  · intro h
    have hc : Complex.cos p = 1 := by
      simpa [Complex.sin_add] using h ((Real.pi : ℂ) / 2)
    obtain ⟨k, hk⟩ := Complex.cos_eq_one_iff.mp hc
    exact ⟨k, hk.symm⟩
  · rintro ⟨k, rfl⟩
    exact Complex.sin_periodic.int_mul k

theorem cos_periodic_iff : Specs.D12Complex.Ch02.Trigonometric.cos_periodic_iff_type := by
  intro p
  constructor
  · intro h
    have hc : Complex.cos p = 1 := by simpa using h 0
    obtain ⟨k, hk⟩ := Complex.cos_eq_one_iff.mp hc
    exact ⟨k, hk.symm⟩
  · rintro ⟨k, rfl⟩
    exact Complex.cos_periodic.int_mul k

/-- Imaginary substitution transports the period condition without assuming
any assertion about the zeros or periods of the hyperbolic functions. -/
private theorem sinh_period_transport (p : ℂ) :
    Function.Periodic Complex.sin (p * Complex.I) ↔ Function.Periodic Complex.sinh p := by
  constructor
  · intro h z
    have he := h (z * Complex.I)
    rw [← add_mul, Complex.sin_mul_I, Complex.sin_mul_I] at he
    exact mul_right_cancel₀ Complex.I_ne_zero he
  · intro h z
    have he := congrArg (fun w : ℂ => w * Complex.I) (h (z / Complex.I))
    rw [← Complex.sin_mul_I, ← Complex.sin_mul_I, add_mul,
      div_mul_cancel₀ _ Complex.I_ne_zero] at he
    exact he

private theorem cosh_period_transport (p : ℂ) :
    Function.Periodic Complex.cos (p * Complex.I) ↔ Function.Periodic Complex.cosh p := by
  constructor
  · intro h z
    have he := h (z * Complex.I)
    simpa only [← add_mul, Complex.cos_mul_I] using he
  · intro h z
    have he := h (z / Complex.I)
    rw [← Complex.cos_mul_I, ← Complex.cos_mul_I, add_mul,
      div_mul_cancel₀ _ Complex.I_ne_zero] at he
    exact he

private theorem imaginary_period_lattice (p : ℂ) :
    (∃ k : ℤ, p * Complex.I = (k : ℂ) * (2 * (Real.pi : ℂ))) ↔
    ∃ k : ℤ, p = (k : ℂ) * (2 * (Real.pi : ℂ)) * Complex.I := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    calc
      p = -(p * Complex.I) * Complex.I := by simp [mul_assoc]
      _ = ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ)) * Complex.I := by
        rw [hk]
        push_cast
        ring
  · rintro ⟨k, rfl⟩
    refine ⟨-k, ?_⟩
    simp only [Int.cast_neg, mul_assoc, Complex.I_mul_I, mul_neg_one]
    ring

theorem sinh_periodic_iff : Specs.D12Complex.Ch02.Trigonometric.sinh_periodic_iff_type := by
  intro p
  rw [← sinh_period_transport, sin_periodic_iff, imaginary_period_lattice]

theorem cosh_periodic_iff : Specs.D12Complex.Ch02.Trigonometric.cosh_periodic_iff_type := by
  intro p
  rw [← cosh_period_transport, cos_periodic_iff, imaginary_period_lattice]

theorem tan_eq_quotient : Specs.D12Complex.Ch02.Trigonometric.tan_eq_quotient_type := by
  intro z
  rfl

theorem hasDerivAt_tan : Specs.D12Complex.Ch02.Trigonometric.hasDerivAt_tan_type := by
  intro z hz
  change HasDerivAt (fun w : ℂ => Complex.sin w / Complex.cos w)
    (1 / Complex.cos z ^ 2) z
  have hd := (hasDerivAt_sin z).div (hasDerivAt_cos z) hz
  have he : ((Complex.cos z) * Complex.cos z - Complex.sin z * (-Complex.sin z)) = 1 := by
    have h := Complex.sin_sq_add_cos_sq z
    linear_combination h
  simpa only [he, Pi.div_def] using hd

theorem holomorphicOn_tan : Specs.D12Complex.Ch02.Trigonometric.holomorphicOn_tan_type := by
  change HolomorphicOn {z : ℂ | Complex.cos z ≠ 0}
    (fun z => Complex.sin z / Complex.cos z)
  have h := holomorphicOn_div_nonzeroSet Set.univ Complex.sin Complex.cos
    holomorphicOn_sin holomorphicOn_cos
  simpa only [Set.mem_univ, true_and] using h

theorem cot_eq_quotient : Specs.D12Complex.Ch02.Trigonometric.cot_eq_quotient_type := by
  intro z
  rfl

theorem hasDerivAt_cot : Specs.D12Complex.Ch02.Trigonometric.hasDerivAt_cot_type := by
  intro z hz
  change HasDerivAt (fun w : ℂ => Complex.cos w / Complex.sin w)
    (-1 / Complex.sin z ^ 2) z
  have hd := (hasDerivAt_cos z).div (hasDerivAt_sin z) hz
  have he : ((-Complex.sin z) * Complex.sin z - Complex.cos z * (Complex.cos z)) = -1 := by
    have h := Complex.sin_sq_add_cos_sq z
    linear_combination -h
  simpa only [he, Pi.div_def] using hd

theorem holomorphicOn_cot : Specs.D12Complex.Ch02.Trigonometric.holomorphicOn_cot_type := by
  change HolomorphicOn {z : ℂ | Complex.sin z ≠ 0}
    (fun z => Complex.cos z / Complex.sin z)
  have h := holomorphicOn_div_nonzeroSet Set.univ Complex.cos Complex.sin
    holomorphicOn_cos holomorphicOn_sin
  simpa only [Set.mem_univ, true_and] using h

theorem tanh_eq_quotient : Specs.D12Complex.Ch02.Trigonometric.tanh_eq_quotient_type := by
  intro z
  rfl

theorem hasDerivAt_tanh : Specs.D12Complex.Ch02.Trigonometric.hasDerivAt_tanh_type := by
  intro z hz
  change HasDerivAt (fun w : ℂ => Complex.sinh w / Complex.cosh w)
    (1 / Complex.cosh z ^ 2) z
  have hd := (hasDerivAt_sinh z).div (hasDerivAt_cosh z) hz
  have he : ((Complex.cosh z) * Complex.cosh z - Complex.sinh z * (Complex.sinh z)) = 1 := by
    have h := Complex.cosh_sq_sub_sinh_sq z
    linear_combination h
  simpa only [he, Pi.div_def] using hd

theorem holomorphicOn_tanh : Specs.D12Complex.Ch02.Trigonometric.holomorphicOn_tanh_type := by
  change HolomorphicOn {z : ℂ | Complex.cosh z ≠ 0}
    (fun z => Complex.sinh z / Complex.cosh z)
  have h := holomorphicOn_div_nonzeroSet Set.univ Complex.sinh Complex.cosh
    holomorphicOn_sinh holomorphicOn_cosh
  simpa only [Set.mem_univ, true_and] using h

theorem coth_eq_quotient : Specs.D12Complex.Ch02.Trigonometric.coth_eq_quotient_type := by
  intro z
  rfl

theorem hasDerivAt_coth : Specs.D12Complex.Ch02.Trigonometric.hasDerivAt_coth_type := by
  intro z hz
  change HasDerivAt (fun w : ℂ => Complex.cosh w / Complex.sinh w)
    (-1 / Complex.sinh z ^ 2) z
  have hd := (hasDerivAt_cosh z).div (hasDerivAt_sinh z) hz
  have he : ((Complex.sinh z) * Complex.sinh z - Complex.cosh z * (Complex.cosh z)) = -1 := by
    have h := Complex.cosh_sq_sub_sinh_sq z
    linear_combination -h
  simpa only [he, Pi.div_def] using hd

theorem holomorphicOn_coth : Specs.D12Complex.Ch02.Trigonometric.holomorphicOn_coth_type := by
  change HolomorphicOn {z : ℂ | Complex.sinh z ≠ 0}
    (fun z => Complex.cosh z / Complex.sinh z)
  have h := holomorphicOn_div_nonzeroSet Set.univ Complex.cosh Complex.sinh
    holomorphicOn_cosh holomorphicOn_sinh
  simpa only [Set.mem_univ, true_and] using h

end D12Complex.Trigonometric
