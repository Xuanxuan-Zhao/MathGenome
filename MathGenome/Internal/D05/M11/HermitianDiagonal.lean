import MathGenome.Internal.D05.M11.Hermitian
import MathGenome.Internal.Specs.D05.M11.HermitianDiagonal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Diagonal recovery for arbitrary complex sesquilinear forms. -/

namespace D05.M11.HermitianDiagonal

theorem polarization : Specs.D05.M11.HermitianDiagonal.polarization := by
  intro V _ _ B u v
  dsimp only
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply,
    smul_eq_mul, Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem diagonal_ext : Specs.D05.M11.HermitianDiagonal.diagonal_ext := by
  intro V _ _ B C h
  ext u v
  rw [polarization B u v, polarization C u v]
  simp only [h]

theorem eq_zero_iff_diagonal_zero :
    Specs.D05.M11.HermitianDiagonal.eq_zero_iff_diagonal_zero := by
  intro V _ _ B
  constructor
  · intro h v
    simp [h]
  · intro h
    exact diagonal_ext B 0 h

theorem hermitian_iff_real_diagonal :
    Specs.D05.M11.HermitianDiagonal.hermitian_iff_real_diagonal := by
  intro V _ _ B
  constructor
  · exact D05.M11.Hermitian.diagonal_real B
  · intro h u v
    -- The imaginary parts at u+v and u+i v recover the two symmetry equations.
    have hi (w : V) : (B w w).im = 0 := by
      obtain ⟨r, hr⟩ := h w
      rw [hr]
      rfl
    have hadd := hi (u + v)
    have hI := hi (u + Complex.I • v)
    simp only [map_add, LinearMap.add_apply] at hadd hI
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply,
      smul_eq_mul, Complex.conj_I, Complex.add_im, Complex.mul_im, Complex.mul_re,
      Complex.neg_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, neg_mul,
      zero_add] at hadd hI
    apply Complex.ext
    · simp only [Complex.star_def, Complex.conj_re]
      linear_combination hI - hi u - hi v
    · simp only [Complex.star_def, Complex.conj_im]
      linear_combination hadd - hi u - hi v

theorem real_skew_counterexample :
    Specs.D05.M11.HermitianDiagonal.real_skew_counterexample := by
  let b := fun (x y : Fin 2 → ℝ) => x 0 * y 1 - x 1 * y 0
  have ha : ∀ x x' y, b (x + x') y = b x y + b x' y := by
    intros
    dsimp [b]
    ring
  have hs : ∀ (a : ℝ) x y, b (a • x) y = a * b x y := by
    intros
    dsimp [b]
    ring
  have hb : ∀ x y y', b x (y + y') = b x y + b x y' := by
    intros
    dsimp [b]
    ring
  have ht : ∀ (a : ℝ) x y, b x (a • y) = a * b x y := by
    intros
    dsimp [b]
    ring
  let B := LinearMap.mk₂ ℝ b ha hs hb ht
  have hB (x y : Fin 2 → ℝ) : B x y = x 0 * y 1 - x 1 * y 0 := rfl
  let e₀ : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
  let e₁ : Fin 2 → ℝ := fun i => if i = 1 then 1 else 0
  have h01 : B e₀ e₁ = 1 := by norm_num [hB, e₀, e₁]
  have h10 : B e₁ e₀ = -1 := by norm_num [hB, e₀, e₁]
  refine ⟨B, hB, ?_, ?_, ?_, ?_⟩
  · intro hz
    have : B e₀ e₁ = 0 := by rw [hz]; rfl
    rw [h01] at this
    exact one_ne_zero this
  · intro x y
    rw [hB, hB]
    ring
  · intro x
    rw [hB]
    ring
  · intro hsymm
    have hh := hsymm e₀ e₁
    rw [h01, h10] at hh
    norm_num at hh

end D05.M11.HermitianDiagonal
