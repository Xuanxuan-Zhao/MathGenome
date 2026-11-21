import MathGenome.Internal.Specs.D05.M12.Parallelogram
import MathGenome.Internal.D05.M12.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! K05.12.parallelogram: expansions, polarization, and uniqueness from the norm. -/

noncomputable section

namespace D05.M12.Parallelogram

open D05

/-- Expand a diagonal using just the two slot rules. -/
theorem diagonal_add {F V : Type*} [RCLike F] [AddCommGroup V] [Module F V]
    (h : V → V → F) (hh : IsFirstInnerProduct h) (u v : V) :
    h (u + v) (u + v) = h u u + h v v + h u v + h v u := by
  have hl (x y z : V) : h (x + y) z = h x z + h y z := by
    simpa using hh.1 1 1 x y z
  have hr (x y z : V) : h x (y + z) = h x y + h x z := by
    simpa using InnerProduct.second_slot_of_axioms h hh 1 1 x y z
  rw [hl, hr, hr]
  ring

theorem norm_sq_expansions : Specs.D05.M12.Parallelogram.norm_sq_expansions := by
  intro F V _ _ _ h hh u v
  have hadd (x y : V) :
      D05.inducedNorm h (x + y) ^ 2 =
        D05.inducedNorm h x ^ 2 + D05.inducedNorm h y ^ 2 +
          2 * RCLike.re (h x y) := by
    simp only [Norm.inducedNorm_sq h hh, diagonal_add h hh, map_add]
    rw [hh.2.1 x y]
    simp only [RCLike.conj_re]
    ring
  refine ⟨hadd u v, ?_⟩
  have hneg : h u (-v) = -h u v := by
    simpa using InnerProduct.second_slot_of_axioms h hh (-1) 0 u v 0
  have hn : D05.inducedNorm h (-v) ^ 2 = D05.inducedNorm h v ^ 2 := by
    simpa using Norm.inducedNorm_smul_sq h hh (-1) v
  rw [sub_eq_add_neg, hadd, hn, hneg, map_neg]
  ring

theorem parallelogram : Specs.D05.M12.Parallelogram.parallelogram := by
  intro F V _ _ _ h hh u v
  obtain ⟨ha, hs⟩ := norm_sq_expansions h hh u v
  rw [ha, hs]
  ring

theorem real_polarization : Specs.D05.M12.Parallelogram.real_polarization := by
  intro V _ _ h hh u v
  obtain ⟨ha, hs⟩ := norm_sq_expansions h hh u v
  change _ = _ + _ + 2 * h u v at ha
  change _ = _ + _ - 2 * h u v at hs
  linarith

theorem complex_polarization : Specs.D05.M12.Parallelogram.complex_polarization := by
  intro V _ _ h hh u v
  obtain ⟨ha, hs⟩ := norm_sq_expansions h hh u v
  obtain ⟨hai, hsi⟩ := norm_sq_expansions h hh u (Complex.I • v)
  have hi : h u (Complex.I • v) = -Complex.I * h u v := by
    simpa using InnerProduct.second_slot_of_axioms h hh Complex.I 0 u v 0
  rw [hi] at hai hsi
  simp only [RCLike.re_to_complex] at ha hs
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.sub_re, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.div_re, Complex.one_re, Complex.one_im]
    norm_num
    linarith
  · simp [RCLike.re_to_complex, Complex.mul_re] at hai hsi
    simp only [Complex.mul_im, Complex.sub_im, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.div_re, Complex.div_im, Complex.one_re, Complex.one_im]
    norm_num
    linarith

theorem real_inner_determined_by_norm :
    Specs.D05.M12.Parallelogram.real_inner_determined_by_norm := by
  intro V _ _ h k hh hk hn
  funext u v
  rw [real_polarization h hh, real_polarization k hk]
  simp only [hn]

theorem complex_inner_determined_by_norm :
    Specs.D05.M12.Parallelogram.complex_inner_determined_by_norm := by
  intro V _ _ h k hh hk hn
  funext u v
  rw [complex_polarization h hh, complex_polarization k hk]
  simp only [hn]

theorem canonical_parallelogram :
    Specs.D05.M12.Parallelogram.canonical_parallelogram := by
  intro F V _ _ _ u v
  have hn (w : V) : D05.inducedNorm (firstInner (F := F)) w = ‖w‖ :=
    Norm.inducedNorm_eq_norm w
  simpa only [hn] using
    parallelogram (firstInner (F := F)) InnerProduct.firstInner_axioms u v

theorem canonical_real_polarization :
    Specs.D05.M12.Parallelogram.canonical_real_polarization := by
  intro V _ _ u v
  have hn (w : V) : D05.inducedNorm (firstInner (F := ℝ)) w = ‖w‖ :=
    Norm.inducedNorm_eq_norm w
  simpa only [hn] using
    real_polarization (firstInner (F := ℝ)) InnerProduct.firstInner_axioms u v

theorem canonical_complex_polarization :
    Specs.D05.M12.Parallelogram.canonical_complex_polarization := by
  intro V _ _ u v
  have hn (w : V) : D05.inducedNorm (firstInner (F := ℂ)) w = ‖w‖ :=
    Norm.inducedNorm_eq_norm w
  simpa only [hn] using
    complex_polarization (firstInner (F := ℂ)) InnerProduct.firstInner_axioms u v

end D05.M12.Parallelogram
