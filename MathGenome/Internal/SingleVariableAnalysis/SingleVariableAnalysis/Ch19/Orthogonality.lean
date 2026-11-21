import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.Orthogonality
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.Representation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.FtcSecond

/-! Orthogonality for the manuscript's proper Riemann pairing on actual functions.
Newton–Leibniz evaluates each integer mode: the zero mode integrates to 2π;
a nonzero mode has primitive eₙ/(in) with equal endpoint values. Euler's
identity gives the real means, and product-to-sum gives real orthogonality.
-/

noncomputable section
namespace SingleVariableAnalysis
open Riemann

abbrev fourierPairing := Specs.SingleVariableAnalysis.Ch19.Orthogonality.pairingValue
abbrev fourierRealMean := Specs.SingleVariableAnalysis.Ch19.Orthogonality.realMeanValue

namespace FourierOrthogonality
open Fourier

private theorem period_order : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]

theorem mode_continuous (n : ℤ) : Continuous (fourierMode n) :=
  Complex.continuous_exp.comp
    (continuous_const.mul (continuous_const.mul Complex.continuous_ofReal))

theorem mode_mul_conj (n m : ℤ) (x : ℝ) :
    fourierMode n x * star (fourierMode m x) = fourierMode (n-m) x := by
  rw [mode_euler, mode_euler, mode_euler]
  simp only [Int.cast_sub, sub_mul, Real.cos_sub, Real.sin_sub]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
      mul_zero, mul_one, add_zero, zero_add, sub_zero] <;> ring

theorem mode_endpoints (n : ℤ) : fourierMode n Real.pi = fourierMode n (-Real.pi) := by
  rw [mode_euler, mode_euler]
  simp [Real.sin_int_mul_pi]

/-- The derivative uses real increments, as required by the source. -/
theorem mode_hasDerivAt (n : ℤ) (x : ℝ) :
    HasDerivAt (fourierMode n) (Complex.I * (n : ℂ) * fourierMode n x) x := by
  have h := expSeries_real_parameter_hasDerivAt (Complex.I * (n : ℂ)) x
  change HasDerivAt (fun s : ℝ => seriesExp ((s : ℂ) * (Complex.I * (n : ℂ))))
    ((Complex.I * (n : ℂ)) * seriesExp ((x : ℂ) * (Complex.I * (n : ℂ)))) x at h
  have heq : seriesExp = Complex.exp := funext (fun z => expSeries_eq_complexExp z)
  rw [heq] at h
  have hf : fourierMode n = fun s : ℝ => Complex.exp ((s : ℂ) * (Complex.I * (n : ℂ))) := by
    funext s
    change Complex.exp (Complex.I * ((n : ℂ) * (s : ℂ))) = _
    congr 1
    ring
  rw [hf]
  exact h

/-- Newton–Leibniz evaluates the unnormalized integral of every integer mode. -/
theorem mode_integral (n : ℤ)
    (h : ComplexIntegrable (fourierMode n) (-Real.pi) Real.pi) :
    complexIntegral _ h = if n = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  by_cases hn : n = 0
  · subst n
    have he := complex_ftc_second (fun x : ℝ => (x : ℂ)) (fourierMode 0)
      (-Real.pi) Real.pi period_order Complex.continuous_ofReal.continuousOn
      (fun x _ => by simpa [fourierMode, Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.modeValue]
        using (hasDerivAt_id x).ofReal_comp) h
    simpa [two_mul] using he
  · have hz : Complex.I * (n : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hn)
    have hd (x : ℝ) : HasDerivAt
        (fun t => fourierMode n t / (Complex.I * (n : ℂ))) (fourierMode n x) x := by
      convert (mode_hasDerivAt n x).div_const (Complex.I * (n : ℂ)) using 1
      exact (mul_div_cancel_left₀ _ hz).symm
    have he := complex_ftc_second
      (fun x => fourierMode n x / (Complex.I * (n : ℂ))) (fourierMode n)
      (-Real.pi) Real.pi period_order
      ((mode_continuous n).div_const _).continuousOn (fun x _ => hd x) h
    rw [mode_endpoints] at he
    simpa [hn] using he

end FourierOrthogonality

open Specs.SingleVariableAnalysis.Ch19.Orthogonality

theorem fourierPairing_integrable : pairingIntegrability := by
  intro f g hf hg
  apply complex_product hf
  refine ⟨?_, ?_⟩
  · simpa using hg.1
  · simpa using (real_mul_value hg.2 (-1)).choose

theorem fourierMode_integrable : modeIntegrability := by
  intro n
  exact Fourier.complexIntegrable_of_continuousOn FourierOrthogonality.period_order
    (FourierOrthogonality.mode_continuous n).continuousOn

theorem fourierMode_orthogonality : modeOrthogonality := by
  intro n m h
  have he : (fun x => fourierMode n x * star (fourierMode m x)) = fourierMode (n-m) :=
    funext (FourierOrthogonality.mode_mul_conj n m)
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegral _ h = _
  have hi : complexIntegral _ h = complexIntegral _ (fourierMode_integrable (n-m)) := by
    congr 1
  rw [hi]
  rw [FourierOrthogonality.mode_integral]
  by_cases hn : n = m
  · subst m
    simp only [sub_self, ite_true, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat]
    exact one_div_mul_cancel (mul_ne_zero (two_ne_zero' ℂ) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  · simp [sub_ne_zero.mpr hn, hn]

namespace FourierOrthogonality
open Fourier

theorem cosine_integrable (n : ℤ) :
    RealIntegrable (fun x => Real.cos ((n : ℝ) * x)) (-Real.pi) Real.pi :=
  realIntegrable_of_continuousOn period_order
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn

theorem sine_integrable (n : ℤ) :
    RealIntegrable (fun x => Real.sin ((n : ℝ) * x)) (-Real.pi) Real.pi :=
  realIntegrable_of_continuousOn period_order
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn

theorem mode_normalized_integral (n : ℤ)
    (h : ComplexIntegrable (fourierMode n) (-Real.pi) Real.pi) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegral _ h =
      if n = 0 then 1 else 0 := by
  rw [mode_integral]
  split_ifs
  · norm_cast
    exact one_div_mul_cancel (mul_ne_zero (two_ne_zero' ℝ) Real.pi_ne_zero)
  · simp

/-- Taking components of the complex mode identity gives the two real means. -/
theorem mode_real_means (n : ℤ)
    (hc : RealIntegrable (fun x => Real.cos ((n : ℝ) * x)) (-Real.pi) Real.pi)
    (hs : RealIntegrable (fun x => Real.sin ((n : ℝ) * x)) (-Real.pi) Real.pi) :
    fourierRealMean _ hc = (if n = 0 then 1 else 0) ∧ fourierRealMean _ hs = 0 := by
  have hm := fourierMode_integrable n
  have hre : (fun x => (fourierMode n x).re) = fun x => Real.cos ((n : ℝ) * x) := by
    funext x
    rw [mode_euler]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
  have him : (fun x => (fourierMode n x).im) = fun x => Real.sin ((n : ℝ) * x) := by
    funext x
    rw [mode_euler]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, mul_one, mul_zero, add_zero, zero_add]
  have he := mode_normalized_integral n hm
  rw [integral_re_im hm hc hs hre him] at he
  constructor
  · have hr := congrArg Complex.re he
    simpa [fourierRealMean, realMeanValue, apply_ite] using hr
  · have hi := congrArg Complex.im he
    simpa [fourierRealMean, realMeanValue, apply_ite] using hi

/-- Linearity of the normalized proper real integral, with arbitrary witnesses. -/
theorem realMean_add {f g : ℝ → ℝ}
    (hf : RealIntegrable f (-Real.pi) Real.pi)
    (hg : RealIntegrable g (-Real.pi) Real.pi)
    (h : RealIntegrable (fun x => f x + g x) (-Real.pi) Real.pi) :
    fourierRealMean _ h = fourierRealMean _ hf + fourierRealMean _ hg := by
  have he := (real_add_value hf hg).choose_spec
  change (1 / (2 * Real.pi)) * realIntegral _ h = _
  rw [he]
  unfold fourierRealMean realMeanValue
  ring

theorem realMean_mul {f : ℝ → ℝ}
    (hf : RealIntegrable f (-Real.pi) Real.pi) (c : ℝ)
    (h : RealIntegrable (fun x => c * f x) (-Real.pi) Real.pi) :
    fourierRealMean _ h = c * fourierRealMean _ hf := by
  have he := (real_mul_value hf c).choose_spec
  change (1 / (2 * Real.pi)) * realIntegral _ h = _
  rw [he]
  unfold fourierRealMean realMeanValue
  ring

/-- Transfer a pointwise product-to-sum identity to its normalized mean. -/
theorem realMean_two_mul {f u v : ℝ → ℝ}
    (hf : RealIntegrable f (-Real.pi) Real.pi)
    (hu : RealIntegrable u (-Real.pi) Real.pi)
    (hv : RealIntegrable v (-Real.pi) Real.pi)
    (he : ∀ x, 2 * f x = u x + v x) :
    2 * fourierRealMean _ hf = fourierRealMean _ hu + fourierRealMean _ hv := by
  have hsum := (real_add_value hu hv).choose
  have hmul := (real_mul_value hf 2).choose
  rw [← realMean_mul hf 2 hmul, ← realMean_add hu hv hsum]
  congr 1
  exact funext he

end FourierOrthogonality

theorem fourierRealProducts_integrable : realProductIntegrability := by
  intro n m
  exact ⟨real_product (FourierOrthogonality.cosine_integrable n) (FourierOrthogonality.cosine_integrable m),
    real_product (FourierOrthogonality.sine_integrable n) (FourierOrthogonality.sine_integrable m),
    real_product (FourierOrthogonality.sine_integrable n) (FourierOrthogonality.cosine_integrable m)⟩

theorem fourierCosine_mean : cosineMean := by
  intro n h
  exact (FourierOrthogonality.mode_real_means n h (FourierOrthogonality.sine_integrable n)).1

theorem fourierSine_mean : sineMean := by
  intro n h
  exact (FourierOrthogonality.mode_real_means n (FourierOrthogonality.cosine_integrable n) h).2

theorem fourierCosine_orthogonality : cosineOrthogonality := by
  intro n m h
  have he := FourierOrthogonality.realMean_two_mul h
    (FourierOrthogonality.cosine_integrable ((n : ℤ) - m))
    (FourierOrthogonality.cosine_integrable ((n : ℤ) + m)) (fun x => ?_)
  · dsimp only [fourierRealMean] at he
    rw [fourierCosine_mean ((n : ℤ) - m), fourierCosine_mean ((n : ℤ) + m)] at he
    have hpos : (n : ℤ) + m ≠ 0 := by
      have hn : (0 : ℤ) < n := by exact_mod_cast n.pos
      have hm : (0 : ℤ) < m := by exact_mod_cast m.pos
      omega
    have heq : (n : ℤ) - m = 0 ↔ n = m := by
      rw [sub_eq_zero]; exact_mod_cast (Iff.rfl : n = m ↔ n = m)
    simp only [hpos, ↓reduceIte, heq] at he
    split_ifs at he ⊢ <;> linarith
  · simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast]
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring

theorem fourierSine_orthogonality : sineOrthogonality := by
  intro n m h
  have hu := FourierOrthogonality.cosine_integrable ((n : ℤ) - m)
  have hv := (real_mul_value (FourierOrthogonality.cosine_integrable ((n : ℤ) + m)) (-1)).choose
  have he := FourierOrthogonality.realMean_two_mul h hu hv (fun x => ?_)
  · have hscale := FourierOrthogonality.realMean_mul (FourierOrthogonality.cosine_integrable ((n : ℤ) + m)) (-1) hv
    dsimp only [fourierRealMean] at he hscale
    rw [fourierCosine_mean ((n : ℤ) - m), hscale,
      fourierCosine_mean ((n : ℤ) + m)] at he
    have hpos : (n : ℤ) + m ≠ 0 := by
      have hn : (0 : ℤ) < n := by exact_mod_cast n.pos
      have hm : (0 : ℤ) < m := by exact_mod_cast m.pos
      omega
    have heq : (n : ℤ) - m = 0 ↔ n = m := by
      rw [sub_eq_zero]; exact_mod_cast (Iff.rfl : n = m ↔ n = m)
    simp only [hpos, ↓reduceIte, heq] at he
    split_ifs at he ⊢ <;> linarith
  · simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast]
    rw [sub_mul, add_mul, Real.cos_sub, Real.cos_add]
    ring

theorem fourierMixed_orthogonality : mixedOrthogonality := by
  intro n m h
  have he := FourierOrthogonality.realMean_two_mul h
    (FourierOrthogonality.sine_integrable (n+m)) (FourierOrthogonality.sine_integrable (n-m)) (fun x => ?_)
  · dsimp only [fourierRealMean] at he
    rw [fourierSine_mean (n+m), fourierSine_mean (n-m)] at he
    linarith
  · simp only [Int.cast_sub, Int.cast_add]
    rw [add_mul, sub_mul, Real.sin_add, Real.sin_sub]
    ring

end SingleVariableAnalysis
