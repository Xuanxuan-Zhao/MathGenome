import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.Representation
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.PeriodicSetup
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.FiniteChanges
import Mathlib.Algebra.BigOperators.Group.Finset.Interval

noncomputable section
namespace SingleVariableAnalysis
open Riemann
open scoped BigOperators
namespace Fourier

/-- Euler's formula with exactly the integer-frequency normalization in the source. -/
theorem mode_euler (n : ℤ) (x : ℝ) :
    fourierMode n x = (Real.cos ((n : ℝ) * x) : ℂ) +
      (Real.sin ((n : ℝ) * x) : ℂ) * Complex.I := by
  unfold fourierMode Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.modeValue
  rw [show (n : ℂ) * (x : ℂ) = (((n : ℝ) * x : ℝ) : ℂ) by simp]
  simpa only [mul_comm] using Complex.exp_ofReal_mul_I ((n : ℝ) * x)

theorem realIntegral_neg {g : ℝ → ℝ} {a b : ℝ}
    (hg : RealIntegrable g a b) (hn : RealIntegrable (fun x => -(g x)) a b) :
    realIntegral _ hn = -(realIntegral g hg) := by
  obtain ⟨h, he⟩ := real_mul_value hg (-1)
  simpa only [neg_one_mul] using he

/-- A complex integral assembled from two integrable real components. -/
theorem integral_re_im {g : ℝ → ℂ} {u v : ℝ → ℝ} {a b : ℝ}
    (hg : ComplexIntegrable g a b) (hu : RealIntegrable u a b)
    (hv : RealIntegrable v a b)
    (hre : (fun x => (g x).re) = u) (him : (fun x => (g x).im) = v) :
    complexIntegral g hg = (realIntegral u hu : ℂ) + (realIntegral v hv : ℂ) * Complex.I := by
  subst u; subst v
  rfl

end Fourier

open Specs.SingleVariableAnalysis.Ch19.Representation

/-- c₀ = a₀/2, with no convergence assertion. -/
theorem fourierCoeff_zero_real :
    Specs.SingleVariableAnalysis.Ch19.Representation.zeroCoefficient := by
  intro f hf h
  have hre : (fun x => (((f x : ℂ) * fourierMode (-0) x)).re) = f := by
    funext x
    rw [Fourier.mode_euler]
    simp only [Int.cast_neg, Int.cast_zero, Int.cast_natCast, neg_mul, Real.cos_neg,
      Real.sin_neg, zero_mul, Real.cos_zero, Real.sin_zero,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero,
      zero_sub, mul_neg, neg_zero, neg_neg]
  have him : (fun x => (((f x : ℂ) * fourierMode (-0) x)).im) = fun _ => 0 := by
    funext x
    rw [Fourier.mode_euler]
    simp only [Int.cast_neg, Int.cast_zero, Int.cast_natCast, neg_mul, Real.cos_neg,
      Real.sin_neg, zero_mul, Real.cos_zero, Real.sin_zero,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero,
      zero_sub, mul_neg, neg_zero, neg_neg]
  obtain ⟨hz, hIz⟩ := real_zero_value (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos])
  have he := Fourier.integral_re_im (h 0) hf.2 hz hre him
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegral _ (h 0) = _
  rw [he, hIz]
  simp only [Complex.ofReal_zero, zero_mul, add_zero]
  simp only [Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.aZeroValue,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

/-- Euler's identity separates a positive-frequency coefficient into its real integrals. -/
theorem fourierCoeff_positive_real :
    Specs.SingleVariableAnalysis.Ch19.Representation.positiveCoefficient := by
  intro f hf h ha hb n
  have hre : (fun x => (((f x : ℂ) * fourierMode (-(n : ℤ)) x)).re) =
      fun x => f x * Real.cos ((n : ℝ) * x) := by
    funext x
    rw [Fourier.mode_euler]
    simp only [Int.cast_neg, Int.cast_zero, Int.cast_natCast, neg_mul, Real.cos_neg,
      Real.sin_neg, zero_mul, Real.cos_zero, Real.sin_zero,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero,
      zero_sub, mul_neg, neg_zero, neg_neg]
  have him : (fun x => (((f x : ℂ) * fourierMode (-(n : ℤ)) x)).im) =
      fun x => -(f x * Real.sin ((n : ℝ) * x)) := by
    funext x
    rw [Fourier.mode_euler]
    simp only [Int.cast_neg, Int.cast_zero, Int.cast_natCast, neg_mul, Real.cos_neg,
      Real.sin_neg, zero_mul, Real.cos_zero, Real.sin_zero,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero,
      zero_sub, mul_neg, neg_zero, neg_neg]
  have hn : RealIntegrable (fun x => -(f x * Real.sin ((n : ℝ) * x)))
      (-Real.pi) Real.pi := by
    simpa only [neg_one_mul] using (real_mul_value (hb n) (-1)).choose
  have he := Fourier.integral_re_im (h n) (ha n) hn hre him
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegral _ (h n) = _
  rw [he, Fourier.realIntegral_neg (hb n) hn]
  simp only [Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.cosineCoefficientValue,
    Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.sineCoefficientValue,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat, Complex.ofReal_neg]
  ring

/-- The negative-frequency formula has the opposite sine sign. -/
theorem fourierCoeff_negative_real :
    Specs.SingleVariableAnalysis.Ch19.Representation.negativeCoefficient := by
  intro f hf h ha hb n
  have hre : (fun x => (((f x : ℂ) * fourierMode (-(-(n : ℤ))) x)).re) =
      fun x => f x * Real.cos ((n : ℝ) * x) := by
    funext x
    rw [Fourier.mode_euler]
    simp only [Int.cast_neg, Int.cast_zero, Int.cast_natCast, neg_mul, Real.cos_neg,
      Real.sin_neg, zero_mul, Real.cos_zero, Real.sin_zero,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero,
      zero_sub, mul_neg, neg_zero, neg_neg]
  have him : (fun x => (((f x : ℂ) * fourierMode (-(-(n : ℤ))) x)).im) =
      fun x => f x * Real.sin ((n : ℝ) * x) := by
    funext x
    rw [Fourier.mode_euler]
    simp only [Int.cast_neg, Int.cast_zero, Int.cast_natCast, neg_mul, Real.cos_neg,
      Real.sin_neg, zero_mul, Real.cos_zero, Real.sin_zero,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, sub_zero,
      zero_sub, mul_neg, neg_zero, neg_neg]
  have he := Fourier.integral_re_im (h (-n)) (ha n) (hb n) hre him
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegral _ (h (-n)) = _
  erw [he]
  simp only [Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.cosineCoefficientValue,
    Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.sineCoefficientValue,
    Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring


namespace Fourier

/-- The two opposite frequencies combine pointwise into one real sine/cosine term. -/
theorem pair_real (f : ℝ → ℝ)
    (hf : Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.periodicRealValue f)
    (h : ComplexWeights (fun x => (f x : ℂ)))
    (ha : CosineWeights f) (hb : SineWeights f) (n : ℕ+) (x : ℝ) :
    fourierCoeff (fun t => (f t : ℂ)) n (h n) * fourierMode n x +
      fourierCoeff (fun t => (f t : ℂ)) (-n) (h (-n)) * fourierMode (-n) x =
    ((fourierCosCoeff f n (ha n) * Real.cos ((n : ℝ) * x) +
      fourierSinCoeff f n (hb n) * Real.sin ((n : ℝ) * x) : ℝ) : ℂ) := by
  dsimp only [fourierCoeff, fourierCosCoeff, fourierSinCoeff]
  rw [fourierCoeff_positive_real f hf h ha hb n,
    fourierCoeff_negative_real f hf h ha hb n, mode_euler, mode_euler]
  simp only [Int.cast_neg, neg_mul, Real.cos_neg, Real.sin_neg]
  apply Complex.ext <;> simp <;> ring

/-- A finite modification of a bounded function is still bounded. -/
theorem norm_bound_of_finite_changes {E : Type*} [NormedAddCommGroup E]
    {f g : ℝ → E} {a b : ℝ}
    (hf : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖f x‖ ≤ M)
    (hs : {x | x ∈ Set.Icc a b ∧ f x ≠ g x}.Finite) :
    ∃ M : ℝ, ∀ x ∈ Set.Icc a b, ‖g x‖ ≤ M := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨C, hC⟩ := (hs.image (fun x => ‖g x‖)).bddAbove
  refine ⟨max M C, fun x hx => ?_⟩
  by_cases he : f x = g x
  · exact (he ▸ hM x hx).trans (le_max_left _ _)
  · exact (hC (Set.mem_image_of_mem _ ⟨hx, he⟩)).trans (le_max_right _ _)

/-- Multiplication by a fixed weight cannot create new exceptional points. -/
theorem finite_changes_mul {K : Type*} [Mul K] {f g w : ℝ → K} {a b : ℝ}
    (hs : {x | x ∈ Set.Icc a b ∧ f x ≠ g x}.Finite) :
    {x | x ∈ Set.Icc a b ∧ f x * w x ≠ g x * w x}.Finite := by
  apply hs.subset
  intro x hx
  exact ⟨hx.1, fun he => hx.2 (congrArg (fun z => z * w x) he)⟩

end Fourier

/-- Finite periodic seam assignments preserve proper Riemann integrability. -/
theorem fourier_finite_changes_integrable :
    Specs.SingleVariableAnalysis.Ch19.Representation.finiteChangesIntegrable := by
  intro f g hf hg hs
  have hb := Fourier.norm_bound_of_finite_changes (ComplexIntegrable.norm_bound hf.2) hs
  obtain ⟨hi, _⟩ := complex_finite_changes f g
    (ComplexIntegrable.norm_bound hf.2) hb hs hf.2
  exact ⟨hg, hi⟩

/-- Every complex Fourier coefficient is unchanged under finite changes per period. -/
theorem fourierCoeff_finite_changes :
    Specs.SingleVariableAnalysis.Ch19.Representation.coefficientsFiniteChanges := by
  intro f g hf hg hs h j n
  obtain ⟨hi, he⟩ := complex_finite_changes
    (fun x => f x * fourierMode (-n) x) (fun x => g x * fourierMode (-n) x)
    (ComplexIntegrable.norm_bound (h n)) (ComplexIntegrable.norm_bound (j n))
    (Fourier.finite_changes_mul hs) (h n)
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegral _ (h n) =
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * complexIntegral _ (j n)
  exact congrArg (fun z : ℂ => ((1 / (2 * Real.pi) : ℝ) : ℂ) * z) he.symm

/-- The a₀, aₙ and bₙ coefficients have the same finite-change invariance. -/
theorem fourierRealCoefficients_finite_changes :
    Specs.SingleVariableAnalysis.Ch19.Representation.realCoefficientsFiniteChanges := by
  intro f g hf hg hs ha hb ja jb
  constructor
  · obtain ⟨hi, he⟩ := real_finite_changes f g (RealIntegrable.bounded hf.2) (RealIntegrable.bounded hg.2) hs hf.2
    change (1 / Real.pi) * realIntegral _ hf.2 = (1 / Real.pi) * realIntegral _ hg.2
    exact congrArg (fun z : ℝ => (1 / Real.pi) * z) he.symm
  · intro n
    constructor
    · obtain ⟨hi, he⟩ := real_finite_changes
        (fun x => f x * Real.cos ((n : ℝ) * x))
        (fun x => g x * Real.cos ((n : ℝ) * x))
        (RealIntegrable.bounded (ha n)) (RealIntegrable.bounded (ja n)) (Fourier.finite_changes_mul hs) (ha n)
      change (1 / Real.pi) * realIntegral _ (ha n) = (1 / Real.pi) * realIntegral _ (ja n)
      exact congrArg (fun z : ℝ => (1 / Real.pi) * z) he.symm
    · obtain ⟨hi, he⟩ := real_finite_changes
        (fun x => f x * Real.sin ((n : ℝ) * x))
        (fun x => g x * Real.sin ((n : ℝ) * x))
        (RealIntegrable.bounded (hb n)) (RealIntegrable.bounded (jb n)) (Fourier.finite_changes_mul hs) (hb n)
      change (1 / Real.pi) * realIntegral _ (hb n) = (1 / Real.pi) * realIntegral _ (jb n)
      exact congrArg (fun z : ℝ => (1 / Real.pi) * z) he.symm

/-- Equality of the complex and real finite Fourier sums, at every point. -/
theorem fourierPartialSum_real :
    Specs.SingleVariableAnalysis.Ch19.Representation.finitePartialSum := by
  intro f hf h ha hb N x
  induction N with
  | zero =>
    simpa [Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.partialSumValue,
      Fourier.mode_euler, Complex.ofReal_div] using fourierCoeff_zero_real f hf h
  | succ N ih =>
    unfold Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.partialSumValue at ih ⊢
    simp only [Nat.cast_add, Nat.cast_one]
    rw [Finset.sum_Icc_succ_eq_add_endpoints]
    rw [show Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.coefficientValue
        (fun t => (f t : ℂ)) ((N : ℤ)+1) (h _) * fourierMode ((N : ℤ)+1) x +
        Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.coefficientValue
        (fun t => (f t : ℂ)) (-((N : ℤ)+1)) (h _) * fourierMode (-((N : ℤ)+1)) x =
        ((fourierCosCoeff f ⟨N+1, Nat.succ_pos N⟩ (ha _) * Real.cos (((N+1 : ℕ) : ℝ) * x) +
          fourierSinCoeff f ⟨N+1, Nat.succ_pos N⟩ (hb _) * Real.sin (((N+1 : ℕ) : ℝ) * x) : ℝ) : ℂ)
        from by simpa using Fourier.pair_real f hf h ha hb ⟨N+1, Nat.succ_pos N⟩ x]
    rw [ih, Finset.sum_range_succ]
    push_cast
    ring

end SingleVariableAnalysis
