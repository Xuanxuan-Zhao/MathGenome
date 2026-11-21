import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Moments.StieltjesExistence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Moments.PolynomialMomentHilbertSpace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.FriedrichsExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.ScalarSpectralMoments
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.NonnegativeSpectralSupport
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Convert
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section
open MeasureTheory Polynomial
open scoped InnerProductSpace
namespace ExpandedFA.Moments.StieltjesExistence
open Unbounded PolynomialMomentHilbertSpaceSpec

/-- Multiplying the second argument by X shifts the real moment sequence. -/
theorem shifted_momentForm : Spec.ShiftedForm := by
  intro m p q
  have hL : ∀ r : ℂ[X], momentFunctional (shiftedMoments m) r =
      momentFunctional m (X * r) := by
    intro r
    induction r using Polynomial.induction_on' with
    | add r s hr hs => simp [mul_add, hr, hs]
    | monomial n c =>
      rw [X_mul_monomial, momentFunctional_monomial, momentFunctional_monomial]
      rfl
  unfold momentForm
  rw [hL]
  congr 1
  ring

/-- The original multiplication operator is nonnegative, with no strict lower
bound required and with the zero Hilbert space allowed. -/
theorem multiplication_semibounded (m : ℕ → ℝ) (h : HankelNonnegative m)
    (hs : HankelNonnegative (shiftedMoments m)) :
    FriedrichsExtension.SemiboundedSymmetric (multiplicationValue m h) 0 := by
  refine ⟨minimalMultiplication_dense m h, minimalMultiplication_symmetric m h, ?_⟩
  intro x
  obtain ⟨p, hp⟩ := x.property
  have hx : x = ⟨polynomialClass m h p, LinearMap.mem_range_self _ p⟩ :=
    Subtype.ext hp.symm
  subst x
  rw [minimalMultiplication_apply]
  change 0 * _ ≤ (inner ℂ (polynomialClass m h p)
    (polynomialClass m h (ofPolynomial (X * rawPolynomial p)))).re
  rw [zero_mul, polynomialClass_inner]
  exact (shifted_momentForm m (rawPolynomial p) (rawPolynomial p) ▸ hs (rawPolynomial p))

/-- Extending the multiplication graph preserves each polynomial vector under
every finite power; this uses the precise domain-carrying powers. -/
theorem polynomial_powers_of_extension (m : ℕ → ℝ) (h : HankelNonnegative m)
    (A : Operator ℂ (MomentHilbertSpace m h) (MomentHilbertSpace m h))
    (hA : multiplicationValue m h ≤ A) : PolynomialPowers m h A := by
  intro n
  induction n with
  | zero =>
    intro p
    refine ⟨Submodule.mem_top, ?_⟩
    change polynomialClass m h p = polynomialClass m h (ofPolynomial (X ^ 0 * rawPolynomial p))
    congr 1
    exact (show rawPolynomial p = X ^ 0 * rawPolynomial p by simp)
  | succ n ih =>
    intro p
    obtain ⟨hp, hev⟩ := ih p
    let q : MomentPolynomials m h := ofPolynomial (X ^ n * rawPolynomial p)
    have hq : polynomialClass m h q ∈ A.domain :=
      hA.1 (LinearMap.mem_range_self _ q)
    have hs : OperatorDomainsSpec.powerValue A n
        ⟨polynomialClass m h p, hp⟩ ∈ A.domain := by rw [hev]; exact hq
    refine ⟨⟨hp, hs⟩, ?_⟩
    change A ⟨OperatorDomainsSpec.powerValue A n ⟨polynomialClass m h p, hp⟩, hs⟩ = _
    have heq : (⟨OperatorDomainsSpec.powerValue A n
        ⟨polynomialClass m h p, hp⟩, hs⟩ : A.domain) =
        ⟨polynomialClass m h q, hq⟩ := Subtype.ext hev
    rw [heq, ← hA.2 (x := ⟨polynomialClass m h q, LinearMap.mem_range_self _ q⟩) rfl,
      minimalMultiplication_apply]
    congr 1
    change X * (X ^ n * rawPolynomial p) = X ^ (n + 1) * rawPolynomial p
    simp only [pow_succ', mul_assoc]

/-- Friedrichs supplies the actual nonnegative extension and its full power
identity on the polynomial core. -/
theorem nonnegative_extension : Spec.ExtensionExists := by
  intro m h hs
  obtain ⟨F, A, hA, _⟩ := FriedrichsExtension.friedrichs_extension (𝕜 := ℂ)
    (multiplicationValue m h) 0 (multiplication_semibounded m h hs)
  obtain ⟨hF, hle, hd, ha, hn⟩ := hA
  refine ⟨A, ⟨hle, hd, ?_, ha, ?_⟩, polynomial_powers_of_extension m h A hle⟩
  · rw [ha]
    exact LinearPMap.adjoint_isClosed hd
  · intro x
    change 0 ≤ RCLike.re (inner ℂ (x : MomentHilbertSpace m h) (A x))
    simpa only [zero_mul] using hn x

/-- Integrate a polynomial from its prescribed monomial moments; integrability
is proved separately so no totalized integral is used outside its domain. -/
theorem integral_polynomial (m : ℕ → ℝ) (μ : Measure ℝ) (hμ : Represents μ m)
    (p : ℂ[X]) :
    Integrable (fun t : ℝ => p.eval (t : ℂ)) μ ∧
      (∫ t : ℝ, p.eval (t : ℂ) ∂μ) = momentFunctional m p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    refine ⟨?_, ?_⟩
    · simp only [eval_add]
      convert! hp.1.add hq.1
    · simp only [eval_add, integral_add hp.1 hq.1, hp.2, hq.2, map_add]
  | monomial n c =>
    have hi : Integrable (fun t : ℝ => (t : ℂ) ^ n) μ := by
      convert! ((hμ.2.2 n).1.ofReal :
        Integrable (fun t : ℝ => ((t ^ n : ℝ) : ℂ)) μ) using 1
      funext t
      exact (Complex.ofReal_pow t n).symm
    refine ⟨by simpa only [eval_monomial] using hi.const_mul c, ?_⟩
    simp only [eval_monomial, integral_const_mul, momentFunctional_monomial]
    have he : (fun t : ℝ => (t : ℂ) ^ n) = (fun t : ℝ => ((t ^ n : ℝ) : ℂ)) := by
      funext t
      exact (Complex.ofReal_pow t n).symm
    rw [he, integral_complex_ofReal, (hμ.2.2 n).2]

/-- Conjugating coefficients conjugates values at real arguments. -/
theorem eval_conjugate (p : ℂ[X]) (t : ℝ) :
    (p.map (starRingEnd ℂ)).eval (t : ℂ) = star (p.eval (t : ℂ)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c => simp

/-- Both Hankel forms of any representing measure are nonnegative. -/
theorem stieltjes_necessity : Spec.Necessity := by
  intro m μ hμ
  have hn : ∀ᵐ t : ℝ ∂μ, 0 ≤ t := by
    have hh : ∀ᵐ t : ℝ ∂μ, t ∉ Set.Iio 0 := by
      apply ae_iff.mpr
      have he : {t : ℝ | ¬ t ∉ Set.Iio 0} = Set.Iio 0 := by ext t; simp
      rw [he]
      exact hμ.2.1
    filter_upwards [hh] with t ht
    exact le_of_not_gt ht
  have hdiag : ∀ (p : ℂ[X]) (t : ℝ),
      0 ≤ ((p.map (starRingEnd ℂ) * p).eval (t : ℂ)).re := by
    intro p t
    rw [eval_mul, eval_conjugate]
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    nlinarith [sq_nonneg (p.eval (t : ℂ)).re, sq_nonneg (p.eval (t : ℂ)).im]
  constructor
  · intro p
    obtain ⟨hi, he⟩ := integral_polynomial m μ hμ (p.map (starRingEnd ℂ) * p)
    change 0 ≤ (momentFunctional m (p.map (starRingEnd ℂ) * p)).re
    rw [← he]
    change 0 ≤ RCLike.re (∫ t : ℝ, (p.map (starRingEnd ℂ) * p).eval (t : ℂ) ∂μ)
    rw [← integral_re hi]
    exact integral_nonneg (fun t => hdiag p t)
  · intro p
    rw [shifted_momentForm]
    obtain ⟨hi, he⟩ := integral_polynomial m μ hμ (p.map (starRingEnd ℂ) * (X * p))
    change 0 ≤ (momentFunctional m (p.map (starRingEnd ℂ) * (X * p))).re
    rw [← he]
    change 0 ≤ RCLike.re (∫ t : ℝ, (p.map (starRingEnd ℂ) * (X * p)).eval (t : ℂ) ∂μ)
    rw [← integral_re hi]
    apply integral_nonneg_of_ae
    filter_upwards [hn] with t ht
    have heval : (p.map (starRingEnd ℂ) * (X * p)).eval (t : ℂ) =
        (t : ℂ) * ((p.map (starRingEnd ℂ) * p).eval (t : ℂ)) := by
      simp only [eval_mul, eval_X]
      ring
    rw [heval]
    change 0 ≤ ((t : ℂ) * ((p.map (starRingEnd ℂ) * p).eval (t : ℂ))).re
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      using mul_nonneg ht (hdiag p t)

/-- Zero total mass forces the zero sequence and the zero measure. -/
theorem zero_mass : Spec.ZeroMass := by
  intro m h h0
  have hm := (zero_mass_moments m h h0).2
  refine ⟨⟨inferInstance, by simp, fun n => ⟨by simp, by simp [hm n]⟩⟩, ?_⟩
  intro μ hμ
  let : IsFiniteMeasure μ := hμ.1
  have hmass := (hμ.2.2 0).2
  simp only [pow_zero, integral_const, smul_eq_mul, mul_one] at hmass
  apply MeasureTheory.Measure.measure_univ_eq_zero.mp
  exact (ENNReal.toReal_eq_zero_iff (μ Set.univ)).mp (hmass.trans h0) |>.resolve_right
    (measure_ne_top μ Set.univ)

/-- The constant vector remains in every extension-power domain, with the
specified (real) moment as its scalar matrix coefficient. -/
theorem extension_constant_moments (m : ℕ → ℝ) (h : HankelNonnegative m)
    (A : Operator ℂ (MomentHilbertSpace m h) (MomentHilbertSpace m h))
    (hp : PolynomialPowers m h A) (n : ℕ) :
    ∃ he : constantValue m h ∈ (OperatorDomainsSpec.powerValue A n).domain,
      inner ℂ (constantValue m h)
        (OperatorDomainsSpec.powerValue A n ⟨constantValue m h, he⟩) = (m n : ℂ) := by
  obtain ⟨he, hev⟩ := hp n 1
  refine ⟨he, ?_⟩
  change inner ℂ (polynomialClass m h 1)
    (OperatorDomainsSpec.powerValue A n ⟨polynomialClass m h 1, he⟩) = (m n : ℂ)
  rw [hev]
  have hone : (ofPolynomial ((X : ℂ[X]) ^ n * rawPolynomial (1 : MomentPolynomials m h)) :
      MomentPolynomials m h) = ofPolynomial ((X : ℂ[X]) ^ n) := by
    change (X : ℂ[X]) ^ n * (1 : ℂ[X]) = (X : ℂ[X]) ^ n
    exact mul_one _
  rw [hone]
  exact constantPolynomialVector_moments m h n

/-- Extract the scalar spectral measure at the constant polynomial vector.
The actual real spectral representation gives all absolute moments, and
quadratic nonnegativity gives concentration on the nonnegative half-line. -/
theorem measure_of_nonnegative_extension (m : ℕ → ℝ) (h : HankelNonnegative m)
    (A : Operator ℂ (MomentHilbertSpace m h) (MomentHilbertSpace m h))
    (hA : NonnegativeExtension m h A) (hp : PolynomialPowers m h A) :
    ∃ μ : Measure ℝ, Represents μ m := by
  obtain ⟨⟨E, C, hrep, _⟩, _⟩ :=
    UnboundedNormalSpectralTheorem.selfadjoint_spectral
      (MomentHilbertSpace m h) A hA.2.1 hA.2.2.1 hA.2.2.2.1.symm
  let e := constantValue m h
  have he : ∀ n : ℕ, e ∈ (OperatorDomainsSpec.powerValue A n).domain :=
    fun n => (extension_constant_moments m h A hp n).choose
  obtain ⟨hfinite, hmom⟩ := ScalarSpectralMoments.scalar_moments A E C hrep e he
  have hsupp := (NonnegativeSpectralSupport.nonnegative_support A E C hrep
    hA.2.2.2.2).2 e
  refine ⟨C.measure e, hfinite, hsupp, fun n => ⟨(hmom n).1, ?_⟩⟩
  rw [(hmom n).2]
  have hcoeff := (extension_constant_moments m h A hp n).choose_spec
  exact congrArg Complex.re hcoeff

/-- Positivity of the two forms yields a representing measure. -/
theorem stieltjes_sufficiency : Spec.Sufficiency := by
  intro m h hs
  obtain ⟨A, hA, hp⟩ := nonnegative_extension m h hs
  exact measure_of_nonnegative_extension m h A hA hp

/-- Full polynomial-positivity formulation of Stieltjes existence. -/
theorem stieltjes_existence : Spec.Existence := by
  intro m
  constructor
  · rintro ⟨μ, hμ⟩
    exact stieltjes_necessity m μ hμ
  · rintro ⟨h, hs⟩
    exact stieltjes_sufficiency m h hs

/-- The equivalent formulation for every finite coefficient Hankel form. -/
theorem stieltjes_existence_finite : Spec.FiniteExistence := by
  intro m
  rw [stieltjes_existence, hankelNonnegative_iff_finite,
    hankelNonnegative_iff_finite]

end ExpandedFA.Moments.StieltjesExistence
