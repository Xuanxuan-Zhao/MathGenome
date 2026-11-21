import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch19.FiniteProjection
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch19.Orthogonality

noncomputable section
namespace SingleVariableAnalysis
open Riemann
open scoped BigOperators

abbrev fourierPolynomial := Specs.SingleVariableAnalysis.Ch19.FiniteProjection.polynomialValue
abbrev fourierProjection := Specs.SingleVariableAnalysis.Ch19.FiniteProjection.projectionValue
abbrev fourierNormSquared := Specs.SingleVariableAnalysis.Ch19.FiniteProjection.normSquaredValue

namespace FourierProjection

abbrev Integrable (f : ℝ → ℂ) := ComplexIntegrable f (-Real.pi) Real.pi

private theorem period_order : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]

theorem integrable_zero : Integrable (fun _ => 0) := (complex_zero_value period_order).choose

theorem integrable_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun x => f x + g x) := (complex_add_value hf hg).choose

theorem integrable_mul {f : ℝ → ℂ} (hf : Integrable f) (c : ℂ) :
    Integrable (fun x => c * f x) := (complex_mul_value hf c).choose

theorem integrable_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun x => f x - g x) := by
  simpa only [neg_one_mul, sub_eq_add_neg] using integrable_add hf (integrable_mul hg (-1))

theorem mode_integrable (n : ℤ) : Integrable (fourierMode n) := fourierMode_integrable n

theorem paired_integrable {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun x => f x * star (g x)) := fourierPairing_integrable f g hf hg

/-- The manuscript's pairing with the automatically supplied product witness. -/
def pair {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) : ℂ :=
  fourierPairing f g (paired_integrable hf hg)

theorem pair_add_left {f g u : ℝ → ℂ} (hf : Integrable f)
    (hg : Integrable g) (hu : Integrable u) :
    pair (integrable_add hf hg) hu = pair hf hu + pair hg hu := by
  have he := (complex_add_value (paired_integrable hf hu)
    (paired_integrable hg hu)).choose_spec
  have heq : (fun x => (f x + g x) * star (u x)) =
      (fun x => f x * star (u x) + g x * star (u x)) := by funext x; ring
  unfold pair fourierPairing Specs.SingleVariableAnalysis.Ch19.Orthogonality.pairingValue
  simp_rw [heq]
  dsimp only [complexIntegral] at he
  rw [he]
  ring

theorem pair_mul_left {f g : ℝ → ℂ} (hf : Integrable f)
    (hg : Integrable g) (c : ℂ) :
    pair (integrable_mul hf c) hg = c * pair hf hg := by
  have he := (complex_mul_value (paired_integrable hf hg) c).choose_spec
  have heq : (fun x => (c * f x) * star (g x)) =
      (fun x => c * (f x * star (g x))) := by funext x; ring
  unfold pair fourierPairing Specs.SingleVariableAnalysis.Ch19.Orthogonality.pairingValue
  simp_rw [heq]
  dsimp only [complexIntegral] at he
  rw [he]
  ring

theorem integral_star {f : ℝ → ℂ} (hf : Integrable f) :
    ∃ hs : Integrable (fun x => star (f x)),
      complexIntegral _ hs = star (complexIntegral _ hf) := by
  refine ⟨⟨by simpa using hf.1, by simpa using (real_mul_value hf.2 (-1)).choose⟩, ?_⟩
  apply Complex.ext
  · simp [complexIntegral, Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegralValue]
  · have he := (real_mul_value hf.2 (-1)).choose_spec
    simp only [neg_one_mul] at he
    simpa [complexIntegral, Specs.SingleVariableAnalysis.Ch08.Integral.complexIntegralValue] using he

theorem pair_symm {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    pair hg hf = star (pair hf hg) := by
  have he := (integral_star (paired_integrable hf hg)).choose_spec
  have heq : (fun x => g x * star (f x)) =
      (fun x => star (f x * star (g x))) := by funext x; simp [mul_comm]
  unfold pair fourierPairing Specs.SingleVariableAnalysis.Ch19.Orthogonality.pairingValue
  simp_rw [heq]
  dsimp only [complexIntegral] at he
  rw [he]
  simp


theorem pair_add_right {f g u : ℝ → ℂ} (hf : Integrable f)
    (hg : Integrable g) (hu : Integrable u) :
    pair hf (integrable_add hg hu) = pair hf hg + pair hf hu := by
  rw [pair_symm (integrable_add hg hu) hf, pair_add_left hg hu hf]
  simp only [star_add, ← pair_symm hg hf, ← pair_symm hu hf]

theorem pair_mul_right {f g : ℝ → ℂ} (hf : Integrable f)
    (hg : Integrable g) (c : ℂ) :
    pair hf (integrable_mul hg c) = star c * pair hf hg := by
  rw [pair_symm (integrable_mul hg c) hf, pair_mul_left hg hf c]
  simp only [star_mul, ← pair_symm hg hf, mul_comm]

theorem pair_sub_left {f g u : ℝ → ℂ} (hf : Integrable f)
    (hg : Integrable g) (hu : Integrable u) :
    pair (integrable_sub hf hg) hu = pair hf hu - pair hg hu := by
  have he := pair_add_left hf (integrable_mul hg (-1)) hu
  rw [pair_mul_left hg hu (-1)] at he
  simpa only [neg_one_mul, sub_eq_add_neg] using he

theorem pair_sub_right {f g u : ℝ → ℂ} (hf : Integrable f)
    (hg : Integrable g) (hu : Integrable u) :
    pair hf (integrable_sub hg hu) = pair hf hg - pair hf hu := by
  rw [pair_symm (integrable_sub hg hu) hf, pair_sub_left hg hu hf]
  simp only [star_sub, ← pair_symm hg hf, ← pair_symm hu hf]

theorem pair_zero_left {f : ℝ → ℂ} (hf : Integrable f) : pair integrable_zero hf = 0 := by
  have he := (complex_zero_value period_order).choose_spec
  unfold pair fourierPairing Specs.SingleVariableAnalysis.Ch19.Orthogonality.pairingValue
  simpa only [zero_mul, mul_zero] using congrArg
    (fun z : ℂ => ((1 / (2 * Real.pi) : ℝ) : ℂ) * z) he

theorem integrable_sum {α : Type*} (E : Finset α) (u : α → ℝ → ℂ)
    (hu : ∀ n, Integrable (u n)) : Integrable (fun x => ∑ n ∈ E, u n x) := by
  classical
  induction E using Finset.induction_on with
  | empty => simpa using integrable_zero
  | @insert n E hn ih =>
    simpa only [Finset.sum_insert hn] using integrable_add
      (hu n) ih

theorem pair_sum_left {α : Type*} (E : Finset α) (u : α → ℝ → ℂ)
    (hu : ∀ n, Integrable (u n)) {f : ℝ → ℂ} (hf : Integrable f) :
    pair (integrable_sum E u hu) hf = ∑ n ∈ E, pair (hu n) hf := by
  classical
  induction E using Finset.induction_on with
  | empty => simp [pair_zero_left]
  | @insert n E hn ih =>
    have he := pair_add_left (hu n)
      (integrable_sum E u hu) hf
    simpa only [Finset.sum_insert hn, ih] using he

theorem pair_sum_right {α : Type*} (E : Finset α) (u : α → ℝ → ℂ)
    (hu : ∀ n, Integrable (u n)) {f : ℝ → ℂ} (hf : Integrable f) :
    pair hf (integrable_sum E u hu) = ∑ n ∈ E, pair hf (hu n) := by
  rw [pair_symm (integrable_sum E u hu) hf, pair_sum_left E u hu hf]
  simp only [star_sum]
  apply Finset.sum_congr rfl
  intro n _
  exact (pair_symm (hu n) hf).symm

theorem polynomial_integrable (E : Finset ℤ) (d : ℤ → ℂ) :
    Integrable (fourierPolynomial E d) :=
  integrable_sum E (fun n x => d n * fourierMode n x)
    (fun n => integrable_mul (mode_integrable n) (d n))

theorem pair_polynomial_left (E : Finset ℤ) (d : ℤ → ℂ)
    {f : ℝ → ℂ} (hf : Integrable f) :
    pair (polynomial_integrable E d) hf = ∑ n ∈ E, d n * pair (mode_integrable n) hf := by
  have he := pair_sum_left E (fun n x => d n * fourierMode n x)
    (fun n => integrable_mul (mode_integrable n) (d n)) hf
  change pair (integrable_sum E (fun n x => d n * fourierMode n x)
    (fun n => integrable_mul (mode_integrable n) (d n))) hf = _
  rw [he]
  apply Finset.sum_congr rfl
  intro n hn
  exact pair_mul_left _ _ _

theorem pair_polynomial_right (E : Finset ℤ) (d : ℤ → ℂ)
    {f : ℝ → ℂ} (hf : Integrable f) :
    pair hf (polynomial_integrable E d) = ∑ n ∈ E, star (d n) * pair hf (mode_integrable n) := by
  rw [pair_symm (polynomial_integrable E d) hf, pair_polynomial_left E d hf]
  simp only [star_sum, star_mul]
  apply Finset.sum_congr rfl
  intro n _
  rw [← pair_symm (mode_integrable n) hf]
  ring

theorem pair_mode_mode (n m : ℤ) :
    pair (mode_integrable n) (mode_integrable m) = if n = m then 1 else 0 :=
  fourierMode_orthogonality n m _

theorem pair_polynomial_mode (E : Finset ℤ) (d : ℤ → ℂ) (m : ℤ) :
    pair (polynomial_integrable E d) (mode_integrable m) =
      if m ∈ E then d m else 0 := by
  rw [pair_polynomial_left]
  simp only [pair_mode_mode]
  classical
  simp

theorem pair_polynomial_self (E : Finset ℤ) (d : ℤ → ℂ) :
    pair (polynomial_integrable E d) (polynomial_integrable E d) =
      ∑ n ∈ E, (‖d n‖ ^ 2 : ℂ) := by
  rw [pair_polynomial_right]
  apply Finset.sum_congr rfl
  intro n hn
  rw [pair_polynomial_mode, ite_eq_left hn]
  exact Complex.conj_mul' _

theorem mode_star (n : ℤ) : (fun x => star (fourierMode n x)) = fourierMode (-n) := by
  funext x
  rw [Fourier.mode_euler, Fourier.mode_euler]
  simp only [Int.cast_neg, neg_mul, Real.cos_neg, Real.sin_neg, star_add, star_mul,
    Complex.star_def, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

theorem pair_mode_coefficient {f : ℝ → ℂ} (hf : Integrable f)
    (h : Specs.SingleVariableAnalysis.Ch19.Representation.ComplexWeights f) (n : ℤ) :
    pair hf (mode_integrable n) = fourierCoeff f n (h n) := by
  unfold pair fourierPairing Specs.SingleVariableAnalysis.Ch19.Orthogonality.pairingValue
    fourierCoeff Specs.SingleVariableAnalysis.Ch19.PeriodicSetup.coefficientValue
  simp_rw [show (fun x => f x * star (fourierMode n x)) =
    (fun x => f x * fourierMode (-n) x) by rw [← mode_star]]

theorem norm_squared_integrable {f : ℝ → ℂ} (hf : Integrable f) :
    RealIntegrable (fun x => ‖f x‖ ^ 2) (-Real.pi) Real.pi := by
  have h := (paired_integrable hf hf).1
  simpa only [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re] using h

theorem pair_self_re {f : ℝ → ℂ} (hf : Integrable f)
    (h : RealIntegrable (fun x => ‖f x‖ ^ 2) (-Real.pi) Real.pi) :
    (pair hf hf).re = fourierNormSquared f h := by
  unfold pair fourierPairing Specs.SingleVariableAnalysis.Ch19.Orthogonality.pairingValue
    fourierNormSquared Specs.SingleVariableAnalysis.Ch19.FiniteProjection.normSquaredValue
  rw [Complex.re_ofReal_mul, (complexIntegral_components _ _).1]
  simp only [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]

theorem polynomial_sub (E : Finset ℤ) (c d : ℤ → ℂ) :
    fourierPolynomial E (fun n => c n - d n) =
      fun x => fourierPolynomial E c x - fourierPolynomial E d x := by
  funext x
  simp only [fourierPolynomial, Specs.SingleVariableAnalysis.Ch19.FiniteProjection.polynomialValue,
    sub_mul, Finset.sum_sub_distrib]

theorem pair_congr {f g u v : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (hu : Integrable u) (hv : Integrable v) (hfu : f = u) (hgv : g = v) :
    pair hf hg = pair hu hv := by
  subst u; subst v
  rfl

/-- The finite residual is orthogonal to every mode in E. -/
theorem residual_mode {f : ℝ → ℂ} (hf : Integrable f)
    (h : Specs.SingleVariableAnalysis.Ch19.Representation.ComplexWeights f)
    (E : Finset ℤ) (n : ℤ) (hn : n ∈ E) :
    pair (integrable_sub hf (polynomial_integrable E (fun m => fourierCoeff f m (h m))))
      (mode_integrable n) = 0 := by
  rw [pair_sub_left hf (polynomial_integrable E (fun m => fourierCoeff f m (h m)))
    (mode_integrable n), pair_mode_coefficient hf h n, pair_polynomial_mode, ite_eq_left hn, sub_self]

/-- Pythagoras here is a finite integral identity, even for zero seminorms. -/
theorem pythagoras {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g)
    (ho : pair hf hg = 0) :
    pair (integrable_add hf hg) (integrable_add hf hg) = pair hf hf + pair hg hg := by
  rw [pair_add_left hf hg (integrable_add hf hg), pair_add_right hf hf hg,
    pair_add_right hg hf hg, ho, pair_symm hf hg, ho]
  simp

end FourierProjection

open Specs.SingleVariableAnalysis.Ch19.FiniteProjection
open FourierProjection

theorem fourierPolynomial_integrable : polynomialIntegrability :=
  polynomial_integrable

theorem fourierNormSquared_integrable : squaredNormIntegrability := by
  intro f hf
  exact norm_squared_integrable hf

theorem fourierResidual_integrable : residualIntegrability := by
  intro f hf E d
  exact norm_squared_integrable (integrable_sub hf (polynomial_integrable E d))

/-- The full finite projection identity, with arbitrary proper integral witnesses.
Periodicity is unnecessary for this finite identity on the fixed interval. -/
theorem fourierProjection_identity : projectionIdentity := by
  intro f hf h E d hd hP
  let c : ℤ → ℂ := fun n => fourierCoeff f n (h n)
  have hr := integrable_sub hf (polynomial_integrable E c)
  have hq := polynomial_integrable E (fun n => c n - d n)
  have ho : pair hr hq = 0 := by
    rw [pair_polynomial_right]
    apply Finset.sum_eq_zero
    intro n hn
    rw [residual_mode hf h E n hn, mul_zero]
  have hp : (fun x => (f x - fourierPolynomial E c x) +
      fourierPolynomial E (fun n => c n - d n) x) =
      (fun x => f x - fourierPolynomial E d x) := by
    rw [polynomial_sub]
    funext x
    ring
  have he := pythagoras hr hq ho
  rw [pair_polynomial_self] at he
  have her := congrArg Complex.re he
  have hleft : (pair (integrable_add hr hq) (integrable_add hr hq)).re =
      fourierNormSquared (fun x => f x - fourierPolynomial E d x) hd := by
    exact (congrArg Complex.re (pair_congr (integrable_add hr hq) (integrable_add hr hq)
      (integrable_sub hf (polynomial_integrable E d))
      (integrable_sub hf (polynomial_integrable E d)) hp hp)).trans
        (pair_self_re (integrable_sub hf (polynomial_integrable E d)) hd)
  have hright : (pair hr hr).re =
      fourierNormSquared (fun x => f x - fourierProjection f h E x) hP :=
    pair_self_re hr hP
  rw [hleft, Complex.add_re, hright] at her
  simpa only [Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re] using her

theorem fourierProjection_bestApproximation : bestApproximation := by
  intro f hf h E d hd hP
  have he := fourierProjection_identity f hf h E d hd hP
  have hs : 0 ≤ ∑ n ∈ E, ‖fourierCoeff f n (h n) - d n‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

theorem fourierProjection_realEmbedding : realEmbedding := by
  intro f hf
  refine ⟨⟨hf.1.comp Complex.ofReal, fourierRealEmbedding_integrable f hf.2⟩, ?_⟩
  intro x
  simp

theorem fourierProjection_empty : emptyProjection := by
  intro f h
  funext x
  simp [projectionValue, polynomialValue]

end SingleVariableAnalysis
