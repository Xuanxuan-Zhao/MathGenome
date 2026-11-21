import MathGenome.Internal.FourierSobolev.Specs.P102.U3.PeriodicConjugation
import MathGenome.Internal.FourierSobolev.P102.Periodic.Foundation
import MathGenome.Internal.FourierSobolev.P102.U3.PeriodicConjugationKernel
import MathGenome.Internal.FourierSobolev.P102.U3.PeriodicConjugationBound
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace P102.Periodic.Conjugation

variable (T : ℝ) [Fact (0 < T)]

@[simp] theorem symbol_zero : symbol 0 = 0 := by simp [symbol]

@[simp] theorem symbol_pos {n : ℤ} (hn : 0 < n) : symbol n = -Complex.I := by
  simp [symbol, Int.sign_eq_one_of_pos hn]

@[simp] theorem symbol_neg {n : ℤ} (hn : n < 0) : symbol n = Complex.I := by
  simp [symbol, Int.sign_eq_neg_one_of_neg hn]

omit [Fact (0 < T)] in
/-- Both polynomial maps send a single frequency to the prescribed mode. -/
@[simp] theorem polynomialAction_single (n : ℤ) (a : ℂ) :
    polynomialAction T (Finsupp.single n a) = (a * symbol n) • mode T n := by
  simp [polynomialAction, smul_smul]

/-- The dense map used for extension is the ordinary finite Fourier synthesis. -/
def polynomialEmbedding (p : Exponent) : (ℤ →₀ ℂ) →ₗ[ℂ] Space T p :=
  (toSpace T p).toLinearMap.comp (synthesis T)

/-- Finite Fourier synthesis has dense image for every 1 < p < ∞. -/
theorem polynomialEmbedding_dense (p : Exponent) : DenseRange (polynomialEmbedding T p) := by
  have hr : LinearMap.range (polynomialEmbedding T p) =
      Submodule.span ℂ (Set.range (@fourierLp T _ p.val _)) := by
    rw [polynomialEmbedding, LinearMap.range_comp,
      show LinearMap.range (synthesis T) = Submodule.span ℂ (Set.range (mode T)) from
        Finsupp.range_linearCombination ℂ, Submodule.map_span]
    rw [← Set.range_comp]
    rfl
  rw [denseRange_iff_closure_range, ← LinearMap.coe_range,
    ← Submodule.topologicalClosure_coe, hr,
    span_fourierLp_closure_eq_top p.lt_top.ne, Submodule.top_coe]

/-- Uniqueness uses the actual dense polynomial subspace, with no analytic
kernel or boundedness assertion hidden in its hypotheses. -/
theorem operator_unique (p : Exponent) (H U : Operator T p)
    (hH : AgreesOnPolynomials T p H) (hU : AgreesOnPolynomials T p U) : U = H := by
  apply ContinuousLinearMap.ext
  intro f
  refine (polynomialEmbedding_dense T p).induction_on f
    (isClosed_eq U.continuous H.continuous) (fun c => ?_)
  exact (hU c).trans (hH c).symm

/-- Extend the finite multiplier using its polynomial norm estimate. -/
theorem operator_of_polynomialBound (p : Exponent) (h : PolynomialBound T p) :
    ∃ (H : Operator T p) (C : ℝ≥0), ‖H‖ ≤ C ∧ AgreesOnPolynomials T p H := by
  obtain ⟨C, hC⟩ := h
  let f : (ℤ →₀ ℂ) →ₗ[ℂ] Space T p :=
    (toSpace T p).toLinearMap.comp (polynomialAction T)
  refine ⟨f.extendOfNorm (polynomialEmbedding T p), C, ?_, ?_⟩
  · exact LinearMap.opNorm_extendOfNorm_le (polynomialEmbedding_dense T p) C.coe_nonneg hC
  · intro c
    exact LinearMap.extendOfNorm_eq (polynomialEmbedding_dense T p) ⟨C, hC⟩ c

/-- Fourier coefficients are linear on Lp because p>1 on a probability space. -/
def coefficientLinear (p : Exponent) (n : ℤ) : Space T p →ₗ[ℂ] ℂ where
  toFun f := coefficient T f n
  map_add' f g := by
    rw [coefficient_congr T _ _ (Lp.coeFn_add f g) n]
    simp only [coefficient_eq_fourierCoeff]
    exact congrFun (fourierCoeff.add ((Lp.memLp f).integrable p.one_lt.le)
      ((Lp.memLp g).integrable p.one_lt.le)) n
  map_smul' a f := by
    rw [coefficient_congr T _ _ (Lp.coeFn_smul a f) n,
      coefficient_eq_fourierCoeff, coefficient_eq_fourierCoeff]
    exact fourierCoeff.const_smul f a n

/-- The coefficient functionals have norm at most one for probability Haar. -/
theorem coefficient_bound (p : Exponent) (f : Space T p) (n : ℤ) :
    ‖coefficient T f n‖ ≤ ‖f‖ := by
  have hm (x : Circle T) : ‖f x * starRingEnd ℂ (mode T n x)‖ = ‖f x‖ := by
    simp [mode, fourier_apply, Circle.norm_coe]
  calc
    ‖coefficient T f n‖ ≤
        (∫⁻ x, ENNReal.ofReal ‖f x * starRingEnd ℂ (mode T n x)‖ ∂haar T).toReal :=
      norm_integral_le_lintegral_norm _
    _ = (eLpNorm f 1 (haar T)).toReal := by
      simp_rw [hm, ofReal_norm]
      rw [eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f)]
    _ ≤ (eLpNorm f p.val (haar T)).toReal :=
      ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
        (eLpNorm_le_eLpNorm_of_exponent_le p.one_lt.le)
    _ = ‖f‖ := rfl

/-- The continuous coefficient functional used to pass multiplier identities
from polynomials to every Lp input. -/
def coefficientCLM (p : Exponent) (n : ℤ) : Space T p →L[ℂ] ℂ :=
  (coefficientLinear T p n).mkContinuous 1 (by
    intro f
    change ‖coefficient T f n‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using coefficient_bound T p f n)

@[simp] theorem coefficientCLM_apply (p : Exponent) (n : ℤ) (f : Space T p) :
    coefficientCLM T p n f = coefficient T f n := rfl

/-- Continuous representatives have the same coefficients as their Lp class. -/
theorem coefficient_toSpace (p : Exponent) (f : C(Circle T, ℂ)) (n : ℤ) :
    coefficient T (toSpace T p f) n = coefficient T f n :=
  coefficient_congr T _ _ (ContinuousMap.coeFn_toLp (haar T) f) n

/-- A mode has exactly its own Fourier coefficient. -/
theorem coefficient_mode (k n : ℤ) :
    coefficient T (mode T k) n = if n = k then 1 else 0 := by
  have h := coefficient_synthesis T (Finsupp.single k 1) n
  simpa [synthesis, Finsupp.single_apply, eq_comm] using h

/-- The finite action has exactly the required Fourier multipliers. -/
theorem coefficient_polynomialAction (p : Exponent) (c : ℤ →₀ ℂ) (n : ℤ) :
    coefficient T (polynomialAction T c) n = symbol n * c n := by
  classical
  let φ : C(Circle T, ℂ) →ₗ[ℂ] ℂ :=
    ((coefficientCLM T p n).comp (toSpace T p)).toLinearMap
  have hφ (P : C(Circle T, ℂ)) : φ P = coefficient T P n :=
    coefficient_toSpace T p P n
  have hv : φ ∘ (fun k => symbol k • mode T k) = Pi.single n (symbol n) := by
    funext k
    rw [Function.comp_apply, φ.map_smul]
    simp only [hφ, coefficient_mode, smul_eq_mul]
    by_cases hk : k = n
    · subst k; simp
    · simp [hk, Ne.symm hk]
  rw [← hφ, polynomialAction, Finsupp.apply_linearCombination, hv,
    Finsupp.linearCombination_single_index, smul_eq_mul, mul_comm]

/-- All coefficients of any bounded extension follow by continuity and density;
no principal-value theorem for arbitrary Lp representatives is being assumed. -/
theorem fourierSymbol_of_agrees (p : Exponent) (H : Operator T p)
    (hH : AgreesOnPolynomials T p H) : HasFourierSymbol T p H := by
  intro f n
  have hmaps : (coefficientCLM T p n).comp H = symbol n • coefficientCLM T p n := by
    ext u
    refine (polynomialEmbedding_dense T p).induction_on u
      (isClosed_eq ((coefficientCLM T p n).comp H).continuous
        (symbol n • coefficientCLM T p n).continuous) (fun c => ?_)
    change coefficient T (H (toSpace T p (synthesis T c))) n =
      symbol n * coefficient T (toSpace T p (synthesis T c)) n
    have hc : H (toSpace T p (synthesis T c)) = toSpace T p (polynomialAction T c) := hH c
    rw [hc, coefficient_toSpace, coefficient_toSpace,
      coefficient_polynomialAction T p, coefficient_synthesis]
  exact congrArg (fun K : Space T p →L[ℂ] ℂ => K f) hmaps

/-- Norms of the canonical continuous representatives are exactly the Lp norms
used in the analytic estimate. -/
theorem norm_toSpace (p : Exponent) (f : C(Circle T, ℂ)) :
    ‖toSpace T p f‖ = (eLpNorm f p.val (haar T)).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae (ContinuousMap.coeFn_toLp (haar T) f)]

/-- The independently stated physical-kernel estimate and identification imply
the explicit finite-multiplier bound, with the same finite constant. -/
theorem polynomialBound_of_cancelledBound (p : Exponent)
    (hpv : PolynomialPrincipalValues T) (hbound : CancelledBound T p) :
    PolynomialBound T p := by
  obtain ⟨C, hC⟩ := hbound
  refine ⟨C, fun c => ?_⟩
  have heq : cancelledValue T (synthesis T c) = (polynomialAction T c : Circle T → ℂ) :=
    funext fun x => (hpv c x).2.2.1
  have hb := hC c
  change eLpNorm (cancelledValue T (synthesis T c)) p.val (haar T) ≤
    (C : ℝ≥0∞) * eLpNorm (synthesis T c) p.val (haar T) at hb
  rw [heq] at hb
  have hfin := (synthesis T c).memLp (p := p.val) (μ := haar T) ℂ
  have ht : (C : ℝ≥0∞) * eLpNorm (synthesis T c) p.val (haar T) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) hfin.eLpNorm_ne_top
  have hb' := ENNReal.toReal_mono ht hb
  simpa only [norm_toSpace, ENNReal.toReal_mul, ENNReal.coe_toReal,
    synthesis, Expected.synthesis] using hb'

/-- Assembly from the two genuine analytic statements. -/
theorem result_of_polynomialBound (p : Exponent)
    (hbound : PolynomialBound T p) (hpv : PolynomialPrincipalValues T) : Result T p := by
  obtain ⟨H, C, hC, hH⟩ := operator_of_polynomialBound T p hbound
  exact ⟨H, C, hC, hH, fourierSymbol_of_agrees T p H hH, hpv,
    fun U hU => operator_unique T p H U hH hU⟩

/-- Assemble the physical-kernel identification and norm estimate by density. -/
theorem assemble : P102.Specs.U3.PeriodicConjugation.assemblyStatement := by
  intro hpv hbound T _ p
  exact result_of_polynomialBound T p
    (polynomialBound_of_cancelledBound T p (hpv T) (hbound T p)) (hpv T)

/-- Periodic conjugation on every probability-Haar Lp space, 1 < p < ∞. -/
theorem full_theorem : P102.Specs.U3.PeriodicConjugation.full_theorem :=
  assemble polynomial_principal_values cancelled_bound

end P102.Periodic.Conjugation
