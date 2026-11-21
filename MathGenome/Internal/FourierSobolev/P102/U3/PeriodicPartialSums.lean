import MathGenome.Internal.FourierSobolev.Specs.P102.U3.PeriodicPartialSums
import MathGenome.Internal.FourierSobolev.P102.U3.PeriodicConjugation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ComplexConjugate ENNReal
namespace P102.Periodic.PartialSums
open P102.Periodic.Expected P102.Periodic.Conjugation
variable (T : ℝ) [Fact (0 < T)] (p : Exponent)

lemma finiteSum_apply (N : ℕ) (f : Circle T → ℂ) (x : Circle T) :
    finiteSum T N f x = partialSum T N f x := by
  simp [finiteSum, partialSum, Expected.frequencies, frequencies,
    Expected.coefficient, coefficient]

/-- Multiplication by a character preserves membership in Lp. -/
lemma modulation_memLp (k : ℤ) (f : Space T p) :
    MemLp (fun x => mode T k x * f x) p.val (haar T) := by
  apply (Lp.memLp f).of_le
    ((mode T k).continuous.aestronglyMeasurable.mul (Lp.memLp f).aestronglyMeasurable)
  exact ae_of_all _ (fun x => by simp [mode, fourier_apply, Circle.norm_coe])

/-- Modulation on the actual quotient Lp space. -/
def modulation (k : ℤ) : Operator T p :=
  LinearMap.mkContinuous
    { toFun := fun f => (modulation_memLp T p k f).toLp _
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (modulation_memLp T p k (f+g)),
          MemLp.coeFn_toLp (modulation_memLp T p k f),
          MemLp.coeFn_toLp (modulation_memLp T p k g), Lp.coeFn_add f g,
          Lp.coeFn_add ((modulation_memLp T p k f).toLp _) ((modulation_memLp T p k g).toLp _)]
          with x h1 h2 h3 h4 h5
        rw [h1, h5, h4]
        simp only [Pi.add_apply]
        rw [h2, h3, mul_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (modulation_memLp T p k (c • f)),
          MemLp.coeFn_toLp (modulation_memLp T p k f), Lp.coeFn_smul c f,
          Lp.coeFn_smul c ((modulation_memLp T p k f).toLp _)] with x h1 h2 h3 h4
        simp only [RingHom.id_apply]
        rw [h1, h4, h3]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [h2]
        ring }
    1 (by
      intro f
      change ‖(modulation_memLp T p k f).toLp _‖ ≤ 1 * ‖f‖
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [MemLp.coeFn_toLp (modulation_memLp T p k f)] with x hx
      rw [hx]
      simp [mode, fourier_apply, Circle.norm_coe])

lemma modulation_ae (k : ℤ) (f : Space T p) :
    (modulation T p k f : Circle T → ℂ) =ᵐ[haar T] fun x => mode T k x * f x :=
  MemLp.coeFn_toLp (modulation_memLp T p k f)

lemma modulation_norm (k : ℤ) (f : Space T p) : ‖modulation T p k f‖ = ‖f‖ := by
  apply le_antisymm <;> apply Lp.norm_le_norm_of_ae_le
  · filter_upwards [modulation_ae T p k f] with x hx
    simp [hx, mode, fourier_apply, Circle.norm_coe]
  · filter_upwards [modulation_ae T p k f] with x hx
    simp [hx, mode, fourier_apply, Circle.norm_coe]

lemma modulation_mode (k n : ℤ) :
    modulation T p k (toSpace T p (mode T n)) = toSpace T p (mode T (k+n)) := by
  apply Lp.ext
  filter_upwards [modulation_ae T p k (toSpace T p (mode T n)),
    ContinuousMap.coeFn_toLp (p := p.val) (𝕜 := ℂ) (haar T) (mode T n),
    ContinuousMap.coeFn_toLp (p := p.val) (𝕜 := ℂ) (haar T) (mode T (k+n))] with x h1 h2 h3
  rw [h1, h2, h3]
  exact fourier_add.symm

/-- Probability Haar makes integration a contraction on every finite Lp here. -/
lemma mean_norm_le (f : Space T p) : ‖∫ x, f x ∂haar T‖ ≤ ‖f‖ := by
  have h := (enorm_integral_le_lintegral_enorm (μ := haar T) (f : Circle T → ℂ)).trans
    ((eLpNorm_one_eq_lintegral_enorm (Lp.memLp f).aestronglyMeasurable).symm.le.trans
      (eLpNorm_le_eLpNorm_of_exponent_le p.one_lt.le))
  have hh := ENNReal.toReal_mono (Lp.memLp f).ne h
  simpa [Lp.norm_def] using hh

def meanFunctional : Space T p →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂haar T
      map_add' := by
        intro f g
        rw [integral_congr_ae (Lp.coeFn_add f g)]
        exact integral_add ((Lp.memLp f).integrable p.one_lt.le)
          ((Lp.memLp g).integrable p.one_lt.le)
      map_smul' := by
        intro c f
        rw [integral_congr_ae (Lp.coeFn_smul c f)]
        exact integral_smul c _ }
    1 (fun f => by simpa using mean_norm_le T p f)

/-- Continuous coefficient functionals, with the source normalization. -/
def coefficientFunctional (n : ℤ) : Space T p →L[ℂ] ℂ :=
  (meanFunctional T p).comp (modulation T p (-n))

lemma coefficientFunctional_eq (n : ℤ) (f : Space T p) :
    coefficientFunctional T p n f = coefficient T f n := by
  change (∫ x, (modulation T p (-n) f) x ∂haar T) = _
  rw [integral_congr_ae (modulation_ae T p (-n) f)]
  simp only [coefficient, mode, fourier_neg, mul_comm]

lemma coefficient_toSpace (n : ℤ) (g : C(Circle T, ℂ)) :
    coefficient T (toSpace T p g) n = coefficient T g n := by
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := p.val) (𝕜 := ℂ) (haar T) g] with x hx
  rw [hx]

lemma coefficient_mode (m n : ℤ) :
    coefficient T (mode T m) n = if n = m then 1 else 0 := by
  have he : coefficient T (mode T m) n = fourierCoeff (mode T m) n := by
    simp [coefficient, fourierCoeff, mode, mul_comm]
  rw [he]
  simp [mode, fourierCoeff_fourier, Pi.single_apply, eq_comm]

/-- The bounded operator is exactly the canonical finite sum for every input. -/
def sumOperator (N : ℕ) : Operator T p :=
  ∑ n ∈ frequencies N,
    (coefficientFunctional T p n).smulRight (toSpace T p (mode T n))

lemma sumOperator_eq (N : ℕ) (f : Space T p) :
    sumOperator T p N f = toSpace T p (finiteSum T N f) := by
  simp only [sumOperator, sum_apply, ContinuousLinearMap.smulRight_apply,
    coefficientFunctional_eq, finiteSum, map_sum, map_smul,
    Expected.frequencies, frequencies, Expected.coefficient, coefficient,
    Expected.mode, mode]

lemma sumOperator_mode (N : ℕ) (n : ℤ) :
    sumOperator T p N (toSpace T p (mode T n)) =
      if n ∈ frequencies N then toSpace T p (mode T n) else 0 := by
  classical
  simp only [sumOperator, sum_apply, ContinuousLinearMap.smulRight_apply,
    coefficientFunctional_eq, coefficient_toSpace, coefficient_mode]
  simp [ite_smul, eq_comm]

/-- Mean projection, including the zero mode. -/
def meanProjection : Operator T p :=
  (coefficientFunctional T p 0).smulRight (toSpace T p (mode T 0))

lemma meanProjection_mode (n : ℤ) :
    meanProjection T p (toSpace T p (mode T n)) =
      if n = 0 then toSpace T p (mode T n) else 0 := by
  classical
  simp only [meanProjection, ContinuousLinearMap.smulRight_apply,
    coefficientFunctional_eq, coefficient_toSpace, coefficient_mode]
  by_cases h : n = 0 <;> simp [h, eq_comm]

lemma conjugation_mode (H : Operator T p) (hH : AgreesOnPolynomials T p H) (n : ℤ) :
    H (toSpace T p (mode T n)) = symbol n • toSpace T p (mode T n) := by
  have h := hH (Finsupp.single n 1)
  simpa only [synthesis, Expected.synthesis, polynomialAction, Finsupp.linearCombination_single,
    one_smul, map_smul] using h

/-- The correct nonnegative-frequency projection is (I + iH + P₀)/2. -/
def positiveProjection (H : Operator T p) : Operator T p :=
  (2 : ℂ)⁻¹ • (ContinuousLinearMap.id ℂ (Space T p) + Complex.I • H + meanProjection T p)

lemma positiveProjection_mode (H : Operator T p) (hH : AgreesOnPolynomials T p H) (n : ℤ) :
    positiveProjection T p H (toSpace T p (mode T n)) =
      if 0 ≤ n then toSpace T p (mode T n) else 0 := by
  classical
  simp only [positiveProjection, smul_apply,
    add_apply, ContinuousLinearMap.id_apply,
    conjugation_mode T p H hH, meanProjection_mode]
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · simp [hn.ne, hn.not_ge, symbol, Int.sign_eq_neg_one_of_neg hn, smul_smul,
      Complex.I_mul_I]
  · simp [symbol, ← two_smul ℂ, smul_smul]
  · simp [hn.ne', hn.le, symbol, Int.sign_eq_one_of_pos hn, smul_smul,
      ← add_smul, Complex.I_mul_I]
    norm_num

/-- Conjugating the projection by modulation shifts the threshold to k. -/
def shiftedProjection (H : Operator T p) (k : ℤ) : Operator T p :=
  (modulation T p k).comp ((positiveProjection T p H).comp (modulation T p (-k)))

lemma shiftedProjection_mode (H : Operator T p) (hH : AgreesOnPolynomials T p H)
    (k n : ℤ) :
    shiftedProjection T p H k (toSpace T p (mode T n)) =
      if k ≤ n then toSpace T p (mode T n) else 0 := by
  simp only [shiftedProjection, ContinuousLinearMap.comp_apply, modulation_mode,
    positiveProjection_mode T p H hH]
  by_cases hn : k ≤ n
  · have h : 0 ≤ -k + n := by omega
    simp [h, hn, modulation_mode]
  · have h : ¬ 0 ≤ -k + n := by omega
    simp [h, hn]

lemma modes_dense : Dense (↑(Submodule.span ℂ
    (Set.range (fun n : ℤ => toSpace T p (mode T n)))) : Set (Space T p)) := by
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (span_fourierLp_closure_eq_top p.lt_top.ne)

/-- Agreement on all Lp inputs follows from the finite-mode calculation and density. -/
lemma sumOperator_eq_shifted (H : Operator T p) (hH : AgreesOnPolynomials T p H) (N : ℕ) :
    sumOperator T p N = shiftedProjection T p H (-(N : ℤ)) -
      shiftedProjection T p H ((N : ℤ) + 1) := by
  apply ContinuousLinearMap.ext_on (modes_dense T p)
  rintro _ ⟨n, rfl⟩
  simp only [sumOperator_mode, sub_apply,
    shiftedProjection_mode T p H hH]
  simp only [frequencies, Finset.mem_Icc]
  split_ifs <;> simp_all <;> omega

lemma shiftedProjection_bound (H : Operator T p) (k : ℤ) (f : Space T p) :
    ‖shiftedProjection T p H k f‖ ≤ ‖positiveProjection T p H‖ * ‖f‖ := by
  simp only [shiftedProjection, ContinuousLinearMap.comp_apply, modulation_norm]
  simpa only [modulation_norm] using
    (positiveProjection T p H).le_opNorm (modulation T p (-k) f)

lemma uniform_bound (H : Operator T p) (hH : AgreesOnPolynomials T p H) (N : ℕ) :
    ‖sumOperator T p N‖ ≤ 2 * ‖positiveProjection T p H‖ := by
  apply (sumOperator T p N).opNorm_le_bound (by positivity)
  intro f
  rw [sumOperator_eq_shifted T p H hH, sub_apply]
  calc
    _ ≤ ‖shiftedProjection T p H (-(N : ℤ)) f‖ +
        ‖shiftedProjection T p H ((N : ℤ)+1) f‖ := norm_sub_le _ _
    _ ≤ ‖positiveProjection T p H‖ * ‖f‖ + ‖positiveProjection T p H‖ * ‖f‖ :=
      add_le_add (shiftedProjection_bound T p H _ f) (shiftedProjection_bound T p H _ f)
    _ = _ := by ring

/-- Finite Fourier sums eventually fix every element of the span of the modes. -/
lemma sumOperator_stabilizes {f : Space T p}
    (hf : f ∈ Submodule.span ℂ (Set.range (fun n : ℤ => toSpace T p (mode T n)))) :
    ∃ M : ℕ, ∀ N ≥ M, sumOperator T p N f = f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨n, rfl⟩ := hf
      refine ⟨n.natAbs, fun N hN => ?_⟩
      rw [sumOperator_mode]
      have hn : n ∈ frequencies N := by
        simp only [frequencies, Finset.mem_Icc]
        have h1 := Int.le_natAbs (a := n)
        have h2 := Int.le_natAbs (a := -n)
        simp only [Int.natAbs_neg] at h2
        constructor <;> omega
      simp [hn]
  | zero => exact ⟨0, fun N _ => map_zero _⟩
  | add f g hf hg ihf ihg =>
      obtain ⟨M, hM⟩ := ihf
      obtain ⟨K, hK⟩ := ihg
      exact ⟨max M K, fun N hN => by
        rw [map_add, hM N (le_trans (le_max_left _ _) hN),
          hK N (le_trans (le_max_right _ _) hN)]⟩
  | smul c f hf ih =>
      obtain ⟨M, hM⟩ := ih
      exact ⟨M, fun N hN => by rw [map_smul, hM N hN]⟩

/-- Uniform boundedness and stabilization on a dense span give norm convergence. -/
lemma sumOperator_tendsto (H : Operator T p) (hH : AgreesOnPolynomials T p H)
    (f : Space T p) : Tendsto (fun N => sumOperator T p N f) atTop (𝓝 f) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let C : ℝ := 2 * ‖positiveProjection T p H‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hC1 : 0 < C + 1 := by positivity
  obtain ⟨g, hg, hfg⟩ := (modes_dense T p).exists_dist_lt f (div_pos hε hC1)
  obtain ⟨M, hM⟩ := sumOperator_stabilizes T p hg
  refine ⟨M, fun N hN => ?_⟩
  rw [dist_eq_norm] at hfg ⊢
  have he : sumOperator T p N f - f = sumOperator T p N (f - g) + (g - f) := by
    rw [map_sub, hM N hN]
    abel
  rw [he]
  calc
    _ ≤ ‖sumOperator T p N (f - g)‖ + ‖g - f‖ := norm_add_le _ _
    _ ≤ C * ‖f - g‖ + ‖g - f‖ := by
      exact add_le_add (((sumOperator T p N).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (uniform_bound T p H hH N) (norm_nonneg _))) le_rfl
    _ = (C + 1) * ‖f - g‖ := by rw [norm_sub_rev g f]; ring
    _ < ε := by nlinarith [(lt_div_iff₀ hC1).mp hfg]

/-- Both conclusions of periodic conjugation and norm convergence, for every
positive period and every finite exponent strictly greater than one. -/
theorem full_theorem : P102.Specs.U3.PeriodicPartialSums.full_theorem := by
  intro T hT p
  have hresult := P102.Periodic.Conjugation.full_theorem T p
  obtain ⟨H, C, hC, hagrees, hsymbol, hpv, hunique⟩ := hresult
  refine ⟨⟨H, C, hC, hagrees, hsymbol, hpv, hunique⟩,
    sumOperator T p, 2 * ‖positiveProjection T p H‖₊, ?_, ?_, ?_⟩
  · exact sumOperator_eq T p
  · intro N
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat, coe_nnnorm] using
      uniform_bound T p H hagrees N
  · exact sumOperator_tendsto T p H hagrees

end P102.Periodic.PartialSums
