import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.IntegralOperators.ContinuousTraceCounterexample
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.HilbertSchmidtKernels
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.TraceClassDefinitions
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Polynomial MeasureTheory
open scoped ComplexConjugate ENNReal
namespace ExpandedFA.IntegralOperators.ContinuousTraceCounterexample
open Spec

@[simp] lemma P_zero : P 0 = 1 := rfl
@[simp] lemma Q_zero : Q 0 = 1 := rfl
lemma P_succ (r : ℕ) : P (r + 1) = P r + X ^ (2 ^ r) * Q r := rfl
lemma Q_succ' (r : ℕ) : Q (r + 1) = P r - X ^ (2 ^ r) * Q r := rfl

/-- The exact Rudin–Shapiro energy identity on the unit circle. -/
lemma energy_identity (r : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(P r).eval z‖ ^ 2 + ‖(Q r).eval z‖ ^ 2 = (2 : ℝ) ^ (r + 1) := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    rw [P_succ, Q_succ']
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X]
    rw [parallelogram_law_with_norm ℂ, norm_mul, norm_pow, hz, one_pow, one_mul,
      ih, pow_succ]
    ring

/-- The even-indexed estimate avoids fractional powers: √2 · 2^m. -/
lemma P_even_bound (m : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(P (2 * m)).eval z‖ ≤ Real.sqrt 2 * (2 : ℝ) ^ m := by
  have h := energy_identity (2 * m) z hz
  have hpow : (2 : ℝ) ^ (2 * m + 1) = 2 * ((2 : ℝ) ^ m) ^ 2 := by
    rw [show 2 * m + 1 = m * 2 + 1 by omega, pow_succ, pow_mul]
    ring
  rw [hpow] at h
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 ≤ Real.sqrt 2 * (2 : ℝ) ^ m := by positivity
  nlinarith [sq_nonneg ‖(Q (2 * m)).eval z‖]

lemma eval_conj (r : ℕ) (z : ℂ) :
    (P r).eval (conj z) = conj ((P r).eval z) ∧
    (Q r).eval (conj z) = conj ((Q r).eval z) := by
  induction r with
  | zero => simp
  | succ r ih =>
    simp only [P_succ, Q_succ', eval_add, eval_sub, eval_mul, eval_pow, eval_X,
      map_add, map_sub, map_mul, map_pow, ih]
    trivial


lemma blockWeight_pos (m : ℕ) : 0 < blockWeight m := by
  unfold blockWeight
  positivity

lemma blockTerm_bound (m : ℕ) (t : Torus) :
    ‖blockTerm m t‖ ≤ Real.sqrt 2 / (((m + 1 : ℕ) : ℝ) ^ 2) := by
  have hz : ‖fourier 1 t‖ = 1 := Circle.norm_coe _
  have hP := P_even_bound (m + 1) (fourier 1 t) hz
  simp only [blockTerm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (blockWeight_pos m), norm_pow, hz, one_pow, mul_one]
  calc
    _ ≤ blockWeight m * (Real.sqrt 2 * (2 : ℝ) ^ (m + 1)) :=
      mul_le_mul_of_nonneg_left hP (blockWeight_pos m).le
    _ = _ := by
      unfold blockWeight
      field_simp

lemma summable_majorant :
    Summable (fun m : ℕ => Real.sqrt 2 / (((m + 1 : ℕ) : ℝ) ^ 2)) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow).2 (by norm_num)
  simpa [div_eq_mul_inv, mul_assoc] using
    ((summable_nat_add_iff 1).2 h).mul_left (Real.sqrt 2)

lemma blockTerm_summable (t : Torus) : Summable (fun m => blockTerm m t) :=
  Summable.of_norm_bounded summable_majorant (fun m => blockTerm_bound m t)

lemma blockTerm_continuous (m : ℕ) : Continuous (blockTerm m) := by
  unfold blockTerm
  exact (continuous_const.mul ((fourier 1).continuous.pow _)).mul
    ((P (2 * (m + 1))).continuous.comp (fourier 1).continuous)

lemma series_uniform :
    TendstoUniformly (fun N t => ∑ m ∈ Finset.range N, blockTerm m t)
      complexSeries Filter.atTop :=
  tendstoUniformly_tsum_nat summable_majorant blockTerm_bound

lemma series_continuous : Continuous complexSeries :=
  continuous_tsum blockTerm_continuous summable_majorant blockTerm_bound

lemma realSeries_continuous : Continuous realSeries :=
  Complex.continuous_re.comp series_continuous

lemma fourier_one_neg (t : Torus) : fourier 1 (-t) = conj (fourier 1 t) := by
  simp only [fourier_one, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]

lemma blockTerm_neg (m : ℕ) (t : Torus) :
    blockTerm m (-t) = conj (blockTerm m t) := by
  simp only [blockTerm, fourier_one_neg, (eval_conj _ _).1,
    map_mul, map_pow, Complex.conj_ofReal]

lemma realSeries_even : Function.Even realSeries := by
  intro t
  have hc : complexSeries (-t) = conj (complexSeries t) := by
    unfold complexSeries
    simp_rw [blockTerm_neg]
    exact (Complex.conjCLE.map_tsum).symm
  change (complexSeries (-t)).re = (complexSeries t).re
  rw [hc, Complex.conj_re]

lemma kernel_continuous : Continuous (convolutionKernel realSeries) :=
  Complex.continuous_ofReal.comp
    (realSeries_continuous.comp (continuous_fst.sub continuous_snd))

lemma kernel_symmetric (x y : Torus) :
    convolutionKernel realSeries (x,y) = convolutionKernel realSeries (y,x) := by
  unfold convolutionKernel
  congr 1
  have h : realSeries (y - x) = realSeries (x - y) := by
    simpa only [neg_sub] using realSeries_even (x - y)
  exact h.symm

/-- Every coefficient in the initial block is ±1; all later ones vanish. -/
lemma coefficient_shape (r : ℕ) :
    (∀ n < 2 ^ r,
      ((P r).coeff n = 1 ∨ (P r).coeff n = -1) ∧
      ((Q r).coeff n = 1 ∨ (Q r).coeff n = -1)) ∧
    (∀ n, 2 ^ r ≤ n → (P r).coeff n = 0 ∧ (Q r).coeff n = 0) := by
  induction r with
  | zero =>
    constructor
    · intro n hn
      have : n = 0 := by simpa using hn
      subst n
      simp
    · intro n hn
      have hn0 : n ≠ 0 := by simpa using Nat.ne_of_gt hn
      simp [coeff_one, hn0]
  | succ r ih =>
    constructor
    · intro n hn
      by_cases h : n < 2 ^ r
      · simpa only [P_succ, Q_succ', coeff_add, coeff_sub,
          coeff_X_pow_mul', ite_eq_right (Nat.not_le_of_lt h), add_zero, sub_zero]
          using And.intro (ih.1 n h).1 (ih.1 n h).1
      · have hle : 2 ^ r ≤ n := Nat.le_of_not_gt h
        have hsub : n - 2 ^ r < 2 ^ r := by rw [pow_succ] at hn; omega
        have hp := (ih.2 n hle).1
        have hq := (ih.1 (n - 2 ^ r) hsub).2
        simp only [P_succ, Q_succ', coeff_add, coeff_sub,
          coeff_X_pow_mul', ite_eq_left hle, hp, zero_add, zero_sub]
        constructor
        · exact hq
        · rcases hq with hq | hq <;> simp [hq]
    · intro n hn
      have hle : 2 ^ r ≤ n := by rw [pow_succ] at hn; omega
      have hsub : 2 ^ r ≤ n - 2 ^ r := by rw [pow_succ] at hn; omega
      have hp := (ih.2 n hle).1
      have hq := (ih.2 (n - 2 ^ r) hsub).2
      simp only [P_succ, Q_succ', coeff_add, coeff_sub,
        coeff_X_pow_mul', ite_eq_left hle, hp, hq, add_zero, sub_zero, and_self]

lemma P_coeff_norm (r n : ℕ) (hn : n < 2 ^ r) : ‖(P r).coeff n‖ = 1 := by
  rcases (coefficient_shape r).1 n hn with ⟨h | h, _⟩ <;> simp [h]

lemma blockStart_succ (m : ℕ) :
    blockStart (m + 1) = blockStart m + 2 ^ (2 * (m + 1)) := by
  simp [blockStart, Finset.sum_range_succ, add_assoc]

lemma blockStart_strictMono : StrictMono blockStart := by
  apply strictMono_nat_of_lt_succ
  intro m
  rw [blockStart_succ]
  exact Nat.lt_add_of_pos_right (by positivity)

lemma P_eval_fin (r : ℕ) (z : ℂ) :
    (P r).eval z = ∑ i : Fin (2 ^ r), (P r).coeff i * z ^ (i : ℕ) := by
  rw [eval_eq_sum]
  exact (Polynomial.sum_fin (fun i a => a * z ^ i) (by simp)
    ((Polynomial.degree_lt_iff_coeff_zero _ _).mpr (fun n hn =>
      ((coefficient_shape r).2 n hn).1))).symm

lemma fourier_nat_pow (i : ℕ) (t : Torus) :
    fourier (i : ℤ) t = fourier 1 t ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [Nat.cast_add, Nat.cast_one, fourier_add, ih, pow_succ]

lemma blockTerm_expansion (m : ℕ) :
    blockTerm m = fun t => ∑ i : Fin (2 ^ (2 * (m + 1))),
      ((blockWeight m : ℂ) * (P (2 * (m + 1))).coeff i) *
        fourier ((blockStart m + (i : ℕ) : ℕ) : ℤ) t := by
  funext t
  simp only [blockTerm, P_eval_fin, Finset.mul_sum, Nat.cast_add, fourier_add,
    fourier_nat_pow]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma realBlock_expansion (m : ℕ) :
    (fun t => ((blockTerm m t).re : ℂ)) = fun t =>
      ∑ i : Fin (2 ^ (2 * (m + 1))),
        ((blockWeight m : ℂ) / 2 * (P (2 * (m + 1))).coeff i) *
          (fourier ((blockStart m + (i : ℕ) : ℕ) : ℤ) t +
            fourier (-((blockStart m + (i : ℕ) : ℕ) : ℤ)) t) := by
  funext t
  rw [blockTerm_expansion]
  simp only [Complex.re_sum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rcases ((coefficient_shape (2 * (m + 1))).1 i i.isLt).1 with h | h <;>
    simp only [h, fourier_neg]
  all_goals apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring_nf; simp
lemma fourierCoeff_fin_sum {ι : Type} [Fintype ι] (f : ι → Torus → ℂ)
    (hf : ∀ i, Continuous (f i)) (n : ℤ) :
    fourierCoeff (fun t => ∑ i, f i t) n = ∑ i, fourierCoeff (f i) n := by
  classical
  have heq : (fun t => ∑ i, f i t) = ∑ i, f i := by ext t; simp
  rw [heq]
  simpa only [Finset.sum_apply] using congrFun
    (fourierCoeff.sum Finset.univ f (fun i _ => (hf i).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))) n

lemma realBlock_coeff (m : ℕ) (n : ℤ) :
    fourierCoeff (fun t => ((blockTerm m t).re : ℂ)) n =
      ∑ i : Fin (2 ^ (2 * (m + 1))),
        ((blockWeight m : ℂ) / 2 * (P (2 * (m + 1))).coeff i) *
          ((if n = ((blockStart m + (i : ℕ) : ℕ) : ℤ) then (1 : ℂ) else 0) +
            (if n = -((blockStart m + (i : ℕ) : ℕ) : ℤ) then (1 : ℂ) else 0)) := by
  rw [realBlock_expansion, fourierCoeff_fin_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [fourierCoeff.const_mul]
    have hi (k : ℤ) : Integrable (fourier k : Torus → ℂ) circleMeasure :=
      (fourier k).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [show (fun t : Torus => fourier ((blockStart m + (i : ℕ) : ℕ) : ℤ) t +
        fourier (-((blockStart m + (i : ℕ) : ℕ) : ℤ)) t) =
        (fourier ((blockStart m + (i : ℕ) : ℕ) : ℤ) : Torus → ℂ) +
        (fourier (-((blockStart m + (i : ℕ) : ℕ) : ℤ)) : Torus → ℂ) from rfl,
      fourierCoeff.add (hi _) (hi _)]
    simp only [Pi.add_apply, fourierCoeff_fourier, Pi.single_apply]
  · intro i
    exact continuous_const.mul ((fourier _).continuous.add (fourier _).continuous)

lemma blockStart_pos (m : ℕ) : 0 < blockStart m := by unfold blockStart; omega

lemma block_frequency_injective : Function.Injective
    (fun p : (Σ m : ℕ, Fin (2 ^ (2 * (m + 1)))) =>
      ((blockStart p.1 + (p.2 : ℕ) : ℕ) : ℤ)) := by
  intro ⟨m,i⟩ ⟨k,j⟩ h
  change ((blockStart m + (i : ℕ) : ℕ) : ℤ) = ((blockStart k + (j : ℕ) : ℕ) : ℤ) at h
  have hnat : blockStart m + (i : ℕ) = blockStart k + (j : ℕ) := by exact_mod_cast h
  have hmk : m = k := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hs := blockStart_strictMono.monotone (Nat.succ_le_of_lt hlt)
      rw [blockStart_succ] at hs
      have := i.isLt
      omega
    · have hs := blockStart_strictMono.monotone (Nat.succ_le_of_lt hlt)
      rw [blockStart_succ] at hs
      have := j.isLt
      omega
  subst k
  have hij : i = j := Fin.ext (by omega)
  subst j
  rfl

lemma block_frequency_ne_neg (m k : ℕ) (i : Fin (2 ^ (2 * (m + 1))))
    (j : Fin (2 ^ (2 * (k + 1)))) :
    ((blockStart m + (i : ℕ) : ℕ) : ℤ) ≠
      -((blockStart k + (j : ℕ) : ℕ) : ℤ) := by
  have hm : (0 : ℤ) < (blockStart m : ℤ) := by exact_mod_cast blockStart_pos m
  have hk : (0 : ℤ) < (blockStart k : ℤ) := by exact_mod_cast blockStart_pos k
  push_cast
  omega

lemma realBlock_coeff_at (k m : ℕ) (i : Fin (2 ^ (2 * (m + 1)))) :
    fourierCoeff (fun t => ((blockTerm k t).re : ℂ))
      ((blockStart m + (i : ℕ) : ℕ) : ℤ) =
      if k = m then ((blockWeight m : ℂ) / 2 * (P (2 * (m + 1))).coeff i) else 0 := by
  classical
  rw [realBlock_coeff]
  by_cases hkm : k = m
  · subst k
    rw [ite_eq_left rfl, Finset.sum_eq_single i]
    · simp only [ite_true, eq_self, ite_eq_right (block_frequency_ne_neg m m i i),
        add_zero, mul_one]
    · intro j _ hji
      have hne : ((blockStart m + (i : ℕ) : ℕ) : ℤ) ≠
          ((blockStart m + (j : ℕ) : ℕ) : ℤ) := by
        intro h
        have heq := block_frequency_injective (a₁ := ⟨m,i⟩) (a₂ := ⟨m,j⟩) h
        have : i = j := by cases heq; rfl
        exact hji this.symm
      simp only [ite_eq_right hne, ite_eq_right (block_frequency_ne_neg m m i j),
        zero_add, mul_zero]
    · simp
  · rw [ite_eq_right hkm]
    apply Finset.sum_eq_zero
    intro j _
    have hne : ((blockStart m + (i : ℕ) : ℕ) : ℤ) ≠
        ((blockStart k + (j : ℕ) : ℕ) : ℤ) := by
      intro h
      have heq := block_frequency_injective (a₁ := ⟨m,i⟩) (a₂ := ⟨k,j⟩) h
      exact hkm (congrArg Sigma.fst heq).symm
    simp only [ite_eq_right hne, ite_eq_right (block_frequency_ne_neg m k i j),
      zero_add, mul_zero]

lemma realBlock_hasSum (t : Torus) :
    HasSum (fun m => ((blockTerm m t).re : ℂ)) (realSeries t : ℂ) := by
  exact Complex.ofRealCLM.hasSum (Complex.reCLM.hasSum (blockTerm_summable t).hasSum)

lemma realSeries_coeff_hasSum (n : ℤ) :
    HasSum (fun m => fourierCoeff (fun t => ((blockTerm m t).re : ℂ)) n)
      (fourierCoeff (fun t => (realSeries t : ℂ)) n) := by
  apply hasSum_integral_of_dominated_convergence
    (fun m (_ : Torus) => Real.sqrt 2 / (((m + 1 : ℕ) : ℝ) ^ 2))
  · intro m
    exact ((fourier (-n)).continuous.mul
      (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (blockTerm_continuous m)))).aestronglyMeasurable
  · intro m
    apply Filter.Eventually.of_forall
    intro t
    simp only [smul_eq_mul, norm_mul, show ‖fourier (-n) t‖ = 1 from Circle.norm_coe _, one_mul]
    calc
      ‖((blockTerm m t).re : ℂ)‖ = |(blockTerm m t).re| := by
        simp only [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖blockTerm m t‖ := Complex.abs_re_le_norm _
      _ ≤ _ := blockTerm_bound m t

  · exact Filter.Eventually.of_forall (fun _ => summable_majorant)
  · exact integrable_const _
  · apply Filter.Eventually.of_forall
    intro t
    exact (realBlock_hasSum t).mul_left (fourier (-n) t)

lemma realSeries_coeff_at (m : ℕ) (i : Fin (2 ^ (2 * (m + 1)))) :
    fourierCoeff (fun t => (realSeries t : ℂ))
      ((blockStart m + (i : ℕ) : ℕ) : ℤ) =
        (blockWeight m : ℂ) / 2 * (P (2 * (m + 1))).coeff i := by
  have hs := realSeries_coeff_hasSum ((blockStart m + (i : ℕ) : ℕ) : ℤ)
  simp_rw [realBlock_coeff_at] at hs
  simpa using hs.tsum_eq.symm

lemma realSeries_coeff_norm_at (m : ℕ) (i : Fin (2 ^ (2 * (m + 1)))) :
    ‖fourierCoeff (fun t => (realSeries t : ℂ))
      ((blockStart m + (i : ℕ) : ℕ) : ℤ)‖ = blockWeight m / 2 := by
  rw [realSeries_coeff_at, norm_mul, P_coeff_norm _ _ i.isLt, mul_one,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (blockWeight_pos m)]
  norm_num

lemma kernel_memLp :
    MemLp (convolutionKernel realSeries) 2 (circleMeasure.prod circleMeasure) :=
  kernel_continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma kernel_hermitian :
    PartV.L2KernelCompactSpec.Hermitian circleMeasure
      (kernel_memLp.toLp (convolutionKernel realSeries)) := by
  have h := kernel_memLp.coeFn_toLp
  have hs := (Measure.measurePreserving_swap (μ := circleMeasure) (ν := circleMeasure)).quasiMeasurePreserving
  have hswap := hs.ae_eq_comp h
  filter_upwards [h, hswap] with p hp hp'
  dsimp only [Function.comp_apply] at hp'
  rw [hp, hp']
  simp only [convolutionKernel, Complex.conj_ofReal]
  congr 1
  have he := realSeries_even (p.1 - p.2)
  change realSeries (p.1 - p.2) = realSeries (p.2 - p.1)
  simpa only [neg_sub] using he.symm

lemma kernel_compact_selfAdjoint :
    let K := PartV.L2KernelSpec.OperatorValue circleMeasure circleMeasure
      (kernel_memLp.toLp (convolutionKernel realSeries))
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap ∧
      IsSelfAdjoint K := by
  have h := PartV.L2KernelCompact.hermitian_kernel_compact_selfadjoint
    circleMeasure _ kernel_hermitian
  exact ⟨h.1, ContinuousLinearMap.isSelfAdjoint_iff'.mpr h.2⟩

lemma kernel_hilbertSchmidt :
    TraceIdeals.HilbertSchmidtDefinitions.Spec.IsHilbertSchmidtValue
      (PartV.L2KernelSpec.OperatorValue circleMeasure circleMeasure
        (kernel_memLp.toLp (convolutionKernel realSeries))) :=
  (TraceIdeals.HilbertSchmidtKernels.kernel_isometry circleMeasure circleMeasure _).1

lemma square_le_two_pow {n : ℕ} (hn : 4 ≤ n) : (n : ℝ) ^ 2 ≤ (2 : ℝ) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    simp only [Nat.cast_add, Nat.cast_one]
    rw [pow_succ (2 : ℝ) n]
    have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n : ℝ) - 2)]
lemma block_mass_not_summable :
    ¬ Summable (fun m : ℕ => (2 : ℝ) ^ (m + 1) / (((m + 1 : ℕ) : ℝ) ^ 2)) := by
  intro h
  have hsmall := (tendsto_order.mp h.tendsto_atTop_zero).2 1 (by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hsmall
  let m := max N 3
  have hlow : (1 : ℝ) ≤ (2 : ℝ) ^ (m + 1) / (((m + 1 : ℕ) : ℝ) ^ 2) := by
    apply (le_div_iff₀ (by positivity)).mpr
    simpa using square_le_two_pow (n := m + 1) (by dsimp [m]; omega)
  exact (not_lt_of_ge hlow) (hN m (by dsimp [m]; omega))

/-- The positive disjoint blocks alone have divergent total Fourier mass. -/
lemma fourier_not_summable :
    ¬ Summable (fun n : ℤ => ‖fourierCoeff (fun t => (realSeries t : ℂ)) n‖) := by
  intro h
  have hs : Summable (fun p : (Σ m : ℕ, Fin (2 ^ (2 * (m + 1)))) =>
      ‖fourierCoeff (fun t => (realSeries t : ℂ))
        ((blockStart p.1 + (p.2 : ℕ) : ℕ) : ℤ)‖) :=
    h.comp_injective block_frequency_injective
  have hm := ((summable_sigma_of_nonneg
    (fun p : (Σ m : ℕ, Fin (2 ^ (2 * (m + 1)))) => norm_nonneg
      (fourierCoeff (fun t => (realSeries t : ℂ))
        ((blockStart p.1 + (p.2 : ℕ) : ℕ) : ℤ)))).mp hs).2
  have hm' : Summable (fun m : ℕ =>
      (2 : ℝ) ^ (2 * (m + 1)) * (blockWeight m / 2)) := by
    simpa only [realSeries_coeff_norm_at, tsum_fintype, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] using hm
  apply block_mass_not_summable
  convert hm'.mul_left 2 using 1
  ext m
  unfold blockWeight
  rw [show 2 * (m + 1) = (m + 1) + (m + 1) by omega, pow_add]
  field_simp
  ring

lemma character_sub (n : ℤ) (x y : Torus) :
    fourier n (x-y) = fourier n x * fourier (-n) y := by
  simp only [fourier_apply, sub_eq_add_neg, smul_add, smul_neg, neg_smul,
    AddCircle.toCircle_add, AddCircle.toCircle_neg, Circle.coe_mul]

lemma convolution_integral (g : Torus → ℂ) (n : ℤ) (x : Torus) :
    (∫ y, g (x-y) * fourier n y ∂circleMeasure) =
      fourierCoeff g n * fourier n x := by
  calc
    _ = ∫ t, g t * fourier n (x-t) ∂circleMeasure := by
      simpa only [sub_sub_cancel] using
        (integral_sub_left_eq_self (fun y => g (x-y) * fourier n y) circleMeasure x).symm
    _ = ∫ t, (fourier (-n) t * g t) * fourier n x ∂circleMeasure := by
      congr 1
      funext t
      rw [character_sub]
      ring
    _ = _ := by rw [integral_mul_const]; rfl
lemma convolution_eigenfunction (n : ℤ) :
    PartV.L2KernelSpec.OperatorValue circleMeasure circleMeasure
      (kernel_memLp.toLp (convolutionKernel realSeries))
      (fourierBasis (T := (1 : ℝ)) n) =
      fourierCoeff (fun t => (realSeries t : ℂ)) n • fourierBasis (T := (1 : ℝ)) n := by
  have hu : MemLp (fourier n : Torus → ℂ) 2 circleMeasure :=
    (fourier n).continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hb : (fourierBasis (T := (1 : ℝ)) n : Torus → ℂ) =ᵐ[circleMeasure] fourier n := by
    simpa only [coe_fourierBasis] using (coeFn_fourierLp (T := (1 : ℝ)) 2 n)
  have heq : hu.toLp (fourier n) = fourierBasis (T := (1 : ℝ)) n :=
    Lp.ext (hu.coeFn_toLp.trans hb.symm)
  have hf := PartV.L2Kernel.kernel_representative_formula circleMeasure circleMeasure
    (convolutionKernel realSeries) (fourier n) kernel_memLp hu
  rw [heq] at hf
  apply Lp.ext
  filter_upwards [hf, Lp.coeFn_smul
    (fourierCoeff (fun t => (realSeries t : ℂ)) n) (fourierBasis (T := (1 : ℝ)) n), hb]
    with x hx hs hb'
  rw [hx, hs]
  simp only [Pi.smul_apply, smul_eq_mul, hb']
  exact convolution_integral (fun t => (realSeries t : ℂ)) n x

/-- The diagonal is computed for the canonical product-L² integral operator. -/
lemma convolution_fourier_diagonal (n : ℤ) :
    inner ℂ (fourierBasis (T := (1 : ℝ)) n)
      (PartV.L2KernelSpec.OperatorValue circleMeasure circleMeasure
        (kernel_memLp.toLp (convolutionKernel realSeries))
        (fourierBasis (T := (1 : ℝ)) n)) =
      fourierCoeff (fun t => (realSeries t : ℂ)) n := by
  rw [convolution_eigenfunction, inner_smul_right]
  rw [inner_self_eq_norm_sq_to_K, (fourierBasis (T := (1 : ℝ))).orthonormal.norm_eq_one n]
  simp

lemma kernel_not_traceClass :
    ¬ TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue
      (PartV.L2KernelSpec.OperatorValue circleMeasure circleMeasure
        (kernel_memLp.toLp (convolutionKernel realSeries))) := by
  intro h
  have hd := (TraceIdeals.TraceClassDefinitions.diagonal_trace ℂ CircleL2 _ h ℤ
    (fourierBasis (T := (1 : ℝ)))).1
  exact fourier_not_summable (by simpa only [convolution_fourier_diagonal] using hd)

theorem explicit_counterexample : Spec.ExplicitCounterexample := by
  refine ⟨realSeries_continuous, realSeries_even, fourier_not_summable,
    kernel_continuous, kernel_symmetric, kernel_memLp, ?_⟩
  exact ⟨kernel_compact_selfAdjoint.1, kernel_compact_selfAdjoint.2,
    kernel_hilbertSchmidt, kernel_not_traceClass⟩

theorem continuous_complex_counterexample : ∃ f : Torus → ℝ, CounterexampleProperties f :=
  ⟨realSeries, explicit_counterexample⟩


lemma real_kernel_continuous : Continuous (realConvolutionKernel realSeries) :=
  realSeries_continuous.comp (continuous_fst.sub continuous_snd)

lemma real_kernel_symmetric (x y : Torus) :
    realConvolutionKernel realSeries (x,y) = realConvolutionKernel realSeries (y,x) := by
  unfold realConvolutionKernel
  have h : realSeries (y - x) = realSeries (x - y) := by
    simpa only [neg_sub] using realSeries_even (x - y)
  exact h.symm

lemma real_kernel_memLp :
    MemLp (realConvolutionKernel realSeries) 2 (circleMeasure.prod circleMeasure) :=
  real_kernel_continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma real_kernel_hermitian :
    PartV.L2KernelCompactSpec.Hermitian circleMeasure
      (real_kernel_memLp.toLp (realConvolutionKernel realSeries)) := by
  have h := real_kernel_memLp.coeFn_toLp
  have hs := (Measure.measurePreserving_swap (μ := circleMeasure) (ν := circleMeasure)).quasiMeasurePreserving
  have hswap := hs.ae_eq_comp h
  filter_upwards [h, hswap] with p hp hp'
  dsimp only [Function.comp_apply] at hp'
  rw [hp, hp']
  simp only [realConvolutionKernel, RCLike.conj_to_real]
  have he := realSeries_even (p.1 - p.2)
  change realSeries (p.1 - p.2) = realSeries (p.2 - p.1)
  simpa only [neg_sub] using he.symm

lemma real_kernel_compact_selfAdjoint :
    let K := PartV.L2KernelSpec.OperatorValue circleMeasure circleMeasure
      (real_kernel_memLp.toLp (realConvolutionKernel realSeries))
    Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap ∧
      IsSelfAdjoint K := by
  have h := PartV.L2KernelCompact.hermitian_kernel_compact_selfadjoint
    circleMeasure _ real_kernel_hermitian
  exact ⟨h.1, ContinuousLinearMap.isSelfAdjoint_iff'.mpr h.2⟩

lemma real_kernel_hilbertSchmidt :
    TraceIdeals.HilbertSchmidtDefinitions.Spec.IsHilbertSchmidtValue
      (PartV.L2KernelSpec.OperatorValue circleMeasure circleMeasure
        (real_kernel_memLp.toLp (realConvolutionKernel realSeries))) :=
  (TraceIdeals.HilbertSchmidtKernels.kernel_isometry circleMeasure circleMeasure _).1

lemma real_kernel_representative_formula (u : Torus → ℝ)
    (hu : MemLp u 2 circleMeasure) :
    (PartV.L2KernelSpec.OperatorValue circleMeasure circleMeasure
      (real_kernel_memLp.toLp (realConvolutionKernel realSeries))
      (hu.toLp u) : Torus → ℝ) =ᵐ[circleMeasure]
      fun x => ∫ y, realSeries (x-y) * u y ∂circleMeasure :=
  PartV.L2Kernel.kernel_representative_formula circleMeasure circleMeasure
    (realConvolutionKernel realSeries) u real_kernel_memLp hu

lemma real_convolution_integral_re (n : ℤ) (x : Torus) :
    (∫ y, realSeries (x-y) * (fourier n y).re ∂circleMeasure) =
      (fourierCoeff (fun t => (realSeries t : ℂ)) n * fourier n x).re := by
  have hi : Integrable (fun y => (realSeries (x-y) : ℂ) * fourier n y) circleMeasure :=
    ((Complex.continuous_ofReal.comp
      (realSeries_continuous.comp (continuous_const.sub continuous_id))).mul
      (fourier n).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ = (∫ y, (realSeries (x-y) : ℂ) * fourier n y ∂circleMeasure).re := by
      simpa [Complex.mul_re] using integral_re hi
    _ = _ := congrArg Complex.re (convolution_integral (fun t => (realSeries t : ℂ)) n x)

lemma real_convolution_re_eigenfunction (n : ℤ)
    (hn : (fourierCoeff (fun t => (realSeries t : ℂ)) n).im = 0) :
    PartV.L2KernelSpec.OperatorValue circleMeasure circleMeasure
      (real_kernel_memLp.toLp (realConvolutionKernel realSeries))
      (Complex.reCLM.compLp (fourierBasis (T := (1 : ℝ)) n)) =
      (fourierCoeff (fun t => (realSeries t : ℂ)) n).re •
        Complex.reCLM.compLp (fourierBasis (T := (1 : ℝ)) n) := by
  have hu : MemLp (fun t => (fourier n t).re) 2 circleMeasure :=
    (Complex.continuous_re.comp (fourier n).continuous).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb : (Complex.reCLM.compLp (fourierBasis (T := (1 : ℝ)) n) : Torus → ℝ)
      =ᵐ[circleMeasure] fun t => (fourier n t).re := by
    have he : (fourierBasis (T := (1 : ℝ)) n : Torus → ℂ)
        =ᵐ[circleMeasure] fourier n := by
      simpa only [coe_fourierBasis] using (coeFn_fourierLp (T := (1 : ℝ)) 2 n)
    filter_upwards [Complex.reCLM.coeFn_compLp (fourierBasis (T := (1 : ℝ)) n), he]
      with t ht he'
    simpa only [Complex.reCLM_apply, he'] using ht
  have heq : hu.toLp (fun t => (fourier n t).re) =
      Complex.reCLM.compLp (fourierBasis (T := (1 : ℝ)) n) :=
    Lp.ext (hu.coeFn_toLp.trans hb.symm)
  have hf := real_kernel_representative_formula (fun t => (fourier n t).re) hu
  rw [heq] at hf
  apply Lp.ext
  filter_upwards [hf, Lp.coeFn_smul
    (fourierCoeff (fun t => (realSeries t : ℂ)) n).re
    (Complex.reCLM.compLp (fourierBasis (T := (1 : ℝ)) n)), hb]
    with x hx hs hb'
  rw [hx, hs]
  simp only [Pi.smul_apply, smul_eq_mul, hb']
  rw [real_convolution_integral_re, Complex.mul_re, hn, zero_mul, sub_zero]

lemma real_convolution_re_eigenfunction_at (m : ℕ)
    (i : Fin (2 ^ (2 * (m + 1)))) :
    PartV.L2KernelSpec.OperatorValue circleMeasure circleMeasure
      (real_kernel_memLp.toLp (realConvolutionKernel realSeries))
      (Complex.reCLM.compLp
        (fourierBasis (T := (1 : ℝ)) ((blockStart m + (i : ℕ) : ℕ) : ℤ))) =
      (fourierCoeff (fun t => (realSeries t : ℂ))
        ((blockStart m + (i : ℕ) : ℕ) : ℤ)).re •
        Complex.reCLM.compLp
          (fourierBasis (T := (1 : ℝ)) ((blockStart m + (i : ℕ) : ℕ) : ℤ)) := by
  apply real_convolution_re_eigenfunction
  rw [realSeries_coeff_at]
  rcases ((coefficient_shape (2 * (m + 1))).1 i i.isLt).1 with h | h <;>
    simp [h]

/-- The ordinary inclusion of real-valued L² into complex-valued L². -/
def realL2Inclusion : RealCircleL2 →L[ℝ] CircleL2 := Complex.ofRealCLM.compLpL 2 circleMeasure

theorem realL2Inclusion_inner (u v : RealCircleL2) :
    inner ℂ (realL2Inclusion u) (realL2Inclusion v) = (inner ℝ u v : ℂ) := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ a, (inner ℝ (u a) (v a) : ℂ) ∂circleMeasure := by
      apply integral_congr_ae
      filter_upwards [Complex.ofRealCLM.coeFn_compLp u, Complex.ofRealCLM.coeFn_compLp v]
        with x hu hv
      change inner ℂ ((Complex.ofRealCLM.compLp u) x) ((Complex.ofRealCLM.compLp v) x) = _
      rw [hu, hv]
      simp
    _ = _ := integral_ofReal

lemma realL2Inclusion_injective : Function.Injective realL2Inclusion := by
  intro u v h
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hh := realL2Inclusion_inner (u-v) (u-v)
  rw [map_sub, h, sub_self, inner_zero_left] at hh
  have he : inner ℝ (u-v) (u-v) = 0 := Complex.ofReal_eq_zero.mp hh.symm
  simpa only [real_inner_self_eq_norm_sq, sq_eq_zero_iff] using he

/-- The normalized real cosine vector at a nonzero frequency. -/
def cosineVector (n : ℤ) : RealCircleL2 :=
  Real.sqrt 2 • Complex.reCLM.compLp (fourierBasis (T := (1 : ℝ)) n)

lemma realL2Inclusion_cosineVector (n : ℤ) :
    realL2Inclusion (cosineVector n) =
      ((Real.sqrt 2 / 2 : ℝ) : ℂ) •
        (fourierBasis (T := (1 : ℝ)) n + fourierBasis (T := (1 : ℝ)) (-n)) := by
  apply Lp.ext
  have he (k : ℤ) : (fourierBasis (T := (1 : ℝ)) k : Torus → ℂ) =ᵐ[circleMeasure] fourier k := by
    simpa only [coe_fourierBasis] using coeFn_fourierLp (T := (1 : ℝ)) 2 k
  filter_upwards [Complex.ofRealCLM.coeFn_compLp (cosineVector n),
    Lp.coeFn_smul (Real.sqrt 2) (Complex.reCLM.compLp (fourierBasis (T := (1 : ℝ)) n)),
    Complex.reCLM.coeFn_compLp (fourierBasis (T := (1 : ℝ)) n),
    Lp.coeFn_smul (((Real.sqrt 2 / 2 : ℝ) : ℂ))
      (fourierBasis (T := (1 : ℝ)) n + fourierBasis (T := (1 : ℝ)) (-n)),
    Lp.coeFn_add (fourierBasis (T := (1 : ℝ)) n) (fourierBasis (T := (1 : ℝ)) (-n)),
    he n, he (-n)] with t hi hs hr hs' ha hn hneg
  change (Complex.ofRealCLM.compLp (cosineVector n)) t = _
  rw [hi, show (cosineVector n) t =
    (Real.sqrt 2 • Complex.reCLM.compLp (fourierBasis (T := (1 : ℝ)) n)) t from rfl,
    hs, hs']
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [ha]
  simp only [Pi.add_apply]
  rw [hr, hn, hneg]
  simp only [Complex.ofRealCLM_apply, Complex.reCLM_apply, Pi.smul_apply, smul_eq_mul,
    fourier_neg]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

lemma cosineVector_orthonormal {ι : Type*} (freq : ι → ℤ)
    (hpos : ∀ i, 0 < freq i) (hinj : Function.Injective freq) :
    Orthonormal ℝ (fun i => cosineVector (freq i)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  have h := realL2Inclusion_inner (cosineVector (freq i)) (cosineVector (freq j))
  rw [realL2Inclusion_cosineVector, realL2Inclusion_cosineVector,
    inner_smul_left, inner_smul_right, inner_add_left, inner_add_right, inner_add_right] at h
  have hfourier := (orthonormal_iff_ite.mp
    (fourierBasis (T := (1 : ℝ))).orthonormal)
  simp only [hfourier] at h
  have hcross₁ : freq i ≠ -freq j := by have := hpos i; have := hpos j; omega
  have hcross₂ : -freq i ≠ freq j := by have := hpos i; have := hpos j; omega
  have hsame : (freq i = freq j) ↔ i = j := hinj.eq_iff
  simp only [hcross₁, hcross₂, neg_inj, hsame, ite_false, add_zero, zero_add] at h
  split_ifs at h ⊢ with hij
  · have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    have hre := congrArg Complex.re h
    simp only [Complex.conj_ofReal, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, mul_zero, sub_zero] at hre
    norm_num at hre
    nlinarith
  · simpa using congrArg Complex.re h.symm
lemma cosineVector_diagonal {ι : Type*} (freq : ι → ℤ)
    (hpos : ∀ i, 0 < freq i) (hinj : Function.Injective freq)
    (T : RealCircleL2 →L[ℝ] RealCircleL2) (a : ι → ℝ)
    (heig : ∀ i, T (Complex.reCLM.compLp (fourierBasis (T := (1 : ℝ)) (freq i))) =
      a i • Complex.reCLM.compLp (fourierBasis (T := (1 : ℝ)) (freq i))) (i : ι) :
    inner ℝ (cosineVector (freq i)) (T (cosineVector (freq i))) = a i := by
  have he : T (cosineVector (freq i)) = a i • cosineVector (freq i) := by
    unfold cosineVector
    rw [map_smul, heig i]
    exact smul_comm _ _ _
  rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K,
    (cosineVector_orthonormal freq hpos hinj).norm_eq_one i]
  simp

universe u v w

/-- Extend an orthonormal family to a basis to apply absolute diagonal summability. -/
lemma traceClass_orthonormal_diagonal {𝕜 : Type u} [RCLike 𝕜]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H →L[𝕜] H) (hT : TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue T)
    {ι : Type w} (e : ι → H) (he : Orthonormal 𝕜 e) :
    Summable (fun i => ‖inner 𝕜 (e i) (T (e i))‖) := by
  obtain ⟨s, b, hs, hb⟩ := he.toSubtypeRange.exists_hilbertBasis_extension
  let j : ι → s := fun i => ⟨e i, hs ⟨i, rfl⟩⟩
  have hj : Function.Injective j := by
    intro i k h
    exact he.linearIndependent.injective (congrArg Subtype.val h)
  have hd := (TraceIdeals.TraceClassDefinitions.diagonal_trace 𝕜 H T hT s b).1
  have hd' := hd.comp_injective hj
  apply hd'.congr
  intro i
  change ‖inner 𝕜 (b (j i)) (T (b (j i)))‖ = _
  rw [congrFun hb (j i)]


lemma realSeries_coeff_re_norm_at (m : ℕ) (i : Fin (2 ^ (2 * (m + 1)))) :
    ‖(fourierCoeff (fun t => (realSeries t : ℂ))
      ((blockStart m + (i : ℕ) : ℕ) : ℤ)).re‖ = blockWeight m / 2 := by
  rw [realSeries_coeff_at]
  rcases ((coefficient_shape (2 * (m + 1))).1 i i.isLt).1 with h | h <;>
    simp [h, Real.norm_eq_abs, abs_of_pos (blockWeight_pos m)]

lemma block_weights_not_summable :
    ¬ Summable (fun p : (Σ m : ℕ, Fin (2 ^ (2 * (m + 1)))) => blockWeight p.1 / 2) := by
  intro h
  have hm := ((summable_sigma_of_nonneg
    (fun p : (Σ m : ℕ, Fin (2 ^ (2 * (m + 1)))) =>
      div_nonneg (blockWeight_pos p.1).le (by norm_num))).mp h).2
  have hm' : Summable (fun m : ℕ =>
      (2 : ℝ) ^ (2 * (m + 1)) * (blockWeight m / 2)) := by
    simpa only [tsum_fintype, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] using hm
  apply block_mass_not_summable
  convert hm'.mul_left 2 using 1
  ext m
  unfold blockWeight
  rw [show 2 * (m + 1) = (m + 1) + (m + 1) by omega, pow_add]
  field_simp
  ring

/-- Positive-frequency cosines already force divergent diagonal mass on real L². -/
lemma real_kernel_not_traceClass :
    ¬ TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue
      (PartV.L2KernelSpec.OperatorValue circleMeasure circleMeasure
        (real_kernel_memLp.toLp (realConvolutionKernel realSeries))) := by
  intro h
  let freq : (Σ m : ℕ, Fin (2 ^ (2 * (m + 1)))) → ℤ :=
    fun p => ((blockStart p.1 + (p.2 : ℕ) : ℕ) : ℤ)
  have hpos : ∀ p, 0 < freq p := by
    intro p
    dsimp [freq]
    have : 0 < blockStart p.1 + (p.2 : ℕ) :=
      Nat.add_pos_left (blockStart_pos p.1) _
    exact_mod_cast this
  have hon := cosineVector_orthonormal freq hpos block_frequency_injective
  have hd := traceClass_orthonormal_diagonal
    _ h
    (fun p => cosineVector (freq p)) hon
  have hdiag (p : (Σ m : ℕ, Fin (2 ^ (2 * (m + 1))))) :
      inner ℝ (cosineVector (freq p))
        (PartV.L2KernelSpec.OperatorValue circleMeasure circleMeasure
          (real_kernel_memLp.toLp (realConvolutionKernel realSeries))
          (cosineVector (freq p))) =
        (fourierCoeff (fun t => (realSeries t : ℂ)) (freq p)).re := by
    apply cosineVector_diagonal freq hpos block_frequency_injective
    intro q
    exact real_convolution_re_eigenfunction_at q.1 q.2
  apply block_weights_not_summable
  apply hd.congr
  intro p
  rw [hdiag]
  exact realSeries_coeff_re_norm_at p.1 p.2



theorem explicit_real_counterexample : Spec.ExplicitRealCounterexample := by
  refine ⟨realSeries_continuous, realSeries_even, real_kernel_continuous,
    real_kernel_symmetric, real_kernel_memLp, ?_⟩
  exact ⟨real_kernel_compact_selfAdjoint.1, real_kernel_compact_selfAdjoint.2,
    real_kernel_hilbertSchmidt, real_kernel_not_traceClass⟩

theorem continuous_counterexample : Spec.ContinuousCounterexample :=
  ⟨realSeries, explicit_counterexample, explicit_real_counterexample⟩

end ExpandedFA.IntegralOperators.ContinuousTraceCounterexample
