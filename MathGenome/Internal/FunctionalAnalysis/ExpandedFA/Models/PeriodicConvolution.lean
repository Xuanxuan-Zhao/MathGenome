import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.PeriodicConvolution
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.TorusFourierBasis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Models.DiagonalLpSpectrum
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense

noncomputable section
open MeasureTheory
open scoped ENNReal Topology

namespace ExpandedFA.Models.PeriodicConvolution
open PeriodicConvolutionSpec

def operator : OperatorType := @operatorValue

lemma enumeratedBasis_apply (T : ℝ) [Fact (0 < T)] (j : ℕ) :
    enumeratedBasis T j = fourierLp 2 (frequency j) := by
  simp [enumeratedBasis]

lemma enumeratedBasis_repr (T : ℝ) [Fact (0 < T)] (f : Space T) (j : ℕ) :
    (enumeratedBasis T).repr f j = fourierCoeff f (frequency j) := by
  rw [HilbertBasis.repr_apply_apply, enumeratedBasis_apply, ← fourierBasis_repr,
    HilbertBasis.repr_apply_apply, coe_fourierBasis]

theorem norm_bound : NormBound := by
  intro T hT k
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  change ‖(enumeratedBasis T).repr.symm
    (DiagonalLpSpectrumSpec.diagonalValue 2 (coefficients k) ((enumeratedBasis T).repr f))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖coefficients k‖ * ‖(enumeratedBasis T).repr f‖ :=
      DiagonalLpSpectrumSpec.diagonalLinear_bound 2 (coefficients k) _
    _ ≤ ‖k‖ * ‖f‖ := by
      rw [LinearIsometryEquiv.norm_map]
      exact mul_le_mul_of_nonneg_right
        (lp.norm_le_of_forall_le (norm_nonneg _) (fun j => coefficient_bound k _))
        (norm_nonneg _)

theorem coefficient_action : CoefficientAction := by
  intro T hT k f n
  obtain ⟨j, rfl⟩ := frequency.surjective n
  rw [← enumeratedBasis_repr, ← enumeratedBasis_repr T f j]
  change (enumeratedBasis T).repr ((enumeratedBasis T).repr.symm _) j = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem fourier_diagonal : FourierDiagonal := by
  intro T hT k n
  apply (enumeratedBasis T).repr.injective
  apply lp.ext
  funext j
  rw [enumeratedBasis_repr, coefficient_action, map_smul]
  change fourierCoeff k (frequency j) * fourierCoeff (fourierLp 2 n) (frequency j) =
    fourierCoeff k n * ((enumeratedBasis T).repr (fourierLp 2 n)) j
  rw [enumeratedBasis_repr, fourierCoeff_congr_ae (coeFn_fourierLp 2 n),
    fourierCoeff_fourier]
  simp only [Pi.single_apply]
  split_ifs with h
  · rw [h]
  · simp

lemma fourier_on_add {T : ℝ} (n : ℤ) (x y : Circle T) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- The convolution theorem uses only L¹ integrability on the compact group. -/
lemma convolution_coefficient {T : ℝ} [Fact (0 < T)]
    (k f : Circle T → ℂ) (hk : Integrable k (Haar T)) (hf : Integrable f (Haar T))
    (n : ℤ) :
    fourierCoeff (fun x => ∫ t, k t * f (x - t) ∂Haar T) n =
      fourierCoeff k n * fourierCoeff f n := by
  have he (x : Circle T) :
      fourier (-n) x * (∫ t, k t * f (x - t) ∂Haar T) =
        ∫ t, (fourier (-n) t * k t) * (fourier (-n) (x - t) * f (x - t)) ∂Haar T := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply ae_of_all
    intro t
    have hc : fourier (-n) x = fourier (-n) t * fourier (-n) (x - t) := by
      rw [← fourier_on_add, add_sub_cancel]
    rw [hc]
    ring
  simp only [fourierCoeff, smul_eq_mul]
  simp_rw [he]
  exact integral_convolution (ContinuousLinearMap.mul ℂ ℂ)
    (hk.fourier_smul (-n)) (hf.fourier_smul (-n))

theorem integral_identification : IntegralIdentification := by
  intro T hT k f
  have hk : Integrable (k : Circle T → ℂ) (Haar T) :=
    memLp_one_iff_integrable.mp (Lp.memLp k)
  have hf : Integrable (f : Circle T → ℂ) (Haar T) :=
    MemLp.integrable (by norm_num) (Lp.memLp f)
  refine ⟨hk.ae_convolution_exists (ContinuousLinearMap.mul ℂ ℂ) hf, ?_⟩
  apply ExpandedFA.Fourier.TorusFourierBasis.l1_unique T
  · exact MemLp.integrable (by norm_num) (Lp.memLp _)
  · exact hk.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hf
  · intro n
    rw [coefficient_action, convolution_coefficient _ _ hk hf]

lemma operator_conjugation {T : ℝ} [Fact (0 < T)] (k : Kernel T) :
    operatorValue k = (enumeratedBasis T).repr.symm.conjStarAlgEquiv
      (diagonalLp 2 (coefficients k)) := by
  ext f
  rfl

theorem spectrum_law : SpectrumLaw := by
  intro T hT k
  rw [operator_conjugation, AlgEquiv.spectrum_eq]
  change spectrum ℂ (DiagonalLpSpectrumSpec.diagonalValue 2 (coefficients k)) = _
  rw [diagonalLp_spectrum]
  congr 1
  exact frequency.surjective.range_comp (fourierCoeff k)

lemma diagonal_star (a : DiagonalLpSpectrumSpec.Sequence ∞) :
    star (diagonalLp 2 a) = diagonalLp 2 (star a) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  change inner ℂ (star (a n) * x n) (y n) = inner ℂ (x n) (a n * y n)
  simp [RCLike.inner_apply, mul_comm, mul_left_comm, mul_assoc]

lemma diagonal_normal (a : DiagonalLpSpectrumSpec.Sequence ∞) :
    IsStarNormal (diagonalLp 2 a) := by
  constructor
  change star (diagonalLp 2 a) * diagonalLp 2 a =
    diagonalLp 2 a * star (diagonalLp 2 a)
  rw [diagonal_star]
  apply ContinuousLinearMap.ext
  intro x
  apply lp.ext
  funext n
  change star (a n) * (a n * x n) = a n * (star (a n) * x n)
  ring

theorem normality : Normality := by
  intro T hT k
  rw [operator_conjugation]
  let _ := diagonal_normal (coefficients k)
  exact IsStarNormal.map _ _

lemma diagonal_injective : Function.Injective
    (diagonalLp 2 : DiagonalLpSpectrumSpec.Sequence ∞ →
      DiagonalLpSpectrumSpec.Sequence 2 →L[ℂ] DiagonalLpSpectrumSpec.Sequence 2) := by
  intro a b h
  apply lp.ext
  funext n
  have hn := congrArg (fun D : DiagonalLpSpectrumSpec.Sequence 2 →L[ℂ]
    DiagonalLpSpectrumSpec.Sequence 2 => D (lp.single 2 n 1) n) h
  change a n * (lp.single (E := fun _ : ℕ => ℂ) 2 n (1 : ℂ)) n =
    b n * (lp.single (E := fun _ : ℕ => ℂ) 2 n (1 : ℂ)) n at hn
  simpa only [lp.single_apply_self, mul_one] using hn

lemma diagonal_selfAdjoint (a : DiagonalLpSpectrumSpec.Sequence ∞) :
    IsSelfAdjoint (diagonalLp 2 a) ↔ ∀ n, (a n).im = 0 := by
  change star (diagonalLp 2 a) = diagonalLp 2 a ↔ _
  rw [diagonal_star, diagonal_injective.eq_iff]
  constructor
  · intro h n
    apply Complex.conj_eq_iff_im.mp
    exact congrArg (fun b : DiagonalLpSpectrumSpec.Sequence ∞ => b n) h
  · intro h
    apply lp.ext
    funext n
    exact Complex.conj_eq_iff_im.mpr (h n)

theorem selfAdjoint_criterion : SelfAdjointCriterion := by
  intro T hT k
  let C := (enumeratedBasis T).repr.symm.conjStarAlgEquiv
  have hc : IsSelfAdjoint (C (diagonalLp 2 (coefficients k))) ↔
      IsSelfAdjoint (diagonalLp 2 (coefficients k)) := by
    constructor
    · intro h
      simpa only [StarAlgEquiv.symm_apply_apply] using h.map C.symm
    · exact fun h => h.map C
  rw [operator_conjugation, hc, diagonal_selfAdjoint]
  constructor
  · intro h n
    obtain ⟨j, rfl⟩ := frequency.surjective n
    exact h j
  · intro h j
    exact h (frequency j)

theorem positivity_criterion : PositivityCriterion := by
  intro T hT k
  constructor
  · intro h n
    refine ⟨(selfAdjoint_criterion T k).mp h.isSelfAdjoint n, ?_⟩
    have hh := h.re_inner_nonneg_right (fourierLp (T := T) 2 n)
    rw [fourier_diagonal, inner_smul_right] at hh
    have he := orthonormal_iff_ite.mp (orthonormal_fourier (T := T)) n n
    simp only [ite_true] at he
    rw [he, mul_one] at hh
    exact hh
  · intro h
    apply ContinuousLinearMap.isPositive_def'.mpr
    refine ⟨(selfAdjoint_criterion T k).mpr (fun n => (h n).1), ?_⟩
    intro f
    change 0 ≤ (inner ℂ (operatorValue k f) f).re
    rw [← (enumeratedBasis T).repr.inner_map_map]
    change 0 ≤ (inner ℂ ((enumeratedBasis T).repr
      ((enumeratedBasis T).repr.symm _)) ((enumeratedBasis T).repr f)).re
    rw [LinearIsometryEquiv.apply_symm_apply, lp.inner_eq_tsum,
      Complex.re_tsum (lp.summable_inner _ _)]
    apply tsum_nonneg
    intro j
    change 0 ≤ (inner ℂ (fourierCoeff k (frequency j) •
      ((enumeratedBasis T).repr f j)) ((enumeratedBasis T).repr f j)).re
    rw [inner_smul_left, inner_self_eq_norm_sq_to_K]
    simp only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow,
      Complex.mul_re, Complex.conj_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    exact mul_nonneg (h (frequency j)).2 (sq_nonneg _)

lemma lp2_tendsto_zero (a : DiagonalLpSpectrumSpec.Sequence 2) :
    Filter.Tendsto (fun j => a j) Filter.atTop (𝓝 0) := by
  have hs : Summable (fun j => ‖a j‖ ^ 2) := by
    simpa using (lp.memℓp a).summable (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs.tendsto_atTop_zero
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht

/-- Riemann--Lebesgue for L¹ kernels: approximate in L¹ by a bounded continuous
function, use its L² coefficients, and use the uniform L¹ coefficient bound. -/
lemma coefficients_tendsto_zero {T : ℝ} [Fact (0 < T)] (k : Kernel T) :
    Filter.Tendsto (fun j => fourierCoeff k (frequency j)) Filter.atTop (𝓝 0) := by
  have hk : Integrable (k : Circle T → ℂ) (Haar T) :=
    memLp_one_iff_integrable.mp (Lp.memLp k)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨g, hg, hgi⟩ := hk.exists_boundedContinuous_integral_sub_le (half_pos hε)
  let G : Space T := BoundedContinuousFunction.toLp 2 (Haar T) ℂ g
  have hG : fourierCoeff (G : Circle T → ℂ) = fourierCoeff g :=
    fourierCoeff_congr_ae (BoundedContinuousFunction.coeFn_toLp 2 (Haar T) ℂ g)
  have ht : Filter.Tendsto (fun j => fourierCoeff g (frequency j)) Filter.atTop (𝓝 0) := by
    simpa only [enumeratedBasis_repr, hG] using lp2_tendsto_zero ((enumeratedBasis T).repr G)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ht (ε / 2) (half_pos hε)
  refine ⟨N, fun j hj => ?_⟩
  have hb : ‖fourierCoeff k (frequency j) - fourierCoeff g (frequency j)‖ ≤ ε / 2 := by
    have he : fourierCoeff k (frequency j) - fourierCoeff g (frequency j) =
        ∫ x, fourier (-(frequency j)) x • (k x - g x) ∂Haar T := by
      simp only [fourierCoeff, smul_sub]
      rw [integral_sub (hk.fourier_smul _) (hgi.fourier_smul _)]
    rw [he]
    apply le_trans (norm_integral_le_of_norm_le (hk.sub hgi).norm ?_) hg
    apply ae_of_all
    intro x
    simp only [norm_smul, fourier_apply, Circle.norm_coe, one_mul, Pi.sub_apply, le_refl]
  calc
    dist (fourierCoeff k (frequency j)) 0 = ‖fourierCoeff k (frequency j)‖ := dist_zero_right _
    _ ≤ ‖fourierCoeff k (frequency j) - fourierCoeff g (frequency j)‖ +
        ‖fourierCoeff g (frequency j)‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (fourierCoeff k (frequency j) - fourierCoeff g (frequency j))
        (fourierCoeff g (frequency j))
    _ ≤ ε / 2 + ‖fourierCoeff g (frequency j)‖ := add_le_add hb le_rfl
    _ < ε := by have hn := hN j hj; rw [dist_zero_right] at hn; linarith

/-- Finite spectral truncation, expressed as a sum of rank-one maps. -/
def finiteDiagonal (a : DiagonalLpSpectrumSpec.Sequence ∞) (N : ℕ) :
    DiagonalLpSpectrumSpec.Sequence 2 →L[ℂ] DiagonalLpSpectrumSpec.Sequence 2 :=
  ∑ j ∈ Finset.range N, (a j) •
    ((lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 j).comp
      (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 j))

lemma finiteDiagonal_apply (a : DiagonalLpSpectrumSpec.Sequence ∞) (N : ℕ)
    (x : DiagonalLpSpectrumSpec.Sequence 2) (j : ℕ) :
    finiteDiagonal a N x j = if j < N then a j * x j else 0 := by
  classical
  simp only [finiteDiagonal, sum_apply, lp.coeFn_sum,
    Finset.sum_apply, smul_apply, lp.coeFn_smul, Pi.smul_apply,
    ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply]
  change (∑ i ∈ Finset.range N, a i * (lp.single (E := fun _ : ℕ => ℂ) 2 i (x i)) j) = _
  simp only [lp.single_apply, Pi.single_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range]

lemma finiteDiagonal_compact (a : DiagonalLpSpectrumSpec.Sequence ∞) (N : ℕ) :
    IsCompactOperator (finiteDiagonal a N) := by
  change finiteDiagonal a N ∈ compactOperator (RingHom.id ℂ)
    (DiagonalLpSpectrumSpec.Sequence 2) (DiagonalLpSpectrumSpec.Sequence 2)
  apply Submodule.sum_mem
  intro j hj
  change IsCompactOperator ((a j) •
    ((lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 j).comp
      (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 j)))
  exact ((isCompactOperator_of_locallyCompactSpace_dom
    (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 j)).clm_comp
      (lp.singleContinuousLinearMap ℂ (fun _ : ℕ => ℂ) 2 j)).smul (a j)

lemma diagonal_compact_of_tendsto_zero (a : DiagonalLpSpectrumSpec.Sequence ∞)
    (ha : Filter.Tendsto (fun j => a j) Filter.atTop (𝓝 0)) :
    IsCompactOperator (diagonalLp 2 a) := by
  have hc : IsClosed {D : DiagonalLpSpectrumSpec.Sequence 2 →L[ℂ]
      DiagonalLpSpectrumSpec.Sequence 2 | IsCompactOperator D} :=
    isClosed_setOfPred_isCompactOperator
  apply hc.closure_subset
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp ha (ε / 2) (half_pos hε)
  refine ⟨finiteDiagonal a N, finiteDiagonal_compact a N, ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt ?_ (half_lt_self hε)
  apply ContinuousLinearMap.opNorm_le_bound _ (half_pos hε).le
  intro x
  calc
    ‖(diagonalLp 2 a - finiteDiagonal a N) x‖ ≤ ‖(ε / 2) • x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro j
      change ‖a j * x j - finiteDiagonal a N x j‖ ≤ ‖(ε / 2) • x j‖
      rw [finiteDiagonal_apply]
      by_cases hj : j < N
      · simp only [ite_eq_left hj, sub_self, norm_zero]
        exact norm_nonneg _
      · rw [ite_eq_right hj, sub_zero, norm_mul, norm_smul, Real.norm_eq_abs,
          abs_of_pos (half_pos hε)]
        exact mul_le_mul_of_nonneg_right
          (by have hn := hN j (Nat.le_of_not_gt hj); simpa only [dist_zero_right] using hn.le)
          (norm_nonneg _)
    _ = ε / 2 * ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hε)]

theorem compactness : Compactness := by
  intro T hT k
  have hd := diagonal_compact_of_tendsto_zero (coefficients k) (coefficients_tendsto_zero k)
  exact (hd.comp_clm (enumeratedBasis T).repr.toLinearIsometry.toContinuousLinearMap).clm_comp
    (enumeratedBasis T).repr.symm.toLinearIsometry.toContinuousLinearMap

end ExpandedFA.Models.PeriodicConvolution
