import MathGenome.Internal.FourierSobolev.P102.Periodic.Foundation
import MathGenome.Internal.FourierSobolev.Specs.P102.Periodic.HilbertBasis

noncomputable section
open MeasureTheory Filter Set
open scoped Topology Real ENNReal ComplexConjugate
namespace P102.Periodic
namespace FourierHilbert

set_option linter.unusedSectionVars false
variable (T : ℝ) [Fact (0 < T)]

theorem expected_coefficient_eq (f : Circle T → ℂ) (k : ℤ) :
    Expected.coefficient T f k = fourierCoeff f k := coefficient_eq_fourierCoeff T f k

theorem complex_fourier_basis : Specs.ComplexBasis := by
  intro T _
  refine ⟨fourierBasis, ?_, ?_⟩
  · intro k
    rw [coe_fourierBasis]
  · intro f k
    rw [fourierBasis_repr, expected_coefficient_eq]

theorem interval_coefficient : Specs.IntervalCoefficient := by
  intro T _ f k a
  exact coefficient_interval T f k a

theorem complex_expansion : Specs.ComplexExpansion := by
  intro T _ f
  constructor
  · simpa only [expected_coefficient_eq] using hasSum_fourier_series_L2 f
  · have h := lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) (fourierBasis.repr f)
    simpa [fourierBasis_repr, ← expected_coefficient_eq] using h

theorem frequencies_tendsto : Tendsto frequencies atTop atTop := by
  apply Monotone.tendsto_atTop_finset
  · intro m n h k hk
    simp only [frequencies, Finset.mem_Icc] at hk ⊢
    constructor <;> omega
  · intro k
    refine ⟨k.natAbs, ?_⟩
    simp only [frequencies, Finset.mem_Icc]
    have h := Int.le_natAbs (a := k)
    have h' := Int.le_natAbs (a := -k)
    simp only [Int.natAbs_neg] at h'
    constructor <;> omega

theorem partial_sum_convergence : Specs.PartialSumConvergence := by
  intro T _ f
  constructor
  · intro N
    change (∑ k ∈ frequencies N, coefficient T f k • fourierLp 2 k : L2C T) =ᵐ[haar T] partialSum T N f
    have hs := Lp.coeFn_fun_finsetSum (frequencies N) (fun k : ℤ => coefficient T f k • (fourierLp 2 k : L2C T))
    filter_upwards [hs, ae_all_iff.mpr (fun k : ℤ =>
      (Lp.coeFn_smul (coefficient T f k) (fourierLp 2 k : L2C T)).trans
        ((coeFn_fourierLp 2 k).const_smul (coefficient T f k)))] with x hx hxk
    simpa only [partialSum, Pi.smul_apply, smul_eq_mul, hxk] using hx
  · exact ((complex_expansion T f).1).comp frequencies_tendsto

theorem real_symmetry : Specs.RealSymmetry := by
  intro T _ f k
  exact coefficient_conj_of_real T (fun x => (f x : ℂ)) (by intro x; rfl) k


/-- Computing real inner products using the real and imaginary Fourier coefficients. -/
theorem real_inner_integral (f : L2R T) (i : RealIndex) :
    inner ℝ (realVector T i) f = ∫ x, f x * realWave T i x ∂haar T := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (haar T) (𝕜 := ℝ) (p := 2) (realWave T i)] with x hx
  change (realVector T i) x = _ at hx
  rw [hx]
  simp [RCLike.inner_apply]

theorem real_coefficient_parts (f : L2R T) (k : ℤ) :
    (coefficient T (fun x => (f x : ℂ)) k).re =
      ∫ x, f x * (mode T k x).re ∂haar T ∧
    (coefficient T (fun x => (f x : ℂ)) k).im =
      -(∫ x, f x * (mode T k x).im ∂haar T) := by
  have hf : Integrable (fun x => (f x : ℂ)) (haar T) :=
    Complex.ofRealCLM.integrable_comp ((Lp.memLp f).integrable (by norm_num))
  have hi := hf.fourier_smul (-k)
  have h : Integrable (fun x => (f x : ℂ) * conj (mode T k x)) (haar T) := by
    simpa only [mode, fourier_neg, smul_eq_mul, mul_comm] using hi
  constructor
  · simpa [coefficient] using (integral_re h).symm
  · simpa [coefficient, integral_neg, mul_neg] using (integral_im h).symm

theorem real_inner_coefficient (f : L2R T) (i : RealIndex) :
    inner ℝ (realVector T i) f = realCoeff T f i := by
  rw [real_inner_integral]
  cases i with
  | none =>
    change (∫ x, f x * 1 ∂haar T) = (coefficient T (fun x => (f x : ℂ)) 0).re
    rw [(real_coefficient_parts T f 0).1]
    simp [mode]
  | some p =>
    rcases p with ⟨n, b⟩
    cases b
    · change (∫ x, f x * (Real.sqrt 2 * (mode T (n+1) x).re) ∂haar T) =
        Real.sqrt 2 * (coefficient T (fun x => (f x : ℂ)) (n+1)).re
      rw [(real_coefficient_parts T f (n+1)).1]
      simp_rw [← mul_assoc, mul_comm (f _) (Real.sqrt 2), mul_assoc]
      exact integral_const_mul _ _
    · change (∫ x, f x * (Real.sqrt 2 * (mode T (n+1) x).im) ∂haar T) =
        -Real.sqrt 2 * (coefficient T (fun x => (f x : ℂ)) (n+1)).im
      rw [(real_coefficient_parts T f (n+1)).2]
      simp_rw [← mul_assoc, mul_comm (f _) (Real.sqrt 2), mul_assoc]
      rw [integral_const_mul]
      ring

/-- The real waves as pairs of complex characters. -/
def pairedWave (i : RealIndex) : C(Circle T, ℂ) :=
  match i with
  | none => mode T 0
  | some (n, false) => (Real.sqrt 2 / 2 : ℂ) • (mode T (n+1) + mode T (-(n+1)))
  | some (n, true) => (-(Real.sqrt 2 : ℂ) * Complex.I / 2) •
      (mode T (n+1) - mode T (-(n+1)))

theorem pairedWave_eq (i : RealIndex) (x : Circle T) :
    pairedWave T i x = (realWave T i x : ℂ) := by
  cases i with
  | none => simp [pairedWave, realWave, mode]
  | some p =>
    rcases p with ⟨n, b⟩
    cases b <;>
      simp only [pairedWave, realWave, ContinuousMap.smul_apply, ContinuousMap.add_apply,
        ContinuousMap.sub_apply, smul_eq_mul, mode, fourier_neg] <;>
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem coefficient_realVector (i : RealIndex) (k : ℤ) :
    coefficient T (fun x => ((realVector T i) x : ℂ)) k =
      fourierCoeff (pairedWave T i) k := by
  rw [← coefficient_eq_fourierCoeff]
  apply coefficient_congr
  filter_upwards [ContinuousMap.coeFn_toLp (haar T) (𝕜 := ℝ) (p := 2) (realWave T i)] with x hx
  change (realVector T i) x = _ at hx
  rw [hx, pairedWave_eq]

theorem pairedWave_coefficient_none (k : ℤ) :
    fourierCoeff (pairedWave T none) k = if k = 0 then 1 else 0 := by
  simp [pairedWave, mode, fourierCoeff_fourier, Pi.single_apply]

theorem pairedWave_coefficient_cos (n : ℕ) (k : ℤ) :
    fourierCoeff (pairedWave T (some (n, false))) k =
      (Real.sqrt 2 / 2 : ℂ) * ((if k = (n+1 : ℤ) then 1 else 0) +
        (if k = -(n+1 : ℤ) then 1 else 0)) := by
  have hi (j : ℤ) : Integrable (mode T j) (haar T) := (mode T j).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  change fourierCoeff ((Real.sqrt 2 / 2 : ℂ) • ((mode T (n+1) : Circle T → ℂ) + (mode T (-(n+1)) : Circle T → ℂ))) k = _
  rw [fourierCoeff.const_smul, fourierCoeff.add (hi _) (hi _)]
  simp [mode, fourierCoeff_fourier, Pi.single_apply]

theorem pairedWave_coefficient_sin (n : ℕ) (k : ℤ) :
    fourierCoeff (pairedWave T (some (n, true))) k =
      (-(Real.sqrt 2 : ℂ) * Complex.I / 2) * ((if k = (n+1 : ℤ) then 1 else 0) -
        (if k = -(n+1 : ℤ) then 1 else 0)) := by
  have hi (j : ℤ) : Integrable (mode T j) (haar T) := (mode T j).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  change fourierCoeff ((-(Real.sqrt 2 : ℂ) * Complex.I / 2) •
    ((mode T (n+1) : Circle T → ℂ) - (mode T (-(n+1)) : Circle T → ℂ))) k = _
  have hsub : fourierCoeff ((mode T (n+1) : Circle T → ℂ) - (mode T (-(n+1)) : Circle T → ℂ)) =
      fourierCoeff (mode T (n+1)) - fourierCoeff (mode T (-(n+1))) := by
    ext j
    simp only [fourierCoeff, Pi.sub_apply, smul_sub]
    exact integral_sub ((hi _).fourier_smul _) ((hi _).fourier_smul _)
  rw [fourierCoeff.const_smul, hsub]
  simp [mode, fourierCoeff_fourier, Pi.single_apply]


theorem expected_coefficient_realVector (i : RealIndex) (k : ℤ) :
    Expected.coefficient T (fun x => ((realVector T i) x : ℂ)) k =
      fourierCoeff (pairedWave T i) k := coefficient_realVector T i k

theorem realVector_orthonormal : Orthonormal ℝ (realVector T) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [real_inner_coefficient]
  have hp (n : ℕ) : (n : ℤ) + 1 ≠ 0 := by omega
  have hn (n : ℕ) : (0 : ℤ) ≠ -1 + -(n : ℤ) := by omega
  have hop (n m : ℕ) : (n : ℤ) + 1 ≠ -((m : ℤ)+1) := by omega
  rcases i with _ | ⟨n, b⟩ <;> rcases j with _ | ⟨m, c⟩
  · simp [realCoeff, expected_coefficient_realVector, pairedWave_coefficient_none]
  · cases c <;> simp [realCoeff, expected_coefficient_realVector,
      pairedWave_coefficient_cos, pairedWave_coefficient_sin, Ne.symm (hp m), hn m]
  · cases b <;> simp [realCoeff, expected_coefficient_realVector,
      pairedWave_coefficient_none, hp n]
  · have he : (n : ℤ) + 1 = (m : ℤ) + 1 ↔ n = m := by omega
    cases b <;> cases c <;>
      simp [realCoeff, expected_coefficient_realVector, pairedWave_coefficient_cos,
        pairedWave_coefficient_sin, he] <;>
      split_ifs <;> simp_all <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]


/-- The real coefficients determine the L² class. This uses the already complete
complex Fourier basis, rather than a pointwise convergence assertion. -/
theorem eq_zero_of_realCoeff (f : L2R T) (h : ∀ i, realCoeff T f i = 0) : f = 0 := by
  let c (k : ℤ) := coefficient T (fun x => (f x : ℂ)) k
  have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hpos (k : ℤ) (hk : 0 < k) : c k = 0 := by
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) + 1 := ⟨(k-1).toNat, by omega⟩
    have hre := h (some (n, false))
    have him := h (some (n, true))
    change Real.sqrt 2 * (c (n+1)).re = 0 at hre
    change -Real.sqrt 2 * (c (n+1)).im = 0 at him
    apply Complex.ext
    · exact (mul_eq_zero.mp hre).resolve_left hsqrt
    · exact (mul_eq_zero.mp him).resolve_left (neg_ne_zero.mpr hsqrt)
  have hzero : c 0 = 0 := by
    have hre := h none
    change (c 0).re = 0 at hre
    have hc := coefficient_conj_of_real T (fun x => (f x : ℂ)) (by intro x; rfl) 0
    change c (-0) = conj (c 0) at hc
    have him := congrArg Complex.im hc
    simp only [neg_zero, Complex.conj_im] at him
    apply Complex.ext
    · exact hre
    · change (c 0).im = 0
      linarith
  have hall (k : ℤ) : c k = 0 := by
    rcases lt_trichotomy k 0 with hk | hk | hk
    · have hc := coefficient_conj_of_real T (fun x => (f x : ℂ)) (by intro x; rfl) (-k)
      change c (- -k) = conj (c (-k)) at hc
      simpa only [neg_neg, hpos (-k) (by omega), map_zero] using hc
    · simpa only [hk] using hzero
    · exact hpos k hk
  let g : L2C T := Complex.ofRealCLM.compLp f
  have hgc (k : ℤ) : coefficient T g k = c k :=
    coefficient_congr T g _ (Complex.ofRealCLM.coeFn_compLp f) k
  have hg : g = 0 := by
    apply (fourierBasis (T := T)).repr.injective
    rw [map_zero]
    ext k
    rw [fourierBasis_repr, ← coefficient_eq_fourierCoeff, hgc, hall]
    rfl
  have hgae : (g : Circle T → ℂ) =ᵐ[haar T] 0 := by
    rw [hg]
    exact Lp.coeFn_zero ℂ 2 (haar T)
  apply Lp.ext
  filter_upwards [Complex.ofRealCLM.coeFn_compLp f, hgae, Lp.coeFn_zero ℝ 2 (haar T)] with x hx hz h0
  change g x = (f x : ℂ) at hx
  rw [h0]
  exact Complex.ofReal_injective (hx.symm.trans hz)

theorem realVector_orthogonal_eq_bot :
    (Submodule.span ℝ (Set.range (realVector T)))ᗮ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  apply eq_zero_of_realCoeff T f
  intro i
  rw [← real_inner_coefficient]
  exact Submodule.inner_right_of_mem_orthogonal
    (Submodule.subset_span (Set.mem_range_self i)) hf

theorem real_fourier_basis : Specs.RealBasis := by
  intro T _
  let b : HilbertBasis RealIndex ℝ (L2R T) :=
    HilbertBasis.mkOfOrthogonalEqBot (realVector_orthonormal T) (realVector_orthogonal_eq_bot T)
  have hb : (b : RealIndex → L2R T) = realVector T := HilbertBasis.coe_mkOfOrthogonalEqBot _ _
  have hr (f : L2R T) (i : RealIndex) : b.repr f i = realCoeff T f i := by
    rw [b.repr_apply_apply, hb, real_inner_coefficient]
  refine ⟨b, congrFun hb, hr, ?_, ?_⟩
  · intro f
    simpa only [hr, hb] using b.hasSum_repr f
  · intro f
    have hs := lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) (b.repr f)
    simpa [hr, Real.norm_eq_abs, sq_abs] using hs

theorem real_wave_formula : Specs.RealWaveFormula := by
  intro T _
  refine ⟨fun x => rfl, ?_⟩
  intro n t
  have he : 2 * (Real.pi : ℂ) * Complex.I * ((n : ℂ)+1) * t / T =
      ((2 * Real.pi * ((n : ℝ)+1) * t / T : ℝ) : ℂ) * Complex.I := by push_cast; ring
  constructor <;> change Real.sqrt 2 * _ = _ <;>
    rw [mode_formula] <;> simp only [Int.cast_add, Int.cast_natCast, Int.cast_one] <;>
    rw [he] <;> simp [Complex.exp_re, Complex.exp_im]

end FourierHilbert
end P102.Periodic
