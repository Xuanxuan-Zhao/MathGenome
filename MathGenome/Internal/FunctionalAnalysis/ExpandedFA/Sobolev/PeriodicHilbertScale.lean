import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.PeriodicHilbertScale
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.TorusFourierBasis
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open MeasureTheory Filter
open scoped Real ENNReal Topology ComplexConjugate
namespace ExpandedFA.Sobolev.PeriodicHilbertScale

/-- The canonical space, with the coefficient interpretation fixed in the Specs. -/
def sobolevSpace : Spec.SpaceType := Hs

theorem weight_add (s t : ℝ) (n : ℤ) : weight (s + t) n = weight s n * weight t n := by
  simp only [weight, add_div, Real.rpow_add (frequencyWeight_pos n)]

@[simp] theorem weight_zero (n : ℤ) : weight 0 n = 1 := by simp [weight]
@[simp] theorem frequencyWeight_neg (n : ℤ) : frequencyWeight (-n) = frequencyWeight n := by
  simp [frequencyWeight]
@[simp] theorem weight_neg_index (s : ℝ) (n : ℤ) : weight s (-n) = weight s n := by
  simp [weight]

theorem weight_neg_order (s : ℝ) (n : ℤ) : weight (-s) n = (weight s n)⁻¹ := by
  simp only [weight, neg_div, Real.rpow_neg (frequencyWeight_pos n).le]

theorem weight_sq (s : ℝ) (n : ℤ) : weight s n ^ 2 = frequencyWeight n ^ s := by
  rw [← Real.rpow_two, weight, ← Real.rpow_mul (frequencyWeight_pos n).le]
  congr 1; ring

theorem weighted_norm_term (s : ℝ) (a : ℤ → ℂ) (n : ℤ) :
    ‖(weight s n : ℂ) * a n‖ ^ 2 = frequencyWeight n ^ s * ‖a n‖ ^ 2 := by
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (weight_pos s n), weight_sq]

theorem identification : Spec.Identification := by
  constructor
  · intro s a
    constructor
    · rintro ⟨u, rfl⟩
      have h := (lp.memℓp (normalize s u)).summable (by simp)
      change Summable (fun n => ‖(weight s n : ℂ) * u n‖ ^ (2 : ℝ≥0∞).toReal) at h
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, weighted_norm_term] using h
    · intro ha
      refine ⟨⟨a, ?_⟩, rfl⟩
      change Memℓp (fun n => (weight s n : ℂ) * a n) 2
      apply memℓp_gen
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, weighted_norm_term] using ha
  · intro s u
    have h := lp.hasSum_norm (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (normalize s u)
    change HasSum (fun n => frequencyWeight n ^ s * ‖u n‖ ^ 2) (‖normalize s u‖ ^ 2)
    convert h using 1 <;> simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    funext n
    exact (weighted_norm_term s u n).symm

theorem zero_fourier : Spec.ZeroFourier := by
  obtain ⟨U, hU⟩ := ExpandedFA.Fourier.TorusFourierBasis.coefficient_unitary 1
  refine ⟨U.trans (normalizedEquiv 0).symm, ?_⟩
  intro f n
  change U f n / (weight 0 n : ℂ) = _
  simpa using hU f n

abbrev FourierL2 := lp (fun _ : ℤ => ℂ) 2

/-- A bounded diagonal multiplier on square-summable Fourier coordinates. -/
def diagonal (m : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C) (hm : ∀ n, ‖m n‖ ≤ C) :
    FourierL2 →L[ℂ] FourierL2 := by
  have hmem (a : FourierL2) : Memℓp (fun n => m n * a n) 2 := by
    apply (lp.memℓp ((C : ℂ) • a)).mono'
    intro n
    simp only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hC, norm_mul]
    exact mul_le_mul_of_nonneg_right (hm n) (norm_nonneg _)
  let L : FourierL2 →ₗ[ℂ] FourierL2 :=
    { toFun := fun a => ⟨fun n => m n * a n, hmem a⟩
      map_add' := by intro a b; apply lp.ext; funext n; exact mul_add _ _ _
      map_smul' := by intro c a; apply lp.ext; funext n; exact mul_left_comm _ _ _ }
  apply L.mkContinuous C
  intro a
  calc
    ‖L a‖ ≤ ‖(C : ℂ) • a‖ := lp.norm_mono (by simp) fun n => by
      change ‖m n * a n‖ ≤ ‖(C : ℂ) * a n‖
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hm n) (norm_nonneg _)
    _ = C * ‖a‖ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]

@[simp] theorem diagonal_apply (m : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ n, ‖m n‖ ≤ C) (a : FourierL2) (n : ℤ) :
    diagonal m C hC hm a n = m n * a n := rfl

theorem diagonal_bound (m : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ n, ‖m n‖ ≤ C) (a : FourierL2) :
    ‖diagonal m C hC hm a‖ ≤ C * ‖a‖ := by
  calc
    _ ≤ ‖(C : ℂ) • a‖ := lp.norm_mono (by simp) fun n => by
      simp only [diagonal_apply, lp.coeFn_smul, Pi.smul_apply, norm_smul,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hm n) (norm_nonneg _)
    _ = _ := by rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]

/-- Transport a Fourier-coordinate multiplier between two Sobolev orders. -/
def transport (s t : ℝ) (A : FourierL2 →L[ℂ] FourierL2) : Hs t →L[ℂ] Hs s :=
  (normalizedEquiv s).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (A.comp (normalizedEquiv t).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem transport_apply (s t : ℝ) (A : FourierL2 →L[ℂ] FourierL2)
    (u : Hs t) (n : ℤ) : transport s t A u n = A (normalize t u) n / (weight s n : ℂ) := rfl

theorem transport_bound (s t : ℝ) (A : FourierL2 →L[ℂ] FourierL2)
    (C : ℝ) (hA : ∀ a, ‖A a‖ ≤ C * ‖a‖) (u : Hs t) :
    ‖transport s t A u‖ ≤ C * ‖u‖ := by
  change ‖(normalizedEquiv s).symm (A (normalizedEquiv t u))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  simpa only [LinearIsometryEquiv.norm_map] using hA (normalizedEquiv t u)

def derivativeSymbol (n : ℤ) : ℂ := (2 * π * Complex.I * n : ℂ) / (weight 1 n : ℂ)

theorem derivativeSymbol_bound (n : ℤ) : ‖derivativeSymbol n‖ ≤ 1 := by
  have hw := weight_sq 1 n
  simp only [Real.rpow_one] at hw
  have hd := ExpandedFA.Fourier.TorusFourierBasis.sobolev_weight n
  change 1 + ‖(2 * π * Complex.I * n : ℂ)‖ ^ 2 = frequencyWeight n at hd
  rw [derivativeSymbol, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (weight_pos 1 n)]
  apply (div_le_one (weight_pos 1 n)).mpr
  have := norm_nonneg (2 * π * Complex.I * n : ℂ)
  have := weight_pos 1 n
  nlinarith

def derivativeMap (s : ℝ) : Hs s →L[ℂ] Hs (s - 1) :=
  transport (s - 1) s (diagonal derivativeSymbol 1 zero_le_one derivativeSymbol_bound)

theorem derivativeMap_apply (s : ℝ) (u : Hs s) (n : ℤ) :
    derivativeMap s u n = (2 * π * Complex.I * n : ℂ) * u n := by
  have hw : (weight s n : ℂ) = (weight 1 n : ℂ) * (weight (s - 1) n : ℂ) := by
    have h := weight_add 1 (s - 1) n
    rw [show 1 + (s - 1) = s by ring] at h
    exact_mod_cast h
  have h1 : (weight 1 n : ℂ) ≠ 0 := by exact_mod_cast (weight_pos 1 n).ne'
  have hs : (weight (s - 1) n : ℂ) ≠ 0 := by
    exact_mod_cast (weight_pos (s - 1) n).ne'
  change ((2 * π * Complex.I * n : ℂ) / (weight 1 n : ℂ)) *
    ((weight s n : ℂ) * u n) / (weight (s - 1) n : ℂ) = _
  rw [hw]; field_simp

theorem derivativeMap_bound (s : ℝ) (u : Hs s) : ‖derivativeMap s u‖ ≤ ‖u‖ := by
  simpa only [derivativeMap, one_mul] using transport_bound (s - 1) s _ 1
    (diagonal_bound derivativeSymbol 1 zero_le_one derivativeSymbol_bound) u

theorem derivative : Spec.Derivative := fun s =>
  ⟨derivativeMap s, derivativeMap_apply s, derivativeMap_bound s⟩

theorem frequencyWeight_one_le (n : ℤ) : 1 ≤ frequencyWeight n := by
  dsimp [frequencyWeight]; exact le_add_of_nonneg_right (by positivity)

def embeddingSymbol (ε : ℝ) (n : ℤ) : ℂ := (weight (-ε) n : ℂ)

theorem embeddingSymbol_bound (ε : ℝ) (hε : 0 ≤ ε) (n : ℤ) :
    ‖embeddingSymbol ε n‖ ≤ 1 := by
  rw [embeddingSymbol, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (weight_pos _ _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (frequencyWeight_one_le n) (by linarith)

def inclusion (s ε : ℝ) (hε : 0 ≤ ε) : Hs (s + ε) →L[ℂ] Hs s :=
  transport s (s + ε) (diagonal (embeddingSymbol ε) 1 zero_le_one
    (embeddingSymbol_bound ε hε))

theorem inclusion_apply (s ε : ℝ) (hε : 0 ≤ ε) (u : Hs (s + ε)) (n : ℤ) :
    inclusion s ε hε u n = u n := by
  have hs : (weight s n : ℂ) ≠ 0 := by exact_mod_cast (weight_pos s n).ne'
  have he : (weight ε n : ℂ) ≠ 0 := by exact_mod_cast (weight_pos ε n).ne'
  change (weight (-ε) n : ℂ) * ((weight (s + ε) n : ℂ) * u n) /
    (weight s n : ℂ) = _
  rw [weight_add, weight_neg_order]
  push_cast
  field_simp

def fourierProjection (N : ℕ) : FourierL2 →L[ℂ] FourierL2 :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).smulRight (lp.single 2 n 1)

theorem mem_frequencyCutoff (N : ℕ) (n : ℤ) :
    n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) ↔ n.natAbs ≤ N := by
  simp only [Finset.mem_Icc]
  omega

theorem fourierProjection_apply (N : ℕ) (a : FourierL2) (n : ℤ) :
    fourierProjection N a n = if n.natAbs ≤ N then a n else 0 := by
  simp only [fourierProjection, sum_apply,
    ContinuousLinearMap.smulRight_apply, lp.coeFn_sum, Finset.sum_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.single_apply,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    mem_frequencyCutoff]
  rfl

theorem fourierProjection_compact (N : ℕ) : IsCompactOperator (fourierProjection N) := by
  change fourierProjection N ∈ compactOperator (RingHom.id ℂ) FourierL2 FourierL2
  apply Submodule.sum_mem
  intro n hn
  exact (isCompactOperator_of_locallyCompactSpace_dom
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n)).clm_comp
      ((ContinuousLinearMap.id ℂ ℂ).smulRight (lp.single 2 n 1))

/-- Reflection of the integer frequency, preserving the ℓ² norm. -/
def frequencyReflection : FourierL2 ≃ₗᵢ[ℂ] FourierL2 := by
  have hm (a : FourierL2) : Memℓp (fun n : ℤ => a (-n)) 2 := by
    apply memℓp_gen
    exact (Equiv.neg ℤ).summable_iff.mpr ((lp.memℓp a).summable (by simp))
  let R : FourierL2 ≃ₗ[ℂ] FourierL2 :=
    { toFun := fun a => ⟨fun n => a (-n), hm a⟩
      invFun := fun a => ⟨fun n => a (-n), hm a⟩
      left_inv := by intro a; apply lp.ext; funext n; exact congrArg a (neg_neg n)
      right_inv := by intro a; apply lp.ext; funext n; exact congrArg a (neg_neg n)
      map_add' := by intro a b; apply lp.ext; rfl
      map_smul' := by intro c a; apply lp.ext; rfl }
  refine ⟨R, fun a => ?_⟩
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have h := (Equiv.neg ℤ).hasSum_iff.mpr
    (lp.hasSum_norm (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) a)
  have h' := lp.hasSum_norm (by simp : (0 : ℝ) < (2 : ℝ≥0∞).toReal) (R a)
  change HasSum (fun n => ‖a (-n)‖ ^ (2 : ℝ≥0∞).toReal) (‖a‖ ^ (2 : ℝ≥0∞).toReal) at h
  change HasSum (fun n => ‖a (-n)‖ ^ (2 : ℝ≥0∞).toReal) (‖R a‖ ^ (2 : ℝ≥0∞).toReal) at h'
  exact HasSum.unique (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h')
    (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h)

@[simp] theorem frequencyReflection_apply (a : FourierL2) (n : ℤ) :
    frequencyReflection a n = a (-n) := rfl

/-- Conjugating the Riesz representing vector produces the scalar-linear dual;
frequency reflection gives the bilinear distribution pairing on the circle. -/
def dualityEquiv (s : ℝ) : Hs (-s) ≃ₗᵢ[ℂ] (Hs s →L[ℂ] ℂ) :=
  (((normalizedEquiv (-s)).trans frequencyReflection).trans (starₗᵢ ℂ)).trans
    ((normalizedEquiv s).symm.trans (InnerProductSpace.toDual ℂ (Hs s)))

theorem duality_term (s : ℝ) (v : Hs (-s)) (u : Hs s) (n : ℤ) :
    inner ℂ (star (frequencyReflection (normalize (-s) v)) n) (normalize s u n) =
      u n * v (-n) := by
  have hs : (weight s n : ℂ) ≠ 0 := by exact_mod_cast (weight_pos s n).ne'
  simp only [lp.star_apply, frequencyReflection_apply, RCLike.inner_apply',
    starRingEnd_apply, star_star]
  change ((weight (-s) (-n) : ℂ) * v (-n)) * ((weight s n : ℂ) * u n) = _
  rw [weight_neg_index, weight_neg_order, Complex.ofReal_inv]
  field_simp

theorem duality : Spec.Duality := by
  intro s
  refine ⟨dualityEquiv s, ?_⟩
  intro v u
  have ht := duality_term s v u
  have hi := lp.summable_inner (𝕜 := ℂ)
    (star (frequencyReflection (normalize (-s) v))) (normalize s u)
  constructor
  · apply Summable.norm
    simpa only [ht] using hi
  · change inner ℂ ((normalizedEquiv s).symm
      (star (frequencyReflection (normalize (-s) v)))) u = _
    change inner ℂ (normalize s ((normalizedEquiv s).symm
      (star (frequencyReflection (normalize (-s) v))))) (normalize s u) = _
    rw [show normalize s ((normalizedEquiv s).symm
      (star (frequencyReflection (normalize (-s) v)))) =
      star (frequencyReflection (normalize (-s) v)) from
        (normalizedEquiv s).apply_symm_apply _]
    rw [lp.inner_eq_tsum]
    exact tsum_congr ht

def tailBound (ε : ℝ) (N : ℕ) : ℝ :=
  (1 + 4 * π ^ 2 * (N : ℝ) ^ 2) ^ (-ε / 2)

theorem tailBound_pos (ε : ℝ) (N : ℕ) : 0 < tailBound ε N := by
  apply Real.rpow_pos_of_pos
  positivity

theorem embeddingSymbol_tail (ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) (n : ℤ)
    (hn : ¬ n.natAbs ≤ N) : ‖embeddingSymbol ε n‖ ≤ tailBound ε N := by
  have hN : N ≤ n.natAbs := (Nat.lt_of_not_ge hn).le
  have hcast : (N : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast hN
  have heq : (n.natAbs : ℝ) = |(n : ℝ)| := by
    calc
      (n.natAbs : ℝ) = ((n.natAbs : ℤ) : ℝ) := by simp
      _ = ((|n| : ℤ) : ℝ) := by rw [Int.natCast_natAbs]
      _ = |(n : ℝ)| := by simp
  have hsq : (N : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
    rw [heq] at hcast
    nlinarith [sq_abs (n : ℝ), abs_nonneg (n : ℝ)]
  have hbase : 1 + 4 * π ^ 2 * (N : ℝ) ^ 2 ≤ frequencyWeight n := by
    dsimp [frequencyWeight]
    have hm : 4 * π ^ 2 * (N : ℝ) ^ 2 ≤ 4 * π ^ 2 * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    linarith
  rw [embeddingSymbol, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (weight_pos _ _)]
  exact Real.rpow_le_rpow_of_nonpos (by positivity) hbase (by linarith)

def truncationMap (s ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) : Hs (s + ε) →L[ℂ] Hs s :=
  transport s (s + ε) ((fourierProjection N).comp
    (diagonal (embeddingSymbol ε) 1 zero_le_one (embeddingSymbol_bound ε hε)))

theorem truncationMap_apply (s ε : ℝ) (hε : 0 ≤ ε) (N : ℕ)
    (u : Hs (s + ε)) (n : ℤ) :
    truncationMap s ε hε N u n = if n.natAbs ≤ N then u n else 0 := by
  rw [truncationMap, transport_apply, ContinuousLinearMap.comp_apply, fourierProjection_apply]
  split_ifs with hn
  · exact inclusion_apply s ε hε u n
  · simp

theorem truncationMap_compact (s ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) :
    IsCompactOperator (truncationMap s ε hε N) :=
  (((fourierProjection_compact N).comp_clm
    (diagonal (embeddingSymbol ε) 1 zero_le_one (embeddingSymbol_bound ε hε))).comp_clm
      (normalizedEquiv (s + ε)).toContinuousLinearEquiv.toContinuousLinearMap).clm_comp
        (normalizedEquiv s).symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem truncation_error (s ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) (u : Hs (s + ε)) :
    ‖inclusion s ε hε u - truncationMap s ε hε N u‖ ≤ tailBound ε N * ‖u‖ := by
  let A := diagonal (embeddingSymbol ε) 1 zero_le_one (embeddingSymbol_bound ε hε)
  let a := normalize (s + ε) u
  change ‖(normalizedEquiv s).symm (A a) -
    (normalizedEquiv s).symm (fourierProjection N (A a))‖ ≤ _
  rw [← map_sub, LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖(tailBound ε N : ℂ) • a‖ := lp.norm_mono (by simp) fun n => by
      simp only [lp.coeFn_sub, Pi.sub_apply, fourierProjection_apply,
        lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (tailBound_pos ε N)]
      split_ifs with hn
      · simp only [sub_self, norm_zero]
        exact mul_nonneg (tailBound_pos ε N).le (norm_nonneg _)
      · simp only [sub_zero, A, diagonal_apply, norm_mul]
        exact mul_le_mul_of_nonneg_right (embeddingSymbol_tail ε hε N n hn) (norm_nonneg _)
    _ = tailBound ε N * ‖u‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (tailBound_pos ε N)]
      rfl

theorem tailBound_tendsto (ε : ℝ) (hε : 0 < ε) :
    Tendsto (tailBound ε) atTop (𝓝 0) := by
  have hN2 : Tendsto (fun N : ℕ => (N : ℝ) ^ 2) atTop atTop := by
    simpa only [Function.comp_def, Real.rpow_two] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hb : Tendsto (fun N : ℕ => 1 + 4 * π ^ 2 * (N : ℝ) ^ 2) atTop atTop :=
    tendsto_const_nhds.add_atTop (hN2.const_mul_atTop (by positivity : 0 < 4 * π ^ 2))
  change Tendsto (fun N : ℕ => (1 + 4 * π ^ 2 * (N : ℝ) ^ 2) ^ (-ε / 2)) atTop (𝓝 0)
  simpa only [Function.comp_def, neg_div] using
    (tendsto_rpow_neg_atTop (by linarith : 0 < ε / 2)).comp hb

theorem truncation_tendsto (s ε : ℝ) (hε : 0 < ε) :
    Tendsto (truncationMap s ε hε.le) atTop (𝓝 (inclusion s ε hε.le)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun N => norm_nonneg _) _ (tailBound_tendsto ε hε)
  intro N
  apply (truncationMap s ε hε.le N - inclusion s ε hε.le).opNorm_le_bound
    (tailBound_pos ε N).le
  intro u
  change ‖truncationMap s ε hε.le N u - inclusion s ε hε.le u‖ ≤ _
  rw [norm_sub_rev]
  exact truncation_error s ε hε.le N u

lemma finiteDimensional_cutoff_range (s t : ℝ) (N : ℕ) (P : Hs t →L[ℂ] Hs s)
    (hP : ∀ u n, P u n = if n.natAbs ≤ N then u n else 0) :
    FiniteDimensional ℂ (LinearMap.range P.toLinearMap) := by
  let F : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let R : LinearMap.range P.toLinearMap →ₗ[ℂ] (↥F → ℂ) :=
    { toFun := fun u n => u.val n.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply FiniteDimensional.of_injective R
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  funext n
  by_cases hn : n.natAbs ≤ N
  · exact congrFun hab ⟨n, (mem_frequencyCutoff N n).2 hn⟩
  · obtain ⟨u, hu⟩ := a.property
    obtain ⟨v, hv⟩ := b.property
    change P u = a.val at hu
    change P v = b.val at hv
    rw [← hu, ← hv, hP, hP, ite_eq_right hn, ite_eq_right hn]

lemma truncationMap_finiteDimensional (s ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) :
    FiniteDimensional ℂ (LinearMap.range (truncationMap s ε hε N).toLinearMap) :=
  finiteDimensional_cutoff_range s (s + ε) N (truncationMap s ε hε N)
    (truncationMap_apply s ε hε N)


theorem compact_embedding : Spec.CompactEmbedding := by
  intro s ε hε
  refine ⟨inclusion s ε hε.le, inclusion_apply s ε hε.le, ?_, ?_,
    truncationMap s ε hε.le, truncationMap_apply s ε hε.le,
    truncationMap_finiteDimensional s ε hε.le,
    truncationMap_compact s ε hε.le, truncation_error s ε hε.le,
    truncation_tendsto s ε hε⟩
  · intro u v huv
    apply Subtype.ext
    funext n
    have h := congrArg (fun a : Hs s => a n) huv
    simpa only [inclusion_apply] using h
  · exact isCompactOperator_of_tendsto (truncation_tendsto s ε hε)
      (Filter.Eventually.of_forall (truncationMap_compact s ε hε.le))

theorem real_identification : Spec.RealIdentification := by
  constructor
  · intro s a
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨(identification.1 s _).mp ⟨u.val, rfl⟩, u.property⟩
    · rintro ⟨ha, hr⟩
      obtain ⟨u, hu⟩ := (identification.1 s a).mpr ha
      refine ⟨⟨u, ?_⟩, hu⟩
      intro n
      simpa only [← hu] using hr n
  · intro s u
    exact identification.2 s u.val

/-- Changing order while preserving normalized Fourier coordinates. This is
an isometry, and is used only for dual representation, not for inclusion. -/
def orderEquiv (s t : ℝ) : Hs s ≃ₗᵢ[ℂ] Hs t :=
  (normalizedEquiv s).trans (normalizedEquiv t).symm

theorem orderEquiv_real (s t : ℝ) (u : Hs s) (hu : u ∈ realSubmodule s) :
    orderEquiv s t u ∈ realSubmodule t := by
  intro n
  change (weight s (-n) : ℂ) * u (-n) / (weight t (-n) : ℂ) =
    star ((weight s n : ℂ) * u n / (weight t n : ℂ))
  rw [weight_neg_index, weight_neg_index, hu n]
  simp [star_div₀, star_mul, mul_comm]

def realOrderEquiv (s t : ℝ) : RealHs s ≃ₗᵢ[ℝ] RealHs t :=
  { toFun := fun u => ⟨orderEquiv s t u.val, orderEquiv_real s t u.val u.property⟩
    invFun := fun u => ⟨orderEquiv t s u.val, orderEquiv_real t s u.val u.property⟩
    left_inv := by
      intro u; apply Subtype.ext
      exact (orderEquiv s t).symm_apply_apply u.val
    right_inv := by
      intro u; apply Subtype.ext
      exact (orderEquiv s t).apply_symm_apply u.val
    map_add' := by intro u v; apply Subtype.ext; exact map_add (orderEquiv s t) u.val v.val
    map_smul' := by
      intro c u; apply Subtype.ext
      change orderEquiv s t ((c : ℂ) • u.val) = (c : ℂ) • orderEquiv s t u.val
      exact map_smul (orderEquiv s t) _ _
    norm_map' := fun u => (orderEquiv s t).norm_map u.val }

theorem normalize_real_symmetry (s : ℝ) (u : RealHs s) (n : ℤ) :
    normalize s u.val (-n) = star (normalize s u.val n) := by
  change (weight s (-n) : ℂ) * u.val (-n) = star ((weight s n : ℂ) * u.val n)
  rw [weight_neg_index, u.property n]
  simp [star_mul, mul_comm]

def realDualityEquiv (s : ℝ) : RealHs (-s) ≃ₗᵢ[ℝ] (RealHs s →L[ℝ] ℝ) :=
  (realOrderEquiv (-s) s).trans (InnerProductSpace.toDual ℝ (RealHs s))

theorem real_duality : Spec.RealDuality := by
  intro s
  refine ⟨realDualityEquiv s, ?_⟩
  intro v u
  refine ⟨(duality s).choose_spec v.val u.val |>.1, ?_⟩
  have hr : star (frequencyReflection (normalize (-s) v.val)) = normalize (-s) v.val := by
    apply lp.ext; funext n
    change star (normalize (-s) v.val (-n)) = normalize (-s) v.val n
    rw [normalize_real_symmetry, star_star]
  have ht := duality_term s v.val u.val
  simp only [hr] at ht
  change (inner ℂ (normalize s (orderEquiv (-s) s v.val)) (normalize s u.val)).re = _
  rw [show normalize s (orderEquiv (-s) s v.val) = normalize (-s) v.val from
    (normalizedEquiv s).apply_symm_apply _]
  rw [lp.inner_eq_tsum]
  exact congrArg Complex.re (tsum_congr ht)

theorem derivativeMap_real (s : ℝ) (u : Hs s) (hu : u ∈ realSubmodule s) :
    derivativeMap s u ∈ realSubmodule (s - 1) := by
  intro n
  rw [derivativeMap_apply, derivativeMap_apply, hu n]
  simp [star_mul, mul_comm, mul_left_comm, mul_assoc]

def realDerivativeMap (s : ℝ) : RealHs s →L[ℝ] RealHs (s - 1) :=
  ((derivativeMap s).restrictScalars ℝ).restrict (derivativeMap_real s)

theorem real_derivative : Spec.RealDerivative := by
  intro s
  refine ⟨realDerivativeMap s, ?_, ?_⟩
  · intro u n
    exact derivativeMap_apply s u.val n
  · intro u
    exact derivativeMap_bound s u.val

theorem inclusion_real (s ε : ℝ) (hε : 0 ≤ ε) (u : Hs (s + ε))
    (hu : u ∈ realSubmodule (s + ε)) : inclusion s ε hε u ∈ realSubmodule s := by
  intro n
  simpa only [inclusion_apply] using hu n

def realInclusion (s ε : ℝ) (hε : 0 ≤ ε) : RealHs (s + ε) →L[ℝ] RealHs s :=
  ((inclusion s ε hε).restrictScalars ℝ).restrict (inclusion_real s ε hε)

theorem truncationMap_real (s ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) (u : Hs (s + ε))
    (hu : u ∈ realSubmodule (s + ε)) : truncationMap s ε hε N u ∈ realSubmodule s := by
  intro n
  simp only [truncationMap_apply, Int.natAbs_neg]
  split_ifs with hn
  · exact hu n
  · simp

def realTruncationMap (s ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) :
    RealHs (s + ε) →L[ℝ] RealHs s :=
  ((truncationMap s ε hε N).restrictScalars ℝ).restrict (truncationMap_real s ε hε N)

theorem realTruncationMap_compact (s ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) :
    IsCompactOperator (realTruncationMap s ε hε N) :=
  ((truncationMap_compact s ε hε N).comp_clm (realSubmodule (s + ε)).subtypeL).codRestrict
    (fun u => truncationMap_real s ε hε N u.val u.property) (realSubmodule_closed s)

theorem realTruncation_error (s ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) (u : RealHs (s + ε)) :
    ‖realInclusion s ε hε u - realTruncationMap s ε hε N u‖ ≤ tailBound ε N * ‖u‖ := by
  exact truncation_error s ε hε N u.val

theorem realTruncation_tendsto (s ε : ℝ) (hε : 0 < ε) :
    Tendsto (realTruncationMap s ε hε.le) atTop (𝓝 (realInclusion s ε hε.le)) := by
  apply (tendsto_iff_norm_sub_tendsto_zero
    (E := RealHs (s + ε) →L[ℝ] RealHs s)).mpr
  apply squeeze_zero
    (f := fun N : ℕ => ‖realTruncationMap s ε hε.le N - realInclusion s ε hε.le‖)
    (g := tailBound ε)
    (fun N => (realTruncationMap s ε hε.le N - realInclusion s ε hε.le).opNorm_nonneg)
    _ (tailBound_tendsto ε hε)
  intro N
  apply (realTruncationMap s ε hε.le N - realInclusion s ε hε.le).opNorm_le_bound
    (tailBound_pos ε N).le
  intro u
  change ‖realTruncationMap s ε hε.le N u - realInclusion s ε hε.le u‖ ≤ _
  rw [norm_sub_rev]
  exact realTruncation_error s ε hε.le N u

lemma finiteDimensional_real_cutoff_range (s t : ℝ) (N : ℕ)
    (P : RealHs t →L[ℝ] RealHs s)
    (hP : ∀ u n, (P u).val n = if n.natAbs ≤ N then u.val n else 0) :
    FiniteDimensional ℝ (LinearMap.range P.toLinearMap) := by
  let F : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let R : LinearMap.range P.toLinearMap →ₗ[ℝ] (↥F → ℂ) :=
    { toFun := fun u n => u.val.val n.val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply FiniteDimensional.of_injective R
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext n
  by_cases hn : n.natAbs ≤ N
  · exact congrFun hab ⟨n, (mem_frequencyCutoff N n).2 hn⟩
  · obtain ⟨u, hu⟩ := a.property
    obtain ⟨v, hv⟩ := b.property
    change P u = a.val at hu
    change P v = b.val at hv
    rw [← hu, ← hv, hP, hP, ite_eq_right hn, ite_eq_right hn]

lemma realTruncationMap_finiteDimensional (s ε : ℝ) (hε : 0 ≤ ε) (N : ℕ) :
    FiniteDimensional ℝ (LinearMap.range (realTruncationMap s ε hε N).toLinearMap) :=
  finiteDimensional_real_cutoff_range s (s + ε) N (realTruncationMap s ε hε N)
    (fun u n => truncationMap_apply s ε hε N u.val n)


theorem real_compact_embedding : Spec.RealCompactEmbedding := by
  intro s ε hε
  refine ⟨realInclusion s ε hε.le, ?_, ?_, ?_,
    realTruncationMap s ε hε.le, ?_, realTruncationMap_finiteDimensional s ε hε.le,
    realTruncationMap_compact s ε hε.le,
    realTruncation_error s ε hε.le, realTruncation_tendsto s ε hε⟩
  · intro u n
    exact inclusion_apply s ε hε.le u.val n
  · intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    funext n
    have h := congrArg (fun a : RealHs s => a.val n) huv
    change inclusion s ε hε.le u.val n = inclusion s ε hε.le v.val n at h
    simpa only [inclusion_apply] using h
  · exact isCompactOperator_of_tendsto (realTruncation_tendsto s ε hε)
      (Filter.Eventually.of_forall (realTruncationMap_compact s ε hε.le))
  · intro N u n
    exact truncationMap_apply s ε hε.le N u.val n

theorem hilbert_structure : Spec.HilbertStructure := by
  intro s
  exact ⟨⟨inferInstance⟩, inferInstance, ⟨inferInstance⟩, inferInstance⟩

set_option backward.isDefEq.respectTransparency false in
theorem higher_derivatives : Spec.HigherDerivatives := by
  intro k
  induction k with
  | zero =>
    intro s
    rw [Nat.cast_zero, sub_zero]
    refine ⟨ContinuousLinearMap.id ℂ (Hs s), ?_, ?_⟩
    · intro u n; change u n = (1 : ℂ) * u n; simp
    · intro u; exact le_rfl
  | succ k ih =>
    intro s
    obtain ⟨D, hD, hnorm⟩ := ih (s - 1)
    rw [show s - ((k + 1 : ℕ) : ℝ) = (s - 1) - (k : ℝ) by push_cast; ring]
    refine ⟨D.comp (derivativeMap s), ?_, ?_⟩
    · intro u n
      rw [ContinuousLinearMap.comp_apply, hD]
      change _ * derivativeMap s u n = _
      rw [derivativeMap_apply, pow_succ]
      simp only [coefficient]
      ring
    · intro u
      exact (hnorm (derivativeMap s u)).trans (derivativeMap_bound s u)

set_option backward.isDefEq.respectTransparency false in
theorem real_higher_derivatives : Spec.RealHigherDerivatives := by
  intro k
  induction k with
  | zero =>
    intro s
    rw [Nat.cast_zero, sub_zero]
    refine ⟨ContinuousLinearMap.id ℝ (RealHs s), ?_, ?_⟩
    · intro u n; change u.val n = (1 : ℂ) * u.val n; simp
    · intro u; exact le_rfl
  | succ k ih =>
    intro s
    obtain ⟨D, hD, hnorm⟩ := ih (s - 1)
    rw [show s - ((k + 1 : ℕ) : ℝ) = (s - 1) - (k : ℝ) by push_cast; ring]
    refine ⟨D.comp (realDerivativeMap s), ?_, ?_⟩
    · intro u n
      rw [ContinuousLinearMap.comp_apply, hD]
      change _ * derivativeMap s u.val n = _
      rw [derivativeMap_apply, pow_succ]
      simp only [coefficient]
      ring
    · intro u
      exact (hnorm (realDerivativeMap s u)).trans (derivativeMap_bound s u.val)

theorem polynomial_differentiation : Spec.PolynomialDifferentiation := by
  intro s
  refine ⟨derivativeMap s, derivativeMap_apply s, ?_⟩
  intro u F x
  have h := HasDerivAt.sum (u := F) (fun n hn =>
    (ExpandedFA.Fourier.TorusFourierBasis.mode_derivatives.2 n x).const_mul (u n))
  convert h using 1
  · funext y
    simp only [fourierPolynomial, Finset.sum_apply]
  · simp only [fourierPolynomial, derivativeMap_apply]
    apply Finset.sum_congr rfl
    intro n hn
    ring

theorem real_pairing_real : Spec.RealPairingReal := by
  intro s v u
  apply Complex.conj_eq_iff_im.mp
  calc
    _ = ∑' n : ℤ, conj (u.val n * v.val (-n)) := RCLike.conjCLE.map_tsum
    _ = ∑' n : ℤ, u.val (-n) * v.val (-(-n)) := by
      apply tsum_congr
      intro n
      change star (u.val n * v.val (-n)) = _
      rw [star_mul, ← u.property n, ← v.property (-n)]
      ring
    _ = _ := (Equiv.neg ℤ).tsum_eq (fun n : ℤ => u.val n * v.val (-n))

open ExpandedFA.PartIV.Periodic

lemma coefficient_norm_bound (s : ℝ) (u : Hs s) (k : ℤ) :
    ‖u k‖ ≤ ‖u‖ * weight (-s) k := by
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (normalize s u) k
  change ‖(weight s k : ℂ) * u k‖ ≤ ‖u‖ at h
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (weight_pos s k)] at h
  rw [weight_neg_order]
  exact (le_mul_inv_iff₀ (weight_pos s k)).2 (by simpa [mul_comm] using h)

lemma coefficient_polynomial_bound (s : ℝ) (N : ℕ) (hN : -s / 2 ≤ N)
    (u : Hs s) (n : Lattice 1) :
    ‖u (n 0)‖ ≤ (‖u‖ * (1 + 4 * Real.pi ^ 2) ^ N) *
      (1 + frequencyNorm n) ^ (2 * N) := by
  have hfreq : 0 ≤ frequencyNorm n := norm_nonneg _
  have hcoord : |(n 0 : ℝ)| ≤ frequencyNorm n := by
    simpa only [Real.norm_eq_abs] using norm_frequency_coordinate_le n 0
  have hsq : (n 0 : ℝ) ^ 2 ≤ (frequencyNorm n) ^ 2 := by
    nlinarith [sq_abs (n 0 : ℝ), abs_nonneg (n 0 : ℝ)]
  have hb : frequencyWeight (n 0) ≤
      (1 + 4 * Real.pi ^ 2) * (1 + frequencyNorm n) ^ 2 := by
    dsimp [frequencyWeight]
    nlinarith [sq_nonneg Real.pi, mul_nonneg (sq_nonneg Real.pi) hfreq,
      mul_nonneg (sq_nonneg Real.pi) (sq_nonneg (frequencyNorm n)),
      mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.mpr hsq)]
  calc
    ‖u (n 0)‖ ≤ ‖u‖ * weight (-s) (n 0) := coefficient_norm_bound s u _
    _ ≤ ‖u‖ * frequencyWeight (n 0) ^ N := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [weight, Real.rpow_natCast] using
        Real.rpow_le_rpow_of_exponent_le (frequencyWeight_one_le (n 0)) hN
    _ ≤ ‖u‖ * ((1 + 4 * Real.pi ^ 2) * (1 + frequencyNorm n) ^ 2) ^ N :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (frequencyWeight_pos _).le hb N)
        (norm_nonneg _)
    _ = (‖u‖ * (1 + 4 * Real.pi ^ 2) ^ N) * (1 + frequencyNorm n) ^ (2 * N) := by
      rw [mul_pow, ← pow_mul]
      ring
lemma sobolev_polynomialGrowth (s : ℝ) (u : Hs s) :
    PolynomialGrowth (fun n : Lattice 1 => u (n 0)) := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_ge (-s / 2)
  exact ⟨‖u‖ * (1 + 4 * Real.pi ^ 2) ^ N, by positivity,
    2 * N, coefficient_polynomial_bound s N hN u⟩


lemma frequencyWeight_polynomial_bound (n : Lattice 1) :
    frequencyWeight (n 0) ≤
      (1 + 4 * Real.pi ^ 2) * (1 + frequencyNorm n) ^ 2 := by
  have hfreq : 0 ≤ frequencyNorm n := norm_nonneg _
  have hcoord : |(n 0 : ℝ)| ≤ frequencyNorm n := by
    simpa only [Real.norm_eq_abs] using norm_frequency_coordinate_le n 0
  have hsq : (n 0 : ℝ) ^ 2 ≤ (frequencyNorm n) ^ 2 := by
    nlinarith [sq_abs (n 0 : ℝ), abs_nonneg (n 0 : ℝ)]
  dsimp [frequencyWeight]
  nlinarith [sq_nonneg Real.pi, mul_nonneg (sq_nonneg Real.pi) hfreq,
    mul_nonneg (sq_nonneg Real.pi) (sq_nonneg (frequencyNorm n)),
    mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.mpr hsq)]

lemma smooth_coefficients_sobolev (s : ℝ) (φ : Smooth ℂ 1) :
    Summable (fun n : ℤ => frequencyWeight n ^ s *
      ‖testFourierCoeff φ (fun _ => n)‖ ^ 2) := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_ge s
  obtain ⟨A, L, hw⟩ := weighted_estimate 1 (2 * N)
  have hinj : Function.Injective (fun n : ℤ => (fun _ : Fin 1 => n)) := by
    intro a b h
    exact congrFun h 0
  have hs := ((hw φ).1.comp_injective hinj).mul_left
    ((1 + 4 * Real.pi ^ 2) ^ N * smoothPartialSeminorm ℂ 1 0 φ)
  apply hs.of_nonneg_of_le
  · intro n
    exact mul_nonneg (Real.rpow_pos_of_pos (frequencyWeight_pos n) s).le (sq_nonneg _)
  intro n
  let k : Lattice 1 := fun _ => n
  have hweight : frequencyWeight n ^ s ≤
      (1 + 4 * Real.pi ^ 2) ^ N * (1 + frequencyNorm k) ^ (2 * N) := by
    calc
      _ ≤ frequencyWeight n ^ N := by
        simpa only [Real.rpow_natCast] using
          Real.rpow_le_rpow_of_exponent_le (frequencyWeight_one_le n) hN
      _ ≤ ((1 + 4 * Real.pi ^ 2) * (1 + frequencyNorm k) ^ 2) ^ N :=
        pow_le_pow_left₀ (frequencyWeight_pos n).le (frequencyWeight_polynomial_bound k) N
      _ = _ := by rw [mul_pow, ← pow_mul]
  have hnorm := norm_testFourierCoeff_le φ k
  have hnormsq : ‖testFourierCoeff φ k‖ ^ 2 ≤
      smoothPartialSeminorm ℂ 1 0 φ * ‖testFourierCoeff φ k‖ := by
    nlinarith [norm_nonneg (testFourierCoeff φ k)]
  change frequencyWeight n ^ s * ‖testFourierCoeff φ k‖ ^ 2 ≤
    ((1 + 4 * Real.pi ^ 2) ^ N * smoothPartialSeminorm ℂ 1 0 φ) *
      ((1 + frequencyNorm k) ^ (2 * N) * ‖testFourierCoeff φ k‖)
  calc
    _ ≤ ((1 + 4 * Real.pi ^ 2) ^ N * (1 + frequencyNorm k) ^ (2 * N)) *
        ‖testFourierCoeff φ k‖ ^ 2 := mul_le_mul_of_nonneg_right hweight (sq_nonneg _)
    _ ≤ ((1 + 4 * Real.pi ^ 2) ^ N * (1 + frequencyNorm k) ^ (2 * N)) *
        (smoothPartialSeminorm ℂ 1 0 φ * ‖testFourierCoeff φ k‖) :=
      mul_le_mul_of_nonneg_left hnormsq (by positivity [frequencyNorm_nonneg k])
    _ = _ := by ring

open CircleBridge

variable {d : ℕ}

def realizeTorus (s : ℝ) (u : Hs s) : TorusDistribution ℂ 1 :=
  (converse 1 (fun n => u (n 0)) (sobolev_polynomialGrowth s u)).exists.choose

lemma realizeTorus_coeff (s : ℝ) (u : Hs s) (n : Lattice 1) :
    distributionCoeff (realizeTorus s u) n = u (n 0) :=
  ((converse 1 (fun n => u (n 0)) (sobolev_polynomialGrowth s u)).exists.choose_spec).1 n

lemma realizeTorus_pairing (s : ℝ) (u : Hs s) (φ : Smooth ℂ 1) :
    Summable (fun n : ℤ => ‖u n * testFourierCoeff φ (fun _ => -n)‖) ∧
    HasSum (fun n : ℤ => u n * testFourierCoeff φ (fun _ => -n)) (realizeTorus s u φ) := by
  have h := reconstruction 1 (realizeTorus s u) φ
  simp only [realizeTorus_coeff] at h
  exact ⟨(latticeInt.symm.summable_iff).mpr h.1, (latticeInt.symm.hasSum_iff).mpr h.2⟩

def realizeTorusLinear (s : ℝ) : Hs s →ₗ[ℂ] TorusDistribution ℂ 1 where
  toFun := realizeTorus s
  map_add' u v := by
    apply uniqueness 1
    funext n
    simp only [realizeTorus_coeff]
    change _ = distributionCoeff (realizeTorus s u) n + distributionCoeff (realizeTorus s v) n
    rw [realizeTorus_coeff, realizeTorus_coeff]
    rfl
  map_smul' c u := by
    apply uniqueness 1
    funext n
    simp only [realizeTorus_coeff]
    change _ = c * distributionCoeff (realizeTorus s u) n
    rw [realizeTorus_coeff]
    rfl

def realizeCircle (s : ℝ) : Hs s →ₗ[ℂ] CircleDistribution :=
  circleDistributionEquiv.toLinearMap.comp (realizeTorusLinear s)

lemma realizeCircle_coeff (s : ℝ) (u : Hs s) (n : ℤ) :
    realizeCircle s u (circleCharacter (-n)) = u n := by
  change circleDistribution (realizeTorus s u) (circleCharacter (-n)) = _
  rw [circleDistribution_coeff, realizeTorus_coeff]
  rfl

lemma realizeCircle_injective (s : ℝ) : Function.Injective (realizeCircle s) := by
  intro u v huv
  apply Subtype.ext
  funext n
  exact (realizeCircle_coeff s u n).symm.trans
    ((congrArg (fun U : CircleDistribution => U (circleCharacter (-n))) huv).trans
    (realizeCircle_coeff s v n))

lemma realizeCircle_pairing (s : ℝ) (u : Hs s) (φ : CircleTest) :
    Summable (fun n : ℤ => ‖u n * fourierCoeff φ.val (-n)‖) ∧
    HasSum (fun n : ℤ => u n * fourierCoeff φ.val (-n)) (realizeCircle s u φ) := by
  have h := realizeTorus_pairing s u (testTorus φ)
  have heq : testCircle (testTorus φ) = φ := testCircleEquiv.right_inv φ
  simp only [testFourierCoeff_circle, heq] at h
  exact h

lemma circle_coeff_unique (U V : CircleDistribution)
    (h : ∀ n : ℤ, U (circleCharacter (-n)) = V (circleCharacter (-n))) : U = V := by
  apply circleDistributionEquiv.symm.injective
  apply uniqueness 1
  funext n
  change U (testCircle (character (-n))) = V (testCircle (character (-n)))
  have hn : latticeInt.symm (-(n 0)) = -n := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  simpa only [circleCharacter, hn] using h (n 0)


lemma realizeCircle_agree (s t : ℝ) (u : Hs s) (v : Hs t)
    (h : ∀ n, u n = v n) : realizeCircle s u = realizeCircle t v := by
  apply circle_coeff_unique
  intro n
  rw [realizeCircle_coeff, realizeCircle_coeff, h]

lemma realizeCircle_image (s : ℝ) (U : CircleDistribution) :
    (∃ u : Hs s, realizeCircle s u = U) ↔
      Summable (fun n : ℤ => frequencyWeight n ^ s * ‖U (circleCharacter (-n))‖ ^ 2) := by
  constructor
  · rintro ⟨u, rfl⟩
    simp only [realizeCircle_coeff]
    exact (identification.2 s u).summable
  · intro h
    obtain ⟨u, hu⟩ := (identification.1 s (fun n => U (circleCharacter (-n)))).mpr h
    refine ⟨u, circle_coeff_unique _ _ (fun n => ?_)⟩
    rw [realizeCircle_coeff]
    exact congrFun hu n


def smoothSobolevElement (s : ℝ) (φ : Smooth ℂ 1) : Hs s :=
  ⟨fun n => testFourierCoeff φ (fun _ => n), by
    change Memℓp (fun n => (weight s n : ℂ) * testFourierCoeff φ (fun _ => n)) 2
    apply memℓp_gen
    have hs : Summable (fun n : ℤ =>
        ‖(weight s n : ℂ) * testFourierCoeff φ (fun _ => n)‖ ^ 2) :=
      (smooth_coefficients_sobolev s φ).congr (fun n =>
        (weighted_norm_term s (fun n => testFourierCoeff φ (fun _ => n)) n).symm)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hs⟩

@[simp] theorem smoothSobolevElement_apply (s : ℝ) (φ : Smooth ℂ 1) (n : ℤ) :
    smoothSobolevElement s φ n = testFourierCoeff φ (fun _ => n) := rfl

lemma distribution_smooth_pairing (s : ℝ) (u : Hs s)
    (U : TorusDistribution ℂ 1) (hU : ∀ n : Lattice 1, distributionCoeff U n = u (n 0))
    (φ : Smooth ℂ 1) :
    U φ = ∑' n : ℤ, u n * smoothSobolevElement (-s) φ (-n) := by
  calc
    U φ = ∑' n : Lattice 1, distributionCoeff U n * testFourierCoeff φ (-n) :=
      (reconstruction 1 U φ).2.tsum_eq.symm
    _ = ∑' n : ℤ, distributionCoeff U (fun _ => n) *
        testFourierCoeff φ (fun _ => -n) :=
      ((Equiv.funUnique (Fin 1) ℤ).symm.tsum_eq _).symm
    _ = _ := by simp only [hU, smoothSobolevElement_apply]


lemma integrable_test_product (f : CircleBridge.Circle → ℂ)
    (hf : Integrable f AddCircle.haarAddCircle) (φ : Smooth ℂ 1) :
    Integrable (fun q : Torus 1 => f (torusCircle q) * φ.val q) (torusHaar 1) := by
  have hcomp : Integrable (fun q : Torus 1 => f (torusCircle q)) (torusHaar 1) :=
    torusCircle_measurePreserving.integrable_comp_of_integrable hf
  exact hcomp.mul_bdd (continuous_smooth φ).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_smooth_apply_le φ))

def regularCircleLM (f : CircleBridge.Circle → ℂ) (hf : Integrable f AddCircle.haarAddCircle) :
    Smooth ℂ 1 →ₗ[ℂ] ℂ where
  toFun φ := ∫ q : Torus 1, f (torusCircle q) * φ.val q ∂torusHaar 1
  map_add' φ ψ := by
    change (∫ q, f (torusCircle q) * (φ.val q + ψ.val q) ∂torusHaar 1) = _
    simp_rw [mul_add]
    exact integral_add (integrable_test_product f hf φ) (integrable_test_product f hf ψ)
  map_smul' c φ := by
    change (∫ q, f (torusCircle q) * (c * φ.val q) ∂torusHaar 1) = _
    simp_rw [mul_left_comm (f _) c]
    exact integral_const_mul c _

lemma norm_regularCircleLM (f : CircleBridge.Circle → ℂ) (hf : Integrable f AddCircle.haarAddCircle)
    (φ : Smooth ℂ 1) :
    ‖regularCircleLM f hf φ‖ ≤ (∫ q : CircleBridge.Circle, ‖f q‖ ∂AddCircle.haarAddCircle) *
      smoothPartialSeminorm ℂ 1 0 φ := by
  change ‖∫ q : Torus 1, f (torusCircle q) * φ.val q ∂torusHaar 1‖ ≤ _
  have hi : Integrable (fun q : Torus 1 => ‖f (torusCircle q)‖) (torusHaar 1) :=
    (torusCircle_measurePreserving.integrable_comp_of_integrable hf).norm
  calc
    _ ≤ ∫ q : Torus 1, ‖f (torusCircle q)‖ * smoothPartialSeminorm ℂ 1 0 φ ∂torusHaar 1 :=
      norm_integral_le_of_norm_le (hi.mul_const _) (Filter.Eventually.of_forall fun q => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_smooth_apply_le φ q) (norm_nonneg _))
    _ = _ := by
      rw [integral_mul_const]
      congr 1
      exact torusCircle_measurePreserving.integral_comp
        (MeasurableEquiv.funUnique (Fin 1) CircleBridge.Circle).measurableEmbedding (fun q => ‖f q‖)

def regularCircleDistribution (f : CircleBridge.Circle → ℂ) (hf : Integrable f AddCircle.haarAddCircle) :
    TorusDistribution ℂ 1 :=
  ⟨regularCircleLM f hf, by
    apply WithSeminorms.continuous_normedSpace_rng ℂ (smooth_partial_topology ℂ 1)
    refine ⟨{0}, ⟨∫ q : CircleBridge.Circle, ‖f q‖ ∂AddCircle.haarAddCircle, integral_nonneg (fun _ => norm_nonneg _)⟩, ?_⟩
    intro φ
    simp only [Finset.sup_singleton]
    change ‖regularCircleLM f hf φ‖ ≤
      (∫ q : CircleBridge.Circle, ‖f q‖ ∂AddCircle.haarAddCircle) *
        smoothPartialSeminorm ℂ 1 0 φ
    exact norm_regularCircleLM f hf φ⟩

lemma regularCircleDistribution_coeff (f : CircleBridge.Circle → ℂ)
    (hf : Integrable f AddCircle.haarAddCircle) (n : Lattice 1) :
    distributionCoeff (regularCircleDistribution f hf) n = fourierCoeff f (n 0) := by
  change (∫ q : Torus 1, f (torusCircle q) * (character (-n)).val q ∂torusHaar 1) = _
  simp only [character_apply, character_circle, Pi.neg_apply]
  unfold fourierCoeff
  simp only [smul_eq_mul]
  rw [← circle_integral (fun q => fourier (-(n 0)) q * f q)]
  apply integral_congr_ae
  filter_upwards [] with q
  exact mul_comm _ _


@[simp] theorem conjugateTest_apply (φ : Smooth ℂ d) (q : Torus d) :
    (conjugateTest φ).val q = conj (φ.val q) := rfl

theorem conjugateTest_character (n : Lattice d) :
    conjugateTest (character n) = character (-n) := by
  apply Subtype.ext
  funext q
  exact (UnitAddTorus.mFourier_neg (n := n) (x := q)).symm

theorem testFourierCoeff_conjugateTest (φ : Smooth ℂ d) (n : Lattice d) :
    testFourierCoeff (conjugateTest φ) n = conj (testFourierCoeff φ (-n)) := by
  rw [testFourierCoeff, testFourierCoeff, ← integral_conj]
  congr 1
  funext q
  simp [conjugateTest, UnitAddTorus.mFourier_neg, map_mul]

theorem coefficient_derivative_pairing
    (U V : TorusDistribution ℂ d) (i : Fin d) (k : ℕ)
    (hc : ∀ n, distributionCoeff V n =
      (2 * (Real.pi : ℂ) * Complex.I * (n i : ℂ)) ^ k * distributionCoeff U n)
    (φ : Smooth ℂ d) :
    V φ = (-1 : ℂ) ^ k * U (FourierDecay.jet φ (fun _ : Fin k => i)) := by
  have hU := (reconstruction d U (FourierDecay.jet φ (fun _ : Fin k => i))).2
  have hV := (reconstruction d V φ).2
  have hm := hU.mul_left ((-1 : ℂ) ^ k)
  apply hV.unique
  convert hm using 1
  funext n
  rw [FourierDecay.coeff_jet_constant_of_multiplier FourierDecay.fourierCoeff_jet_one,
    phase_coordinate, Pi.neg_apply, Int.cast_neg, hc]
  rw [mul_neg, neg_pow (2 * (Real.pi : ℂ) * Complex.I * (n i : ℂ))]
  have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  symm
  calc
    _ = ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) * ((2 * (Real.pi : ℂ) * Complex.I * (n i : ℂ)) ^ k * distributionCoeff U n * testFourierCoeff φ (-n)) := by ring
    _ = _ := by rw [hsign]; ring

theorem real_distribution_iff (U : TorusDistribution ℂ d) :
    (∀ n, distributionCoeff U (-n) = conj (distributionCoeff U n)) ↔
      ∀ φ, U (conjugateTest φ) = conj (U φ) := by
  constructor
  · intro hc φ
    have h1 := (reconstruction d U (conjugateTest φ)).2
    have h2 := (Equiv.neg (Lattice d)).hasSum_iff.mpr ((reconstruction d U φ).2.star)
    simp only [testFourierCoeff_conjugateTest, neg_neg] at h1
    change HasSum (fun n => star (distributionCoeff U (-n) * testFourierCoeff φ (-(-n)))) (star (U φ)) at h2
    apply h1.unique
    simpa only [starRingEnd_apply, star_mul, neg_neg, hc, star_star, mul_comm] using h2
  · intro hreal n
    have h := hreal (character (-n))
    simpa only [conjugateTest_character, neg_neg, distributionCoeff] using h


lemma circleConjugateTest_value (φ : CircleTest) (q : CircleBridge.Circle) :
    (circleConjugateTest φ).val q = conj (φ.val q) := by
  change conj (φ.val (torusCircle (torusCircle.symm q))) = _
  rw [torusCircle.apply_symm_apply]

lemma realizeCircle_real (s : ℝ) (u : Hs s) :
    (∀ n : ℤ, u (-n) = conj (u n)) ↔
      ∀ φ : CircleTest, realizeCircle s u (circleConjugateTest φ) = conj (realizeCircle s u φ) := by
  have h := real_distribution_iff (realizeTorus s u)
  simp only [realizeTorus_coeff, Pi.neg_apply] at h
  constructor
  · intro hu φ
    change realizeTorus s u (testTorus (testCircle (conjugateTest (testTorus φ)))) = _
    rw [show testTorus (testCircle (conjugateTest (testTorus φ))) =
      conjugateTest (testTorus φ) from testCircleEquiv.left_inv _]
    exact h.mp (fun n => hu (n 0)) (testTorus φ)
  · intro hu n
    have ht : ∀ ψ : Smooth ℂ 1, realizeTorus s u (conjugateTest ψ) =
        conj (realizeTorus s u ψ) := by
      intro ψ
      have hp := hu (testCircle ψ)
      have heq : testTorus (testCircle ψ) = ψ := testCircleEquiv.left_inv ψ
      change realizeTorus s u (testTorus (circleConjugateTest (testCircle ψ))) = _ at hp
      change realizeTorus s u (testTorus (testCircle (conjugateTest (testTorus (testCircle ψ))))) =
        conj (realizeTorus s u (testTorus (testCircle ψ))) at hp
      simpa only [testTorus_testCircle] using hp
    exact h.mpr ht (fun _ => n)

lemma realizeCircle_derivative (k : ℕ) (s : ℝ) :
    ∃ D : Hs s →L[ℂ] Hs (s - (k : ℝ)),
      (∀ u n, D u n = (2 * Real.pi * Complex.I * n : ℂ) ^ k * u n) ∧
      (∀ u, ‖D u‖ ≤ ‖u‖) ∧
      ∀ (u : Hs s) (φ : CircleTest),
        realizeCircle (s - (k : ℝ)) (D u) φ =
          (-1 : ℂ) ^ k * realizeCircle s u (circleHigherTestDerivative k φ) := by
  obtain ⟨D, hD, hnorm⟩ := higher_derivatives k s
  refine ⟨D, hD, hnorm, ?_⟩
  intro u φ
  change realizeTorus (s - (k : ℝ)) (D u) (testTorus φ) = _
  have h := coefficient_derivative_pairing (realizeTorus s u)
    (realizeTorus (s - (k : ℝ)) (D u)) (0 : Fin 1) k
    (fun n => by rw [realizeTorus_coeff, realizeTorus_coeff]; exact hD u (n 0)) (testTorus φ)
  rw [h]
  congr 1
  change realizeTorus s u _ = realizeTorus s u (testTorus (testCircle _))
  rw [testTorus_testCircle]

lemma realizeCircle_regular (s : ℝ) (u : Hs s) (f : CircleBridge.Circle → ℂ)
    (hf : Integrable f AddCircle.haarAddCircle) (hu : ∀ n, u n = fourierCoeff f n)
    (φ : CircleTest) : realizeCircle s u φ =
      ∫ x : CircleBridge.Circle, f x * φ.val x ∂AddCircle.haarAddCircle := by
  have heq : realizeTorus s u = regularCircleDistribution f hf := by
    apply uniqueness 1
    funext n
    rw [realizeTorus_coeff, regularCircleDistribution_coeff, hu]
  change realizeTorus s u (testTorus φ) = _
  rw [heq]
  change (∫ q : Torus 1, f (torusCircle q) * φ.val (torusCircle q) ∂torusHaar 1) = _
  exact circle_integral (fun x => f x * φ.val x)

lemma realizeCircle_zero :
    ∃ U : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) ≃ₗᵢ[ℂ] Hs 0,
      (∀ f n, U f n = fourierCoeff f n) ∧
      ∀ f (φ : CircleTest), realizeCircle 0 (U f) φ =
        ∫ x : CircleBridge.Circle, f x * φ.val x ∂AddCircle.haarAddCircle := by
  obtain ⟨U, hU⟩ := zero_fourier
  refine ⟨U, hU, fun f φ => ?_⟩
  exact realizeCircle_regular 0 (U f) f
    (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp f)) (hU f) φ

lemma realizeCircle_duality (s : ℝ) :
    ∃ V : Hs (-s) ≃ₗᵢ[ℂ] (Hs s →L[ℂ] ℂ),
      (∀ v u, Summable (fun n : ℤ => ‖u n * v (-n)‖) ∧
        V v u = ∑' n : ℤ, u n * v (-n)) ∧
      ∀ φ : CircleTest, ∃ v : Hs (-s),
        (∀ n, v n = fourierCoeff φ.val n) ∧ ∀ u : Hs s, V v u = realizeCircle s u φ := by
  obtain ⟨V, hV⟩ := duality s
  refine ⟨V, hV, fun φ => ?_⟩
  refine ⟨smoothSobolevElement (-s) (testTorus φ), ?_, ?_⟩
  · intro n
    rw [smoothSobolevElement_apply, testFourierCoeff_circle]
    rw [testCircle_testTorus]
  · intro u
    rw [(hV _ u).2]
    exact (distribution_smooth_pairing s u (realizeTorus s u)
      (realizeTorus_coeff s u) (testTorus φ)).symm

lemma realizeCircle_real_image (s : ℝ) (U : CircleDistribution) :
    (∃ u : RealHs s, realizeCircle s u.val = U) ↔
      Summable (fun n : ℤ => frequencyWeight n ^ s * ‖U (circleCharacter (-n))‖ ^ 2) ∧
      (∀ φ : CircleTest, U (circleConjugateTest φ) = conj (U φ)) := by
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨(realizeCircle_image s _).mp ⟨u.val, rfl⟩,
      (realizeCircle_real s u.val).mp u.property⟩
  · rintro ⟨hsum, hreal⟩
    obtain ⟨u, hu⟩ := (realizeCircle_image s U).mpr hsum
    have hr : u ∈ realSubmodule s := by
      apply (realizeCircle_real s u).mpr
      simpa only [hu] using hreal
    exact ⟨⟨u, hr⟩, hu⟩

lemma realizeCircle_real_derivative (k : ℕ) (s : ℝ) :
    ∃ D : RealHs s →L[ℝ] RealHs (s - (k : ℝ)),
      (∀ u n, (D u).val n = (2 * π * Complex.I * n : ℂ) ^ k * u.val n) ∧
      (∀ u, ‖D u‖ ≤ ‖u‖) ∧
      ∀ (u : RealHs s) (φ : CircleTest),
        realizeCircle (s - (k : ℝ)) (D u).val φ =
          (-1 : ℂ) ^ k * realizeCircle s u.val (circleHigherTestDerivative k φ) := by
  obtain ⟨D, hD, hnorm⟩ := real_higher_derivatives k s
  refine ⟨D, hD, hnorm, ?_⟩
  intro u φ
  change realizeTorus (s - (k : ℝ)) (D u).val (testTorus φ) = _
  have h := coefficient_derivative_pairing (realizeTorus s u.val)
    (realizeTorus (s - (k : ℝ)) (D u).val) (0 : Fin 1) k
    (fun n => by rw [realizeTorus_coeff, realizeTorus_coeff]; exact hD u (n 0)) (testTorus φ)
  rw [h]
  congr 1
  change realizeTorus s u.val _ = realizeTorus s u.val (testTorus (testCircle _))
  rw [testTorus_testCircle]

lemma realizeCircle_real_duality (s : ℝ) :
    ∃ V : RealHs (-s) ≃ₗᵢ[ℝ] (RealHs s →L[ℝ] ℝ),
      (∀ v u, Summable (fun n : ℤ => ‖u.val n * v.val (-n)‖) ∧
        V v u = (∑' n : ℤ, u.val n * v.val (-n)).re) ∧
      ∀ φ : CircleTest, (∀ x, conj (φ.val x) = φ.val x) → ∃ v : RealHs (-s),
        (∀ n, v.val n = fourierCoeff φ.val n) ∧
          ∀ u : RealHs s, V v u = (realizeCircle s u.val φ).re := by
  obtain ⟨V, hV⟩ := real_duality s
  refine ⟨V, hV, ?_⟩
  intro φ hφ
  let ψ := testTorus φ
  have hc : conjugateTest ψ = ψ := by
    apply Subtype.ext
    funext q
    exact hφ (torusCircle q)
  have hv : smoothSobolevElement (-s) ψ ∈ realSubmodule (-s) := by
    intro n
    change testFourierCoeff ψ (fun _ => -n) = conj (testFourierCoeff ψ (fun _ => n))
    have hn := testFourierCoeff_conjugateTest ψ (fun _ : Fin 1 => -n)
    rw [hc] at hn
    simpa only [Pi.neg_def, neg_neg] using hn
  refine ⟨⟨smoothSobolevElement (-s) ψ, hv⟩, ?_, ?_⟩
  · intro n
    rw [smoothSobolevElement_apply, testFourierCoeff_circle]
    rw [show testCircle ψ = φ from testCircle_testTorus φ]
  · intro u
    rw [(hV _ u).2]
    exact congrArg Complex.re ((distribution_smooth_pairing s u.val
      (realizeTorus s u.val) (realizeTorus_coeff s u.val) ψ).symm)


theorem distribution_realization : Spec.DistributionRealization := by
  exact ⟨realizeCircle, realizeCircle_coeff, realizeCircle_injective, realizeCircle_image,
    realizeCircle_pairing, realizeCircle_agree, realizeCircle_real, realizeCircle_real_image,
    realizeCircle_derivative, realizeCircle_real_derivative, realizeCircle_zero,
    realizeCircle_duality, realizeCircle_real_duality⟩


end ExpandedFA.Sobolev.PeriodicHilbertScale
namespace ExpandedFA.Sobolev.CircleBridge
open ExpandedFA.PartIV.Periodic
theorem iteratedDeriv_circleTest (φ : Smooth ℂ 1) (k : ℕ) :
    iteratedDeriv k (fun x : ℝ => (testCircle φ).val (x : Circle)) =
      fun x : ℝ => (testCircle (FourierDecay.jet φ (fun _ : Fin k => (0 : Fin 1)))).val (x : Circle) := by
  induction k with
  | zero =>
    have hz : FourierDecay.jet φ (fun _ : Fin 0 => (0 : Fin 1)) = φ := by
      convert FourierDecay.jet_zero φ using 1
      congr 1
      funext i
      exact Fin.elim0 i
    rw [iteratedDeriv_zero, hz]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [(hasDerivAt_circleTest (FourierDecay.jet φ (fun _ : Fin k => (0 : Fin 1))) x).deriv,
      FourierDecay.jet_one_jet]
    have heq : (Fin.cons (0 : Fin 1) (fun _ : Fin k => (0 : Fin 1))) =
        (fun _ : Fin (k + 1) => (0 : Fin 1)) := Subsingleton.elim _ _
    rw [heq]

theorem iteratedDeriv_circleHigherTestDerivative (k : ℕ) (φ : CircleTest) :
    iteratedDeriv k (fun x : ℝ => φ.val (x : Circle)) =
      fun x : ℝ => (circleHigherTestDerivative k φ).val (x : Circle) := by
  have h := iteratedDeriv_circleTest (testTorus φ) k
  have heq : testCircle (testTorus φ) = φ := testCircleEquiv.right_inv φ
  simpa only [heq, circleHigherTestDerivative] using h


end ExpandedFA.Sobolev.CircleBridge

namespace ExpandedFA.Sobolev.CircleBridge
open Set ExpandedFA.Distributions ExpandedFA.PartIV.Periodic
lemma quotient_one_coordinate (x : Domain 1) :
    quotient x = torusCircle.symm (x 0 : Circle) := by
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

lemma circle_coordinate_jet (φ : CircleTest) (k : ℕ) (a : Fin k → Fin 1)
    (x : Domain 1) :
    iteratedFDeriv ℝ k (lift (testTorus φ)) x (fun j => coordinateVector (a j)) =
      iteratedDeriv k (fun y : ℝ => φ.val (y : Circle)) (x 0) := by
  have ha : a = fun _ : Fin k => (0 : Fin 1) := Subsingleton.elim _ _
  subst a
  rw [← FourierDecay.lift_jet]
  rw [iteratedDeriv_circleHigherTestDerivative]
  change (FourierDecay.jet (testTorus φ) (fun _ : Fin k => (0 : Fin 1))).val (quotient x) =
    (FourierDecay.jet (testTorus φ) (fun _ : Fin k => (0 : Fin 1))).val
      (torusCircle.symm (x 0 : Circle))
  rw [quotient_one_coordinate]

/-- The transported seminorms are exactly the usual C∞ circle seminorms:
all ordinary derivatives through order L, uniformly over a full period. -/
theorem circle_smooth_partial_formula (φ : CircleTest) (L : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    smoothPartialSeminorm ℂ 1 L (testTorus φ) ≤ C ↔
      ∀ k ≤ L, ∀ x ∈ Icc (0 : ℝ) 1,
        ‖iteratedDeriv k (fun y : ℝ => φ.val (y : Circle)) x‖ ≤ C := by
  rw [smooth_partial_formula ℂ 1 L (testTorus φ) C hC]
  constructor
  · intro h k hk x hx
    have hxD : (fun _ : Fin 1 => x) ∈ cube 1 := by
      constructor
      · intro i
        exact hx.1
      · intro i
        exact hx.2
    simpa only [circle_coordinate_jet] using
      h k hk (fun _ : Fin k => (0 : Fin 1)) (fun _ : Fin 1 => x) hxD
  · intro h k hk a x hx
    rw [circle_coordinate_jet]
    exact h k hk (x 0) ⟨hx.1 0, hx.2 0⟩


end ExpandedFA.Sobolev.CircleBridge

namespace ExpandedFA.Sobolev.PeriodicHilbertScale
open ExpandedFA.PartIV.Periodic CircleBridge

theorem circle_identification : Spec.CircleIdentification := by
  refine ⟨torusCircle_measurePreserving, fun _ _ => rfl, testFourierCoeff_circle, ?_,
    circle_smooth_partial_formula⟩
  intro k φ x
  exact (congrFun (iteratedDeriv_circleHigherTestDerivative k φ) x).symm

end ExpandedFA.Sobolev.PeriodicHilbertScale
