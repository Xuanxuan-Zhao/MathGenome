import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.VolterraSingularSystem
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.L2KernelCompact
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.CompactSpectral.SingularApproximation
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.ODE.Gronwall
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.CompactNonzeroSpectrum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace ComplexConjugate BoundedContinuousFunction
namespace ExpandedFA.PartV.VolterraSingularSystem
open VolterraSingularSystemSpec

theorem compact : VolterraSingularSystemSpec.Compact := by
  intro 𝕜 _ T _
  exact L2KernelCompact.kernel_compact _ _ _

lemma kernel_integral (𝕜 : Type) [RCLike 𝕜] (T t : ℝ) (ht : t ∈ Ioo 0 T)
    (u : ℝ → 𝕜) :
    (∫ s, kernelFunction 𝕜 (t,s) * u s ∂intervalMeasure T) =
      ∫ s in Ioo 0 t, u s := by
  calc
    _ = ∫ s, (Iio t).indicator u s ∂intervalMeasure T := by
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by
        by_cases hs : s < t <;> simp [kernelFunction, hs]
    _ = ∫ s in Iio t, u s ∂intervalMeasure T := integral_indicator measurableSet_Iio
    _ = ∫ s in Ioo 0 t, u s := by
      have hset : Iio t ∩ Ioo 0 T = Ioo 0 t := by
        ext s
        simp only [mem_inter_iff, mem_Iio, mem_Ioo]
        exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans ht.2⟩⟩
      rw [intervalMeasure, Measure.restrict_restrict measurableSet_Iio, hset]

theorem integral_formula : IntegralFormula := by
  intro 𝕜 _ T _ u
  have h := L2Kernel.kernel_representative_formula (intervalMeasure T) (intervalMeasure T)
    (kernelFunction 𝕜) u (kernel_memLp 𝕜 T) (Lp.memLp u)
  simp only [Lp.toLp_coeFn] at h
  filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with t ht hmem
  exact ht.trans (kernel_integral 𝕜 T t hmem u)

lemma adjoint_kernel_integral (𝕜 : Type) [RCLike 𝕜] (T s : ℝ) (hs : s ∈ Ioo 0 T)
    (u : ℝ → 𝕜) :
    (∫ t, conj (kernelFunction 𝕜 (t,s)) * u t ∂intervalMeasure T) =
      ∫ t in Ioo s T, u t := by
  calc
    _ = ∫ t, (Ioi s).indicator u t ∂intervalMeasure T := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        by_cases ht : s < t <;> simp [kernelFunction, ht]
    _ = ∫ t in Ioi s, u t ∂intervalMeasure T := integral_indicator measurableSet_Ioi
    _ = ∫ t in Ioo s T, u t := by
      have hset : Ioi s ∩ Ioo 0 T = Ioo s T := by
        ext t
        simp only [mem_inter_iff, mem_Ioi, mem_Ioo]
        exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hs.1.trans h.1, h.2⟩⟩
      rw [intervalMeasure, Measure.restrict_restrict measurableSet_Ioi, hset]

theorem adjoint_formula : AdjointFormula := by
  intro 𝕜 _ T _ u
  have h := (L2KernelCompact.l2_kernel_adjoint_correct
    (intervalMeasure T) (intervalMeasure T) (kernel 𝕜 T)).2 u
  filter_upwards [h.2, ae_restrict_mem measurableSet_Ioo,
    Measure.ae_ae_of_ae_prod ((Measure.measurePreserving_swap
      (μ := intervalMeasure T) (ν := intervalMeasure T)).quasiMeasurePreserving.ae_eq_comp
      (kernel_memLp 𝕜 T).coeFn_toLp)] with s hs hmem hk
  apply hs.trans
  calc
    _ = ∫ t, conj (kernelFunction 𝕜 (t,s)) * u t ∂intervalMeasure T := by
      apply integral_congr_ae
      filter_upwards [hk] with t ht
      change kernel 𝕜 T (t,s) = kernelFunction 𝕜 (t,s) at ht
      rw [ht]
    _ = _ := adjoint_kernel_integral 𝕜 T s hmem u

lemma sigma_pos (T : ℝ) (hT : 0 < T) (n : ℕ) : 0 < sigma T n := by
  exact div_pos hT (mul_pos (by positivity) Real.pi_pos)

lemma frequency_pos (T : ℝ) (hT : 0 < T) (n : ℕ) : 0 < frequency T n := by
  exact div_pos (mul_pos (by positivity) Real.pi_pos) hT

lemma inv_frequency (T : ℝ) (n : ℕ) : (frequency T n)⁻¹ = sigma T n := by
  simp only [frequency, sigma, inv_div]

lemma cosine_at_right_endpoint (T : ℝ) (hT : 0 < T) (n : ℕ) :
    Real.cos (frequency T n * T) = 0 := by
  rw [frequency, div_mul_cancel₀ _ hT.ne']
  have he : ((n : ℝ) + 1 / 2) * Real.pi = n * Real.pi + Real.pi / 2 := by ring
  rw [he, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero]

lemma integral_cosineFunction (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (hT : 0 < T)
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ s in Ioo 0 t, cosineFunction 𝕜 T n s) =
      (sigma T n : 𝕜) * sineFunction 𝕜 T n t := by
  simp only [cosineFunction, integral_ofReal, integral_const_mul,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht]
  rw [intervalIntegral.integral_comp_mul_left _ (frequency_pos T hT n).ne', integral_cos]
  simp only [mul_zero, Real.sin_zero, sub_zero, smul_eq_mul, inv_frequency,
    sineFunction, ← RCLike.ofReal_mul]
  congr 1
  ring

lemma integral_sineFunction (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (hT : 0 < T)
    (n : ℕ) (s : ℝ) (hs : s ≤ T) :
    (∫ t in Ioo s T, sineFunction 𝕜 T n t) =
      (sigma T n : 𝕜) * cosineFunction 𝕜 T n s := by
  simp only [sineFunction, integral_ofReal, integral_const_mul,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs]
  rw [intervalIntegral.integral_comp_mul_left _ (frequency_pos T hT n).ne', integral_sin]
  simp only [cosine_at_right_endpoint T hT n, sub_zero, smul_eq_mul, inv_frequency,
    cosineFunction, ← RCLike.ofReal_mul]
  congr 1
  ring

/-- Formula on arbitrary L² representatives; this avoids making pointwise
claims about the quotient's chosen representative. -/
lemma operator_toLp (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (u : ℝ → 𝕜)
    (hu : MemLp u 2 (intervalMeasure T)) :
    (operator 𝕜 T (hu.toLp u) : ℝ → 𝕜) =ᵐ[intervalMeasure T]
      fun t => ∫ s in Ioo 0 t, u s := by
  have h := L2Kernel.kernel_representative_formula (intervalMeasure T) (intervalMeasure T)
    (kernelFunction 𝕜) u (kernel_memLp 𝕜 T) hu
  filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with t ht hmem
  exact ht.trans (kernel_integral 𝕜 T t hmem u)

lemma adjoint_toLp (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (hT : 0 < T) (u : ℝ → 𝕜)
    (hu : MemLp u 2 (intervalMeasure T)) :
    (ContinuousLinearMap.adjoint (operator 𝕜 T) (hu.toLp u) : ℝ → 𝕜)
      =ᵐ[intervalMeasure T] fun s => ∫ t in Ioo s T, u t := by
  filter_upwards [adjoint_formula 𝕜 T hT (hu.toLp u),
    ae_restrict_mem measurableSet_Ioo] with s hs hmem
  apply hs.trans
  exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset
    (show Ioo s T ⊆ Ioo 0 T from fun t ht => ⟨hmem.1.trans ht.1, ht.2⟩)
      hu.coeFn_toLp)

theorem singular_identities : SingularIdentities := by
  intro 𝕜 _ T hT n
  constructor
  · apply Lp.ext
    filter_upwards [operator_toLp 𝕜 T (cosineFunction 𝕜 T n) (cosine_memLp 𝕜 T n),
      Lp.coeFn_smul (sigma T n : 𝕜) (leftVector 𝕜 T n),
      (sine_memLp 𝕜 T n).coeFn_toLp, ae_restrict_mem measurableSet_Ioo]
        with t ht hs hf hmem
    change operator 𝕜 T (rightVector 𝕜 T n) t = _ at ht
    change leftVector 𝕜 T n t = _ at hf
    rw [ht, hs, Pi.smul_apply, hf, smul_eq_mul]
    exact integral_cosineFunction 𝕜 T hT n t hmem.1.le
  · apply Lp.ext
    filter_upwards [adjoint_toLp 𝕜 T hT (sineFunction 𝕜 T n) (sine_memLp 𝕜 T n),
      Lp.coeFn_smul (sigma T n : 𝕜) (rightVector 𝕜 T n),
      (cosine_memLp 𝕜 T n).coeFn_toLp, ae_restrict_mem measurableSet_Ioo]
        with t ht hs he hmem
    change ContinuousLinearMap.adjoint (operator 𝕜 T) (leftVector 𝕜 T n) t = _ at ht
    change rightVector 𝕜 T n t = _ at he
    rw [ht, hs, Pi.smul_apply, he, smul_eq_mul]
    exact integral_sineFunction 𝕜 T hT n t hmem.2.le

theorem singular_values : SingularValues := by
  intro T hT
  refine ⟨sigma_pos T hT, ?_, ?_, ?_⟩
  · intro m n hmn
    apply div_le_div_of_nonneg_left hT.le (by positivity)
    apply mul_le_mul_of_nonneg_right _ Real.pi_pos.le
    have hc : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
    linarith
  · exact tendsto_const_nhds.div_atTop
      ((tendsto_atTop_mono (fun n : ℕ => show (n : ℝ) ≤ (n : ℝ) + 1 / 2 by linarith)
        tendsto_natCast_atTop_atTop).atTop_mul_const Real.pi_pos)
  · dsimp [sigma]
    norm_num
    field_simp

/-- Assembly of the norm-convergent singular expansions from the explicit bases. -/
theorem expansions_from_complete_systems (h : CompleteOrthonormalSystems) :
    SingularExpansions := by
  intro 𝕜 _ T hT x
  obtain ⟨he, hf, hspan_e, hspan_f⟩ := h 𝕜 T hT
  let b : HilbertBasis ℕ 𝕜 (Space 𝕜 T) := HilbertBasis.mk he (by rw [hspan_e])
  let c : HilbertBasis ℕ 𝕜 (Space 𝕜 T) := HilbertBasis.mk hf (by rw [hspan_f])
  constructor
  · have hb := (b.hasSum_repr x).mapL (operator 𝕜 T)
    simpa only [HilbertBasis.repr_apply_apply, b, HilbertBasis.coe_mk, map_smul,
      fun n => (singular_identities 𝕜 T hT n).1, smul_smul, mul_comm] using hb
  · have hc := (c.hasSum_repr x).mapL (ContinuousLinearMap.adjoint (operator 𝕜 T))
    simpa only [HilbertBasis.repr_apply_apply, c, HilbertBasis.coe_mk, map_smul,
      fun n => (singular_identities 𝕜 T hT n).2, smul_smul, mul_comm] using hc

/-- The norm computation from the two complete explicit systems. -/
theorem norm_from_complete_systems (h : CompleteOrthonormalSystems) : NormFormula := by
  intro 𝕜 _ T hT
  classical
  obtain ⟨he, hf, hspan, _⟩ := h 𝕜 T hT
  have hvalues := singular_values T hT
  have hupper : ‖operator 𝕜 T‖ ≤ sigma T 0 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (sigma_pos T hT 0).le
    intro x
    have hsum : HasSum (fun n => ((sigma T n : 𝕜) * inner 𝕜 (rightVector 𝕜 T n) x) •
        leftVector 𝕜 T n) (operator 𝕜 T x) := by
      exact (expansions_from_complete_systems h 𝕜 T hT x).1
    apply le_of_tendsto hsum.norm
    apply Eventually.of_forall
    intro s
    have hs : ‖∑ n ∈ s,
        ((sigma T n : 𝕜) * inner 𝕜 (rightVector 𝕜 T n) x) • leftVector 𝕜 T n‖ ^ 2 ≤
        (sigma T 0 * ‖x‖) ^ 2 := by
      rw [CompactSpectral.SingularApproximation.norm_sum_orthonormal_sq _ hf]
      calc
        _ ≤ ∑ n ∈ s, (sigma T 0) ^ 2 * ‖inner 𝕜 (rightVector 𝕜 T n) x‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro n _
          rw [norm_mul, RCLike.norm_ofReal, abs_of_pos (sigma_pos T hT n), mul_pow]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (sigma_pos T hT n).le (hvalues.2.1 (Nat.zero_le n)) 2)
            (sq_nonneg _)
        _ = (sigma T 0) ^ 2 * ∑ n ∈ s, ‖inner 𝕜 (rightVector 𝕜 T n) x‖ ^ 2 := by
          rw [Finset.mul_sum]
        _ ≤ (sigma T 0) ^ 2 * ‖x‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (he.sum_inner_products_le x) (sq_nonneg _)
        _ = _ := (mul_pow _ _ _).symm
    have hp := mul_nonneg (sigma_pos T hT 0).le (norm_nonneg x)
    nlinarith [norm_nonneg (∑ n ∈ s,
      ((sigma T n : 𝕜) * inner 𝕜 (rightVector 𝕜 T n) x) • leftVector 𝕜 T n)]
  have hlower := (operator 𝕜 T).le_opNorm (rightVector 𝕜 T 0)
  rw [(singular_identities 𝕜 T hT 0).1, norm_smul, RCLike.norm_ofReal,
    abs_of_pos (sigma_pos T hT 0), hf.norm_eq_one, he.norm_eq_one, mul_one, mul_one] at hlower
  exact (le_antisymm hupper hlower).trans hvalues.2.2.2

lemma rightVector_inner_self (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (hT : 0 < T) (n : ℕ) :
    inner 𝕜 (rightVector 𝕜 T n) (rightVector 𝕜 T n) = 1 := by
  rw [L2.inner_def]
  have hc : (∫ t in Ioo 0 T, Real.cos (frequency T n * t) ^ 2) = T / 2 := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hT.le]
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x ^ 2) (frequency_pos T hT n).ne', integral_cos_sq]
    simp only [mul_zero, Real.cos_zero, Real.sin_zero, mul_zero, sub_zero,
      cosine_at_right_endpoint T hT n, zero_mul, zero_add, smul_eq_mul]
    field_simp [(frequency_pos T hT n).ne']
  calc
    _ = algebraMap ℝ 𝕜 (∫ t in Ioo 0 T, ((Real.sqrt (2 / T)) ^ 2 *
        Real.cos (frequency T n * t) ^ 2 : ℝ)) := by
      change _ = ((∫ t in Ioo 0 T, Real.sqrt (2 / T) ^ 2 * Real.cos (frequency T n * t) ^ 2 : ℝ) : 𝕜)
      rw [← integral_ofReal]
      apply integral_congr_ae
      filter_upwards [(cosine_memLp 𝕜 T n).coeFn_toLp] with t ht
      change rightVector 𝕜 T n t = cosineFunction 𝕜 T n t at ht
      rw [ht]
      simp only [cosineFunction, RCLike.inner_apply, RCLike.conj_ofReal,
        RCLike.ofReal_pow, map_mul, RCLike.conj_ofReal]
      ring
    _ = 1 := by
      rw [integral_const_mul, hc, Real.sq_sqrt (by positivity)]
      simp only [map_mul, map_div₀, map_ofNat]
      field_simp [(map_ne_zero (algebraMap ℝ 𝕜)).mpr hT.ne']

lemma sigma_strictAnti (T : ℝ) (hT : 0 < T) : StrictAnti (sigma T) := by
  intro m n hmn
  apply div_lt_div_of_pos_left hT (by positivity)
  apply mul_lt_mul_of_pos_right _ Real.pi_pos
  have hc : (m : ℝ) < n := Nat.cast_lt.mpr hmn
  linarith

/-- The displayed trigonometric vectors are unit orthogonal families.
Completeness is a separate assertion. -/
theorem orthonormal_systems (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (hT : 0 < T) :
    Orthonormal 𝕜 (rightVector 𝕜 T) ∧ Orthonormal 𝕜 (leftVector 𝕜 T) := by
  classical
  have hrel (m n : ℕ) :
      (sigma T m : 𝕜) * inner 𝕜 (leftVector 𝕜 T m) (leftVector 𝕜 T n) =
        (sigma T n : 𝕜) * inner 𝕜 (rightVector 𝕜 T m) (rightVector 𝕜 T n) := by
    have h := (operator 𝕜 T).adjoint_inner_right (rightVector 𝕜 T m) (leftVector 𝕜 T n)
    rw [(singular_identities 𝕜 T hT n).2,
      (singular_identities 𝕜 T hT m).1, inner_smul_right, inner_smul_left,
      RCLike.conj_ofReal] at h
    exact h.symm
  have hrel' (m n : ℕ) :
      (sigma T m : 𝕜) * inner 𝕜 (rightVector 𝕜 T m) (rightVector 𝕜 T n) =
        (sigma T n : 𝕜) * inner 𝕜 (leftVector 𝕜 T m) (leftVector 𝕜 T n) := by
    have h := (operator 𝕜 T).adjoint_inner_left (rightVector 𝕜 T n) (leftVector 𝕜 T m)
    rw [(singular_identities 𝕜 T hT m).2,
      (singular_identities 𝕜 T hT n).1, inner_smul_right, inner_smul_left,
      RCLike.conj_ofReal] at h
    exact h
  have hzero (m n : ℕ) (hmn : m ≠ n) :
      inner 𝕜 (rightVector 𝕜 T m) (rightVector 𝕜 T n) = 0 := by
    have hneq : (sigma T m : 𝕜) ^ 2 ≠ (sigma T n : 𝕜) ^ 2 := by
      intro heq
      have heq' : sigma T m ^ 2 = sigma T n ^ 2 := by exact_mod_cast heq
      have hpos := sigma_pos T hT m
      have hpos' := sigma_pos T hT n
      have he : sigma T m = sigma T n := by nlinarith
      exact hmn ((sigma_strictAnti T hT).injective he)
    apply (mul_eq_zero.mp (show ((sigma T m : 𝕜) ^ 2 - (sigma T n : 𝕜) ^ 2) *
      inner 𝕜 (rightVector 𝕜 T m) (rightVector 𝕜 T n) = 0 from ?_)).resolve_left
        (sub_ne_zero.mpr hneq)
    calc
      _ = (sigma T m : 𝕜) * ((sigma T m : 𝕜) *
          inner 𝕜 (rightVector 𝕜 T m) (rightVector 𝕜 T n)) -
          (sigma T n : 𝕜) * ((sigma T n : 𝕜) *
          inner 𝕜 (rightVector 𝕜 T m) (rightVector 𝕜 T n)) := by ring
      _ = 0 := by rw [hrel' m n, ← hrel m n]; ring
  constructor <;> apply orthonormal_iff_ite.mpr <;> intro m n
  · split_ifs with hmn
    · subst n; exact rightVector_inner_self 𝕜 T hT m
    · exact hzero m n hmn
  · split_ifs with hmn
    · subst n
      have h := hrel m m
      rw [rightVector_inner_self 𝕜 T hT m, mul_one] at h
      apply mul_left_cancel₀ (RCLike.ofReal_ne_zero.mpr (sigma_pos T hT m).ne')
      simpa using h
    · have h := hrel m n
      rw [hzero m n hmn, mul_zero] at h
      exact (mul_eq_zero.mp h).resolve_left
        (RCLike.ofReal_ne_zero.mpr (sigma_pos T hT m).ne')

lemma norm_lower_bound (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (hT : 0 < T) :
    2 * T / Real.pi ≤ ‖operator 𝕜 T‖ := by
  obtain ⟨he, hf⟩ := orthonormal_systems 𝕜 T hT
  have h := (operator 𝕜 T).le_opNorm (rightVector 𝕜 T 0)
  rw [(singular_identities 𝕜 T hT 0).1, norm_smul, RCLike.norm_ofReal,
    abs_of_pos (sigma_pos T hT 0), he.norm_eq_one, hf.norm_eq_one, mul_one, mul_one,
    (singular_values T hT).2.2.2] at h
  exact h
/-- A nonzero eigenvalue would yield a continuous primitive solving a
homogeneous scalar ODE with zero initial value. -/
lemma eigenvector_eq_zero (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (hT : 0 < T)
    (z : 𝕜) (hz : z ≠ 0) (u : Space 𝕜 T) (hu : operator 𝕜 T u = z • u) :
    u = 0 := by
  let g : ℝ → 𝕜 := (Ioo 0 T).indicator (u : ℝ → 𝕜)
  have hg : Integrable g :=
    (integrable_indicator_iff measurableSet_Ioo).mpr
      (MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp u))
  let F : ℝ → 𝕜 := fun t => ∫ s in 0..t, g s
  have hF : Continuous F := hg.continuous_primitive 0
  have hFI (t : ℝ) (ht : t ∈ Icc 0 T) : F t = ∫ s in Ioo 0 t, u s := by
    dsimp [F]
    rw [intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact indicator_of_mem (show s ∈ Ioo 0 T from ⟨hs.1, hs.2.trans_le ht.2⟩) _
  have hue : (u : ℝ → 𝕜) =ᵐ[intervalMeasure T] fun t => z⁻¹ * F t := by
    filter_upwards [integral_formula 𝕜 T hT u, Lp.coeFn_smul z u,
      ae_restrict_mem measurableSet_Ioo] with t ht hs hmem
    rw [hu, hs, Pi.smul_apply, smul_eq_mul] at ht
    rw [hFI t ⟨hmem.1.le, hmem.2.le⟩, ← ht, inv_mul_cancel_left₀ hz]
  let q : ℝ → 𝕜 := fun t => z⁻¹ * F t
  have hq : Continuous q := continuous_const.mul hF
  let H : ℝ → 𝕜 := fun t => ∫ s in 0..t, q s
  have hH : Continuous H :=
    intervalIntegral.continuous_primitive (fun a b => hq.intervalIntegrable a b) 0
  have hHF (t : ℝ) (ht : t ∈ Icc 0 T) : H t = F t := by
    rw [hFI t ht]
    dsimp [H]
    rw [intervalIntegral.integral_of_le ht.1, integral_Ioc_eq_integral_Ioo]
    exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset
      (show Ioo 0 t ⊆ Ioo 0 T from fun s hs => ⟨hs.1, hs.2.trans_le ht.2⟩) hue.symm)
  have hzero : ∀ t ∈ Icc 0 T, H t = 0 := by
    apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
      (f' := q) (K := ‖z⁻¹‖) hH.continuousOn
    · intro t ht
      exact (intervalIntegral.integral_hasDerivAt_right (hq.intervalIntegrable 0 t)
        hq.stronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt).hasDerivWithinAt
    · simp [H]
    · intro t ht
      change ‖z⁻¹ * F t‖ ≤ ‖z⁻¹‖ * ‖H t‖
      rw [hHF t ⟨ht.1, ht.2.le⟩, norm_mul]
  apply Lp.ext
  filter_upwards [hue, ae_restrict_mem measurableSet_Ioo, Lp.coeFn_zero 𝕜 2 (intervalMeasure T)]
    with t ht hmem hz0
  rw [ht, ← hHF t ⟨hmem.1.le, hmem.2.le⟩, hzero t ⟨hmem.1.le, hmem.2.le⟩,
    mul_zero, hz0]
  rfl

lemma zero_mem_spectrum (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (hT : 0 < T) :
    (0 : 𝕜) ∈ spectrum 𝕜 (operator 𝕜 T) := by
  apply (spectrum.zero_mem_iff 𝕜).mpr
  rintro ⟨U, hU⟩
  obtain ⟨he, hf⟩ := orthonormal_systems 𝕜 T hT
  have hbound (n : ℕ) : 1 ≤ ‖(↑U⁻¹ : Space 𝕜 T →L[𝕜] Space 𝕜 T)‖ * sigma T n := by
    have hinv : (↑U⁻¹ : Space 𝕜 T →L[𝕜] Space 𝕜 T) (operator 𝕜 T (rightVector 𝕜 T n)) =
        rightVector 𝕜 T n := by
      have h := congrArg (fun A : Space 𝕜 T →L[𝕜] Space 𝕜 T => A (rightVector 𝕜 T n)) U.inv_mul
      simpa only [hU, mul_apply_eq_comp, one_apply_eq_self] using h
    have h := (↑U⁻¹ : Space 𝕜 T →L[𝕜] Space 𝕜 T).le_opNorm
      (operator 𝕜 T (rightVector 𝕜 T n))
    rw [hinv, he.norm_eq_one, (singular_identities 𝕜 T hT n).1, norm_smul,
      RCLike.norm_ofReal, abs_of_pos (sigma_pos T hT n), hf.norm_eq_one, mul_one] at h
    exact h
  have hlim := (singular_values T hT).2.2.1.const_mul
    ‖(↑U⁻¹ : Space 𝕜 T →L[𝕜] Space 𝕜 T)‖
  have hbad : (1 : ℝ) ≤ 0 := by
    simpa only [mul_zero] using ge_of_tendsto hlim (Eventually.of_forall hbound)
  norm_num at hbad

theorem spectrum_formula : SpectrumFormula := by
  intro 𝕜 _ T hT
  apply Set.Subset.antisymm
  · intro z hz
    by_contra hne
    have hz0 : z ≠ 0 := by simpa only [mem_singleton_iff] using hne
    obtain ⟨u, hu0, hu⟩ :=
      (Fredholm.compact_nonzero_spectrum_iff_eigenvalue
        (operator 𝕜 T) (compact 𝕜 T hT) z hz0).mp hz
    exact hu0 (eigenvector_eq_zero 𝕜 T hT z hz0 u hu)
  · intro z hz
    rw [mem_singleton_iff.mp hz]
    exact zero_mem_spectrum 𝕜 T hT
lemma reflection_preserves_measure (T : ℝ) :
    MeasurePreserving (fun t : ℝ => T - t) (intervalMeasure T) (intervalMeasure T) := by
  have hs : (fun t : ℝ => T - t) ⁻¹' Ioo 0 T = Ioo 0 T := by
    ext t
    simp only [mem_preimage, mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  simpa only [hs] using (volume.measurePreserving_sub_left T).restrict_preimage (s := Ioo 0 T) measurableSet_Ioo

/-- Reflection at the midpoint transports cosine modes to sine modes, with
an alternating sign. -/
lemma left_complete_of_right_complete (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (hT : 0 < T)
    (he : (Submodule.span 𝕜 (range (rightVector 𝕜 T))).topologicalClosure = ⊤) :
    (Submodule.span 𝕜 (range (leftVector 𝕜 T))).topologicalClosure = ⊤ := by
  let R : Space 𝕜 T →ₗᵢ[𝕜] Space 𝕜 T :=
    Lp.compMeasurePreservingₗᵢ 𝕜 (fun t : ℝ => T - t) (reflection_preserves_measure T)
  have hinvol (x : Space 𝕜 T) : R (R x) = x := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (R x) (reflection_preserves_measure T),
      (reflection_preserves_measure T).quasiMeasurePreserving.ae_eq_comp
        (Lp.coeFn_compMeasurePreserving x (reflection_preserves_measure T))] with t ht ht'
    change R (R x) t = R x (T - t) at ht
    change R x (T - t) = x (T - (T - t)) at ht'
    rw [ht, ht', sub_sub_cancel]
  have hmode (n : ℕ) : R (rightVector 𝕜 T n) = (-1 : 𝕜) ^ n • leftVector 𝕜 T n := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (rightVector 𝕜 T n)
        (reflection_preserves_measure T),
      (reflection_preserves_measure T).quasiMeasurePreserving.ae_eq_comp
        (cosine_memLp 𝕜 T n).coeFn_toLp,
      Lp.coeFn_smul ((-1 : 𝕜) ^ n) (leftVector 𝕜 T n),
      (sine_memLp 𝕜 T n).coeFn_toLp] with t ht hc hs hf
    change R (rightVector 𝕜 T n) t = rightVector 𝕜 T n (T - t) at ht
    change rightVector 𝕜 T n (T - t) = cosineFunction 𝕜 T n (T - t) at hc
    change leftVector 𝕜 T n t = sineFunction 𝕜 T n t at hf
    rw [ht, hc, hs, Pi.smul_apply, hf, smul_eq_mul]
    have hend : Real.sin (frequency T n * T) = (-1 : ℝ) ^ n := by
      rw [frequency, div_mul_cancel₀ _ hT.ne']
      have heq : ((n : ℝ) + 1 / 2) * Real.pi = n * Real.pi + Real.pi / 2 := by ring
      rw [heq, Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]
    simp only [cosineFunction, sineFunction, mul_sub, Real.cos_sub,
      cosine_at_right_endpoint T hT n, hend, zero_mul, zero_add,
      RCLike.ofReal_mul, RCLike.ofReal_pow, RCLike.ofReal_neg, RCLike.ofReal_one]
    ring
  have hsurj : Function.Surjective R := fun x => ⟨R x, hinvol x⟩
  have htop := DenseRange.topologicalClosure_map_submodule
    (f := R.toContinuousLinearMap) (show DenseRange R.toContinuousLinearMap from hsurj.denseRange) he
  have hmap : (Submodule.span 𝕜 (range (rightVector 𝕜 T))).map R.toLinearMap ≤
      Submodule.span 𝕜 (range (leftVector 𝕜 T)) := by
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    change R (rightVector 𝕜 T n) ∈ _
    rw [hmode]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self n))
  apply top_unique
  rw [← htop]
  exact Submodule.topologicalClosure_mono hmap

/-- Reflection reduces completeness of both orthonormal systems to completeness
of the cosine family. -/
theorem complete_systems_of_right_complete
    (h : ∀ (𝕜 : Type) [RCLike 𝕜] (T : ℝ), 0 < T →
      (Submodule.span 𝕜 (range (rightVector 𝕜 T))).topologicalClosure = ⊤) :
    CompleteOrthonormalSystems := by
  intro 𝕜 _ T hT
  obtain ⟨he, hf⟩ := orthonormal_systems 𝕜 T hT
  exact ⟨he, hf, h 𝕜 T hT, left_complete_of_right_complete 𝕜 T hT (h 𝕜 T hT)⟩

/-! Completeness by weighted polynomial approximation. The coordinate
`cos (πt/T)` separates points on the closed interval. Its polynomial algebra
is uniformly dense, and multiplication by `cos (πt/(2T))` has dense L² range
because that weight is nonzero on the open interval. -/
namespace Completeness

lemma polynomial_coordinate_dense {𝕜 X : Type*} [RCLike 𝕜]
    [TopologicalSpace X] [CompactSpace X] (c : C(X, 𝕜))
    (hc : Function.Injective c) (hstar : star c = c) :
    Dense (Set.range (Polynomial.aeval c : Polynomial 𝕜 → C(X, 𝕜))) := by
  let A : StarSubalgebra 𝕜 C(X, 𝕜) := StarAlgebra.adjoin 𝕜 {c}
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    refine ⟨c, ⟨c, ?_, rfl⟩, ?_⟩
    · exact StarAlgebra.subset_adjoin 𝕜 {c} (mem_singleton c)
    · exact fun h => hxy (hc h)
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have heq : A.toSubalgebra = (Polynomial.aeval c).range := by
    dsimp [A]
    rw [StarAlgebra.adjoin_toSubalgebra, Set.star_singleton, hstar, union_self,
      Algebra.adjoin_singleton_eq_range_aeval]
  rw [dense_iff_closure_eq]
  change closure ((Polynomial.aeval c).range : Set C(X, 𝕜)) = univ
  rw [← heq]
  exact congrArg (fun B : StarSubalgebra 𝕜 C(X, 𝕜) => (B : Set C(X, 𝕜))) htop

lemma cosine_coordinate_injective (T : ℝ) (hT : 0 < T) :
    Function.Injective (fun t : Icc (0 : ℝ) T => Real.cos (Real.pi / T * t)) := by
  intro x y hxy
  have hmem (t : Icc (0 : ℝ) T) : Real.pi / T * (t : ℝ) ∈ Icc 0 Real.pi := by
    constructor
    · exact mul_nonneg (div_pos Real.pi_pos hT).le t.2.1
    · calc
        Real.pi / T * (t : ℝ) ≤ Real.pi / T * T :=
          mul_le_mul_of_nonneg_left t.2.2 (by positivity)
        _ = Real.pi := div_mul_cancel₀ _ hT.ne'
  apply Subtype.ext
  exact mul_left_cancel₀ (div_pos Real.pi_pos hT).ne' (Real.injOn_cos (hmem x) (hmem y) hxy)


def cosineCoordinate (𝕜 : Type*) [RCLike 𝕜] (T : ℝ) : C(Icc (0 : ℝ) T, 𝕜) :=
  ⟨fun t => (Real.cos (Real.pi / T * (t : ℝ)) : 𝕜), by fun_prop⟩

lemma cosine_polynomials_dense (𝕜 : Type*) [RCLike 𝕜] (T : ℝ) (hT : 0 < T) :
    Dense (range (Polynomial.aeval (cosineCoordinate 𝕜 T) :
      Polynomial 𝕜 → C(Icc (0 : ℝ) T, 𝕜))) := by
  apply polynomial_coordinate_dense
  · intro x y hxy
    apply cosine_coordinate_injective T hT
    exact RCLike.ofReal_injective hxy
  · ext t
    exact RCLike.conj_ofReal _

lemma half_cosine_pos (T : ℝ) (hT : 0 < T) (t : ℝ) (ht : t ∈ Ioo 0 T) :
    0 < Real.cos (Real.pi / T * t / 2) := by
  apply Real.cos_pos_of_mem_Ioo
  have h0 : 0 < Real.pi / T * t := mul_pos (div_pos Real.pi_pos hT) ht.1
  have h1 : Real.pi / T * t < Real.pi := by
    calc
      _ < Real.pi / T * T := mul_lt_mul_of_pos_left ht.2 (div_pos Real.pi_pos hT)
      _ = _ := div_mul_cancel₀ _ hT.ne'
  constructor <;> linarith [Real.pi_pos]

variable {α 𝕜 : Type*} [TopologicalSpace α] [NormalSpace α]
  [MeasurableSpace α] [BorelSpace α] [RCLike 𝕜]
  [SecondCountableTopologyEither α 𝕜]
  {μ : Measure α} [IsFiniteMeasure μ] [μ.WeaklyRegular]

lemma eq_zero_of_forall_boundedContinuous_inner (u : Lp 𝕜 2 μ)
    (h : ∀ f : α →ᵇ 𝕜,
      inner 𝕜 (BoundedContinuousFunction.toLp 2 μ 𝕜 f) u = 0) : u = 0 := by
  have hz : inner 𝕜 u u = 0 :=
    (BoundedContinuousFunction.toLp_denseRange 𝕜 μ 𝕜 (by simp)).induction_on (p := fun x => inner 𝕜 x u = 0) u
      (isClosed_eq (continuous_id.inner continuous_const) continuous_const) h
  exact inner_self_eq_zero.mp hz

lemma eq_zero_of_forall_weighted_boundedContinuous_inner
    (w : α →ᵇ 𝕜) (hw : ∀ᵐ t ∂μ, w t ≠ 0) (u : Lp 𝕜 2 μ)
    (h : ∀ f : α →ᵇ 𝕜,
      inner 𝕜 (BoundedContinuousFunction.toLp 2 μ 𝕜 (w * f)) u = 0) : u = 0 := by
  have hg : MemLp (fun t => star (w t) * u t) 2 μ :=
    (star w).memLp_top.fun_mul (Lp.memLp u)
  let g : Lp 𝕜 2 μ := hg.toLp _
  have hgz : g = 0 := eq_zero_of_forall_boundedContinuous_inner g fun f => by
    rw [L2.inner_def]
    calc
      _ = inner 𝕜 (BoundedContinuousFunction.toLp 2 μ 𝕜 (w * f)) u := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 μ 𝕜 f,
          BoundedContinuousFunction.coeFn_toLp 2 μ 𝕜 (w * f), hg.coeFn_toLp] with t hf hwf hgt
        change g t = _ at hgt
        rw [hf, hwf, hgt]
        simp [RCLike.inner_apply, mul_comm, mul_left_comm]
      _ = 0 := h f
  apply Lp.ext
  have hga : (g : α → 𝕜) =ᵐ[μ] 0 := by rw [hgz]; exact Lp.coeFn_zero 𝕜 2 μ
  filter_upwards [hg.coeFn_toLp, hga, hw, Lp.coeFn_zero 𝕜 2 μ] with t hgt hzt hwt h0t
  change g t = _ at hgt
  rw [h0t]
  have : star (w t) * u t = 0 := hgt.symm.trans hzt
  exact (mul_eq_zero.mp this).resolve_left (star_ne_zero.mpr hwt)


/-- Extend a continuous function on a compact interval by freezing its endpoints. -/
def extendIcc {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ} (hab : a ≤ b)
    (f : C(Icc a b, 𝕜)) : ℝ →ᵇ 𝕜 :=
  (BoundedContinuousFunction.mkOfCompact f).compContinuous
    ⟨projIcc a b hab, continuous_projIcc⟩

lemma continuous_extendIcc {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ} (hab : a ≤ b) :
    Continuous (extendIcc (𝕜 := 𝕜) hab) := by
  exact (BoundedContinuousFunction.continuous_compContinuous
    (⟨projIcc a b hab, continuous_projIcc⟩ : C(ℝ, Icc a b))).comp
      (ContinuousMap.linearIsometryBoundedOfCompact (Icc a b) 𝕜 𝕜).continuous

@[simp] lemma extendIcc_apply {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ} (hab : a ≤ b)
    (f : C(Icc a b, 𝕜)) (t : ℝ) : extendIcc hab f t = f (projIcc a b hab t) := rfl

lemma closed_submodule_eq_top_of_weighted_polynomials
    {𝕜 : Type*} [RCLike 𝕜] {a b : ℝ} (hab : a ≤ b)
    {μ : Measure ℝ} [IsFiniteMeasure μ] [μ.WeaklyRegular]
    (hμ : ∀ᵐ t ∂μ, t ∈ Icc a b) (w : ℝ →ᵇ 𝕜) (hw : ∀ᵐ t ∂μ, w t ≠ 0)
    (c : C(Icc a b, 𝕜))
    (hdense : Dense (range (Polynomial.aeval c : Polynomial 𝕜 → C(Icc a b, 𝕜))))
    (M : Submodule 𝕜 (Lp 𝕜 2 μ)) (hM : IsClosed (M : Set (Lp 𝕜 2 μ)))
    (hmem : ∀ p : Polynomial 𝕜,
      BoundedContinuousFunction.toLp 2 μ 𝕜 (w * extendIcc hab (Polynomial.aeval c p)) ∈ M) :
    M = ⊤ := by
  let F : C(Icc a b, 𝕜) → Lp 𝕜 2 μ := fun f =>
    BoundedContinuousFunction.toLp 2 μ 𝕜 (w * extendIcc hab f)
  have hF : Continuous F :=
    (BoundedContinuousFunction.toLp 2 μ 𝕜).continuous.comp
      (continuous_const.mul (continuous_extendIcc hab))
  have hall : ∀ f : C(Icc a b, 𝕜), F f ∈ M := fun f =>
    DenseRange.induction_on hdense (p := fun x => F x ∈ M) f (hM.preimage hF) hmem
  have hbcf : ∀ f : ℝ →ᵇ 𝕜,
      BoundedContinuousFunction.toLp 2 μ 𝕜 (w * f) ∈ M := by
    intro f
    let fr : C(Icc a b, 𝕜) := ⟨fun t => f t, f.continuous.comp continuous_subtype_val⟩
    have heq : F fr = BoundedContinuousFunction.toLp 2 μ 𝕜 (w * f) := by
      apply Lp.ext
      filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 μ 𝕜 (w * extendIcc hab fr),
        BoundedContinuousFunction.coeFn_toLp 2 μ 𝕜 (w * f), hμ] with t ht ht' htmem
      change F fr t = _ at ht
      rw [ht, ht']
      simp [extendIcc_apply, projIcc_of_mem hab htmem, fr]
    rw [← heq]
    exact hall fr
  have hclosure : M.topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro u hu
    exact eq_zero_of_forall_weighted_boundedContinuous_inner w hw u fun f =>
      M.inner_right_of_mem_orthogonal (hbcf f) hu
  have heq : M.topologicalClosure = M := by
    exact SetLike.coe_injective hM.closure_eq
  rwa [heq] at hclosure

lemma half_cosine_ne_zero {𝕜 : Type*} [RCLike 𝕜] (T : ℝ) (hT : 0 < T)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    (Real.cos (Real.pi / T * t / 2) : 𝕜) ≠ 0 := by
  have hangle : Real.pi / T * t / 2 ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have hpos : 0 < Real.pi / T * t := mul_pos (div_pos Real.pi_pos hT) ht.1
    have hlt : Real.pi / T * t < Real.pi := by
      calc
        _ < Real.pi / T * T := mul_lt_mul_of_pos_left ht.2 (div_pos Real.pi_pos hT)
        _ = Real.pi := div_mul_cancel₀ _ hT.ne'
    constructor <;> linarith [Real.pi_pos]
  exact_mod_cast (Real.cos_pos_of_mem_Ioo hangle).ne'

lemma half_cos_recurrence (x : ℝ) (n : ℕ) :
    2 * Real.cos x * Real.cos (((n : ℝ) + 1 / 2) * x) =
      Real.cos ((((n : ℝ) + 1 / 2) + 1) * x) +
      Real.cos ((((n : ℝ) + 1 / 2) - 1) * x) := by
  have h := Real.cos_add_cos (((n : ℝ) + 1 / 2) * x + x)
      (((n : ℝ) + 1 / 2) * x - x)
  have h1 : ((((n : ℝ) + 1 / 2) * x + x) +
      (((n : ℝ) + 1 / 2) * x - x)) / 2 = ((n : ℝ) + 1 / 2) * x := by ring
  have h2 : ((((n : ℝ) + 1 / 2) * x + x) -
      (((n : ℝ) + 1 / 2) * x - x)) / 2 = x := by ring
  rw [h1, h2] at h
  have h3 : ((n : ℝ) + 1 / 2) * x + x = (((n : ℝ) + 1 / 2) + 1) * x := by ring
  have h4 : ((n : ℝ) + 1 / 2) * x - x = (((n : ℝ) + 1 / 2) - 1) * x := by ring
  rw [h3, h4] at h
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h.symm

lemma half_cos_recurrence_zero (x : ℝ) :
    2 * Real.cos x * Real.cos (x / 2) =
      Real.cos (((1 : ℝ) + 1 / 2) * x) + Real.cos (x / 2) := by
  have h := half_cos_recurrence x 0
  norm_num at h
  convert h using 1 <;> congr 1 <;> ring_nf

lemma half_cos_recurrence_succ (x : ℝ) (n : ℕ) :
    2 * Real.cos x * Real.cos ((((n+1 : ℕ) : ℝ) + 1 / 2) * x) =
      Real.cos ((((n+2 : ℕ) : ℝ) + 1 / 2) * x) +
      Real.cos (((n : ℝ) + 1 / 2) * x) := by
  convert half_cos_recurrence x (n+1) using 1
  push_cast
  ring_nf

lemma weighted_polynomial_mem_span {α : Type*} (𝕜 : Type*) [RCLike 𝕜]
    (x : α → ℝ) (p : Polynomial 𝕜) :
    (fun t => (Real.cos (x t / 2) : 𝕜) * p.eval (Real.cos (x t) : 𝕜)) ∈
      Submodule.span 𝕜 (range (fun n : ℕ => fun t =>
        (Real.cos (((n : ℝ) + 1 / 2) * x t) : 𝕜))) := by
  let c : α → 𝕜 := fun t => (Real.cos (x t) : 𝕜)
  let f : ℕ → α → 𝕜 := fun n t => (Real.cos (((n : ℝ) + 1 / 2) * x t) : 𝕜)
  let M : Submodule 𝕜 (α → 𝕜) := Submodule.span 𝕜 (range f)
  have hcf (n : ℕ) : c * f n ∈ M := by
    cases n with
    | zero =>
      have heq : c * f 0 = (2 : 𝕜)⁻¹ • (f 1 + f 0) := by
        funext t
        have h := half_cos_recurrence_zero (x t)
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        dsimp [c, f]
        have h' := congrArg (fun r : ℝ => (r : 𝕜)) h
        push_cast at h'
        norm_num at h' ⊢
        have he : (1 / 2 : ℝ) * x t = x t / 2 := by ring
        rw [he]
        linear_combination (1 / 2 : 𝕜) * h'
      rw [heq]
      exact M.smul_mem _ (M.add_mem (Submodule.subset_span (mem_range_self 1))
        (Submodule.subset_span (mem_range_self 0)))
    | succ n =>
      have heq : c * f (n+1) = (2 : 𝕜)⁻¹ • (f (n+2) + f n) := by
        funext t
        have h := congrArg (fun r : ℝ => (r : 𝕜)) (half_cos_recurrence_succ (x t) n)
        push_cast at h
        simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
        dsimp [c, f]
        push_cast
        linear_combination (1 / 2 : 𝕜) * h
      rw [heq]
      exact M.smul_mem _ (M.add_mem (Submodule.subset_span (mem_range_self (n+2)))
        (Submodule.subset_span (mem_range_self n)))
  have hmul {g : α → 𝕜} (hg : g ∈ M) : c * g ∈ M := by
    induction hg using Submodule.span_induction with
    | mem g hg => obtain ⟨n, rfl⟩ := hg; exact hcf n
    | zero => simp
    | add g h _ _ hg hh => simpa only [mul_add] using M.add_mem hg hh
    | smul a g _ hg => simpa only [mul_smul_comm] using M.smul_mem a hg
  have hpow (n : ℕ) : c ^ n * f 0 ∈ M := by
    induction n with
    | zero => simpa using (Submodule.subset_span (mem_range_self 0) : f 0 ∈ M)
    | succ n ih => simpa only [pow_succ', mul_assoc] using hmul ih
  change (fun t => (Real.cos (x t / 2) : 𝕜) * p.eval (Real.cos (x t) : 𝕜)) ∈ M
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [Polynomial.eval_add, mul_add, ← Pi.add_def] using M.add_mem hp hq
  | monomial n a =>
    have heq : (fun t => (Real.cos (x t / 2) : 𝕜) * (Polynomial.monomial n a).eval
        (Real.cos (x t) : 𝕜)) = a • (c ^ n * f 0) := by
      funext t
      simp only [Polynomial.eval_monomial, Pi.smul_apply, Pi.mul_apply, Pi.pow_apply,
        smul_eq_mul, c, f]
      norm_num
      have he : (1 / 2 : ℝ) * x t = x t / 2 := by ring
      rw [he]
      ring
    rw [heq]
    exact M.smul_mem a (hpow n)

open MeasureTheory
open scoped ENNReal

lemma toLp_mem_of_mem_span {α : Type*} [MeasurableSpace α] (𝕜 : Type*) [RCLike 𝕜]
    (μ : Measure α) (M : Submodule 𝕜 (Lp 𝕜 2 μ)) (f : ℕ → α → 𝕜)
    (hf : ∀ n, ∃ v ∈ M, (v : α → 𝕜) =ᵐ[μ] f n)
    {g : α → 𝕜} (hg : MemLp g 2 μ) (hspan : g ∈ Submodule.span 𝕜 (range f)) :
    hg.toLp g ∈ M := by
  let P : Submodule 𝕜 (α → 𝕜) :=
    { carrier := {g | ∃ v ∈ M, (v : α → 𝕜) =ᵐ[μ] g}
      zero_mem' := ⟨0, M.zero_mem, Lp.coeFn_zero _ _ _⟩
      add_mem' := by
        rintro g h ⟨u, hu, heu⟩ ⟨v, hv, hev⟩
        exact ⟨u + v, M.add_mem hu hv, (Lp.coeFn_add u v).trans (heu.add hev)⟩
      smul_mem' := by
        rintro a g ⟨u, hu, heu⟩
        exact ⟨a • u, M.smul_mem a hu, (Lp.coeFn_smul a u).trans (heu.const_smul a)⟩ }
  have hle : Submodule.span 𝕜 (range f) ≤ P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact hf n
  obtain ⟨v, hv, hev⟩ := hle hspan
  have heq : hg.toLp g = v := Lp.ext (hg.coeFn_toLp.trans hev.symm)
  exact heq.symm ▸ hv

open ExpandedFA.PartV.VolterraSingularSystemSpec

lemma weighted_polynomial_toLp_mem (𝕜 : Type) [RCLike 𝕜]
    (T : ℝ) (hT : 0 < T) (p : Polynomial 𝕜)
    (hg : MemLp (fun t => (Real.cos (Real.pi / T * t / 2) : 𝕜) *
      p.eval (Real.cos (Real.pi / T * t) : 𝕜)) 2 (intervalMeasure T)) :
    hg.toLp _ ∈ Submodule.span 𝕜 (range (rightVector 𝕜 T)) := by
  apply toLp_mem_of_mem_span 𝕜 (intervalMeasure T)
    (Submodule.span 𝕜 (range (rightVector 𝕜 T)))
    (fun n t => (Real.cos (((n : ℝ) + 1 / 2) * (Real.pi / T * t)) : 𝕜))
  · intro n
    refine ⟨(Real.sqrt (2 / T) : 𝕜)⁻¹ • rightVector 𝕜 T n,
      Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self n)), ?_⟩
    filter_upwards [Lp.coeFn_smul (Real.sqrt (2 / T) : 𝕜)⁻¹ (rightVector 𝕜 T n),
      (cosine_memLp 𝕜 T n).coeFn_toLp] with t hs hc
    change rightVector 𝕜 T n t = cosineFunction 𝕜 T n t at hc
    rw [hs, Pi.smul_apply, smul_eq_mul, hc]
    simp only [cosineFunction, RCLike.ofReal_mul]
    have hb : (Real.sqrt (2 / T) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.mpr (div_pos (by norm_num) hT)))
    rw [inv_mul_cancel_left₀ hb]
    congr 2
    dsimp [frequency]
    ring
  · exact weighted_polynomial_mem_span 𝕜 (fun t : ℝ => Real.pi / T * t) p

end Completeness

/-- The half-integer cosine system is complete in the actual interval L² space. -/
theorem right_complete (𝕜 : Type) [RCLike 𝕜] (T : ℝ) (hT : 0 < T) :
    (Submodule.span 𝕜 (range (rightVector 𝕜 T))).topologicalClosure = ⊤ := by
  let a : C(Icc (0 : ℝ) T, 𝕜) :=
    ⟨fun t => (Real.cos (Real.pi / T * (t : ℝ) / 2) : 𝕜), by fun_prop⟩
  let w : ℝ →ᵇ 𝕜 := Completeness.extendIcc hT.le a
  have hμ : ∀ᵐ t ∂intervalMeasure T, t ∈ Icc (0 : ℝ) T :=
    (ae_restrict_mem measurableSet_Ioo).mono (fun _ ht => ⟨ht.1.le, ht.2.le⟩)
  have hw : ∀ᵐ t ∂intervalMeasure T, w t ≠ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simpa only [w, Completeness.extendIcc_apply, projIcc_of_mem hT.le ⟨ht.1.le, ht.2.le⟩,
      a, ContinuousMap.coe_mk, Subtype.coe_mk] using
      (Completeness.half_cosine_ne_zero (𝕜 := 𝕜) T hT t ht)
  apply Completeness.closed_submodule_eq_top_of_weighted_polynomials hT.le hμ w hw
    (Completeness.cosineCoordinate 𝕜 T) (Completeness.cosine_polynomials_dense 𝕜 T hT)
    _ (Submodule.isClosed_topologicalClosure _)
  intro p
  let v : Space 𝕜 T := BoundedContinuousFunction.toLp 2 (intervalMeasure T) 𝕜
    (w * Completeness.extendIcc hT.le (Polynomial.aeval (Completeness.cosineCoordinate 𝕜 T) p))
  have hv : (v : ℝ → 𝕜) =ᵐ[intervalMeasure T] fun t =>
      (Real.cos (Real.pi / T * t / 2) : 𝕜) * p.eval (Real.cos (Real.pi / T * t) : 𝕜) := by
    filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 (intervalMeasure T) 𝕜
      (w * Completeness.extendIcc hT.le (Polynomial.aeval (Completeness.cosineCoordinate 𝕜 T) p)),
      hμ] with t ht htmem
    change v t = _ at ht
    rw [ht]
    simp [w, Completeness.extendIcc_apply, projIcc_of_mem hT.le htmem,
      a, Completeness.cosineCoordinate]
  have hg := MemLp.ae_eq hv (Lp.memLp v)
  have heq : v = hg.toLp _ := Lp.ext (hv.trans hg.coeFn_toLp.symm)
  change v ∈ _
  rw [heq]
  exact Submodule.le_topologicalClosure _
    (Completeness.weighted_polynomial_toLp_mem 𝕜 T hT p hg)

/-- Both displayed systems are orthonormal bases, over ℝ and over ℂ. -/
theorem complete_systems : CompleteOrthonormalSystems :=
  complete_systems_of_right_complete right_complete

/-- The exact operator norm of integration on L²(0,T). -/
theorem norm_formula : NormFormula := norm_from_complete_systems complete_systems

/-- The two norm-convergent singular expansions for integration and its adjoint. -/
theorem singular_expansions : SingularExpansions :=
  expansions_from_complete_systems complete_systems

end ExpandedFA.PartV.VolterraSingularSystem
