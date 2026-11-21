import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C04.InverseCounterexamples
import MathGenome.Internal.MultivariableAnalysis.D04.C01.EuclideanInterfaces
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace D04.InverseCounterexamples
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C04.InverseCounterexamples
open Specs.D04.C04.InverseCounterexamples.Model

abbrev polarExpMap : E 2 → E 2 := Model.polarExp
abbrev circleMap : ℝ → E 2 := Model.circle
abbrev oscillatoryMap : ℝ → ℝ := Model.oscillatory

theorem interval_injective_monotone : interval_injective_monotoneType := by
  intro f a b hab hc hi
  exact hc.strictMonoOn_of_injOn_Ioo hab hi

theorem exponential_submersion : exponential_submersionType := by
  refine ⟨?_, Real.range_exp, ?_, ?_⟩
  · intro x y
    refine ⟨y / Real.exp x, ?_⟩
    rw [(Real.hasDerivAt_exp x).hasFDerivAt.fderiv]
    simp [div_eq_mul_inv, Real.exp_ne_zero]
  · rw [Real.range_exp]
    exact isOpen_Ioi
  · rw [Real.range_exp]
    intro h
    have : (0 : ℝ) ∈ Ioi 0 := h.symm ▸ mem_univ 0
    exact (lt_irrefl (0 : ℝ)) this

theorem cubic_failure : cubic_failureType := by
  have hd : HasDerivAt (fun x : ℝ => x ^ 3) 0 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).fun_pow 3
  refine ⟨?_, hd, ?_⟩
  · refine ⟨(Odd.strictMono_pow (by decide : Odd 3)).injective, ?_⟩
    intro y
    by_cases hy : 0 ≤ y
    · exact ⟨y ^ ((3 : ℝ)⁻¹), Real.rpow_inv_natCast_pow hy (by decide : (3 : ℕ) ≠ 0)⟩
    · refine ⟨-((-y) ^ ((3 : ℝ)⁻¹)), ?_⟩
      have hh : ((-y) ^ ((3 : ℝ)⁻¹)) ^ 3 = -y := by
        simpa using Real.rpow_inv_natCast_pow (le_of_lt (neg_pos.mpr (lt_of_not_ge hy)))
          (by decide : (3 : ℕ) ≠ 0)
      calc
        (-((-y) ^ ((3 : ℝ)⁻¹))) ^ 3 = -(((-y) ^ ((3 : ℝ)⁻¹)) ^ 3) := by ring
        _ = y := by rw [hh]; ring
  · intro g hg hdiff
    have hh : HasDerivAt (g ∘ (fun x : ℝ => x ^ 3)) (deriv g 0 * 0) 0 := by
      apply HasDerivAt.comp (0 : ℝ) ?_ hd
      simpa using hdiff.hasDerivAt
    have he : (g ∘ (fun x : ℝ => x ^ 3)) = id := funext hg
    have heq := (he ▸ hh).unique (hasDerivAt_id (0 : ℝ))
    norm_num at heq

theorem square_failure : square_failureType := by
  have hd : HasDerivAt (fun x : ℝ => x ^ 2) 0 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).fun_pow 2
  refine ⟨?_, ?_⟩
  · simpa using hd.hasFDerivAt.fderiv
  · intro U hU ⟨c, hc⟩
    obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hU
    have h0 := hc (hsub (Metric.mem_ball_self hε))
    have hp := hc (hsub (show ε / 2 ∈ Metric.ball (0 : ℝ) ε by
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity : 0 < ε / 2)]
      linarith))
    norm_num at h0
    rw [← h0] at hp
    nlinarith

theorem oscillatory_derivative_zero : oscillatory_derivative_zeroType := by
  have hlim : Tendsto (fun x : ℝ => x * Real.sin (1 / x)) (𝓝 0) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun x => norm_nonneg _) (fun x => ?_)
      (by simpa using (continuous_norm.tendsto (0 : ℝ)))
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (Real.abs_sin_le_one _)
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have hl : Tendsto (fun x : ℝ => 1 / 2 + x * Real.sin (1 / x))
      (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    simpa using (tendsto_const_nhds.add hlim).mono_left nhdsWithin_le_nhds
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx : x ≠ 0 := hx
  simp only [zero_add, smul_eq_mul, Model.oscillatory,
    ite_true, ite_eq_right hx, sub_zero]
  field_simp

theorem oscillatory_derivative_ne_zero : oscillatory_derivative_ne_zeroType := by
  intro x hx
  have hd := ((hasDerivAt_id x).div_const 2).add
    (((hasDerivAt_id x).fun_pow 2).mul
      (((hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx).sin))
  have hh : HasDerivAt (fun y : ℝ => y / 2 + y ^ 2 * Real.sin (1 / y))
      (1 / 2 + 2 * x * Real.sin (1 / x) - Real.cos (1 / x)) x := by
    convert hd using 1
    · rfl
    · simp only [id_eq, Pi.div_apply]
      norm_num
      field_simp
      ring
  apply hh.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with y hy
  simp [Model.oscillatory, hy]

theorem polar_smooth : ContDiff ℝ ∞ polarExp := by
  apply (contDiff_piLp 2).mpr
  intro i
  fin_cases i
  · change ContDiff ℝ ∞ (fun z : E 2 => Real.exp (z 0) * Real.cos (z 1))
    exact (contDiff_piLp_apply (i := (0 : Fin 2)) 2).exp.mul (contDiff_piLp_apply (i := (1 : Fin 2)) 2).cos
  · change ContDiff ℝ ∞ (fun z : E 2 => Real.exp (z 0) * Real.sin (z 1))
    exact (contDiff_piLp_apply (i := (0 : Fin 2)) 2).exp.mul (contDiff_piLp_apply (i := (1 : Fin 2)) 2).sin

theorem polar_jacobian : polar_jacobianType := by
  intro z
  have hd := polar_smooth.differentiable (by simp) z
  have h0 := ((PiLp.hasFDerivAt_apply 2 z 0).exp).mul
    ((PiLp.hasFDerivAt_apply 2 z 1).cos)
  have h1 := ((PiLp.hasFDerivAt_apply 2 z 0).exp).mul
    ((PiLp.hasFDerivAt_apply 2 z 1).sin)
  have hc0 := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (polarExp z) 0).comp z hd.hasFDerivAt
  have hc1 := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (polarExp z) 1).comp z hd.hasFDerivAt
  change HasFDerivAt (fun z : E 2 => Real.exp (z 0) * Real.cos (z 1)) _ z at hc0
  change HasFDerivAt (fun z : E 2 => Real.exp (z 0) * Real.sin (z 1)) _ z at hc1
  have hc0 := hc0.unique h0
  have hc1 := hc1.unique h1
  ext i j
  change D04.matrixOfLinearMap (fderiv ℝ polarExp z).toLinearMap i j = _
  rw [D04.matrixOfLinearMap_apply]
  fin_cases i <;> fin_cases j
  all_goals first
    | simpa [PiLp.proj_apply, D04.standardBasis_apply, mul_comm] using
        congrArg (fun L : E 2 →L[ℝ] ℝ => L (D04.standardBasis 2 0)) hc0
    | simpa [PiLp.proj_apply, D04.standardBasis_apply, mul_comm] using
        congrArg (fun L : E 2 →L[ℝ] ℝ => L (D04.standardBasis 2 1)) hc0
    | simpa [PiLp.proj_apply, D04.standardBasis_apply, mul_comm] using
        congrArg (fun L : E 2 →L[ℝ] ℝ => L (D04.standardBasis 2 0)) hc1
    | simpa [PiLp.proj_apply, D04.standardBasis_apply, mul_comm] using
        congrArg (fun L : E 2 →L[ℝ] ℝ => L (D04.standardBasis 2 1)) hc1

theorem polar_determinant : polar_determinantType := by
  intro z
  rw [polar_jacobian, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have ht := Real.sin_sq_add_cos_sq (z 1)
  have he : Real.exp (2 * z 0) = Real.exp (z 0) ^ 2 := by
    rw [two_mul, Real.exp_add, pow_two]
  constructor
  · rw [he]
    nlinarith [congrArg (fun t : ℝ => Real.exp (z 0) ^ 2 * t) ht]
  · nlinarith [sq_pos_of_pos (Real.exp_pos (z 0)),
      congrArg (fun t : ℝ => Real.exp (z 0) ^ 2 * t) ht]

theorem polar_periodic : polar_periodicType := by
  intro z
  ext i
  fin_cases i <;>
    simp [Model.polarExp, PiLp.add_apply, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem polar_global_failure : polar_global_failureType := by
  have hi : ¬ Function.Injective polarExp := by
    intro h
    have hh := h (polar_periodic (0 : E 2))
    have hh := congrArg (fun z : E 2 => z 1) hh
    simp only [PiLp.zero_apply, zero_add, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at hh
    exact (ne_of_gt Real.pi_pos) (by linarith)
  refine ⟨hi, fun ⟨g, hg⟩ => hi hg.injective, ?_⟩
  rintro ⟨z, hz⟩
  have h0 := congrArg (fun z : E 2 => z 0) hz
  have h1 := congrArg (fun z : E 2 => z 1) hz
  change Real.exp (z 0) * Real.cos (z 1) = 0 at h0
  change Real.exp (z 0) * Real.sin (z 1) = 0 at h1
  have hc := (mul_eq_zero.mp h0).resolve_left (Real.exp_ne_zero _)
  have hs := (mul_eq_zero.mp h1).resolve_left (Real.exp_ne_zero _)
  have := Real.sin_sq_add_cos_sq (z 1)
  simp [hc, hs] at this

private def polarDerivativeEquiv (z : E 2) : E 2 ≃L[ℝ] E 2 :=
  ((matrixOfLinearMap (fderiv ℝ polarExp z).toLinearMap).toLinearEquiv (standardBasis 2)
    (isUnit_iff_ne_zero.mpr (polar_determinant z).2.ne')).toContinuousLinearEquiv

private theorem polarDerivativeEquiv_coe (z : E 2) :
    (polarDerivativeEquiv z).toContinuousLinearMap = fderiv ℝ polarExp z := by
  apply ContinuousLinearMap.coe_injective
  apply LinearMap.ext
  intro v
  change matrixLinearEquiv 2 2 (matrixOfLinearMap (fderiv ℝ polarExp z).toLinearMap) v = _
  exact congrArg (fun L : E 2 →ₗ[ℝ] E 2 => L v)
    ((matrixLinearEquiv 2 2).apply_symm_apply _)

theorem polar_local_inverse : polar_local_inverseType := by
  intro a
  have hc := polar_smooth.contDiffAt (x := a)
  have hd : HasFDerivAt polarExp (polarDerivativeEquiv a).toContinuousLinearMap a := by
    rw [polarDerivativeEquiv_coe]
    exact (polar_smooth.differentiable (by simp) a).hasFDerivAt
  let e := hc.toOpenPartialHomeomorph polarExp hd (by simp)
  refine ⟨e, hc.mem_toOpenPartialHomeomorph_source hd (by simp), rfl, ?_⟩
  intro y hy
  apply (e.contDiffAt_symm hy (f₀' := polarDerivativeEquiv (e.symm y)) ?_
    polar_smooth.contDiffAt).contDiffWithinAt
  change HasFDerivAt polarExp (polarDerivativeEquiv (e.symm y)).toContinuousLinearMap (e.symm y)
  rw [polarDerivativeEquiv_coe]
  exact (polar_smooth.differentiable (by simp) _).hasFDerivAt

theorem circle_derivative : circle_derivativeType := by
  intro t
  have hdpi : HasDerivAt (fun s : ℝ => ![Real.cos s, Real.sin s])
      ![-Real.sin t, Real.cos t] t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact Real.hasDerivAt_cos t
    · exact Real.hasDerivAt_sin t
  have hd : HasDerivAt circle (WithLp.toLp 2 ![-Real.sin t, Real.cos t]) t :=
    by
      change HasDerivAt (WithLp.toLp 2 ∘ (fun s : ℝ => ![Real.cos s, Real.sin s])) _ t
      exact (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt t hdpi
  refine ⟨hd, ?_⟩
  rw [hd.hasFDerivAt.fderiv]
  intro x y hxy
  have h0 := congrArg (fun z : E 2 => z 0) hxy
  have h1 := congrArg (fun z : E 2 => z 1) hxy
  change x * (-Real.sin t) = y * (-Real.sin t) at h0
  change x * Real.cos t = y * Real.cos t at h1
  have ht := Real.sin_sq_add_cos_sq t
  by_cases hs : Real.sin t = 0
  · have hc : Real.cos t ≠ 0 := by intro hc; simp [hs, hc] at ht
    exact mul_right_cancel₀ hc h1
  · exact mul_right_cancel₀ (neg_ne_zero.mpr hs) h0

theorem circle_global_failure : circle_global_failureType := by
  have hp : Function.Periodic circle (2 * Real.pi) := by
    intro t
    ext i
    fin_cases i <;> simp [Model.circle, Real.sin_add_two_pi, Real.cos_add_two_pi]
  have hi : ¬ Function.Injective circle := by
    intro h
    have := h (hp 0)
    exact (ne_of_gt Real.pi_pos) (by linarith)
  exact ⟨hp, hi, fun he => hi he.injective⟩

theorem circle_local_embedding : circle_local_embeddingType := by
  intro a
  have hc : Continuous circle := continuous_iff_continuousAt.mpr (fun t => (circle_derivative t).1.continuousAt)
  have hi : InjOn circle (Icc (a - Real.pi / 2) (a + Real.pi / 2)) := by
    intro x hx y hy hxy
    have h0 := congrArg (fun z : E 2 => z 0) hxy
    have h1 := congrArg (fun z : E 2 => z 1) hxy
    change Real.cos x = Real.cos y at h0
    change Real.sin x = Real.sin y at h1
    have hs : Real.sin (x - a) = Real.sin (y - a) := by
      simp only [Real.sin_sub, h0, h1]
    have he := Real.strictMonoOn_sin.injOn
      (show x - a ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) by constructor <;> linarith [hx.1, hx.2])
      (show y - a ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) by constructor <;> linarith [hy.1, hy.2]) hs
    linarith
  have he := (hc.comp (continuous_subtype_val :
    Continuous (Subtype.val : Icc (a - Real.pi / 2) (a + Real.pi / 2) → ℝ))).isClosedEmbedding hi.injective
  refine ⟨Ioo (a - Real.pi / 2) (a + Real.pi / 2), isOpen_Ioo, ?_, ?_⟩
  · constructor <;> linarith [Real.pi_pos]
  · exact he.isEmbedding.comp (Topology.IsEmbedding.inclusion Ioo_subset_Icc_self)

private theorem reciprocal_pi_small (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      0 < 1 / ((n + 1 : ℕ) * Real.pi) ∧ 1 / ((n + 1 : ℕ) * Real.pi) < ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (ε * Real.pi))
  refine ⟨N, fun n hn => ?_⟩
  have hh : 1 / (ε * Real.pi) < ((n + 1 : ℕ) : ℝ) := by
    exact hN.trans (by exact_mod_cast Nat.lt_succ_of_le hn)
  have hnpos : 0 < ((n + 1 : ℕ) : ℝ) * Real.pi := by positivity
  refine ⟨one_div_pos.mpr hnpos, (div_lt_iff₀ hnpos).mpr ?_⟩
  have := (div_lt_iff₀ (mul_pos hε Real.pi_pos)).mp hh
  nlinarith

theorem oscillatory_derivative_values : oscillatory_derivative_valuesType := by
  have hd (k : ℕ) (hk : 0 < k) :
      deriv oscillatory (1 / (k * Real.pi)) = 1 / 2 - (-1 : ℝ) ^ k := by
    have hk' : (k : ℝ) * Real.pi ≠ 0 := mul_ne_zero (by exact_mod_cast hk.ne') Real.pi_ne_zero
    rw [(oscillatory_derivative_ne_zero _ (one_div_ne_zero hk')).deriv]
    simp only [one_div_one_div, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi, mul_zero, add_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    rw [hd (2 * (n + 1)) (by omega)]
    norm_num [pow_mul]
  · intro n
    rw [hd (2 * n + 1) (by omega)]
    norm_num [pow_add, pow_mul]
  · intro ε hε
    obtain ⟨N, hN⟩ := reciprocal_pi_small ε hε
    refine ⟨N, ?_⟩
    have hh := hN (2 * N + 1) (by omega)
    convert hh using 1
  · intro ε hε
    obtain ⟨N, hN⟩ := reciprocal_pi_small ε hε
    refine ⟨N + 1, ?_⟩
    have hh := hN (2 * (N + 1)) (by omega)
    convert hh using 1

theorem oscillatory_not_locally_injective : oscillatory_not_locally_injectiveType := by
  have hd : Differentiable ℝ oscillatory := by
    intro x
    by_cases hx : x = 0
    · subst x; exact oscillatory_derivative_zero.differentiableAt
    · exact (oscillatory_derivative_ne_zero x hx).differentiableAt
  intro U hU hi
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hU
  have hI : Ioo (-ε) ε ⊆ U := by
    intro x hx
    apply hsub
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt] using (show -ε < x ∧ x < ε from hx)
  obtain hm | hm := interval_injective_monotone oscillatory (-ε) ε (by linarith)
    hd.continuous.continuousOn (hi.mono hI)
  · obtain ⟨n, hpos, hsmall⟩ := oscillatory_derivative_values.2.2.1 ε hε
    let x : ℝ := 1 / ((2 * (n + 1) : ℕ) * Real.pi)
    have hx : x ∈ Ioo (-ε) ε := ⟨by dsimp [x]; linarith, hsmall⟩
    have hnonneg := hm.monotoneOn.derivWithin_nonneg (x := x)
    rw [derivWithin_of_isOpen isOpen_Ioo hx,
      oscillatory_derivative_values.1 n] at hnonneg
    norm_num at hnonneg
  · have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
    have hnonpos := hm.antitoneOn.derivWithin_nonpos (x := (0 : ℝ))
    rw [derivWithin_of_isOpen isOpen_Ioo h0, oscillatory_derivative_zero.deriv] at hnonpos
    norm_num at hnonpos

end D04.InverseCounterexamples
