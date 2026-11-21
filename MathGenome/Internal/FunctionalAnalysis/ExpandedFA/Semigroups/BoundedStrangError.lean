import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.BoundedStrangError
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing

/-! Bounded Strang splitting: agreement of quadratic Taylor polynomials gives
cubic consistency; a noncommutative power estimate gives uniform second order.
No commutativity or contraction hypothesis is imposed on the operators. -/

noncomputable section
open Filter Topology Asymptotics NormedSpace
open scoped Nat

namespace ExpandedFA.Semigroups
namespace StrangProof

variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E]

/-- The quadratic Taylor polynomial with constant coefficient one. -/
private def quadratic (a b : E) (h : ℝ) : E := 1 + h • a + h^2 • b

@[fun_prop]
private lemma exp_real_continuous [CompleteSpace E] : Continuous (exp : E → E) :=
  continuous_iff_continuousAt.mpr fun x => (exp_analytic (𝕂 := ℝ) x).continuousAt

private lemma quadratic_continuous (a b : E) : Continuous (quadratic a b) := by
  unfold quadratic
  fun_prop

private lemma quadratic_mul (a b c d : E) (h : ℝ) :
    quadratic a b h * quadratic c d h - quadratic (a+c) (b+a*c+d) h =
      h^3 • (a*d + b*c + h • (b*d)) := by
  simp only [quadratic, add_mul, mul_add, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, smul_smul, smul_add]
  module

/-- Multiplication of two quadratic expansions, with cubic norm remainders. -/
private lemma quadratic_approx_mul {f g : ℝ → E} {a b c d : E}
    (hg : ContinuousAt g 0)
    (hf : (fun h => f h - quadratic a b h) =O[𝓝 0] (fun h : ℝ => ‖h‖^3))
    (hgg : (fun h => g h - quadratic c d h) =O[𝓝 0] (fun h : ℝ => ‖h‖^3)) :
    (fun h => f h * g h - quadratic (a+c) (b+a*c+d) h)
      =O[𝓝 0] (fun h : ℝ => ‖h‖^3) := by
  have h₁ := hf.mul (hg.tendsto.isBigO_one ℝ)
  have h₂ := ((quadratic_continuous a b).continuousAt.tendsto.isBigO_one ℝ).mul hgg
  have h₃ : (fun h : ℝ => h^3 • (a*d+b*c+h • (b*d)))
      =O[𝓝 0] (fun h : ℝ => ‖h‖^3) := by
    have hb : Continuous (fun h : ℝ => a*d+b*c+h • (b*d)) := by fun_prop
    have ht := (((isBigO_refl (fun h : ℝ => h^3) (𝓝 0)).smul
        (hb.continuousAt.tendsto.isBigO_one ℝ)).norm_right)
    apply ht.congr_right
    intro h
    change ‖h^3 * (1:ℝ)‖ = ‖h‖^3
    rw [mul_one, norm_pow]
  simp only [mul_one, one_mul] at h₁ h₂
  have hh := (h₁.add h₂).add h₃
  apply hh.congr_left
  intro h
  rw [← quadratic_mul]
  noncomm_ring

/-- Norm Taylor expansion of the exponential along a fixed algebra element. -/
private lemma exp_quadratic [CompleteSpace E] (a : E) :
    (fun h : ℝ => exp (h • a) - quadratic a ((1/2:ℝ) • a^2) h)
      =O[𝓝 0] (fun h : ℝ => ‖h‖^3) := by
  let u : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight a
  have h : HasFPowerSeriesAt exp (expSeries ℝ E) (u 0) := by
    simpa using (exp_hasFPowerSeriesAt_zero (𝕂 := ℝ) (𝔸 := E))
  have hp (n : ℕ) :
      ((expSeries ℝ E).compContinuousLinearMap u).coeff n =
        (n.factorial⁻¹ : ℝ) • a^n := by
    change expSeries ℝ E n (fun _ => (1:ℝ) • a) = _
    simpa only [one_smul] using (expSeries_apply_eq (𝕂 := ℝ) a n)
  have hh := h.compContinuousLinearMap.isBigO_sub_partialSum_pow 3
  simpa [quadratic, u, FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
    hp, smul_smul, Nat.factorial] using hh

private def strangStep (a b : E) (h : ℝ) : E :=
  exp (h • ((1/2:ℝ) • a)) * exp (h • b) * exp (h • ((1/2:ℝ) • a))

private lemma strangStep_continuous [CompleteSpace E] (a b : E) : Continuous (strangStep a b) := by
  unfold strangStep
  fun_prop

/-- The linear and quadratic coefficients agree, even for noncommuting elements. -/
private lemma strangStep_error_isBigO [CompleteSpace E] (a b : E) :
    (fun h : ℝ => strangStep a b h - exp (h • (a+b)))
      =O[𝓝 0] (fun h : ℝ => ‖h‖^3) := by
  let a' := (1/2:ℝ) • a
  have hc : Continuous (fun h : ℝ => exp (h • a')) := by fun_prop
  have hb : Continuous (fun h : ℝ => exp (h • b)) := by fun_prop
  have h₁ := quadratic_approx_mul hb.continuousAt (exp_quadratic a') (exp_quadratic b)
  have h₂ := quadratic_approx_mul hc.continuousAt h₁ (exp_quadratic a')
  have e₁ : a'+b+a' = a+b := by dsimp [a']; module
  have e₂ : (1/2:ℝ) • a'^2+a'*b+(1/2:ℝ) • b^2+(a'+b)*a'+(1/2:ℝ) • a'^2 =
      (1/2:ℝ) • (a+b)^2 := by
    dsimp [a']
    simp only [pow_two, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul,
      smul_add]
    module
  rw [e₁, e₂] at h₂
  have hh := h₂.sub (exp_quadratic (a+b))
  apply hh.congr_left
  intro h
  dsimp [strangStep, a']
  abel

omit [NormedAlgebra ℝ E] in
/-- A continuous cubic remainder near zero has a cubic bound on any compact
nonnegative time interval. This also handles time zero directly. -/
private lemma cubic_bound_on_interval {f : ℝ → E} (hf : Continuous f)
    (hO : f =O[𝓝 0] (fun h : ℝ => ‖h‖^3)) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ Set.Icc 0 T, ‖f h‖ ≤ C * h^3 := by
  obtain ⟨c, hc, hc'⟩ := hO.exists_nonneg
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp hc'.bound
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hf.continuousOn
  let D := (|K|+1) / δ^3
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨c+D, add_nonneg hc hD, ?_⟩
  intro h hh
  by_cases hsmall : h < δ
  · have he := hδ' (y := h) (by simpa [Real.dist_eq, abs_of_nonneg hh.1] using hsmall)
    have he' : ‖f h‖ ≤ c * h^3 := by
      simpa [norm_pow, Real.norm_eq_abs, abs_of_nonneg hh.1] using he
    exact he'.trans (by nlinarith [mul_nonneg hD (pow_nonneg hh.1 3)])
  · have hpow : δ^3 ≤ h^3 := pow_le_pow_left₀ (le_of_lt hδ) (le_of_not_gt hsmall) 3
    have hDp : D * δ^3 = |K|+1 := by dsimp [D]; field_simp
    have hKd : K ≤ D * h^3 := by
      have := mul_le_mul_of_nonneg_left hpow hD
      linarith [le_abs_self K]
    exact (hK h hh).trans (hKd.trans (by nlinarith [mul_nonneg hc (pow_nonneg hh.1 3)]))

/-- The one-step Strang defect has a uniform cubic bound. -/
private lemma strangStep_cubic [CompleteSpace E] (a b : E) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h ∈ Set.Icc 0 T,
      ‖strangStep a b h - exp (h • (a+b))‖ ≤ C * h^3 := by
  apply cubic_bound_on_interval
  · exact (strangStep_continuous a b).sub (by fun_prop)
  · exact strangStep_error_isBigO a b

/-- The usual scalar exponential majorizes the Banach-algebra exponential. -/
private lemma norm_exp_le [NormOneClass E] (a : E) : ‖exp a‖ ≤ Real.exp ‖a‖ := by
  rw [exp_eq_tsum ℝ, Real.exp_eq_exp_ℝ, exp_eq_tsum ℝ]
  apply (norm_tsum_le_tsum_norm (norm_expSeries_summable' (𝕂 := ℝ) a)).trans
  apply Summable.tsum_le_tsum
  · intro n
    simpa only [smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast] using
      mul_le_mul_of_nonneg_left (norm_pow_le a n)
        (inv_nonneg.mpr (Nat.cast_nonneg n.factorial))
  · exact norm_expSeries_summable' (𝕂 := ℝ) a
  · simpa [smul_eq_mul] using (expSeries_summable' (𝕂 := ℝ) ‖a‖)

omit [NormedAlgebra ℝ E] in
/-- A noncommutative telescoping estimate, with a harmless extra factor `q`. -/
private lemma norm_pow_sub_pow_le [NormOneClass E] (u v : E) {q : ℝ}
    (hq : 1 ≤ q) (hu : ‖u‖ ≤ q) (hv : ‖v‖ ≤ q) (n : ℕ) :
    ‖u^n-v^n‖ ≤ (n:ℝ) * q^n * ‖u-v‖ := by
  have hq0 : 0 ≤ q := le_trans zero_le_one hq
  induction n with
  | zero => simp
  | succ n ih =>
    have he : u^(n+1)-v^(n+1) = (u^n-v^n)*u + v^n*(u-v) := by
      simp only [pow_succ]
      noncomm_ring
    have hvn : ‖v^n‖ ≤ q^n := (norm_pow_le v n).trans (pow_le_pow_left₀ (norm_nonneg v) hv n)
    calc
      ‖u^(n+1)-v^(n+1)‖ ≤ ‖u^n-v^n‖ * ‖u‖ + ‖v^n‖ * ‖u-v‖ := by
        rw [he]
        exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ ((n:ℝ)*q^n*‖u-v‖)*q + q^n*‖u-v‖ := by gcongr
      _ ≤ ((n+1:ℕ):ℝ)*q^(n+1)*‖u-v‖ := by
        rw [Nat.cast_add, Nat.cast_one, pow_succ]
        nlinarith [mul_nonneg (mul_nonneg (pow_nonneg hq0 n) (norm_nonneg (u-v)))
          (sub_nonneg.mpr hq)]

private lemma norm_strangStep_le [NormOneClass E] (a b : E) {h : ℝ} (hh : 0 ≤ h) :
    ‖strangStep a b h‖ ≤ Real.exp (h * (‖a‖+‖b‖)) := by
  have he (x : E) : ‖exp (h • x)‖ ≤ Real.exp (h * ‖x‖) := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh] using norm_exp_le (h • x)
  calc
    ‖strangStep a b h‖ ≤
        ‖exp (h • ((1/2:ℝ) • a))‖ * ‖exp (h • b)‖ * ‖exp (h • ((1/2:ℝ) • a))‖ := by
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ Real.exp (h * ‖(1/2:ℝ) • a‖) * Real.exp (h * ‖b‖) *
        Real.exp (h * ‖(1/2:ℝ) • a‖) := by gcongr <;> apply he
    _ = Real.exp (h * (‖a‖+‖b‖)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [norm_smul]
      norm_num
      ring

private lemma norm_exactStep_le [NormOneClass E] (a b : E) {h : ℝ} (hh : 0 ≤ h) :
    ‖exp (h • (a+b))‖ ≤ Real.exp (h * (‖a‖+‖b‖)) := by
  apply (norm_exp_le (h • (a+b))).trans
  apply Real.exp_le_exp.mpr
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
  exact mul_le_mul_of_nonneg_left (norm_add_le a b) hh

/-- Cubic one-step consistency and exponential stability imply second order
uniformly in time. -/
private lemma strang_error_algebra [CompleteSpace E] [NormOneClass E] (a b : E) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, 0 ≤ t → t ≤ T →
      ‖(strangStep a b (t/(n:ℝ)))^n - exp (t • (a+b))‖ ≤ C / (n:ℝ)^2 := by
  let : NormedAlgebra ℚ E := NormedAlgebra.restrictScalars ℚ ℝ E
  obtain ⟨K, hK, hlocal⟩ := strangStep_cubic a b T
  let L := ‖a‖+‖b‖
  have hL : 0 ≤ L := add_nonneg (norm_nonneg a) (norm_nonneg b)
  refine ⟨K * T^3 * Real.exp (T*L), by positivity, ?_⟩
  intro n hn t ht htT
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hn_ne : (n:ℝ) ≠ 0 := ne_of_gt hn0
  let h := t/(n:ℝ)
  have hh0 : 0 ≤ h := div_nonneg ht hn0.le
  have hhT : h ≤ T := by
    have : h ≤ t := by dsimp [h]; exact div_le_self ht hn1
    exact this.trans htT
  have hnt : (n:ℝ)*h = t := by dsimp [h]; field_simp
  have hexact : (exp (h • (a+b)))^n = exp (t • (a+b)) := by
    rw [← exp_nsmul]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hnt]
  have hq : 1 ≤ Real.exp (h*L) := Real.one_le_exp (mul_nonneg hh0 hL)
  have hpower := norm_pow_sub_pow_le (strangStep a b h) (exp (h • (a+b))) hq
    (norm_strangStep_le a b hh0) (norm_exactStep_le a b hh0) n
  rw [hexact] at hpower
  have hqpow : (Real.exp (h*L))^n ≤ Real.exp (T*L) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    calc (n:ℝ)*(h*L) = t*L := by rw [← mul_assoc, hnt]
         _ ≤ T*L := mul_le_mul_of_nonneg_right htT hL
  have herr := hlocal h ⟨hh0, hhT⟩
  calc
    ‖strangStep a b h ^ n - exp (t • (a+b))‖
        ≤ (n:ℝ) * (Real.exp (h*L))^n * ‖strangStep a b h - exp (h • (a+b))‖ := hpower
    _ ≤ (n:ℝ) * Real.exp (T*L) * (K*h^3) := by gcongr
    _ = (K * t^3 * Real.exp (T*L)) / (n:ℝ)^2 := by dsimp [h]; field_simp
    _ ≤ (K * T^3 * Real.exp (T*L)) / (n:ℝ)^2 := by gcongr

end StrangProof

/-- Uniform `C_T / n²` operator-norm error for the symmetric Strang product of
arbitrary bounded operators on a real or complex Banach space. -/
theorem bounded_strang_error : BoundedStrangErrorSpec.BoundedStrangError := by
  intro 𝕜 X _ _ _ _ A B T
  by_cases hT : 0 ≤ T
  · rcases subsingleton_or_nontrivial X with hX | hX
    · let := hX
      refine ⟨0, le_rfl, ?_⟩
      intro n hn t ht htT
      simp only [Subsingleton.eq_zero, norm_zero, zero_div, le_refl]
    · let := hX
      let : NormedAlgebra ℝ (X →L[𝕜] X) :=
        NormedAlgebra.restrictScalars ℝ 𝕜 (X →L[𝕜] X)
      obtain ⟨C, hC, hbound⟩ := StrangProof.strang_error_algebra A B T hT
      refine ⟨C, hC, ?_⟩
      intro n hn t ht htT
      have hh := hbound n hn t ht htT
      change ‖(exp ((t/(2*(n:ℝ))) • A) * exp ((t/(n:ℝ)) • B) *
        exp ((t/(2*(n:ℝ))) • A))^n - exp (t • (A+B))‖ ≤ C/(n:ℝ)^2
      have he : (t/(n:ℝ)) * (1/2:ℝ) = t/(2*(n:ℝ)) := by ring
      simpa only [StrangProof.strangStep, smul_smul, he] using hh
  · refine ⟨0, le_rfl, ?_⟩
    intro n hn t ht htT
    exact (hT (ht.trans htT)).elim

end ExpandedFA.Semigroups
