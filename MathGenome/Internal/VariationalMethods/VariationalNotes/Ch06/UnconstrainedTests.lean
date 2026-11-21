import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.UnconstrainedTests
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Set Filter Asymptotics
open scoped Topology

namespace VariationalNotes.Ch06

open Specs.VariationalNotes.Ch06 (TwiceFrechetAt)

universe u

theorem firstOrder : Specs.VariationalNotes.Ch06.FirstOrder.{u} := by
  intro X _ _ _ U f a hU ha hmin hf
  exact (hmin.isLocalMin (hU.mem_nhds ha)).fderiv_eq_zero

section Remainder
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {f : X → ℝ} {a : X} {B : X →L[ℝ] X →L[ℝ] ℝ}

/-- Taylor's expansion with a Peano remainder under pointwise second
Fréchet differentiability. -/
theorem secondOrderRemainder (h : TwiceFrechetAt f a B) :
    (fun x => f x - f a - fderiv ℝ f a (x-a) - (1/2 : ℝ) * B (x-a) (x-a))
      =o[𝓝 a] (fun x => ‖x-a‖ ^ 2) := by
  have he : ∀ᶠ x in 𝓝 a, HasFDerivAt f (fderiv ℝ f x) x :=
    h.1.mono fun x hx => hx.hasFDerivAt
  have hsym := second_derivative_symmetric_of_eventually_of_real he h.2
  let R := fun x => f x - f a - fderiv ℝ f a (x-a) - (1/2 : ℝ) * B (x-a) (x-a)
  let R' := fun x => fderiv ℝ f x - fderiv ℝ f a - B (x-a)
  have hd : ∀ᶠ x in 𝓝 a, HasFDerivAt R (R' x) x := by
    filter_upwards [he] with x hx
    have hi := (hasFDerivAt_id (𝕜 := ℝ) x).sub_const a
    have hq := (B.hasFDerivAt_of_bilinear hi hi).const_mul (1/2 : ℝ)
    have hlin := (fderiv ℝ f a).hasFDerivAt.comp x hi
    apply (((hx.sub_const (f a)).sub hlin).sub hq).congr_fderiv
    ext v
    simp [R', ContinuousLinearMap.precompR, ContinuousLinearMap.precompL, hsym]
    ring
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hd
  have ht := (convex_ball a r).isLittleO_pow_succ (Metric.mem_ball_self hr)
    (fun x hx => (hball hx).hasFDerivWithinAt)
    (by simpa [R', pow_one] using
      ((h.2.isLittleO.norm_right).mono (l := 𝓝[Metric.ball a r] a) nhdsWithin_le_nhds))
    (n := 1)
  have hn : 𝓝[Metric.ball a r] a = 𝓝 a :=
    Metric.isOpen_ball.nhdsWithin_eq (Metric.mem_ball_self hr)
  simpa [hn, R, R', pow_one] using ht

end Remainder

/-- Compactness supplies a uniform lower bound, also when the sphere is
empty. This formulation therefore covers the zero-dimensional space. -/
theorem positiveDefinite_lowerBound {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (B : X →L[ℝ] X →L[ℝ] ℝ) (hB : ∀ d : X, d ≠ 0 → 0 < B d d) :
    ∃ m > 0, ∀ d : X, m * ‖d‖ ^ 2 ≤ B d d := by
  have hc : Continuous (fun d : X => B d d) := by fun_prop
  obtain ⟨m, hm, hbound⟩ := (isCompact_sphere (0 : X) 1).exists_forall_le'
    hc.continuousOn (a := (0 : ℝ)) (by
      intro d hd
      apply hB d
      intro he
      simp [he] at hd)
  refine ⟨m, hm, fun d => ?_⟩
  by_cases hd : d = 0
  · simp [hd]
  have hn : ‖d‖ ≠ 0 := norm_ne_zero_iff.mpr hd
  let v := ‖d‖⁻¹ • d
  have hv : v ∈ Metric.sphere (0 : X) 1 := by
    simp [v, norm_smul, hn]
  have hdv : ‖d‖ • v = d := by simp [v, smul_smul, hn]
  have heq : B d d = ‖d‖ ^ 2 * B v v := by
    calc
      B d d = B (‖d‖ • v) (‖d‖ • v) := by rw [hdv]
      _ = ‖d‖ ^ 2 * B v v := by simp [map_smul, smul_eq_mul]; ring
  rw [heq]
  nlinarith [mul_le_mul_of_nonneg_right (hbound v hv) (sq_nonneg ‖d‖)]

theorem secondOrderSufficient : Specs.VariationalNotes.Ch06.SecondOrderSufficient.{u} := by
  intro X _ _ _ U f a B hU ha htwo hzero hpos
  obtain ⟨m, hm, hbound⟩ := positiveDefinite_lowerBound B hpos
  have hrem := secondOrderRemainder htwo
  have he := hrem.bound (show 0 < m / 4 by positivity)
  have he' : ∀ᶠ x in 𝓝 a,
      f a + (m/4) * ‖x-a‖ ^ 2 ≤ f x := by
    filter_upwards [he] with x hx
    have habs := (neg_le_abs (f x - f a - (1/2 : ℝ) * B (x-a) (x-a))).trans
      (by simpa [hzero, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖x-a‖)] using hx)
    have hlow := hbound (x-a)
    nlinarith
  obtain ⟨ρ, hρ, hρball⟩ := Metric.eventually_nhds_iff.mp
    (he'.and (hU.mem_nhds ha))
  exact ⟨m/4, by positivity, ρ, hρ, fun x hx => (hρball hx).2,
    fun x hx => (hρball hx).1⟩

theorem secondOrderNecessary : Specs.VariationalNotes.Ch06.SecondOrderNecessary.{u} := by
  intro X _ _ _ U f a B hU ha hmin htwo d
  have hlocal := hmin.isLocalMin (hU.mem_nhds ha)
  have hzero := hlocal.fderiv_eq_zero
  have hrem := secondOrderRemainder htwo
  by_contra! hneg
  have hd : d ≠ 0 := by intro hd; simp [hd] at hneg
  have hn : 0 < ‖d‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hd)
  let ε : ℝ := -(B d d) / (4 * ‖d‖ ^ 2)
  have hε : 0 < ε := div_pos (neg_pos.mpr hneg) (mul_pos (by norm_num) hn)
  have hεeq : ε * ‖d‖ ^ 2 = -(B d d) / 4 := by
    dsimp [ε]
    field_simp
  have hcont : Tendsto (fun t : ℝ => a + t • d) (𝓝[>] 0) (𝓝 a) := by
    have hc : ContinuousAt (fun t : ℝ => a + t • d) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have he := hcont.eventually ((hrem.bound hε).and hlocal)
  obtain ⟨t, htbound, ht⟩ := (he.and self_mem_nhdsWithin).exists
  have htpos : 0 < t := ht
  rcases htbound with ⟨hb, hminb⟩
  have habs := (le_abs_self (f (a+t•d)-f a-(1/2 : ℝ) * (t*t*(B d d)))).trans
    (by simpa [hzero, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖a+t•d-a‖),
      norm_smul, abs_of_pos htpos, map_smul, smul_eq_mul, mul_assoc] using hb)
  have hnonneg : 0 ≤ t^2 * ((1/2 : ℝ) * B d d + ε * ‖d‖ ^ 2) := by
    nlinarith
  have hcoef := nonneg_of_mul_nonneg_right hnonneg (sq_pos_of_pos htpos)
  linarith

/-- Relate scalar second derivatives to the Fréchet Hessian used above. -/
private theorem scalar_zeroHessian {f : ℝ → ℝ}
    (hf : ∀ᶠ x in 𝓝 (0 : ℝ), DifferentiableAt ℝ f x)
    (hderiv : HasDerivAt (deriv f) 0 0) : TwiceFrechetAt f 0 0 := by
  refine ⟨hf, ?_⟩
  have hd := hderiv.smul_const (ContinuousLinearMap.id ℝ ℝ)
  have hh : HasFDerivAt (𝕜 := ℝ) (fun x => deriv f x • ContinuousLinearMap.id ℝ ℝ) 0 0 := by
    simpa using hd.hasFDerivAt
  convert hh using 1
  ext x v
  simp [fderiv_eq_deriv_mul, smul_eq_mul]

theorem fourthPowerExamples : Specs.VariationalNotes.Ch06.FourthPowerExamples := by
  have hp : deriv (fun x : ℝ => x ^ 4) = fun x => 4 * x ^ 3 := by
    funext x
    simpa using (deriv_pow_field (𝕜 := ℝ) (x := x) 4)
  have hn : deriv (fun x : ℝ => -(x ^ 4)) = fun x => -(4 * x ^ 3) := by
    funext x
    simpa using (((hasDerivAt_id x).pow 4).neg).deriv
  have hdp : HasDerivAt (fun x : ℝ => 4 * x ^ 3) 0 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).pow 3).const_mul 4 using 1 <;> norm_num
  have hdn : HasDerivAt (fun x : ℝ => -(4 * x ^ 3)) 0 0 := by
    convert hdp.neg using 1; norm_num
  have hstrict : ∀ x : ℝ, x ≠ 0 → (0 : ℝ)^4 < x^4 := by
    intro x hx
    have hs := sq_pos_of_ne_zero hx
    nlinarith [sq_pos_of_pos hs]
  have hp2 : TwiceFrechetAt (fun x : ℝ => x ^ 4) 0 0 := by
    apply scalar_zeroHessian (Eventually.of_forall fun x => by fun_prop)
    rw [hp]
    exact hdp
  have hn2 : TwiceFrechetAt (fun x : ℝ => -(x ^ 4)) 0 0 := by
    apply scalar_zeroHessian (Eventually.of_forall fun x => by fun_prop)
    rw [hn]
    exact hdn
  have hp0 : fderiv ℝ (fun x : ℝ => x ^ 4) 0 = 0 := by
    ext v
    simp [fderiv_eq_deriv_mul, hp]
  have hn0 : fderiv ℝ (fun x : ℝ => -(x ^ 4)) 0 = 0 := by
    ext v
    simp [fderiv_eq_deriv_mul, hn]
  exact ⟨by fun_prop, by fun_prop, by simp [hp], by rw [hp]; exact hdp.deriv,
    by simp [hn], by rw [hn]; exact hdn.deriv,
    hp2, hp0, hn2, hn0, hstrict, fun x hx => neg_lt_neg (hstrict x hx)⟩

end VariationalNotes.Ch06
