import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.PiPeriod
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.TrigInverses

/-!
Principal inverse trigonometric functions (K03.07.trig_inverses).

We choose the canonical ambient representatives and prove that their restrictions
are exactly the inverses of the manuscript's series functions on its analytic-π
branches. Mathlib constructs arcsin using `Real.sinOrderIso.symm` and arctan
using `Real.tanOrderIso.symm`; arccos is π/2 − arcsin. The inverse identities
and unique solutions below certify these constructions on the stated domains.
The library inverse derivative proofs use the inverse function theorem.
For the endpoint obstruction its proof differentiates sin ∘ arcsin = id:
a finite one-sided derivative would force 0 = 1. This avoids assuming that
unbounded interior derivatives alone imply failure of an endpoint derivative.
-/
noncomputable section
namespace SingleVariableAnalysis
open Set Filter
open scoped Topology

/-- Only the restriction to [-1,1] is asserted to invert sine. -/
def principalArcsin : ℝ → ℝ := Real.arcsin
/-- Only the restriction to [-1,1] is asserted to invert cosine. -/
def principalArccos : ℝ → ℝ := Real.arccos
/-- The inverse of tangent on its open principal interval. -/
def principalArctan : ℝ → ℝ := Real.arctan

namespace TrigInverses
open Specs.SingleVariableAnalysis.Ch07.SinCos
open Specs.SingleVariableAnalysis.Ch07.PiPeriod
open Specs.SingleVariableAnalysis.Ch07.TrigInverses

private theorem sine_eq : realSeriesSinValue = Real.sin :=
  funext fun x => (sinCosSeries_eq_real x).1
private theorem cosine_eq : realSeriesCosValue = Real.cos :=
  funext fun x => (sinCosSeries_eq_real x).2
private theorem pi_eq : analyticPiValue = Real.pi := PiPeriod.analyticPi_eq_pi
private theorem tangent_eq : (fun x => realSeriesSinValue x / realSeriesCosValue x) = Real.tan := by
  funext x
  rw [sine_eq, cosine_eq, Real.tan_eq_sin_div_cos]

theorem sine_branch : sineBranch := by
  simp only [sineBranch, sine_eq, pi_eq]
  exact ⟨Real.strictMonoOn_sin, Real.bijOn_sin⟩

theorem cosine_branch : cosineBranch := by
  simp only [cosineBranch, cosine_eq, pi_eq]
  exact ⟨Real.strictAntiOn_cos, Real.bijOn_cos⟩

theorem tangent_branch : tangentBranch := by
  simp only [tangentBranch, sine_eq, cosine_eq, pi_eq, ← Real.tan_eq_sin_div_cos]
  exact ⟨fun _ hx => Real.cos_pos_of_mem_Ioo hx, Real.continuousOn_tan_Ioo,
    Real.strictMonoOn_tan, fun _ _ => mem_univ _, Real.injOn_tan, Real.surjOn_tan⟩

theorem tangent_endpoint_limits : tangentEndpointLimits := by
  simp only [tangentEndpointLimits, tangent_eq, pi_eq]
  exact ⟨Real.tendsto_tan_neg_pi_div_two, Real.tendsto_tan_pi_div_two⟩

theorem tangent_derivative : tangentDerivative := by
  simp only [tangentDerivative, sine_eq, cosine_eq, pi_eq, ← Real.tan_eq_sin_div_cos]
  intro x hx
  exact ⟨Real.hasDerivAt_tan_of_mem_Ioo hx,
    one_div_pos.mpr (sq_pos_of_pos (Real.cos_pos_of_mem_Ioo hx))⟩

theorem arcsin_inverse : arcsinInverse := by
  simp only [arcsinInverse, principalArcsinValue, sine_eq, pi_eq]
  exact ⟨fun x _ => Real.arcsin_mem_Icc x, fun _ hx => Real.sin_arcsin' hx,
    fun _ hy => Real.arcsin_sin' hy⟩

theorem arccos_inverse : arccosInverse := by
  simp only [arccosInverse, principalArccosValue, cosine_eq, pi_eq]
  exact ⟨fun x _ => ⟨Real.arccos_nonneg x, Real.arccos_le_pi x⟩,
    fun _ hx => Real.cos_arccos hx.1 hx.2, fun _ hy => Real.arccos_cos hy.1 hy.2⟩

theorem arctan_inverse : arctanInverse := by
  simp only [arctanInverse, principalArctanValue, sine_eq, cosine_eq, pi_eq,
    ← Real.tan_eq_sin_div_cos]
  exact ⟨Real.arctan_mem_Ioo, Real.tan_arctan, fun _ hy => Real.arctan_tan hy.1 hy.2⟩

theorem branch_unique_solutions : branchUniqueness := by
  simp only [branchUniqueness, sine_eq, cosine_eq, pi_eq, ← Real.tan_eq_sin_div_cos]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    refine ⟨Real.arcsin x, ⟨Real.arcsin_mem_Icc x, Real.sin_arcsin' hx⟩, ?_⟩
    intro y hy
    exact Real.injOn_sin hy.1 (Real.arcsin_mem_Icc x) (hy.2.trans (Real.sin_arcsin' hx).symm)
  · intro x hx
    refine ⟨Real.arccos x, ⟨⟨Real.arccos_nonneg x, Real.arccos_le_pi x⟩,
      Real.cos_arccos hx.1 hx.2⟩, ?_⟩
    intro y hy
    exact Real.injOn_cos hy.1 ⟨Real.arccos_nonneg x, Real.arccos_le_pi x⟩
      (hy.2.trans (Real.cos_arccos hx.1 hx.2).symm)
  · intro x
    refine ⟨Real.arctan x, ⟨Real.arctan_mem_Ioo x, Real.tan_arctan x⟩, ?_⟩
    intro y hy
    exact Real.injOn_tan hy.1 (Real.arctan_mem_Ioo x) (hy.2.trans (Real.tan_arctan x).symm)

theorem inverse_continuity : inverseContinuity :=
  ⟨Real.continuous_arcsin.continuousOn, Real.continuous_arccos.continuousOn,
    Real.continuous_arctan⟩

theorem inverse_monotonicity : inverseMonotonicity :=
  ⟨Real.strictMonoOn_arcsin, Real.strictAntiOn_arccos, Real.arctan_strictMono⟩

theorem inverse_endpoint_values : endpointValues := by
  simp only [endpointValues, principalArcsinValue, principalArccosValue, pi_eq]
  exact ⟨Real.arcsin_neg_one, Real.arcsin_one, Real.arccos_neg_one, Real.arccos_one⟩

theorem inverse_derivatives : inverseDerivatives := by
  refine ⟨?_, ?_, Real.hasDerivAt_arctan⟩
  · intro x hx
    obtain ⟨hl, hr⟩ := abs_lt.mp hx
    exact Real.hasDerivAt_arcsin (by linarith) (ne_of_lt hr)
  · intro x hx
    obtain ⟨hl, hr⟩ := abs_lt.mp hx
    exact Real.hasDerivAt_arccos (by linarith) (ne_of_lt hr)

theorem no_finite_endpoint_derivatives : noFiniteEndpointDerivatives := by
  have hlt : (-1 : ℝ) < 1 := by norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨L, hL⟩
    have h := (hL.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hlt)).differentiableWithinAt
    exact (Real.differentiableWithinAt_arcsin_Ici.mp h) rfl
  · rintro ⟨L, hL⟩
    have h := (hL.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hlt)).differentiableWithinAt
    exact (Real.differentiableWithinAt_arcsin_Iic.mp h) rfl
  · rintro ⟨L, hL⟩
    have h := (hL.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE hlt)).differentiableWithinAt
    exact (Real.differentiableWithinAt_arccos_Ici.mp h) rfl
  · rintro ⟨L, hL⟩
    have h := (hL.mono_of_mem_nhdsWithin (Icc_mem_nhdsLE hlt)).differentiableWithinAt
    exact (Real.differentiableWithinAt_arccos_Iic.mp h) rfl

end TrigInverses
end SingleVariableAnalysis
