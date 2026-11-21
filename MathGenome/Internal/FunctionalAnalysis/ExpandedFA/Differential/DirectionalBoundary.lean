import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Differential.DirectionalBoundary
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter
open scoped Topology

namespace ExpandedFA.Differential

/-- The quotient from the paper, including its prescribed value at the origin. -/
noncomputable def directionalExample : Spec.DirectionalExampleType :=
  Spec.directionalExampleValue

theorem directionalExample_formula : Spec.DirectionalExampleFormula := by
  constructor
  · norm_num [Spec.directionalExampleValue]
  · intro p _
    rfl

/-- Cancelling the common factor `t²` exposes the second-order vanishing
along any line whose second coordinate is nonzero. -/
lemma directionalExample_on_line (a b t : ℝ) (hb : b ≠ 0) :
    directionalExample (t • (a, b)) =
      t ^ 2 * a ^ 3 * b / (t ^ 4 * a ^ 6 + b ^ 2) := by
  change (t * a) ^ 3 * (t * b) / ((t * a) ^ 6 + (t * b) ^ 2) = _
  by_cases ht : t = 0
  · simp [ht]
  have hd : t ^ 4 * a ^ 6 + b ^ 2 ≠ 0 := by positivity
  have he : (t * a) ^ 6 + (t * b) ^ 2 ≠ 0 := by positivity
  field_simp

/-- Every direction, including the zero direction, has derivative zero. -/
theorem directionalExample_directional_derivatives : Spec.ZeroDirectionalDerivatives := by
  intro v
  rcases v with ⟨a, b⟩
  by_cases hb : b = 0
  · simpa [Spec.directionalExampleValue, hb] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have hn := (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (a ^ 3)).mul_const b
  have hd := (((hasDerivAt_id (0 : ℝ)).pow 4).mul_const (a ^ 6)).add_const (b ^ 2)
  have hq := hn.fun_div hd (by simpa using pow_ne_zero 2 hb)
  have hder : HasDerivAt
      (fun t : ℝ => t ^ 2 * a ^ 3 * b / (t ^ 4 * a ^ 6 + b ^ 2)) 0 0 := by
    simpa using! hq
  apply hder.congr_of_eventuallyEq
  exact Eventually.of_forall (fun t => directionalExample_on_line a b t hb)

theorem directionalExample_on_cubic : Spec.ValueOnCubicCurve := by
  intro x hx
  change x ^ 3 * x ^ 3 / (x ^ 6 + (x ^ 3) ^ 2) = 1 / 2
  have hd : x ^ 6 + (x ^ 3) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem directionalExample_not_continuous : Spec.NotContinuousAtOrigin := by
  intro h
  have hc : ContinuousAt (fun x : ℝ => (x, x ^ 3)) 0 :=
    continuousAt_id.prodMk (continuousAt_id.pow 3)
  have hz : Tendsto (fun x : ℝ => Spec.directionalExampleValue (x, x ^ 3))
      (𝓝[≠] 0) (𝓝 0) := by
    have hh : ContinuousAt (fun x : ℝ => Spec.directionalExampleValue (x, x ^ 3)) 0 :=
      h.comp_of_eq hc (by simp)
    have hzero : Spec.directionalExampleValue ((0 : ℝ), (0 : ℝ) ^ 3) = 0 := by
      norm_num [Spec.directionalExampleValue]
    rw [ContinuousAt, hzero] at hh
    exact hh.mono_left nhdsWithin_le_nhds
  have he : (fun x : ℝ => Spec.directionalExampleValue (x, x ^ 3)) =ᶠ[𝓝[≠] 0]
      (fun _ => (1 / 2 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact directionalExample_on_cubic x hx
  have hh : Tendsto (fun x : ℝ => Spec.directionalExampleValue (x, x ^ 3))
      (𝓝[≠] 0) (𝓝 (1 / 2 : ℝ)) := tendsto_const_nhds.congr' he.symm
  have := tendsto_nhds_unique hz hh
  norm_num at this

theorem directionalExample_not_frechet_differentiable : Spec.NotFrechetDifferentiableAtOrigin := by
  intro h
  exact directionalExample_not_continuous h.continuousAt

end ExpandedFA.Differential
