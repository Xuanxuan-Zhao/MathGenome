import Specs.ExpandedFA.PartV.VolterraOperator
import Mathlib.Topology.MetricSpace.Contracting

/-! Independent statement of paper.tex:22186–22213, fa2:p5:nonlinear-volterra.
`G` is defined only on the actual triangle times the closed state ball.
The function ball has the native supremum metric and its inherited uniformity. -/
noncomputable section
namespace ExpandedFA.PartV
open Set MeasureTheory Filter
open scoped Topology

namespace NonlinearVolterra
variable {E : Type*} [NormedAddCommGroup E]

abbrev Ball (a b : ℝ) (x₀ : E) (R : ℝ) :=
  Metric.closedBall (ContinuousMap.const (VolterraInterval a b) x₀) R

/-- Evaluation of a curve in the function ball lies in the state ball. -/
def state {a b : ℝ} {x₀ : E} {R : ℝ} (u : Ball a b x₀ R)
    (t : VolterraInterval a b) : Metric.closedBall x₀ R :=
  ⟨u.val t, (ContinuousMap.dist_apply_le_dist t).trans u.property⟩

/-- Extension by interval projections, which fix the original integrand on
`a ≤ s ≤ t`. There is no extension of `G` to states outside its domain. -/
def integrand {a b : ℝ} (hab : a ≤ b) {x₀ : E} {R : ℝ}
    (G : C(volterraTriangle a b × Metric.closedBall x₀ R, E))
    (u : Ball a b x₀ R) (t : VolterraInterval a b) (s : ℝ) : E :=
  G (volterraRetraction t s, state u (Set.projIcc a b hab s))

variable [NormedSpace ℝ E]

def rhs {a b : ℝ} (hab : a ≤ b) {x₀ : E} {R : ℝ}
    (f : C(VolterraInterval a b, E))
    (G : C(volterraTriangle a b × Metric.closedBall x₀ R, E))
    (u : Ball a b x₀ R) (t : VolterraInterval a b) : E :=
  f t + ∫ s in a..(t : ℝ), integrand hab G u t s

/-- Explicit pointwise equation; the only ambient completeness assumption
occurs in the theorem, not in this solution predicate. -/
def IsSolution {a b : ℝ} (hab : a ≤ b) {x₀ : E} {R : ℝ}
    (f : C(VolterraInterval a b, E))
    (G : C(volterraTriangle a b × Metric.closedBall x₀ R, E))
    (u : Ball a b x₀ R) : Prop := ∀ t, u.val t = rhs hab f G u t

/-- Uniform convergence is recorded both in the native supremum-norm topology
and pointwise as `TendstoUniformly`, for every initial member of the ball. -/
def SolvesAndIterates {a b : ℝ} (hab : a ≤ b) {x₀ : E} {R : ℝ}
    (f : C(VolterraInterval a b, E))
    (G : C(volterraTriangle a b × Metric.closedBall x₀ R, E))
    (T : Ball a b x₀ R → Ball a b x₀ R) : Prop :=
  (∀ u t, (T u).val t = rhs hab f G u t) ∧
  ∃ u : Ball a b x₀ R, IsSolution hab f G u ∧
    (∀ v, IsSolution hab f G v → v = u) ∧
    (∀ v, Tendsto (fun n => ((T^[n]) v).val) atTop (𝓝 u.val)) ∧
    (∀ v, TendstoUniformly (fun n t => ((T^[n]) v).val t) u.val atTop)

end NonlinearVolterra

namespace NonlinearVolterra.WeaklySingular
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def rhs {h : ℝ} (hh : 0 ≤ h) {x₀ : E} {R : ℝ} (α : ℝ)
    (f : C(VolterraInterval 0 h, E))
    (G : C(volterraTriangle 0 h × Metric.closedBall x₀ R, E))
    (u : Ball 0 h x₀ R) (t : VolterraInterval 0 h) : E :=
  f t + ∫ s in Ioc 0 (t : ℝ),
    ((t : ℝ)-s) ^ (α-1) • integrand hh G u t s

def IsSolution {h : ℝ} (hh : 0 ≤ h) {x₀ : E} {R : ℝ} (α : ℝ)
    (f : C(VolterraInterval 0 h, E))
    (G : C(volterraTriangle 0 h × Metric.closedBall x₀ R, E))
    (u : Ball 0 h x₀ R) : Prop := ∀ t, u.val t = rhs hh α f G u t

def SolvesAndIterates {h : ℝ} (hh : 0 ≤ h) {x₀ : E} {R : ℝ} (α : ℝ)
    (f : C(VolterraInterval 0 h, E))
    (G : C(volterraTriangle 0 h × Metric.closedBall x₀ R, E))
    (T : Ball 0 h x₀ R → Ball 0 h x₀ R) : Prop :=
  (∀ u (t : VolterraInterval 0 h), IntegrableOn (fun s => ((t : ℝ)-s) ^ (α-1) • integrand hh G u t s)
    (Ioc 0 (t : ℝ)) ∧ (T u).val t = rhs hh α f G u t) ∧
  ∃ u : Ball 0 h x₀ R, IsSolution hh α f G u ∧
    (∀ v, IsSolution hh α f G v → v = u) ∧
    (∀ v, Tendsto (fun n => ((T^[n]) v).val) atTop (𝓝 u.val)) ∧
    (∀ v, TendstoUniformly (fun n t => ((T^[n]) v).val t) u.val atTop)
end NonlinearVolterra.WeaklySingular

namespace NonlinearVolterraSpec
open NonlinearVolterra

/-- The invariant ball theorem, including singleton intervals and radius zero.
For the manuscript take `a = 0`, `b = h`, and `x₀ = f 0`.
There is no smallness restriction on `L * (b-a)`. -/
def InvariantBallTheorem : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (a b R : ℝ) (hab : a ≤ b) (_hR : 0 ≤ R) (x₀ : E)
  (f : C(VolterraInterval a b, E))
  (G : C(volterraTriangle a b × Metric.closedBall x₀ R, E))
  (B L : ℝ) (_hB : 0 ≤ B) (hL : 0 ≤ L)
  (_bound : ∀ p z, ‖G (p, z)‖ ≤ B)
  (_lip : ∀ p (z w : Metric.closedBall x₀ R),
    ‖G (p, z) - G (p, w)‖ ≤ L * ‖(z : E) - (w : E)‖)
  (_invariant : ‖f - ContinuousMap.const _ x₀‖ + (b-a) * B ≤ R),
  letI := NormedSpace.restrictScalars ℝ 𝕜 E
  ∃ T : Ball a b x₀ R → Ball a b x₀ R,
    LipschitzWith ⟨(b-a) * L, mul_nonneg (sub_nonneg.mpr hab) hL⟩ T ∧
    SolvesAndIterates hab f G T

/-- The full weakly singular analogue for every positive real order.
The sole interval-size condition is invariance of the given closed ball. -/
def WeaklySingularTheorem : Prop := ∀ (𝕜 E : Type*) [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  (α h R : ℝ) (_hα : 0 < α) (hh : 0 ≤ h) (_hR : 0 ≤ R) (x₀ : E)
  (f : C(VolterraInterval 0 h, E))
  (G : C(volterraTriangle 0 h × Metric.closedBall x₀ R, E))
  (B L : ℝ) (_hB : 0 ≤ B) (_hL : 0 ≤ L)
  (_bound : ∀ p z, ‖G (p, z)‖ ≤ B)
  (_lip : ∀ p (z w : Metric.closedBall x₀ R),
    ‖G (p, z) - G (p, w)‖ ≤ L * ‖(z : E) - (w : E)‖)
  (_invariant : ‖f - ContinuousMap.const _ x₀‖ + B * h ^ α / α ≤ R),
  letI := NormedSpace.restrictScalars ℝ 𝕜 E
  ∃ T : Ball 0 h x₀ R → Ball 0 h x₀ R,
    WeaklySingular.SolvesAndIterates hh α f G T

end NonlinearVolterraSpec
end ExpandedFA.PartV
