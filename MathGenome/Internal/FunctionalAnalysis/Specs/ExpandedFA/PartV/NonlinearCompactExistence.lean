import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc

/-! Independent formulation of `fa2:p5:hammerstein-extremal`, existence part.
The scalar field is ℝ or ℂ. The kernel is only defined on the closed triangular
cylinder; no extension or Lipschitz hypothesis is imposed. Radius zero and
T = 0 are retained. Endpoint values of the singular integrand do not affect
its Lebesgue integral. The order-extremal assertion is allocated separately. -/

noncomputable section
open Set MeasureTheory

universe u
namespace ExpandedFA.PartV.NonlinearCompactExistence

abbrev Time (T : ℝ) := Icc (0 : ℝ) T
abbrev Triangle (T : ℝ) := {p : ℝ × ℝ // 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}
abbrev Curve (𝕜 : Type u) [RCLike 𝕜] (T : ℝ) := C(Time T, 𝕜)
abbrev Ball (𝕜 : Type u) [RCLike 𝕜] (T R : ℝ) :=
  Metric.closedBall (0 : Curve 𝕜 T) R
abbrev Kernel (𝕜 : Type u) [RCLike 𝕜] (T R : ℝ) :=
  C(Triangle T × Metric.closedBall (0 : 𝕜) R, 𝕜)

instance (T : ℝ) : CompactSpace (Triangle T) := by
  apply isCompact_iff_compactSpace.mp
  have hclosed : IsClosed {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T} :=
    (isClosed_le continuous_const continuous_snd).inter
      ((isClosed_le continuous_snd continuous_fst).inter
        (isClosed_le continuous_fst continuous_const))
  exact (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hclosed
    (fun p hp => ⟨⟨hp.1.trans hp.2.1, hp.2.2⟩, ⟨hp.1, hp.2.1.trans hp.2.2⟩⟩)

/-- The state of a curve in the closed supremum-norm ball. -/
def state {𝕜 : Type u} [RCLike 𝕜] {T R : ℝ} (u : Ball 𝕜 T R) (s : Time T) :
    Metric.closedBall (0 : 𝕜) R :=
  ⟨u.val s, by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (u.val.norm_coe_le_norm s).trans (by
      simpa only [Metric.mem_closedBall, dist_zero_right] using u.property)⟩

/-- Retraction in the integration variable, used only to give the integrand
values outside [0,t]. It fixes every point of the original triangle. -/
def trianglePoint {T : ℝ} (t : Time T) (s : ℝ) : Triangle T :=
  ⟨(t, max 0 (min (t : ℝ) s)), le_max_left _ _,
    max_le t.property.1 (min_le_left _ _), t.property.2⟩

def integrand {𝕜 : Type u} [RCLike 𝕜] {T R : ℝ} (hT : 0 ≤ T)
    (G : Kernel 𝕜 T R) (u : Ball 𝕜 T R) (t : Time T) (s : ℝ) : 𝕜 :=
  G (trianglePoint t (projIcc 0 T hT s), state u (projIcc 0 T hT s))

def rhs {𝕜 : Type u} [RCLike 𝕜] {T R : ℝ} (hT : 0 ≤ T)
    (f : Curve 𝕜 T) (G : Kernel 𝕜 T R) (u : Ball 𝕜 T R) (t : Time T) : 𝕜 :=
  f t + ∫ s in 0..(t : ℝ), integrand hT G u t s

def fractionalRhs {𝕜 : Type u} [RCLike 𝕜] {T R : ℝ} (hT : 0 ≤ T)
    (α : ℝ) (f : Curve 𝕜 T) (G : Kernel 𝕜 T R)
    (u : Ball 𝕜 T R) (t : Time T) : 𝕜 :=
  f t + ∫ s in 0..(t : ℝ), (t.val - s) ^ (α - 1) • integrand hT G u t s

namespace Spec

/-- Besides a solution, records that the actual integral map is continuous,
relatively compact, and preserves the closed ball. These are conclusions,
not additional assumptions on G. -/
def OrdinaryExistence : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (T R : ℝ) (hT : 0 ≤ T)
    (f : Curve 𝕜 T) (G : Kernel 𝕜 T R),
    ‖f‖ + T * ‖G‖ ≤ R →
    ∃ V : Ball 𝕜 T R → Curve 𝕜 T,
      (∀ u t, V u t = rhs hT f G u t) ∧
      Continuous V ∧ IsCompact (closure (range V)) ∧
      (∀ u, ‖V u‖ ≤ R) ∧
      ∃ u : Ball 𝕜 T R, V u = u.val

/-- The same full assertion for every α > 0, with the exact mass T^α/α. -/
def FractionalExistence : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (T R α : ℝ) (hT : 0 ≤ T), 0 < α →
    ∀ (f : Curve 𝕜 T) (G : Kernel 𝕜 T R),
    ‖f‖ + (T ^ α / α) * ‖G‖ ≤ R →
    ∃ V : Ball 𝕜 T R → Curve 𝕜 T,
      (∀ u t, V u t = fractionalRhs hT α f G u t) ∧
      Continuous V ∧ IsCompact (closure (range V)) ∧
      (∀ u, ‖V u‖ ≤ R) ∧
      ∃ u : Ball 𝕜 T R, V u = u.val

end Spec
end ExpandedFA.PartV.NonlinearCompactExistence
