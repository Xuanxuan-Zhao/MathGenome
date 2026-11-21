import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.NonlinearCompactExistence
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.NonlinearCounterexamples
import Mathlib.Topology.ContinuousMap.Ordered

/-! Order-interval formulation of the real extremal part of
`fa2:p5:hammerstein-extremal`. No ball invariance, Lipschitz condition,
or positive interval length is required. The kernel is defined only between
the two bounding curves. Clipping below only supplies irrelevant values
outside that interval and outside the integration triangle. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace ExpandedFA.PartV.VolterraExtremal
open NonlinearCompactExistence

abbrev RealCurve (T : ℝ) := Curve ℝ T

def timeOf {T : ℝ} (p : Triangle T) : Time T :=
  ⟨p.val.2, p.property.1, p.property.2.1.trans p.property.2.2⟩

abbrev Strip {T : ℝ} (ℓ v : RealCurve T) :=
  {q : Triangle T × ℝ // ℓ (timeOf q.1) ≤ q.2 ∧ q.2 ≤ v (timeOf q.1)}

abbrev OrderKernel {T : ℝ} (ℓ v : RealCurve T) := C(Strip ℓ v, ℝ)

def stripPoint {T : ℝ} {ℓ v : RealCurve T} (hlv : ℓ ≤ v)
    (p : Triangle T) (z : ℝ) : Strip ℓ v :=
  ⟨(p, max (ℓ (timeOf p)) (min (v (timeOf p)) z)),
    le_max_left _ _, max_le (hlv _) (min_le_left _ _)⟩

def orderIntegrand {T : ℝ} (hT : 0 ≤ T) {ℓ v : RealCurve T}
    (hlv : ℓ ≤ v) (G : OrderKernel ℓ v) (u : RealCurve T) (t : Time T) (s : ℝ) : ℝ :=
  G (stripPoint hlv (trianglePoint t (projIcc 0 T hT s)) (u (projIcc 0 T hT s)))

def ordinaryRhs {T : ℝ} (hT : 0 ≤ T) {ℓ v : RealCurve T}
    (hlv : ℓ ≤ v) (f : RealCurve T) (G : OrderKernel ℓ v)
    (u : RealCurve T) (t : Time T) : ℝ :=
  f t + ∫ s in 0..t.val, orderIntegrand hT hlv G u t s

def singularRhs {T : ℝ} (hT : 0 ≤ T) (α : ℝ) {ℓ v : RealCurve T}
    (hlv : ℓ ≤ v) (f : RealCurve T) (G : OrderKernel ℓ v)
    (u : RealCurve T) (t : Time T) : ℝ :=
  f t + ∫ s in 0..t.val, (t.val - s) ^ (α - 1) * orderIntegrand hT hlv G u t s

def KernelMonotone {T : ℝ} {ℓ v : RealCurve T} (G : OrderKernel ℓ v) : Prop :=
  ∀ (p : Triangle T) (z z' : ℝ)
    (hz : ℓ (timeOf p) ≤ z ∧ z ≤ v (timeOf p))
    (hz' : ℓ (timeOf p) ≤ z' ∧ z' ≤ v (timeOf p)),
    z ≤ z' → G ⟨(p, z), hz⟩ ≤ G ⟨(p, z'), hz'⟩

/-- Norm convergence here is precisely uniform convergence on [0,T].
The recurrences are equations for the original integral operator. -/
def ExtremalConclusion {T : ℝ} (ℓ v : RealCurve T)
    (rhs : RealCurve T → Time T → ℝ) : Prop :=
  ∃ (lower upper : ℕ → RealCurve T) (least greatest : RealCurve T),
    lower 0 = ℓ ∧ upper 0 = v ∧
    (∀ n t, lower (n+1) t = rhs (lower n) t) ∧
    (∀ n t, upper (n+1) t = rhs (upper n) t) ∧
    Monotone lower ∧ Antitone upper ∧
    (∀ n, lower n ∈ Icc ℓ v ∧ upper n ∈ Icc ℓ v) ∧
    Tendsto lower atTop (𝓝 least) ∧ Tendsto upper atTop (𝓝 greatest) ∧
    least ∈ Icc ℓ v ∧ greatest ∈ Icc ℓ v ∧
    (∀ t, least t = rhs least t) ∧ (∀ t, greatest t = rhs greatest t) ∧
    ∀ u ∈ Icc ℓ v, (∀ t, u t = rhs u t) → least ≤ u ∧ u ≤ greatest

def IsMaxWaitingSolution (T : ℝ) (u : ℝ → ℝ) : Prop :=
  ContinuousOn u (Icc 0 T) ∧
    ∀ t ∈ Icc 0 T, u t = ∫ s in 0..t, 2 * Real.sqrt (max (u s) 0)

/-- The square curve and the actual bracketed fixed-point set in C[0,T]. -/
def squareCurve (T : ℝ) : RealCurve T :=
  ⟨fun t => t.val^2, continuous_subtype_val.pow 2⟩

def waitingCurveSet {T : ℝ} (hT : 0 ≤ T) : Set (RealCurve T) :=
  {u | (∀ t, 0 ≤ u t ∧ u t ≤ t.val^2) ∧
    ∀ t, u t = ∫ s in 0..t.val, 2 * Real.sqrt (max (u (projIcc 0 T hT s)) 0)}

namespace Spec

def OrdinaryExtremal : Prop := ∀ (T : ℝ) (hT : 0 ≤ T)
    (ℓ v : RealCurve T) (hlv : ℓ ≤ v) (f : RealCurve T) (G : OrderKernel ℓ v),
  KernelMonotone G →
  (∀ t, ℓ t ≤ ordinaryRhs hT hlv f G ℓ t) →
  (∀ t, ordinaryRhs hT hlv f G v t ≤ v t) →
  ExtremalConclusion ℓ v (ordinaryRhs hT hlv f G)

def SingularExtremal : Prop := ∀ (T : ℝ) (hT : 0 ≤ T) (α : ℝ), 0 < α →
  ∀ (ℓ v : RealCurve T) (hlv : ℓ ≤ v) (f : RealCurve T) (G : OrderKernel ℓ v),
  KernelMonotone G →
  (∀ t, ℓ t ≤ singularRhs hT α hlv f G ℓ t) →
  (∀ t, singularRhs hT α hlv f G v t ≤ v t) →
  ExtremalConclusion ℓ v (singularRhs hT α hlv f G)

def WaitingExtremes : Prop := ∀ (T : ℝ) (hT : 0 ≤ T),
  IsLeast (waitingCurveSet hT) 0 ∧
  IsGreatest (waitingCurveSet hT) (squareCurve T) ∧
  (∀ c : ℝ, 0 ≤ c → IsMaxWaitingSolution T (NonlinearCounterexamples.waiting c) ∧
    ∀ t ∈ Icc 0 T, 0 ≤ NonlinearCounterexamples.waiting c t ∧
      NonlinearCounterexamples.waiting c t ≤ t^2) ∧
  (∀ c : ℝ, 0 < c → c < T →
    NonlinearCounterexamples.waiting c c = 0 ∧
    NonlinearCounterexamples.waiting c T < T^2 ∧
    0 < NonlinearCounterexamples.waiting c T)

end Spec
end ExpandedFA.PartV.VolterraExtremal
