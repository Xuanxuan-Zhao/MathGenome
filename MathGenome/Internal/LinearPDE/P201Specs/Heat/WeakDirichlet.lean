import MathGenome.Internal.LinearPDE.P201Specs.Common.TimeTrace
import MathGenome.Internal.LinearPDE.P201Specs.Common.ExactTrace

/-! Independent concrete statement of paper.tex, theorem pde:heat-dirichlet-weak.
The time classes use the open time interval, the curve includes both endpoints,
and the derivative is a vector-valued distribution in the actual continuous
H₀¹ dual, with its full H¹ norm. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4000
open MeasureTheory
open scoped ENNReal Topology
namespace P201Specs.Heat.WeakDirichlet
open ExpandedFA.Evolution HilbertTripleSpec HilbertTripleTraceSpec

/-- L² inner product of the actual weak gradients. By `L2.inner_def` this is
exactly the spatial integral of their Euclidean dot product. -/
def heatEnergy {n : ℕ} (Ω : Domain n) (u v : H10 ℝ Ω) : ℝ :=
  inner ℝ (hGradient u.val) (hGradient v.val)

/-- A solution is three a.e./continuous representatives with compatibility;
no equation, trace theorem, or existence assertion is assumed. -/
structure Solution {n : ℕ} (Ω : Domain n) (T : ℝ) (hT : 0 ≤ T)
    (f : timeLpValue (Hminus1 ℝ Ω) 2 T) (u₀ : Lp ℝ Ω 2) where
  value : timeLpValue (H10 ℝ Ω) 2 T
  derivative : timeLpValue (Hminus1 ℝ Ω) 2 T
  curve : C(Set.Icc 0 T, Lp ℝ Ω 2)
  represents : extendCurve curve =ᵐ[timeMeasureValue T]
    fun t => hZeroUnderlying Ω (value t)
  has_derivative : derivativeValue T
    (fun t => pivot Ω (hZeroUnderlying Ω (value t))) derivative
  equation : ∀ᵐ t ∂timeMeasureValue T, ∀ v : H10 ℝ Ω,
    derivative t v + heatEnergy Ω (value t) v = f t v
  initial : curve ⟨0, by simp [hT]⟩ = u₀

def EnergyIdentity {n : ℕ} {Ω : Domain n} {T : ℝ} {hT : 0 ≤ T}
    {f : timeLpValue (Hminus1 ℝ Ω) 2 T} {u₀ : Lp ℝ Ω 2}
    (z : Solution Ω T hT f u₀) : Prop :=
  ∀ t : Set.Icc 0 T,
    IntervalIntegrable (fun s => ‖hGradient (z.value s).val‖ ^ 2) volume 0 t.val ∧
    IntervalIntegrable (fun s => f s (z.value s)) volume 0 t.val ∧
    (1 / 2 : ℝ) * ‖z.curve t‖ ^ 2 +
        (∫ s in 0..t.val, ‖hGradient (z.value s).val‖ ^ 2) =
      (1 / 2 : ℝ) * ‖u₀‖ ^ 2 + (∫ s in 0..t.val, f s (z.value s))

/-- The constant precedes the data and controls all three original norms.
The norm of the continuous curve is the supremum on the closed interval.
The lateral statement uses the smooth-compatible, exact Sobolev trace. -/
def TheoremStatement : Prop :=
  ∀ (m : ℕ) (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω),
    ∃ Tr : H ℝ Ω 1 →L[ℝ] Hhalf Ω hΩ,
      Trace.AgreesWithSmooth Tr ∧ Tr.ker = hZeroSubmodule ℝ Ω ∧
      ∀ (T : ℝ) (hT : 0 < T), ∃ K : ℝ, 0 ≤ K ∧
        ∀ (f : timeLpValue (Hminus1 ℝ Ω) 2 T) (u₀ : Lp ℝ Ω 2),
          ∃ z : Solution Ω T hT.le f u₀,
            EnergyIdentity z ∧
            ‖z.curve‖ ^ 2 + ‖z.value‖ ^ 2 + ‖z.derivative‖ ^ 2 ≤
              K * (‖u₀‖ ^ 2 + ‖f‖ ^ 2) ∧
            (∀ᵐ t ∂timeMeasureValue T, Tr (z.value t).val = 0) ∧
            ∀ w : Solution Ω T hT.le f u₀, w = z

end P201Specs.Heat.WeakDirichlet
