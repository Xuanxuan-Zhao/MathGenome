import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Norm
import Mathlib.Analysis.Convex.Uniform

/-!
Independent specification for `fa2:p1:c14:uniform-convexity`, paper.tex:2849–2860.
The shared predicate `Spec.UniformlyConvexValue` below is also the interface
for later modulus and rotundity statements. The candidate defines the public
`UniformlyConvex` to be this predicate. `RCLike` covers both fields, ℝ and ℂ.
The norm is the given norm; no completeness or nontriviality is assumed.
-/
namespace ExpandedFA.P1.C14UniformConvexity

universe u v

namespace Spec

def UniformlyConvexType :=
  (𝕜 : Type u) → (E : Type v) → [RCLike 𝕜] → [NormedAddCommGroup E] →
    [NormedSpace 𝕜 E] → Prop

/-- The full epsilon--delta formula, independent of any implementation. -/
def UniformlyConvexValue : UniformlyConvexType.{u,v} :=
  fun 𝕜 E _ _ _ => ∀ ε : ℝ, 0 < ε → ε ≤ 2 →
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : E,
      ‖x‖ ≤ 1 → ‖y‖ ≤ 1 → ε ≤ ‖x - y‖ →
        ‖(2 : 𝕜)⁻¹ • (x + y)‖ ≤ 1 - δ

def MidpointNorm : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] (x y : E),
    ‖(2 : 𝕜)⁻¹ • (x + y)‖ = ‖x + y‖ / 2

/-- Agreement with Mathlib's unit-sphere formulation. -/
def NativeIff : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E],
    UniformConvexSpace E ↔ UniformlyConvexValue 𝕜 E

/-- Strict convexity uses the underlying real vector space for either field. -/
def StrictConvexity : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E],
    UniformlyConvexValue 𝕜 E →
      letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
      StrictConvexSpace ℝ E

/-- The explicit unit-sphere conclusion stated in the manuscript. -/
def StrictMidpoint : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E],
    UniformlyConvexValue 𝕜 E → ∀ x y : E,
      ‖x‖ = 1 → ‖y‖ = 1 → x ≠ y → ‖(2 : 𝕜)⁻¹ • (x + y)‖ < 1

/-- In particular, the zero space is included. -/
def SubsingletonCase : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [Subsingleton E], UniformlyConvexValue 𝕜 E

end Spec
end ExpandedFA.P1.C14UniformConvexity
