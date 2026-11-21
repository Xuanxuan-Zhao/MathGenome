import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.BanachAdjoint

/-! The four equivalent conditions in `fa2:p3:banach-closed-range`.
The adjoint is the scalar-linear extension relation on the original normed
continuous duals. The annihilators use the original ambient spaces. -/
namespace ExpandedFA.Unbounded.BanachClosedRangeTheoremSpec

def ClosedRangeEquivalences : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (A : Operator 𝕜 X Y), Dense (A.domain : Set X) → A.IsClosed →
    let B := BanachAdjointSpec.adjointValue A
    (IsClosed (A.toFun.range : Set Y) ↔ IsClosed (B.toFun.range : Set (X →L[𝕜] 𝕜))) ∧
    (IsClosed (A.toFun.range : Set Y) ↔
      (B.toFun.range : Set (X →L[𝕜] 𝕜)) =
        {f | ∀ x ∈ A.ker, f x = 0}) ∧
    (IsClosed (A.toFun.range : Set Y) ↔
      (A.toFun.range : Set Y) =
        {y | ∀ q ∈ B.ker, q y = 0})

end ExpandedFA.Unbounded.BanachClosedRangeTheoremSpec
