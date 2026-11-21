import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.BanachAdjoint

/-! The two surjectivity criteria in `fa2:p3:banach-closed-range`.
The domain subtype carries the ambient norm. The adjoint is the scalar-linear
continuous extension in the original X norm, as in BanachAdjointSpec.
No nontriviality or reflexivity hypothesis is imposed. -/
namespace ExpandedFA.Unbounded.BanachAdjointSurjectivitySpec

def SurjectivityCriterion : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (A : Operator 𝕜 X Y), Dense (A.domain : Set X) → A.IsClosed →
    (Function.Surjective A.toFun ↔
      ∃ C : ℝ, 0 < C ∧ ∀ q : (BanachAdjointSpec.adjointValue A).domain,
        ‖(q : Y →L[𝕜] 𝕜)‖ ≤ C * ‖BanachAdjointSpec.adjointValue A q‖)

def AdjointSurjectivityCriterion : Prop :=
  ∀ {𝕜 X Y : Type*} [RCLike 𝕜]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]
    (A : Operator 𝕜 X Y), Dense (A.domain : Set X) → A.IsClosed →
    (Function.Surjective (BanachAdjointSpec.adjointValue A).toFun ↔
      ∃ C : ℝ, 0 < C ∧ ∀ x : A.domain, ‖(x : X)‖ ≤ C * ‖A x‖)

end ExpandedFA.Unbounded.BanachAdjointSurjectivitySpec
