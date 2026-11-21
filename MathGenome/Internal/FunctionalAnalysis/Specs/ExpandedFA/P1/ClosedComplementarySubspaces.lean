import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02TopologicalSum

/-!
Independent statements for paper.tex 570–577: closed complementary subspaces
of a Banach space. Subspaces carry the inherited norm, and the product carries
the standard maximum norm. Algebraic complementarity is `IsCompl M N`.
Both real and complex scalars and all zero-space cases are included.
-/

namespace ExpandedFA.P1.ClosedComplementarySubspaces.Spec

universe u v

/-- Closed algebraic complements in a Banach space are topological complements,
in the sense of the shared Chapter 2 interface. -/
def TopologicalSum : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (M N : Submodule 𝕜 E), IsClosed (M : Set E) → IsClosed (N : Set E) →
      IsCompl M N → Submodule.IsTopCompl M N

/-- Bounds on the actual algebraic coordinate projections, in the original
norm. Neither bound nor continuity is assumed. -/
def CoordinateBounds : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (M N : Submodule 𝕜 E), IsClosed (M : Set E) → IsClosed (N : Set E) →
      ∀ h : IsCompl M N,
        (∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖M.projectionOnto N h x‖ ≤ C * ‖x‖) ∧
        (∃ D : ℝ, 0 ≤ D ∧ ∀ x : E, ‖N.projectionOnto M h.symm x‖ ≤ D * ‖x‖)

/-- Addition is a bounded linear isomorphism, and its inverse consists of
exactly the original algebraic coordinates. -/
def AdditionEquivalence : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (M N : Submodule 𝕜 E), IsClosed (M : Set E) → IsClosed (N : Set E) →
      ∀ h : IsCompl M N,
        ∃ A : (M × N) ≃L[𝕜] E,
          (∀ z : M × N, A z = (z.1 : E) + (z.2 : E)) ∧
          ∀ x : E, A.symm x = (M.projectionOnto N h x, N.projectionOnto M h.symm x)

end ExpandedFA.P1.ClosedComplementarySubspaces.Spec
