import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C03OperatorNorm
import Mathlib.Topology.Algebra.Module.Complement

/-!
Independent specification for Definition `fa2:p1:c02:topological-sum`, paper.tex
535–542. All subspaces have the inherited norm and topology. In particular,
neither completeness nor closedness is assumed, and zero spaces are included.
-/
namespace ExpandedFA.P1.C02TopologicalSum.Spec

universe u v

section
variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The native predicate asks for an algebraic complement and a continuous
coordinate projection. The characterization below checks both coordinates
and the unique-decomposition meaning of this representation. -/
def TopologicalDirectSumType :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    Submodule 𝕜 E → Submodule 𝕜 E → Prop

def TopologicalDirectSumValue : TopologicalDirectSumType :=
  fun {_ _} [_] [_] [_] M N => Submodule.IsTopCompl M N

def ComplementedType :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E], Submodule 𝕜 E → Prop

def ComplementedValue : ComplementedType :=
  fun {_ _} [_] [_] [_] M => ∃ N : Submodule _ _, Submodule.IsTopCompl M N

def IsBoundedProjectionType :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E], (E →L[𝕜] E) → Prop

def IsBoundedProjectionValue : IsBoundedProjectionType :=
  fun {_ _} [_] [_] [_] P => P.comp P = P

def LeftCoordinateType :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M N : Submodule 𝕜 E), Submodule.IsTopCompl M N → E →L[𝕜] M

noncomputable def LeftCoordinateValue : LeftCoordinateType :=
  fun {_ _} [_] [_] [_] M N h => M.projectionOntoL N h

def RightCoordinateType :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M N : Submodule 𝕜 E), Submodule.IsTopCompl M N → E →L[𝕜] N

noncomputable def RightCoordinateValue : RightCoordinateType :=
  fun {_ _} [_] [_] [_] M N h => N.projectionOntoL M h.symm

/-- Literal unique decomposition by bounded linear coordinate maps. -/
def CoordinateCharacterization : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (M N : Submodule 𝕜 E),
    Submodule.IsTopCompl M N ↔
      ∃ (p : E →L[𝕜] M) (q : E →L[𝕜] N),
        ∀ x, (p x : E) + (q x : E) = x ∧
          ∀ (m : M) (n : N), (m : E) + (n : E) = x → m = p x ∧ n = q x

/-- The source definition with explicit nonnegative bounds on both linear
coordinate maps. The maps take values in the subspaces with their inherited norms. -/
def BoundedCoordinateCharacterization : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (M N : Submodule 𝕜 E),
    Submodule.IsTopCompl M N ↔
      ∃ (p : E →ₗ[𝕜] M) (q : E →ₗ[𝕜] N) (C D : ℝ),
        0 ≤ C ∧ 0 ≤ D ∧
        (∀ x, ‖p x‖ ≤ C * ‖x‖) ∧ (∀ x, ‖q x‖ ≤ D * ‖x‖) ∧
        ∀ x, (p x : E) + (q x : E) = x ∧
          ∀ (m : M) (n : N), (m : E) + (n : E) = x → m = p x ∧ n = q x

def UniqueDecomposition : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (M N : Submodule 𝕜 E)
    (h : Submodule.IsTopCompl M N) (x : E),
    ∃! z : M × N, (z.1 : E) + (z.2 : E) = x

/-- Both coordinate bounds are actual inequalities in the original norm. -/
def CoordinateBounds : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (M N : Submodule 𝕜 E)
    (h : Submodule.IsTopCompl M N),
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖M.projectionOntoL N h x‖ ≤ C * ‖x‖) ∧
    (∃ D : ℝ, 0 ≤ D ∧ ∀ x, ‖N.projectionOntoL M h.symm x‖ ≤ D * ‖x‖)

/-- Despite its name, `ClosedComplemented` does not assume closedness. -/
def ComplementedIdentification : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (M : Submodule 𝕜 E),
    (∃ N : Submodule 𝕜 E, Submodule.IsTopCompl M N) ↔ M.ClosedComplemented

def ProjectionIdempotence : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (P : E →L[𝕜] E),
    P.comp P = P ↔ IsIdempotentElem P

/-- The native projection is onto precisely the original range along its kernel. -/
def ProjectionIdentification : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (P : E →L[𝕜] E),
    P.comp P = P ↔
      ∃ h : Submodule.IsTopCompl P.range P.ker,
        P = P.range.projectionL P.ker h

end
end ExpandedFA.P1.C02TopologicalSum.Spec
