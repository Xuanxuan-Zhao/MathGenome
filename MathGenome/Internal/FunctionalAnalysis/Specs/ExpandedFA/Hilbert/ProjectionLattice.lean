import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Projection
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent

/-!
Independent interface for paper.tex 7409–7414. The monotone-limit assertion
7415–7418 is allocated separately to MonotoneOperatorLimits.
Projections are all bounded self-adjoint idempotents on an arbitrary real or
complex Hilbert space. Their order is the native Loewner order; the explicit
quadratic-form statement below identifies it without any extra hypotheses.
All sets of projections, including the empty set, are allowed.
-/
noncomputable section
open scoped InnerProductSpace

namespace ExpandedFA.Hilbert.ProjectionLattice.Spec
universe u v

def OrthogonalProjectionType :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H], Type v
abbrev OrthogonalProjectionValue : OrthogonalProjectionType.{u, v} :=
  fun 𝕜 H _ _ _ _ => {P : H →L[𝕜] H // IsStarProjection P}

section Objects
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The range is closed because the operator is idempotent. -/
def closedRange (P : OrthogonalProjectionValue 𝕜 H) : ClosedSubmodule 𝕜 H :=
  ⟨P.val.range, ContinuousLinearMap.IsIdempotentElem.isClosed_range P.property.isIdempotentElem⟩

/-- This is exactly the native shared orthogonal projector onto M. -/
def ofClosedSubspace (M : ClosedSubmodule 𝕜 H) : OrthogonalProjectionValue 𝕜 H :=
  letI : CompleteSpace M.toSubmodule := M.isClosed.completeSpace_coe
  ⟨M.toSubmodule.starProjection, isStarProjection_starProjection⟩

/-- Candidate infimum: projection onto the intersection of all ranges. -/
def meet (S : Set (OrthogonalProjectionValue 𝕜 H)) : OrthogonalProjectionValue 𝕜 H :=
  ofClosedSubspace (sInf (closedRange '' S))

/-- Candidate supremum: projection onto the closed linear span of all ranges. -/
def join (S : Set (OrthogonalProjectionValue 𝕜 H)) : OrthogonalProjectionValue 𝕜 H :=
  ofClosedSubspace (sSup (closedRange '' S))
end Objects

def ProjectionIdentification : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (P : H →L[𝕜] H),
    (∃ p : OrthogonalProjectionValue 𝕜 H, p.val = P) ↔
      IsSelfAdjoint P ∧ P.comp P = P

def RangeCorrespondence : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H],
    (∀ P : OrthogonalProjectionValue 𝕜 H, ofClosedSubspace (closedRange P) = P) ∧
    (∀ M : ClosedSubmodule 𝕜 H, closedRange (ofClosedSubspace M) = M)

def QuadraticOrder : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (P Q : OrthogonalProjectionValue 𝕜 H),
    P ≤ Q ↔ ∀ x : H, RCLike.re ⟪x, P.val x⟫_𝕜 ≤ RCLike.re ⟪x, Q.val x⟫_𝕜

def OrderRange : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (P Q : OrthogonalProjectionValue 𝕜 H), P ≤ Q ↔ P.val.range ≤ Q.val.range

def OrderProduct : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (P Q : OrthogonalProjectionValue 𝕜 H),
    P ≤ Q ↔ P.val.comp Q.val = P.val ∧ Q.val.comp P.val = P.val

/-- GLB/LUB laws in the native operator order assert completeness, without
assuming a lattice structure as a hypothesis of the assertion. -/
def CompleteLatticeLaws : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (S : Set (OrthogonalProjectionValue 𝕜 H)),
    IsGLB S (meet S) ∧ IsLUB S (join S)

def MeetRange : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (S : Set (OrthogonalProjectionValue 𝕜 H)),
    (meet S).val.range = ⨅ P ∈ S, P.val.range

def JoinRange : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (S : Set (OrthogonalProjectionValue 𝕜 H)),
    (join S).val.range = (⨆ P ∈ S, P.val.range).topologicalClosure

/-- The product of commuting projections is the meet as an actual operator. -/
def CommutingProduct : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (P Q : OrthogonalProjectionValue 𝕜 H),
    P.val.comp Q.val = Q.val.comp P.val →
      P.val.comp Q.val = (meet {P, Q}).val

end ExpandedFA.Hilbert.ProjectionLattice.Spec
