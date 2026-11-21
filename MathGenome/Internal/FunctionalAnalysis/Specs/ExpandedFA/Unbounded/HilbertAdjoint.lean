import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.OperatorDomains
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
Independent specification for the adjoint construction in paper.tex 13499–13526.
The scalar field is real or complex and inner products are conjugate-linear first.
The representation is the canonical partial linear map from OperatorDomains.

Mathlib totalizes the adjoint away from densely defined operators. Every semantic
law below assumes density, and in particular specifies the exact existential
domain from the manuscript. Only the source Hilbert space needs completeness;
thus these laws also apply when the target is merely an inner product space.
The remaining conclusions of the source theorem (closability, double adjoints,
and kernel/range identities) belong to the separately allocated closability goal.
-/

noncomputable section

namespace ExpandedFA.Unbounded.HilbertAdjointSpec

section Construction
variable {𝕜 H K : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]

/-- The canonical library construction; its exact-domain meaning is specified below. -/
def adjointValue (A : Operator 𝕜 H K) : Operator 𝕜 K H := A.adjoint

end Construction

def AdjointTypeExpected :=
  ∀ {𝕜 H K : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K],
    Operator 𝕜 H K → Operator 𝕜 K H

def DomainExpected : Prop :=
  ∀ {𝕜 H K : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    (A : Operator 𝕜 H K), Dense (A.domain : Set H) → ∀ y : K,
    y ∈ (adjointValue A).domain ↔
      ∃ z : H, ∀ x : A.domain, inner 𝕜 (A x) y = inner 𝕜 (x : H) z

def EvaluationExpected : Prop :=
  ∀ {𝕜 H K : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    (A : Operator 𝕜 H K), Dense (A.domain : Set H) →
    ∀ (y : (adjointValue A).domain) (x : A.domain),
      inner 𝕜 (A x) (y : K) = inner 𝕜 (x : H) (adjointValue A y)

def UniquenessExpected : Prop :=
  ∀ {𝕜 H K : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    (A : Operator 𝕜 H K), Dense (A.domain : Set H) → ∀ (y : K) (z w : H),
    (∀ x : A.domain, inner 𝕜 (A x) y = inner 𝕜 (x : H) z) →
    (∀ x : A.domain, inner 𝕜 (A x) y = inner 𝕜 (x : H) w) → z = w

def ApplyEqExpected : Prop :=
  ∀ {𝕜 H K : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    (A : Operator 𝕜 H K), Dense (A.domain : Set H) →
    ∀ (y : (adjointValue A).domain) (z : H),
    (∀ x : A.domain, inner 𝕜 (A x) (y : K) = inner 𝕜 (x : H) z) →
    adjointValue A y = z

def ClosedExpected : Prop :=
  ∀ {𝕜 H K : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    (A : Operator 𝕜 H K), Dense (A.domain : Set H) →
    (adjointValue A).IsClosed

/-- An exact graph characterization, with the manuscript's order of inner products. -/
def GraphMembershipExpected : Prop :=
  ∀ {𝕜 H K : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    (A : Operator 𝕜 H K), Dense (A.domain : Set H) → ∀ (y : K) (z : H),
    (y, z) ∈ (adjointValue A).graph ↔
      ∀ x : A.domain, inner 𝕜 (A x) y = inner 𝕜 (x : H) z

/-- G(A*) = (J G(A))⊥ in K ⊕₂ H, with exactly J(x,y)=(-y,x).
The explicit `WithLp 2` transfer equips the product with its Hilbert inner product. -/
def RotatedGraphExpected : Prop :=
  ∀ {𝕜 H K : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    (A : Operator 𝕜 H K), Dense (A.domain : Set H) →
    (adjointValue A).graph.map (WithLp.linearEquiv 2 𝕜 (K × H)).symm.toLinearMap =
      (A.graph.map ((LinearEquiv.skewSwap 𝕜 H K).trans
        (WithLp.linearEquiv 2 𝕜 (K × H)).symm).toLinearMap).orthogonal

end ExpandedFA.Unbounded.HilbertAdjointSpec
