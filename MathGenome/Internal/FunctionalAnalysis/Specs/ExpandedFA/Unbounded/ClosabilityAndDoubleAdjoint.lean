import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.HilbertAdjoint

/-! Independent statements for paper.tex:13499–13526, the closability and
kernel/range conclusions of the theorem on graphs and Hilbert adjoints.
Both spaces are Hilbert spaces, over either of the manuscript's scalar fields.
Operator equality is equality of partial linear maps, including their domains.
-/

noncomputable section

namespace ExpandedFA.Unbounded.ClosabilityAndDoubleAdjointSpec

open HilbertAdjointSpec OperatorDomainsSpec

def ClosabilityExpected : Prop :=
  ∀ {𝕜 H K : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (A : Operator 𝕜 H K), Dense (A.domain : Set H) →
    (A.IsClosable ↔ Dense ((adjointValue A).domain : Set K))

def DoubleAdjointExpected : Prop :=
  ∀ {𝕜 H K : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (A : Operator 𝕜 H K), Dense (A.domain : Set H) →
    ∀ h : A.IsClosable, closureValue A h = adjointValue (adjointValue A)

def DoubleAdjointGraphExpected : Prop :=
  ∀ {𝕜 H K : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (A : Operator 𝕜 H K), Dense (A.domain : Set H) → A.IsClosable →
    (adjointValue (adjointValue A)).graph = A.graph.topologicalClosure

def ClosedDoubleAdjointExpected : Prop :=
  ∀ {𝕜 H K : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (A : Operator 𝕜 H K), Dense (A.domain : Set H) → A.IsClosed →
    adjointValue (adjointValue A) = A

/-- The first identity even holds before assuming closedness of A. -/
def RangeOrthogonalExpected : Prop :=
  ∀ {𝕜 H K : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (A : Operator 𝕜 H K), Dense (A.domain : Set H) →
    (rangeValue A).orthogonal = (adjointValue A).ker

def AdjointRangeOrthogonalExpected : Prop :=
  ∀ {𝕜 H K : Type*} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
    (A : Operator 𝕜 H K), Dense (A.domain : Set H) → A.IsClosed →
    (rangeValue (adjointValue A)).orthogonal = A.ker

end ExpandedFA.Unbounded.ClosabilityAndDoubleAdjointSpec
