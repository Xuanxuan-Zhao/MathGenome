import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.SymmetryAndDeficiencies
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! The first assertion of paper.tex:13687–13704. The graph is realized in
`H ⊕₂ H`; its subtype norm is the Hilbert graph norm, not the ambient domain
norm. The three summands are the actual graphs of S and its ±i eigenspaces.
Orthogonality together with their algebraic supremum being the whole adjoint
graph states an orthogonal direct sum, including infinite-dimensional H. -/
noncomputable section
universe u
namespace ExpandedFA.Unbounded.DeficiencyGraphDecompositionSpec
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The exact graph, transported to the Hilbert product. -/
def graphSpace (A : Operator ℂ H H) : Submodule ℂ (WithLp 2 (H × H)) :=
  A.graph.map (WithLp.linearEquiv 2 ℂ (H × H)).symm.toLinearMap

/-- The graph of the z eigenspace of S*, with the same graph norm as D(S*). -/
def defectSpace (S : Operator ℂ H H) (z : ℂ) : Submodule ℂ (WithLp 2 (H × H)) :=
  graphSpace (HilbertAdjointSpec.adjointValue S) ⊓
    (WithLp.sndL 2 ℂ H H - z • WithLp.fstL 2 ℂ H H).ker

def DecompositionExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H), S.IsClosed → SymmetryAndDeficienciesSpec.symmetricValue S →
    graphSpace (HilbertAdjointSpec.adjointValue S) =
      graphSpace S ⊔ defectSpace S Complex.I ⊔ defectSpace S (-Complex.I) ∧
    (graphSpace S).IsOrtho (defectSpace S Complex.I) ∧
    (graphSpace S).IsOrtho (defectSpace S (-Complex.I)) ∧
    (defectSpace S Complex.I).IsOrtho (defectSpace S (-Complex.I)) ∧
    Disjoint (graphSpace S) (defectSpace S Complex.I ⊔ defectSpace S (-Complex.I)) ∧
    Disjoint (defectSpace S Complex.I) (defectSpace S (-Complex.I)) ∧
    _root_.IsClosed (graphSpace S : Set (WithLp 2 (H × H))) ∧
    _root_.IsClosed (defectSpace S Complex.I : Set (WithLp 2 (H × H))) ∧
    _root_.IsClosed (defectSpace S (-Complex.I) : Set (WithLp 2 (H × H))) ∧
    _root_.IsClosed (graphSpace (HilbertAdjointSpec.adjointValue S) :
      Set (WithLp 2 (H × H)))

/-- This is the bridge to the already shared deficiency subspaces, not a new
notion of deficiency. It also states the second (operator) coordinate. -/
def MembershipExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H) (z : ℂ) (x b : H),
    WithLp.toLp 2 (x, b) ∈ defectSpace S z ↔
      x ∈ SymmetryAndDeficienciesSpec.deficiencySpaceValue S z ∧ b = z • x

def GraphMembershipExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : Operator ℂ H H) (x b : H),
    WithLp.toLp 2 (x, b) ∈ graphSpace A ↔ (x, b) ∈ A.graph

def GraphInnerExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : Operator ℂ H H) (x y : A.domain),
    inner ℂ (WithLp.toLp 2 ((x : H), A x)) (WithLp.toLp 2 ((y : H), A y)) =
      inner ℂ (x : H) (y : H) + inner ℂ (A x) (A y)

def GraphNormExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : Operator ℂ H H) (x : A.domain),
    ‖WithLp.toLp 2 ((x : H), A x)‖ ^ 2 = ‖(x : H)‖ ^ 2 + ‖A x‖ ^ 2

/-- Equivalence with the canonical sum graph norm used elsewhere in Part III.
Consequently the closed summands above are closed for that norm as well. -/
def GraphNormEquivalenceExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : Operator ℂ H H) (x : A.domain),
    ‖WithLp.toLp 2 ((x : H), A x)‖ ≤ OperatorDomainsSpec.graphNormValue A x ∧
    OperatorDomainsSpec.graphNormValue A x ≤ 2 * ‖WithLp.toLp 2 ((x : H), A x)‖

/-- A topological linear identification with the shared sum-norm domain.
It fixes the underlying vector and operator value exactly. -/
def GraphDomainEquivalenceExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : Operator ℂ H H),
    ∃ e : GraphDomain A ≃L[ℂ] graphSpace A, ∀ x : GraphDomain A,
      (e x : WithLp 2 (H × H)) = WithLp.toLp 2
        ((GraphDomain.toDomain A x : H), A (GraphDomain.toDomain A x))

/-- Closedness in the shared graph-norm topology on the actual adjoint domain. -/
def ClosedSummandsExpected : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Operator ℂ H H), S.IsClosed → SymmetryAndDeficienciesSpec.symmetricValue S →
    _root_.IsClosed {x : GraphDomain (HilbertAdjointSpec.adjointValue S) |
      (GraphDomain.toDomain _ x : H) ∈ S.domain} ∧
    _root_.IsClosed {x : GraphDomain (HilbertAdjointSpec.adjointValue S) |
      (GraphDomain.toDomain _ x : H) ∈ SymmetryAndDeficienciesSpec.deficiencyPlusValue S} ∧
    _root_.IsClosed {x : GraphDomain (HilbertAdjointSpec.adjointValue S) |
      (GraphDomain.toDomain _ x : H) ∈ SymmetryAndDeficienciesSpec.deficiencyMinusValue S}

end ExpandedFA.Unbounded.DeficiencyGraphDecompositionSpec
