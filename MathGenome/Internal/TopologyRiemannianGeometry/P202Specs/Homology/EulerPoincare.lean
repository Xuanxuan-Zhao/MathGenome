import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.CellularComparison
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Rat.Defs

/-! Euler--Poincaré, paper.tex 1665–1678, and the canonical topological
Euler invariant required by later applications. All homology groups below
are the shared ordinary singular homology groups, with coefficients in the
field itself. Finiteness of a CW structure means finitely many cells in total.
The canonical invariant requires the rational finiteness hypotheses explicitly;
it is independent of any chosen CW structure. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe u v w
namespace P202Specs.EulerPoincare
open P202.Cellular P202Specs.SingularChains

/-- Finite dimensional in each nonnegative degree and zero eventually. -/
def HomologyFiniteType (F : Type u) [Field F] (X : Type w) [TopologicalSpace X] : Prop :=
  (∀ n : ℕ, FiniteDimensional F (homology F F (TopCat.of X) (n : ℤ))) ∧
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → IsZero (homology F F (TopCat.of X) (n : ℤ))

/-- The homological alternating sum. It represents a finite sum whenever
`HomologyFiniteType F X` holds, as proved by `finiteSumFormula`. -/
def homologicalEuler (F : Type u) [Field F] (X : Type w) [TopologicalSpace X] : ℤ :=
  ∑ᶠ n : ℕ, (-1 : ℤ)^n * (Module.finrank F (homology F F (TopCat.of X) (n : ℤ)) : ℤ)

/-- Canonical topological Euler characteristic, on its finite-type domain.
Later users must supply the rational singular-homology finiteness proof. -/
def topologicalEuler (X : Type w) [TopologicalSpace X]
    (_h : HomologyFiniteType ℚ X) : ℤ := homologicalEuler ℚ X

/-- The cell-count alternating sum for the specified CW structure. -/
def cellEuler (X : Type w) [TopologicalSpace X] [CellStructure X] : ℤ :=
  ∑ᶠ n : ℕ, (-1 : ℤ)^n * (Nat.card (Cell X n) : ℤ)

namespace Expected

def eulerCharacteristic_type :=
  ∀ (X : Type w) [TopologicalSpace X], HomologyFiniteType ℚ X → ℤ

def eulerCharacteristic_value (X : Type w) [TopologicalSpace X]
    (h : HomologyFiniteType ℚ X) : ℤ := topologicalEuler X h

def finiteSumFormula : Prop :=
  ∀ (F : Type u) [Field F] (X : Type w) [TopologicalSpace X]
    (_h : HomologyFiniteType F X) (N : ℕ),
    (∀ n : ℕ, N ≤ n → IsZero (homology F F (TopCat.of X) (n : ℤ))) →
    homologicalEuler F X = ∑ n ∈ Finset.range N,
      (-1 : ℤ)^n * (Module.finrank F (homology F F (TopCat.of X) (n : ℤ)) : ℤ)

def finiteCWFiniteType : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X],
    Finite (Σ n, Cell X n) → ∀ (F : Type u) [Field F], HomologyFiniteType F X

/-- Full Euler--Poincaré statement, including existence of the rational
finiteness certificate needed to evaluate the canonical invariant. -/
def eulerPoincare : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X],
    Finite (Σ n, Cell X n) → ∀ (F : Type u) [Field F],
    ∃ hQ : HomologyFiniteType ℚ X,
      HomologyFiniteType F X ∧ topologicalEuler X hQ = cellEuler X ∧
      cellEuler X = homologicalEuler F X

/-- Any upper bound on cell dimensions gives actual finite sums. -/
def finiteCWFormula : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X],
    Finite (Σ n, Cell X n) → ∀ (F : Type u) [Field F] (N : ℕ),
    (∀ n : ℕ, N ≤ n → IsEmpty (Cell X n)) →
    ∃ hQ : HomologyFiniteType ℚ X,
      topologicalEuler X hQ = ∑ n ∈ Finset.range N, (-1 : ℤ)^n * (Nat.card (Cell X n) : ℤ) ∧
      (∑ n ∈ Finset.range N, (-1 : ℤ)^n * (Nat.card (Cell X n) : ℤ)) =
        ∑ n ∈ Finset.range N, (-1 : ℤ)^n *
          (Module.finrank F (homology F F (TopCat.of X) (n : ℤ)) : ℤ)

def structureIndependence : Prop :=
  ∀ (X : Type w) [t : TopologicalSpace X] (s₁ s₂ : CWStructure X),
    Finite (Σ n, @Cell X t s₁.toCellStructure n) →
    Finite (Σ n, @Cell X t s₂.toCellStructure n) →
    @cellEuler X t s₁.toCellStructure = @cellEuler X t s₂.toCellStructure

def fieldIndependence : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X],
    Finite (Σ n, Cell X n) → ∀ (F : Type u) [Field F] (K : Type v) [Field K],
      homologicalEuler F X = homologicalEuler K X

/-- A finite graph is a finite CW complex with no cells of dimension ≥ 2.
This includes loops, repeated edges, isolated vertices and the empty graph. -/
def graphFormula : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X],
    Finite (Σ n, Cell X n) → (∀ n : ℕ, 2 ≤ n → IsEmpty (Cell X n)) →
    ∃ hQ : HomologyFiniteType ℚ X,
      topologicalEuler X hQ = (Nat.card (Cell X 0) : ℤ) - (Nat.card (Cell X 1) : ℤ)

def zeroDimensionalFormula : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X],
    Finite (Σ n, Cell X n) → (∀ n : ℕ, 1 ≤ n → IsEmpty (Cell X n)) →
    ∃ hQ : HomologyFiniteType ℚ X, topologicalEuler X hQ = (Nat.card (Cell X 0) : ℤ)

def emptyFormula : Prop :=
  ∀ (X : Type w) [TopologicalSpace X] [IsEmpty X],
    ∃ hQ : HomologyFiniteType ℚ X, topologicalEuler X hQ = 0

end Expected
end P202Specs.EulerPoincare
