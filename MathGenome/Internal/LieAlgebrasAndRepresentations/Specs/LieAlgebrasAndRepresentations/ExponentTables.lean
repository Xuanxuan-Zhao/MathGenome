import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.ExceptionalCoordinateE
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Order.Floor.Semiring

/-! The height table following res:E09, source lines 2500–2525.
A height functional takes value 1 on the given simple roots. Positivity
uses the regular vector of the coordinate realization. -/

noncomputable section
open scoped Classical
open Finset Polynomial

namespace LieAlgebrasAndRepresentations.ExponentTables
open ClassicalCoordinates
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def heightSlice (R : Set V) (v : V) (f : V → ℝ) (k : ℕ) : Set V :=
  {a ∈ positiveRoots R v | f a = (k : ℝ)}

def heightPolynomial (R : Set V) (v : V) (f : V → ℝ)
    (hfin : (positiveRoots R v).Finite) : ℕ[X] :=
  ∑ a ∈ hfin.toFinset, X ^ ⌊f a⌋₊

/-- One exponent of size m contributes one root at each height 1 through m. -/
def heightStrip (m : ℕ) : ℕ[X] :=
  ∑ i ∈ range m, X ^ (i + 1)

def exponentPolynomial (ms : List ℕ) : ℕ[X] :=
  (ms.map heightStrip).sum

/-- A row of the table, with multiplicities defined by successive height counts.
The highest-root height is the greatest positive height, by res:E09. -/
def TableRow {ι : Type*} [Fintype ι] (R : Set V) (simple : ι → V)
    (ms : List ℕ) (h : ℕ) : Prop :=
  ∃ (v : V) (b : Module.Basis ι ℝ V) (f : V →ₗ[ℝ] ℝ) (hfin : (positiveRoots R v).Finite),
    RootRegular R v ∧ IsSimpleBasis R v b ∧ (∀ i, b i = simple i) ∧
    (∀ i, f (simple i) = 1) ∧
    (∀ a ∈ positiveRoots R v, ∃ k : ℕ, 0 < k ∧ f a = (k : ℝ)) ∧
    heightPolynomial R v f hfin = exponentPolynomial ms ∧
    (∀ m : ℕ, 0 < m →
      (heightSlice R v f m).ncard - (heightSlice R v f (m + 1)).ncard = ms.count m) ∧
    (∃ k : ℕ, h = k + 1 ∧ IsGreatest (f '' positiveRoots R v) (k : ℝ))

namespace Specs

def typeA : Prop :=
  ∀ n : ℕ, 1 ≤ n → TableRow (rootsA n) (simpleA n) ((List.range n).map (· + 1)) (n + 1)

def typeB : Prop :=
  ∀ n : ℕ, 2 ≤ n → TableRow (rootsB n) (simpleB n) ((List.range n).map (fun i => 2*i+1)) (2*n)

def typeC : Prop :=
  ∀ n : ℕ, 2 ≤ n → TableRow (rootsC n) (simpleC n) ((List.range n).map (fun i => 2*i+1)) (2*n)

def typeD : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    TableRow (rootsD n) (simpleD n) (((List.range (n-1)).map (fun i => 2*i+1)) ++ [n-1]) (2*n-2)

/-- The repeated exponent for even Dₙ ranks is counted twice. -/
def typeD_forkMultiplicity : Prop :=
  ∀ n : ℕ, 4 ≤ n →
    ((((List.range (n-1)).map (fun i => 2*i+1)) ++ [n-1]).count (n-1)) =
      if Even n then 2 else 1

open ExceptionalGF ExceptionalE

def typeG₂ : Prop := TableRow g2Roots g2Simple [1,5] 6
def typeF₄ : Prop := TableRow f4Roots f4Simple [1,5,7,11] 12
def typeE₆ : Prop := TableRow e6Roots e6Simple [1,4,5,7,8,11] 12
def typeE₇ : Prop := TableRow e7Roots e7Simple [1,5,7,9,11,13,17] 18
def typeE₈ : Prop := TableRow e8Roots e8Simple [1,7,11,13,17,19,23,29] 30

end Specs
end LieAlgebrasAndRepresentations.ExponentTables
