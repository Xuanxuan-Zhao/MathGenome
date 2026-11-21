import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CartanMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Card

/-!
LA-E06-Classical, source res:E06, expanded lines 2243–2274, with the
rank ranges from res:E05, lines 2170–2176. Coordinates are numbered from zero.
These are explicit subsets of real Euclidean coordinate spaces. No root axiom,
root count, simple-basis property or diagram identification is assumed here.
-/
noncomputable section
namespace LieAlgebrasAndRepresentations.ClassicalCoordinates
open Set Module
open scoped Classical

abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The source's coordinate vectors εᵢ. -/
def epsilon {n : ℕ} (i : Fin n) : Space n := EuclideanSpace.single i 1

/-- The ambient hyperplane for Aₙ, in n+1 coordinates. -/
def zeroSum (n : ℕ) : Submodule ℝ (Space (n + 1)) where
  carrier := {x | ∑ i, x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change ∑ i, (x i + y i) = 0
    rw [Finset.sum_add_distrib, hx, hy, add_zero]
  smul_mem' := by
    intro c x hx
    change ∑ i, c * x i = 0
    rw [← Finset.mul_sum, hx, mul_zero]

/-- Ordered coordinate differences, regarded in their actual hyperplane. -/
def rootsA (n : ℕ) : Set (zeroSum n) :=
  {x | ∃ i j : Fin (n + 1), i ≠ j ∧ (x : Space (n + 1)) = epsilon i - epsilon j}

/-- Exactly the two signs, used independently for the two nonzero coordinates. -/
def sign (s : Bool) : ℝ := if s then -1 else 1

/-- The common two-coordinate part of Bₙ, Cₙ and Dₙ. -/
def pairRoots (n : ℕ) : Set (Space n) :=
  {x | ∃ i j : Fin n, i ≠ j ∧ ∃ s t : Bool,
    x = sign s • epsilon i + sign t • epsilon j}

/-- Coordinate roots of a specified length. -/
def axisRoots (n : ℕ) (length : ℝ) : Set (Space n) :=
  {x | ∃ i : Fin n, ∃ s : Bool, x = (length * sign s) • epsilon i}

def rootsB (n : ℕ) : Set (Space n) := axisRoots n 1 ∪ pairRoots n

def rootsC (n : ℕ) : Set (Space n) := axisRoots n 2 ∪ pairRoots n

def rootsD (n : ℕ) : Set (Space n) := pairRoots n

/-- The displayed adjacent coordinate differences for Aₙ. -/
def simpleA (n : ℕ) (i : Fin n) : zeroSum n :=
  ⟨epsilon i.castSucc - epsilon i.succ, by
    change ∑ j, (epsilon i.castSucc - epsilon i.succ) j = 0
    simp [epsilon, PiLp.sub_apply, Finset.sum_sub_distrib, PiLp.single_apply]⟩

/-- Adjacent differences and final coordinate root for Bₙ. -/
def simpleB (n : ℕ) (i : Fin n) : Space n :=
  if h : i.val + 1 < n then epsilon i - epsilon ⟨i.val + 1, h⟩ else epsilon i

/-- Adjacent differences and final doubled coordinate root for Cₙ. -/
def simpleC (n : ℕ) (i : Fin n) : Space n :=
  if h : i.val + 1 < n then epsilon i - epsilon ⟨i.val + 1, h⟩ else 2 • epsilon i

/-- Adjacent differences, with the last replaced by εₙ₋₂+εₙ₋₁ for Dₙ.
The definition is total; its asserted application below is n ≥ 4. -/
def simpleD (n : ℕ) (i : Fin n) : Space n :=
  if h : i.val + 1 < n then epsilon i - epsilon ⟨i.val + 1, h⟩
  else epsilon ⟨n - 2, by have := i.isLt; omega⟩ + epsilon i

/-- The unoriented path on the indexed simple roots. -/
def adjacent {n : ℕ} (i j : Fin n) : Prop := i.val + 1 = j.val ∨ j.val + 1 = i.val

/-- The last edge of the B/C path. -/
def terminalEdge {n : ℕ} (i j : Fin n) : Prop :=
  (i.val + 2 = n ∧ j.val + 1 = n) ∨ (j.val + 2 = n ∧ i.val + 1 = n)

/-- Dₙ has chain 0--...--(n-3) and two leaves n-2,n-1 attached at n-3. -/
def forkAdjacent {n : ℕ} (i j : Fin n) : Prop :=
  (i.val + 1 = j.val ∧ j.val + 1 < n) ∨
  (j.val + 1 = i.val ∧ i.val + 1 < n) ∨
  (i.val + 3 = n ∧ j.val + 1 = n) ∨
  (j.val + 3 = n ∧ i.val + 1 = n)

namespace Specs

/-- Each assertion preserves the rank ranges of the source's finite list. -/
def rootSystemAType : Prop := ∀ n : ℕ, 1 ≤ n → IsRootSystem (rootsA n)
def rootSystemBType : Prop := ∀ n : ℕ, 2 ≤ n → IsRootSystem (rootsB n)
def rootSystemCType : Prop := ∀ n : ℕ, 2 ≤ n → IsRootSystem (rootsC n)
def rootSystemDType : Prop := ∀ n : ℕ, 4 ≤ n → IsRootSystem (rootsD n)

def countAType : Prop := ∀ n : ℕ, 1 ≤ n → (rootsA n).ncard = n * (n + 1)
def countBType : Prop := ∀ n : ℕ, 2 ≤ n → (rootsB n).ncard = 2 * n ^ 2
def countCType : Prop := ∀ n : ℕ, 2 ≤ n → (rootsC n).ncard = 2 * n ^ 2
def countDType : Prop := ∀ n : ℕ, 4 ≤ n → (rootsD n).ncard = 2 * n * (n - 1)

/-- A basis must have exactly the source's vectors and be a simple system for
an actual regular positive system, in the canonical upstream sense. -/
def simpleDiagramAType : Prop := ∀ n : ℕ, 1 ≤ n →
  ∃ (v : zeroSum n) (b : Basis (Fin n) ℝ (zeroSum n)),
    (∀ i, b i = simpleA n i) ∧ RootRegular (rootsA n) v ∧ IsSimpleBasis (rootsA n) v b ∧
    (∀ i j, (dynkinDiagram b).edges i j = if adjacent i j then 1 else 0) ∧
    (∀ i j, ¬ (dynkinDiagram b).arrow i j)

def simpleDiagramBType : Prop := ∀ n : ℕ, 2 ≤ n →
  ∃ (v : Space n) (b : Basis (Fin n) ℝ (Space n)),
    (∀ i, b i = simpleB n i) ∧ RootRegular (rootsB n) v ∧ IsSimpleBasis (rootsB n) v b ∧
    (∀ i j, (dynkinDiagram b).edges i j =
      if terminalEdge i j then 2 else if adjacent i j then 1 else 0) ∧
    (∀ i j, (dynkinDiagram b).arrow i j ↔ i.val + 2 = n ∧ j.val + 1 = n)

def simpleDiagramCType : Prop := ∀ n : ℕ, 2 ≤ n →
  ∃ (v : Space n) (b : Basis (Fin n) ℝ (Space n)),
    (∀ i, b i = simpleC n i) ∧ RootRegular (rootsC n) v ∧ IsSimpleBasis (rootsC n) v b ∧
    (∀ i j, (dynkinDiagram b).edges i j =
      if terminalEdge i j then 2 else if adjacent i j then 1 else 0) ∧
    (∀ i j, (dynkinDiagram b).arrow i j ↔ i.val + 1 = n ∧ j.val + 2 = n)

def simpleDiagramDType : Prop := ∀ n : ℕ, 4 ≤ n →
  ∃ (v : Space n) (b : Basis (Fin n) ℝ (Space n)),
    (∀ i, b i = simpleD n i) ∧ RootRegular (rootsD n) v ∧ IsSimpleBasis (rootsD n) v b ∧
    (∀ i j, (dynkinDiagram b).edges i j = if forkAdjacent i j then 1 else 0) ∧
    (∀ i j, ¬ (dynkinDiagram b).arrow i j)

end Specs
end LieAlgebrasAndRepresentations.ClassicalCoordinates
