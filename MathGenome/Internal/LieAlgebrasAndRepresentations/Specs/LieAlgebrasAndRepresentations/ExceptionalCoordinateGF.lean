import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CartanMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Fin.Tuple.Basic

/-! The G₂ and F₄ parts of res:E06 (source lines 2276–2319).
The finite rational lists are precisely the source coordinate formulas, not
abstract root systems selected by their cardinalities or diagrams. -/
noncomputable section
namespace LieAlgebrasAndRepresentations.ExceptionalGF
open Set Module

abbrev QVec (n : ℕ) := Fin n → ℚ
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

def unit {n : ℕ} (i : Fin n) : QVec n := Pi.single i 1

def sign (b : Bool) : ℚ := if b then -1 else 1

def realize {n : ℕ} (q : QVec n) : Space n :=
  WithLp.toLp 2 (fun i => (q i : ℝ))

def g2Short : Finset (QVec 3) :=
  ((Finset.univ : Finset (Fin 3 × Fin 3)).filter (fun p => p.1 ≠ p.2)).image
    (fun p => unit p.1 - unit p.2)

/-- `3 εᵢ − (1,1,1)` is `2 εᵢ − εⱼ − εₖ` for the other two indices. -/
def g2Long : Finset (QVec 3) :=
  (Finset.univ : Finset (Fin 3 × Bool)).image
    (fun p => sign p.2 • (3 • unit p.1 - fun _ => 1))

def g2List : Finset (QVec 3) := g2Short ∪ g2Long

def g2AmbientRoots : Set (Space 3) := realize '' (g2List : Set (QVec 3))

def g2Plane : Submodule ℝ (Space 3) where
  carrier := {x | ∑ i, x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change ∑ i, x i = 0 at hx
    change ∑ i, y i = 0 at hy
    change ∑ i, (x i + y i) = 0
    rw [Finset.sum_add_distrib, hx, hy, add_zero]
  smul_mem' := by
    intro t x hx
    change ∑ i, x i = 0 at hx
    change ∑ i, t * x i = 0
    rw [← Finset.mul_sum, hx, mul_zero]

def g2Roots : Set g2Plane := {x | (x : Space 3) ∈ g2AmbientRoots}

def g2SimpleAmbient : Fin 2 → Space 3 :=
  ![realize ![1,-1,0], realize ![-2,1,1]]

def g2RegularAmbient : Space 3 := realize ![-1,-2,3]

def g2Simple : Fin 2 → g2Plane := fun i =>
  ⟨g2SimpleAmbient i, by fin_cases i <;>
    norm_num [g2SimpleAmbient, realize, g2Plane, Fin.sum_univ_succ]⟩

def g2Regular : g2Plane :=
  ⟨g2RegularAmbient, by norm_num [g2RegularAmbient, realize, g2Plane, Fin.sum_univ_succ]⟩

def f4Coordinate : Finset (QVec 4) :=
  (Finset.univ : Finset (Fin 4 × Bool)).image (fun p => sign p.2 • unit p.1)

def f4Long : Finset (QVec 4) :=
  ((Finset.univ : Finset ((Fin 4 × Fin 4) × (Bool × Bool))).filter
    (fun p => p.1.1 < p.1.2)).image
    (fun p => sign p.2.1 • unit p.1.1 + sign p.2.2 • unit p.1.2)

def f4Half : Finset (QVec 4) :=
  (Finset.univ : Finset (Fin 4 → Bool)).image (fun b i => sign (b i) / 2)

def f4List : Finset (QVec 4) := f4Coordinate ∪ f4Long ∪ f4Half

def f4Roots : Set (Space 4) := realize '' (f4List : Set (QVec 4))

def f4Simple : Fin 4 → Space 4 :=
  ![realize ![0,1,-1,0], realize ![0,0,1,-1], realize ![0,0,0,1],
    realize ![1/2,-1/2,-1/2,-1/2]]

def f4Regular : Space 4 := realize ![8,3,2,1]

namespace Specs

def g2Axioms : Prop := IsRootSystem g2Roots

def f4Axioms : Prop := IsRootSystem f4Roots

def g2Count : Prop := g2Roots.ncard = 12

def f4Count : Prop := f4Roots.ncard = 48 ∧
  (realize '' (f4Coordinate : Set (QVec 4))).ncard = 8 ∧
  (realize '' (f4Long : Set (QVec 4))).ncard = 24 ∧
  (realize '' (f4Half : Set (QVec 4))).ncard = 16 ∧
  Disjoint f4Coordinate f4Long ∧ Disjoint f4Coordinate f4Half ∧ Disjoint f4Long f4Half

def g2Basis : Prop :=
  RootRegular g2Roots g2Regular ∧
  ∃ b : Basis (Fin 2) ℝ g2Plane,
    (∀ i, b i = g2Simple i) ∧ IsSimpleBasis g2Roots g2Regular b

def f4Basis : Prop :=
  RootRegular f4Roots f4Regular ∧
  ∃ b : Basis (Fin 4) ℝ (Space 4),
    (∀ i, b i = f4Simple i) ∧ IsSimpleBasis f4Roots f4Regular b

def g2Diagram : Prop :=
  cartanMatrix g2Simple = !![2,-3; -1,2] ∧
  (∀ i j, (dynkinDiagram g2Simple).edges i j = if i = j then 0 else 3) ∧
  (∀ i j, (dynkinDiagram g2Simple).arrow i j ↔ i = 1 ∧ j = 0)

def f4Diagram : Prop :=
  cartanMatrix f4Simple = !![2,-1,0,0; -1,2,-1,0; 0,-2,2,-1; 0,0,-1,2] ∧
  (∀ i j, (dynkinDiagram f4Simple).edges i j =
    (!![0,1,0,0; 1,0,2,0; 0,2,0,1; 0,0,1,0] : Matrix (Fin 4) (Fin 4) ℕ) i j) ∧
  (∀ i j, (dynkinDiagram f4Simple).arrow i j ↔ i = 1 ∧ j = 2)

end Specs
end LieAlgebrasAndRepresentations.ExceptionalGF
