import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.CellularComparison
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Fintype.Powerset

/-!
The torus part of paper.tex, Proposition `prop:p202-homology-computations`,
lines 1597–1599 and 1624–1627. The space below is the actual finite product
of unit circles, with its product topology. The CW assertion specifies both
its open cells and its characteristic maps, rather than an abstract complex
with the desired ranks. All nonnegative homology degrees are included.
-/
noncomputable section
open CategoryTheory Topology

namespace P202Specs.TorusHomology
open P202.Cellular P202Specs.CellularChains P202Specs.SingularChains

/-- The unit complex circle is the standard geometric circle S¹. -/
abbrev Torus (m : ℕ) := Fin m → Circle

/-- One n-cell for each n-element set of active circle coordinates. -/
abbrev ActiveSet (m n : ℕ) := {s : Finset (Fin m) // s.card = n}

/-- Cubes indexed by the selected coordinates, with the ordinary product topology. -/
abbrev Cube {m : ℕ} (s : Finset (Fin m)) := s → unitInterval

def cubeInterior {m : ℕ} (s : Finset (Fin m)) : Set (Cube s) :=
  {x | ∀ i, 0 < (x i : ℝ) ∧ (x i : ℝ) < 1}

/-- The standard oriented loop, starting and ending at 1. -/
def circleLoop : C(unitInterval, Circle) where
  toFun t := Circle.exp (2 * Real.pi * (t : ℝ))
  continuous_toFun := Circle.exp.continuous.comp (by fun_prop)

/-- Inactive coordinates are the vertex 1; active ones traverse the circle. -/
def cubeChart {m : ℕ} (s : Finset (Fin m)) : C(Cube s, Torus m) where
  toFun x i := if h : i ∈ s then circleLoop (x ⟨i, h⟩) else 1
  continuous_toFun := by
    classical
    apply continuous_pi
    intro i
    by_cases h : i ∈ s
    · simpa only [dite_eq_left h, Function.comp_def] using circleLoop.continuous.comp (continuous_apply (⟨i, h⟩ : s))
    · simpa only [dite_eq_right h] using (continuous_const : Continuous (fun _ : Cube s => (1 : Circle)))

/-- The actual product open cell: precisely the selected coordinates differ from 1. -/
def coordinateStratum {m : ℕ} (s : Finset (Fin m)) : Set (Torus m) :=
  {z | ∀ i, z i ≠ 1 ↔ i ∈ s}

/-- This specifies the product cubical CW structure, retaining its actual disk
parametrizations and the identification of disk interiors with cube interiors.
The choice of a disk-to-cube homeomorphism does not prescribe an orientation. -/
def IsProductCubical {m : ℕ} (C : CWStructure (Torus m)) : Prop :=
  letI : CWStructure (Torus m) := C
  ∃ cells : ∀ n, Cell (Torus m) n ≃ ActiveSet m n,
    ∀ n (c : Cell (Torus m) n),
      openCell (Torus m) n c = coordinateStratum (cells n c).val ∧
      ∃ h : Disk n ≃ₜ Cube (cells n c).val,
        (∀ x : Disk n, h x ∈ cubeInterior (cells n c).val ↔ ‖x.val‖ < 1) ∧
        characteristic (Torus m) n c =
          (cubeChart (cells n c).val).comp ⟨h, h.continuous⟩

namespace Expected

/-- Existence is unconditional; a CW structure is not an input assumption. -/
def cubicalStructure : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ C : CWStructure (Torus m), IsProductCubical C

/-- Vanishing concerns the connecting-map differential of the genuine skeleta,
for every dimension and every disk orientation of the specified product cells. -/
def zeroDifferentials : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ C : CWStructure (Torus m), IsProductCubical C →
    letI : CWStructure (Torus m) := C
    ∀ n : ℕ, differential (Torus m) ℤ ℤ n = 0

/-- Ordinary integral singular homology of the actual torus, including j=0,
j=m and j>m. A function on Fin 0 is the zero module. -/
def homology : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ j : ℕ,
    Nonempty (P202Specs.SingularChains.homology ℤ ℤ (TopCat.of (Torus m)) (j : ℤ)
      ≃ₗ[ℤ] (Fin (m.choose j) → ℤ))

end Expected
end P202Specs.TorusHomology
