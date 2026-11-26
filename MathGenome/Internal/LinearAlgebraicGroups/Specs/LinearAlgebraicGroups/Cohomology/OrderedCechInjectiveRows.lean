import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Topology.Sheaves.SheafCondition.Sites

open CategoryTheory Opposite TopologicalSpace

universe u v
noncomputable section

namespace LinearAlgebraicGroups.Specs.OrderedCechInjectiveRows

variable {X : TopCat.{u}} {I : Type v} [LinearOrder I]

abbrev RingSheaf (X : TopCat.{u}) := Sheaf (Opens.grothendieckTopology X) RingCat.{u}

/-- The open on which the component of an ordered Čech cochain is defined. -/
def tupleOpen (U : I → Opens X) {p : ℕ} (e : Fin (p + 1) ↪o I) : Opens X :=
  ⨅ j, U (e j)

/-- Delete the vertex in position `i`. -/
def face {p : ℕ} (e : Fin (p + 2) ↪o I) (i : Fin (p + 2)) : Fin (p + 1) ↪o I :=
  i.succAboveOrderEmb.trans e

theorem tupleOpen_le_face (U : I → Opens X) {p : ℕ} (e : Fin (p + 2) ↪o I)
    (i : Fin (p + 2)) : tupleOpen U e ≤ tupleOpen U (face e i) :=
  le_iInf fun j => iInf_le _ (i.succAbove j)

abbrev Cochains {R : RingSheaf X} (M : SheafOfModules.{u} R) (U : I → Opens X)
    (p : ℕ) : Type (max u v) :=
  ∀ e : Fin (p + 1) ↪o I, M.val.obj (op (tupleOpen U e))

/-- The signed sum of the restrictions from the faces of each tuple. -/
def differential {R : RingSheaf X} (M : SheafOfModules.{u} R) (U : I → Opens X)
    (p : ℕ) (c : Cochains M U p) : Cochains M U (p + 1) :=
  fun e => ∑ i : Fin (p + 2),
    (-1 : ℤ) ^ (i : ℕ) • M.val.map (homOfLE (tupleOpen_le_face U e i)).op (c (face e i))

/-- Positive-degree ordered Čech cocycles with injective coefficients are coboundaries. -/
def InjectiveRowExactness : Prop :=
  ∀ (X : TopCat.{u}) (R : RingSheaf X) (I : Type v) [LinearOrder I] [Finite I]
    (U : I → Opens X), (⨆ i, U i) = ⊤ →
    ∀ (M : SheafOfModules.{u} R), Injective M →
    ∀ (p : ℕ) (c : Cochains M U (p + 1)),
      differential M U (p + 1) c = 0 →
        ∃ b : Cochains M U p, differential M U p b = c

end LinearAlgebraicGroups.Specs.OrderedCechInjectiveRows
