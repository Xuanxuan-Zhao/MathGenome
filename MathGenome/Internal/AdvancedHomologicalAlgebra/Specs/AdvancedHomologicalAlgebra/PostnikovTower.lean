import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.GoodTruncations
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.StandardHeart
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.Data.Int.Interval

/-!
HA-D08 (first conclusion), notes/002/advanced-homological-algebra.tex:1715–1730.
The ambient category and cochain shifts are those of HA-D03 and HA-D07.
`stage A i` is τ≤i, represented by the standard t-structure truncation.
Thus `truncLT i` is precisely τ≤(i-1). The index set of attachments of a
bounded tower is the finite integer interval [a,b]. No resolution hypothesis
or Ext vanishing is imposed. Natural transformations below include the
naturality of the attachment maps, not merely objectwise triangles.
-/
set_option linter.checkUnivs false
universe w v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Specs.AdvancedHomologicalAlgebra.DerivedCategory
open Specs.AdvancedHomologicalAlgebra.StandardHeart

namespace Specs.AdvancedHomologicalAlgebra.PostnikovTower

noncomputable abbrev stage (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (i : ℤ) : D A ⥤ D A := (standardT A).truncLT (i + 1)

noncomputable abbrev layer (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (i : ℤ) : D A ⥤ D A :=
  HD A i ⋙ stalk A ⋙ shiftFunctor (D A) (-i)

noncomputable abbrev step (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (i : ℤ) :
    (standardT A).truncLT i ⟶ stage A i :=
  (standardT A).natTransTruncLTOfLE i (i + 1) (by omega)

/-- One family, natural in all objects of D(A), of the displayed triangles. -/
structure NaturalTower (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] where
  projection (i : ℤ) : stage A i ⟶ layer A i
  attachment (i : ℤ) : layer A i ⟶
    (standardT A).truncLT i ⋙ shiftFunctor (D A) (1 : ℤ)
  distinguished (i : ℤ) (K : D A) :
    Triangle.mk ((step A i).app K) ((projection i).app K)
      ((attachment i).app K) ∈ distTriang (D A)

/-- A finite restriction, with the chosen cohomological bounds as endpoints.
The initial vertex is τ≤(a-1) and the last is τ≤b. The endpoint map is
specifically the truncation inclusion, not an unrelated isomorphism. -/
structure FiniteTower {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (K : D A) (a b : ℤ) where
  naturalTower : NaturalTower A
  ordered : a ≤ b
  initial : IsZero (((standardT A).truncLT a).obj K)
  terminal : IsIso (((standardT A).truncLTι (b + 1)).app K)
  /-- Explicit finite list of all the successive attachment triangles. -/
  rows (i : ℤ) (_ : i ∈ Finset.Icc a b) :
    Triangle.mk ((step A i).app K) ((naturalTower.projection i).app K)
      ((naturalTower.attachment i).app K) ∈ distTriang (D A)

/-- The triangles exist even without boundedness. -/
def naturalTowerType := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A], Nonempty (NaturalTower A)

/-- At any chosen ordered cohomological bounds the tower starts at zero and ends at K. -/
def finiteTowerType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (K : D A) (a b : ℤ), a ≤ b →
  (∀ i : ℤ, i < a → IsZero ((HD A i).obj K)) →
  (∀ i : ℤ, b < i → IsZero ((HD A i).obj K)) →
  Nonempty (FiniteTower K a b)

/-- Bounded cohomology alone suffices, including acyclic objects and unordered
initial witnesses for bounds. -/
def boundedTowerType : Prop := ∀ (A : Type u) [Category.{v} A] [Abelian A]
  [HasDerivedCategory.{w} A] (K : D A),
  (∃ a b : ℤ, (∀ i : ℤ, i < a → IsZero ((HD A i).obj K)) ∧
    (∀ i : ℤ, b < i → IsZero ((HD A i).obj K))) →
  ∃ a b : ℤ, Nonempty (FiniteTower K a b)

end Specs.AdvancedHomologicalAlgebra.PostnikovTower
