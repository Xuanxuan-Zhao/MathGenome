import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.GroupSchemes
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u

namespace LinearAlgebraicGroups

noncomputable section

variable {k : Type u} [Field k] {H X T Z : SchemeOver k}

/-- A morphism is fixed if the action on its family is the projection over the family. -/
def IsFixedBy (a : H ⊗ X ⟶ X) (x : T ⟶ X) : Prop :=
  (H ◁ x) ≫ a = snd H T ≫ x

/-- The inclusion represents fixed families by its canonical map on points.
Closed immersions make the lifts unique. -/
def RepresentsFixedPoints (a : H ⊗ X ⟶ X) (i : Z ⟶ X) : Prop :=
  ∀ (T : SchemeOver k) (x : T ⟶ X), IsFixedBy a x ↔ ∃ y : T ⟶ Z, y ≫ i = x

/-- The action on the scalar extensions, expressed using the product comparison. -/
def baseChangeAction (K : Type u) [Field K] [Algebra k K] (a : H ⊗ X ⟶ X) :
    (baseChange k K).obj H ⊗ (baseChange k K).obj X ⟶ (baseChange k K).obj X :=
  (prodComparisonIso (baseChange k K) H X).inv ≫ (baseChange k K).map a

namespace Specs

def FixedPointScheme : Prop :=
  ∀ (k : Type u) [Field k] (H : AffineAlgebraicGroup k) (X : SchemeOver k)
    (act : ModObj H.1.X X), IsSeparated X.hom → LocallyOfFiniteType X.hom →
    QuasiCompact X.hom →
    ∃ (Z : SchemeOver k) (i : Z ⟶ X), IsClosedImmersion i.left ∧
      RepresentsFixedPoints act.smul i

def FixedPointSchemeBaseChange : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    {H X Z : SchemeOver k} (a : H ⊗ X ⟶ X) (i : Z ⟶ X),
    IsClosedImmersion i.left → RepresentsFixedPoints a i →
    IsClosedImmersion ((baseChange k K).map i).left ∧
      RepresentsFixedPoints (baseChangeAction K a) ((baseChange k K).map i)

def IsFixedByIffForallPoints : Prop :=
  ∀ (k : Type u) [Field k] {H X : SchemeOver k}, IsAffine H.left →
    (∀ (a : H ⊗ X ⟶ X) {R : TestAlgebra k} (x : Points X R),
    IsFixedBy a x ↔ ∀ (S : TestAlgebra k) (f : R ⟶ S) (h : Points H S),
      lift h (mapPoints f x) ≫ a = mapPoints f x)

end Specs
end
end LinearAlgebraicGroups
