import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.GroupSchemes
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj

universe u

namespace LinearAlgebraicGroups.Specs.WordDomainGeometry

/-- A smooth connected affine algebraic group is integral. -/
def SmoothConnectedGroupIntegral : Prop :=
  ∀ {k : Type u} [Field k] [PerfectField k] (G : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left → IsIntegral G.val.X.left

/-- The binary fiber product of smooth connected affine algebraic groups over the field. -/
def SmoothConnectedGroupProduct : Prop :=
  ∀ {k : Type u} [Field k] [PerfectField k] (G H : AffineAlgebraicGroup k),
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left →
    Smooth H.val.X.hom → ConnectedSpace H.val.X.left →
    let X := G.val.X ⊗ H.val.X
    Smooth X.hom ∧ ConnectedSpace X.left ∧ IsIntegral X.left

/-- Smoothness, connectedness and integrality of a finite product over the field. -/
def SmoothConnectedGroupFiniteProduct : Prop :=
  ∀ {k : Type u} [Field k] [PerfectField k] (I : Type u) [Finite I]
    (G : I → AffineAlgebraicGroup k),
    (∀ i, Smooth (G i).val.X.hom ∧ ConnectedSpace (G i).val.X.left) →
    let X := ∏ᶜ fun i ↦ (G i).val.X
    Smooth X.hom ∧ ConnectedSpace X.left ∧ IsIntegral X.left

/-- The image on rational points of a dominant morphism generates the target group. -/
def DominantImageGenerates : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOver k)
    [IsAffine X.left] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (Q : AffineAlgebraicGroup k) [IsReduced Q.val.X.left] [IrreducibleSpace Q.val.X.left]
    (f : X ⟶ Q.val.X) [IsDominant f.left]
    (S : Subgroup ((𝟙_ (SchemeOver k)) ⟶ Q.val.X)),
    (∀ p : (𝟙_ (SchemeOver k)) ⟶ X, p ≫ f ∈ S) → S = ⊤

end LinearAlgebraicGroups.Specs.WordDomainGeometry
