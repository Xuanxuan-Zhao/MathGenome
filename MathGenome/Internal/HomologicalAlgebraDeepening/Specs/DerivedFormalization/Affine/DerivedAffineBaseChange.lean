import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.TensorResolutionComparison
import Mathlib.RingTheory.TensorProduct.Basic

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v

namespace Specs.DerivedFormalization.Affine.DerivedAffineBaseChange

open _root_.DerivedFormalization.Affine
open NonpositiveCDGA (h0Functor h0Map)
open Tensor (ModuleTensor dgCat)
open TensorResolutionComparison

noncomputable section

variable {k : Type u} [Field k] [CharZero k]
variable {A B C : NonpositiveCDGA.{u,v} k}

/-- The ordinary tensor of the cohomology algebras, with the two
`H⁰(A)`-actions induced by the specified maps. -/
def h0Tensor (f : A ⟶ B) (g : A ⟶ C) :
    PushoutCocone ((h0Functor k).map f) ((h0Functor k).map g) := by
  letI : Algebra A.H0 B.H0 := (h0Map f).toRingHom.toAlgebra
  letI : Algebra A.H0 C.H0 := (h0Map g).toRingHom.toAlgebra
  letI : IsScalarTower k A.H0 B.H0 := IsScalarTower.of_algHom (h0Map f)
  letI : IsScalarTower k A.H0 C.H0 := IsScalarTower.of_algHom (h0Map g)
  let L := B.H0 ⊗[A.H0] C.H0
  let l : B.H0 →ₐ[k] L := Algebra.TensorProduct.includeLeft
  let r : C.H0 →ₐ[k] L := Algebra.TensorProduct.includeRight.restrictScalars k
  refine PushoutCocone.mk (W := CommAlgCat.of k L)
    (CommAlgCat.ofHom l) (CommAlgCat.ofHom r) ?_
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  exact (Algebra.TensorProduct.includeLeft (R := A.H0) (S := A.H0)
    (A := B.H0) (B := C.H0)).commutes x |>.trans
    ((Algebra.TensorProduct.includeRight (R := A.H0) (A := B.H0)
      (B := C.H0)).commutes x).symm

variable {T : ModuleTensor.{u,v} k} (S : CoproductModel T)

/-- The isomorphism identifies the two factor maps, using the augmentation on
the resolved factor. Thus the left equation also determines the canonical
map from `H⁰(B)` via the inverse of `H⁰(P) → H⁰(B)`. -/
def IsH0Comparison {f : A ⟶ B} (P : Resolution f) (g : A ⟶ C)
    (e : (h0Functor k).obj (S.tensor P.base g) ≅ (h0Tensor f g).pt) : Prop :=
  (h0Functor k).map (S.inl P.base g) ≫ e.hom =
      (h0Functor k).map P.augmentation ≫ (h0Tensor f g).inl ∧
    (h0Functor k).map (S.inr P.base g) ≫ e.hom = (h0Tensor f g).inr

/-- The canonical `k`-algebra isomorphism for every allowed one-sided model. -/
def H0Comparisons : Prop :=
  ∀ {A B C : NonpositiveCDGA.{u,v} k} {f : A ⟶ B} (P : Resolution f) (g : A ⟶ C),
    ∃! e : (h0Functor k).obj (S.tensor P.base g) ≅ (h0Tensor f g).pt,
      IsH0Comparison S P g e

/-- A compatible map of resolved diagrams induces the ordinary tensor map
on `H⁰`. The base algebras may vary. -/
def H0Naturality : Prop :=
  ∀ {A B C A' B' C' : NonpositiveCDGA.{u,v} k}
    {f : A ⟶ B} {g : A ⟶ C} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
    (P : Resolution f) (P' : Resolution f')
    (p : P.obj ⟶ P'.obj) (b : B ⟶ B') (c : C ⟶ C')
    (t : S.tensor P.base g ⟶ S.tensor P'.base g'),
    p ≫ P'.augmentation = P.augmentation ≫ b →
    S.inl P.base g ≫ t = p ≫ S.inl P'.base g' →
    S.inr P.base g ≫ t = c ≫ S.inr P'.base g' →
    ∀ {e : (h0Functor k).obj (S.tensor P.base g) ≅ (h0Tensor f g).pt}
      {e' : (h0Functor k).obj (S.tensor P'.base g') ≅ (h0Tensor f' g').pt},
    IsH0Comparison S P g e → IsH0Comparison S P' g' e' →
    ∃ m : (h0Tensor f g).pt ⟶ (h0Tensor f' g').pt,
      (h0Tensor f g).inl ≫ m = (h0Functor k).map b ≫ (h0Tensor f' g').inl ∧
      (h0Tensor f g).inr ≫ m = (h0Functor k).map c ≫ (h0Tensor f' g').inr ∧
      e.hom ≫ m = (h0Functor k).map t ≫ e'.hom

/-- The model, its strict quasi-isomorphism comparisons, the opposite-variance
affine diagrams, and the natural zeroth cohomology formula for the same
one-sided tensor model. -/
def BaseChange : Prop :=
  TensorModels.{u,v} ∧
    ∀ {k : Type u} [Field k] [CharZero k]
      {T : ModuleTensor.{u,v} k} (S : CoproductModel T),
      H0Comparisons S ∧ H0Naturality S

end

end Specs.DerivedFormalization.Affine.DerivedAffineBaseChange
