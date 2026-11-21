import MathGenome.Internal.AlgebraCore.Specs.P103.Ch02.FlatnessTests
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Module.ULift
import Mathlib.LinearAlgebra.StdBasis

/-!
The filtered-colimit part of Theorem 2.5, paper.tex 419–479.
The base ring need not be commutative or nonzero. No injectivity condition is
imposed on transition maps. Right modules use the opposite ring.
-/

noncomputable section
universe u v w

open CategoryTheory CategoryTheory.Limits

namespace P103.Specs.Ch02.GovorovLazard

variable (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]

/-- Objects are all maps from standard finite free left modules to M. -/
structure FreeTo where
  rank : ℕ
  toM : (Fin rank → R) →ₗ[R] M

namespace FreeTo
variable {R M}

/-- Arrows are arbitrary linear maps over M. -/
@[ext] structure Hom (X Y : FreeTo R M) : Type (max u v) where
  linear : (Fin X.rank → R) →ₗ[R] (Fin Y.rank → R)
  over : Y.toM.comp linear = X.toM

instance : Category (FreeTo R M) where
  Hom := Hom
  id X := ⟨LinearMap.id, by simp⟩
  comp f g := ⟨g.linear.comp f.linear, by rw [← LinearMap.comp_assoc, g.over, f.over]⟩

/-- Raise the carrier universe to accommodate the canonical cocone over M. -/
abbrev carrier (X : FreeTo R M) := ULift.{v} (Fin X.rank → R)

/-- The underlying standard-free-module diagram. -/
def diagram : FreeTo R M ⥤ ModuleCat.{max u v} R where
  obj X := ModuleCat.of R X.carrier
  map f := ModuleCat.ofHom
    (ULift.moduleEquiv.symm.toLinearMap.comp (f.linear.comp ULift.moduleEquiv.toLinearMap))

/-- The given maps to M form the canonical cocone. -/
def cocone : Cocone (diagram (R := R) (M := M)) where
  pt := ModuleCat.of R (ULift.{u} M)
  ι :=
    { app := fun X => ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap.comp (X.toM.comp ULift.moduleEquiv.toLinearMap))
      naturality := by
        intro X Y f
        apply ModuleCat.hom_ext
        ext x
        exact congrArg ULift.up (LinearMap.congr_fun f.over x.down) }

end FreeTo

/-- A categorical filtered colimit of finite-rank free modules, with no
restrictions on the transition maps. The category is a set-sized category. -/
def IsFilteredColimitOfFiniteFree : Prop :=
  ∃ (J : Type (max u v)) (_ : SmallCategory J) (_ : IsFiltered J)
    (F : J ⥤ ModuleCat.{max u v} R) (c : Cocone F),
    Nonempty (c.pt ≃ₗ[R] M) ∧
    (∀ j, ∃ n : ℕ, Nonempty ((Fin n → R) ≃ₗ[R] F.obj j)) ∧
    Nonempty (IsColimit c)

def canonical_filteredType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
    FlatnessTests.FiniteRelations R M → IsFiltered (FreeTo R M)

/-- When the finite-free category is filtered, its canonical cocone is a colimit. -/
def canonical_colimitType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
    IsFiltered (FreeTo R M) →
    Nonempty (IsColimit (FreeTo.cocone (R := R) (M := M)))

def flat_filteredColimitType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
    FlatnessTests.Flat.{u,v,w} R M → IsFilteredColimitOfFiniteFree R M

def flat_iff_filteredColimitType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
    FlatnessTests.Flat.{u,v,w} R M ↔ IsFilteredColimitOfFiniteFree R M

def right_flat_iff_filteredColimitType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module Rᵐᵒᵖ M],
    FlatnessTests.RightFlat.{u,v,w} R M ↔ IsFilteredColimitOfFiniteFree Rᵐᵒᵖ M

/-- Every natural transformation of filtered diagrams which is injective
at each object induces an injective map on their colimits. -/
def filtered_colimit_injectiveType : Prop :=
  ∀ (R : Type u) [Ring R] (J : Type v) [SmallCategory J] [IsFiltered J]
    (F G : J ⥤ ModuleCat.{max u v} R) (α : F ⟶ G)
    (c : Cocone F) (d : Cocone G) (_hc : IsColimit c) (_hd : IsColimit d)
    (f : c.pt ⟶ d.pt),
    (∀ j, Function.Injective (α.app j)) →
    (∀ j, c.ι.app j ≫ f = α.app j ≫ d.ι.app j) → Function.Injective f

/-- Balanced tensor with any fixed right module commutes with filtered
module colimits. The comparisons specify the diagram and cocone on elementary
tensors; the colimit comparison is an additive isomorphism. -/
def tensor_colimitType : Prop :=
  ∀ (R : Type u) [Ring R] (J : Type v) [SmallCategory J] [IsFiltered J]
    (F : J ⥤ ModuleCat.{max u v} R) (c : Cocone F) (_hc : IsColimit c)
    (A : Type w) [AddCommGroup A] [Module Rᵐᵒᵖ A],
    ∃ (D : J ⥤ AddCommGrpCat.{max u v w}) (d : Cocone D)
      (e : ∀ j, P103.BalancedTensor.Tensor R A (F.obj j) ≃+ D.obj j)
      (ept : P103.BalancedTensor.Tensor R A c.pt ≃+ d.pt),
      (∀ (i j : J) (f : i ⟶ j) a m,
        D.map f (e i (P103.BalancedTensor.tmul R a m)) =
          e j (P103.BalancedTensor.tmul R a (F.map f m))) ∧
      (∀ j a m, d.ι.app j (e j (P103.BalancedTensor.tmul R a m)) =
        ept (P103.BalancedTensor.tmul R a (c.ι.app j m))) ∧
      Nonempty (IsColimit d)

/-- The complete four-way equivalence, also recording the exactness formulation. -/
def characterizationsType : Prop :=
  ∀ (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M],
    (FlatnessTests.Flat.{u,v,w} R M ↔ FlatnessTests.TensorExact.{u,v,w} R M) ∧
    (FlatnessTests.Flat.{u,v,w} R M ↔ FlatnessTests.IdealTest R M) ∧
    (FlatnessTests.Flat.{u,v,w} R M ↔ FlatnessTests.FiniteRelations R M) ∧
    (FlatnessTests.Flat.{u,v,w} R M ↔ IsFilteredColimitOfFiniteFree R M)

end P103.Specs.Ch02.GovorovLazard
