import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainModels
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainCoefficientLift
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.CategoryTheory.Products.Basic

/-! The signed internal derived Hom and its natural model comparisons. -/

namespace Specs.DerivedFormalization.DerivedHomModels

open CategoryTheory Opposite
open Cochains (compValue homotopyValue derivedValue qValue qhValue quotientValue)
open CochainModels (internalHomValue internalHomMapValue)

universe u a v w t
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

/-- A homotopy-category representative of a derived object, with its identification. -/
structure Representative (X : (derivedValue.{a} R)) where
  obj : (homotopyValue.{a} R)
  iso : (qhValue.{a} R).obj obj ≅ X

variable (R) in
/-- The bifunctor induced by the product signed Hom complex on the homotopy category. -/
structure SignedHom where
  functor : (homotopyValue.{a} R)ᵒᵖ × (homotopyValue.{a} R) ⥤ (derivedValue.{a} R)
  obj_eq (A B : (homotopyValue.{a} R)) :
    functor.obj (op A, B) = (qValue.{a} R).obj (internalHomValue A.as B.as)
  map_eq {A A' B B' : (compValue.{a} R)} (f : A' ⟶ A) (g : B ⟶ B') :
    functor.map (Prod.mkHom ((quotientValue.{a} R).map f).op ((quotientValue.{a} R).map g)) =
      eqToHom (obj_eq ((quotientValue.{a} R).obj A) ((quotientValue.{a} R).obj B)) ≫
        (qValue.{a} R).map (internalHomMapValue f g) ≫
      eqToHom (obj_eq ((quotientValue.{a} R).obj A') ((quotientValue.{a} R).obj B')).symm

variable (R) in
/-- Choices needed to compute the derived bifunctor on all derived objects and maps. -/
structure Models where
  hom : SignedHom.{u,a} R
  projective (X : (derivedValue.{a} R)) : Representative X
  injective (Y : (derivedValue.{a} R)) : Representative Y
  isProjective (X : (derivedValue.{a} R)) : CochainComplex.IsKProjective ((projective X).obj.as)
  isInjective (Y : (derivedValue.{a} R)) : CochainComplex.IsKInjective ((injective Y).obj.as)

namespace Representative

/-- A map of representatives induces the prescribed derived morphism. -/
def Over {X Y : (derivedValue.{a} R)} (A : Representative X) (B : Representative Y)
    (f : X ⟶ Y) (g : A.obj ⟶ B.obj) : Prop :=
  (qhValue.{a} R).map g = A.iso.hom ≫ f ≫ B.iso.inv

end Representative

/-- Lift a derived morphism from a projective representative. -/
def projectiveLift {X Y : (derivedValue.{a} R)} (A : Representative X) (B : Representative Y)
    (hA : CochainComplex.IsKProjective (A.obj.as)) (f : X ⟶ Y) : A.obj ⟶ B.obj :=
  letI := hA
  (Equiv.ofBijective _ (CochainComplex.IsKProjective.Qh_map_bijective A.obj.as B.obj)).symm
    (A.iso.hom ≫ f ≫ B.iso.inv)

/-- Lift a derived morphism to an injective representative. -/
def injectiveLift {X Y : (derivedValue.{a} R)} (A : Representative X) (B : Representative Y)
    (hB : CochainComplex.IsKInjective (B.obj.as)) (f : X ⟶ Y) : A.obj ⟶ B.obj :=
  letI := hB
  (Equiv.ofBijective _ (CochainComplex.IsKInjective.Qh_map_bijective A.obj B.obj.as)).symm
    (A.iso.hom ≫ f ≫ B.iso.inv)

theorem projectiveLift_over {X Y : (derivedValue.{a} R)} (A : Representative X) (B : Representative Y)
    (hA : CochainComplex.IsKProjective (A.obj.as)) (f : X ⟶ Y) :
    A.Over B f (projectiveLift A B hA f) :=
  Equiv.apply_symm_apply (Equiv.ofBijective _
    (letI := hA; CochainComplex.IsKProjective.Qh_map_bijective A.obj.as B.obj)) _

theorem injectiveLift_over {X Y : (derivedValue.{a} R)} (A : Representative X) (B : Representative Y)
    (hB : CochainComplex.IsKInjective (B.obj.as)) (f : X ⟶ Y) :
    A.Over B f (injectiveLift A B hB f) :=
  Equiv.apply_symm_apply (Equiv.ofBijective _
    (letI := hB; CochainComplex.IsKInjective.Qh_map_bijective A.obj B.obj.as)) _

/-- The K-projective section of the localization. -/
def projectiveSection (M : Models.{u,a} R) : (derivedValue.{a} R) ⥤ (homotopyValue.{a} R) where
  obj X := (M.projective X).obj
  map {X Y} f := projectiveLift (M.projective X) (M.projective Y) (M.isProjective X) f
  map_id X := by
    letI := M.isProjective X
    apply (CochainComplex.IsKProjective.Qh_map_bijective (M.projective X).obj.as _).injective
    change (qhValue.{a} R).map _ = (qhValue.{a} R).map _
    rw [projectiveLift_over (M.projective X) (M.projective X) (M.isProjective X) (𝟙 X)]
    simpa only [Category.id_comp, Iso.hom_inv_id] using
      ((qhValue.{a} R).map_id (M.projective X).obj).symm
  map_comp {X Y Z} f g := by
    letI := M.isProjective X
    apply (CochainComplex.IsKProjective.Qh_map_bijective (M.projective X).obj.as _).injective
    change (qhValue.{a} R).map _ = (qhValue.{a} R).map _
    rw [projectiveLift_over (M.projective X) (M.projective Z) (M.isProjective X) (f ≫ g),
      (qhValue.{a} R).map_comp, projectiveLift_over (M.projective X) (M.projective Y) (M.isProjective X) f,
      projectiveLift_over (M.projective Y) (M.projective Z) (M.isProjective Y) g]
    simp

/-- The K-injective section of the localization. -/
def injectiveSection (M : Models.{u,a} R) : (derivedValue.{a} R) ⥤ (homotopyValue.{a} R) where
  obj Y := (M.injective Y).obj
  map {X Y} f := injectiveLift (M.injective X) (M.injective Y) (M.isInjective Y) f
  map_id X := by
    letI := M.isInjective X
    apply (CochainComplex.IsKInjective.Qh_map_bijective _ (M.injective X).obj.as).injective
    change (qhValue.{a} R).map _ = (qhValue.{a} R).map _
    rw [injectiveLift_over (M.injective X) (M.injective X) (M.isInjective X) (𝟙 X)]
    simpa only [Category.id_comp, Iso.hom_inv_id] using
      ((qhValue.{a} R).map_id (M.injective X).obj).symm
  map_comp {X Y Z} f g := by
    letI := M.isInjective Z
    apply (CochainComplex.IsKInjective.Qh_map_bijective _ (M.injective Z).obj.as).injective
    change (qhValue.{a} R).map _ = (qhValue.{a} R).map _
    rw [injectiveLift_over (M.injective X) (M.injective Z) (M.isInjective Z) (f ≫ g),
      (qhValue.{a} R).map_comp, injectiveLift_over (M.injective X) (M.injective Y) (M.isInjective Y) f,
      injectiveLift_over (M.injective Y) (M.injective Z) (M.isInjective Z) g]
    simp

/-- The derived functor on the chosen projective and injective sections. -/
def rHomValue (M : Models.{u,a} R) : (derivedValue.{a} R)ᵒᵖ × (derivedValue.{a} R) ⥤ (derivedValue.{a} R) :=
  (projectiveSection M).op.prod (injectiveSection M) ⋙ M.hom.functor

def rHomUsingType :=
  ∀ (R : Type u) [CommRing R], Models.{u,a} R →
    (derivedValue.{a} R)ᵒᵖ × derivedValue.{a} R ⥤ derivedValue.{a} R

def rHomUsingValue : rHomUsingType.{u,a} := fun _ _ M => rHomValue M

/-- The map to derived Hom induced by the augmentation and coaugmentation
in the homotopy category. -/
def modelMap (M : Models.{u,a} R) {X Y : (derivedValue.{a} R)}
    (A : Representative X) (B : Representative Y) :
    M.hom.functor.obj (op A.obj, B.obj) ⟶ (rHomValue M).obj (op X, Y) :=
  M.hom.functor.map (Prod.mkHom
    (projectiveLift (M.projective X) A (M.isProjective X) (𝟙 X)).op
    (injectiveLift B (M.injective Y) (M.isInjective Y) (𝟙 Y)))

/-- The construction has an unconditional specialization at every adequate
coefficient level. -/
def canonicalDerivedHomType : Prop :=
  ∀ (R : Type u) [CommRing R],
    ∃ (M : Models.{u,max u v} R)
      (F : (derivedValue.{max u v} R)ᵒᵖ × derivedValue.{max u v} R ⥤ derivedValue.{max u v} R),
      F = rHomValue M

/-- Naturality for every derived pair of morphisms and all representatives of
those morphisms on the chosen input models. -/
def modelMapNaturalType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Models.{u,a} R)
    {X X' Y Y' : derivedValue.{a} R}
    (A : Representative X) (A' : Representative X')
    (B : Representative Y) (B' : Representative Y')
    (f : X' ⟶ X) (g : Y ⟶ Y')
    (α : A'.obj ⟶ A.obj) (β : B.obj ⟶ B'.obj),
    A'.Over A f α → B.Over B' g β →
    M.hom.functor.map (Prod.mkHom α.op β) ≫ modelMap M A' B' =
      modelMap M A B ≫ (rHomValue M).map (Prod.mkHom f.op g)

/-- A single good variable suffices, and two good variables give the double
replacement. The complex computed on these representatives is given by obj_eq. -/
def modelMapIsIsoType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Models.{u,a} R)
    {X Y : derivedValue.{a} R} (A : Representative X) (B : Representative Y),
    CochainComplex.IsKProjective (A.obj.as) ∨ CochainComplex.IsKInjective (B.obj.as) → IsIso (modelMap M A B)

/-- The resulting bifunctor is naturally independent of the choice of
representatives. -/
def modelChoiceIndependenceType : Prop :=
  ∀ {R : Type u} [CommRing R] (M N : Models.{u,a} R),
    Nonempty (rHomValue M ≅ rHomValue N)

/-- For any strict replacements, the two single models compare to the
double model by applying signed Hom to the given replacement maps. -/
def strictComparisonsType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Models.{u,a} R)
    {X Y P I : compValue.{a} R} (p : P ⟶ X) (i : Y ⟶ I),
    QuasiIso p → QuasiIso i →
    CochainComplex.IsKProjective P → CochainComplex.IsKInjective I →
    let H := (rHomValue M).obj (op ((qValue R).obj X), (qValue R).obj Y)
    ∃ (e : (qValue R).obj (internalHomValue P I) ≅ H)
      (eP : (qValue R).obj (internalHomValue P Y) ≅ H)
      (eI : (qValue R).obj (internalHomValue X I) ≅ H),
      (qValue R).map (internalHomMapValue (𝟙 P) i) ≫ e.hom = eP.hom ∧
      (qValue R).map (internalHomMapValue p (𝟙 I)) ≫ e.hom = eI.hom


open CochainCoefficientLift (lift termEquiv liftD)
open CochainComplex.HomComplex (Cochain)

/-- The two exact same-ring lifts, to a common coefficient level containing
the two original levels and the ring. -/
abbrev liftSource (X : compValue.{v} R) : compValue.{max u v w t} R :=
  (lift.{max u w t,v} R).obj X

abbrev liftTarget (Y : compValue.{w} R) : compValue.{max u v w t} R :=
  (lift.{max u v t,w} R).obj Y

/-- The degree-n term of the signed Hom before choosing ambient carriers. -/
abbrev MixedProduct (X : compValue.{v} R) (Y : compValue.{w} R) (n : ℤ) :=
  ∀ ij : {ij : ℤ × ℤ // ij.1 + n = ij.2}, X.X ij.1.1 →ₗ[R] Y.X ij.1.2

/-- Conjugation identifies the full product of original homogeneous maps,
and identifies the differential and the action on maps in both variables. -/
def mixedProductComparisonType : Prop :=
  ∀ {R : Type u} [CommRing R],
    ∃ e : ∀ (X : compValue.{v} R) (Y : compValue.{w} R) (n : ℤ),
        (internalHomValue (liftSource.{u,v,w,t} X) (liftTarget.{u,v,w,t} Y)).X n
          ≃ₗ[R] MixedProduct X Y n,
      (∀ (X : compValue.{v} R) (Y : compValue.{w} R) (n i j : ℤ) (h : i + n = j)
          (z : Cochain (liftSource.{u,v,w,t} X) (liftTarget.{u,v,w,t} Y) n)
          (x : X.X i),
        z.v i j h (termEquiv.{max u w t} X i x) =
          termEquiv.{max u v t} Y j (e X Y n z ⟨(i, j), h⟩ x)) ∧
      (∀ (X : compValue.{v} R) (Y : compValue.{w} R) (n i : ℤ)
          (z : Cochain (liftSource.{u,v,w,t} X) (liftTarget.{u,v,w,t} Y) n)
          (x : X.X i),
        e X Y (n + 1) ((internalHomValue (liftSource.{u,v,w,t} X)
          (liftTarget.{u,v,w,t} Y)).d n (n + 1) z) ⟨(i, i + n + 1), by omega⟩ x =
          Y.d (i + n) (i + n + 1) (e X Y n z ⟨(i, i + n), rfl⟩ x) -
            n.negOnePow • e X Y n z ⟨(i + 1, i + n + 1), by omega⟩ (X.d i (i + 1) x)) ∧
      (∀ {X X' : compValue.{v} R} {Y Y' : compValue.{w} R}
          (f : X' ⟶ X) (g : Y ⟶ Y') (n i j : ℤ) (h : i + n = j)
          (z : Cochain (liftSource.{u,v,w,t} X) (liftTarget.{u,v,w,t} Y) n)
          (x : X'.X i),
        e X' Y' n ((internalHomMapValue ((lift.{max u w t,v} R).map f)
          ((lift.{max u v t,w} R).map g)).f n z) ⟨(i, j), h⟩ x =
            g.f j (e X Y n z ⟨(i, j), h⟩ (f.f i x)))

/-- At the common level the two original localized inputs identify with the
objects of the strict lift. Each of the three models computes derived Hom on
those inputs. -/
def originalComparisonType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Models.{u,max u v w t} R)
    (X : compValue.{v} R) (Y : compValue.{w} R),
    let A := liftSource.{u,v,w,t} X
    let B := liftTarget.{u,v,w,t} Y
    let X' := (liftD.{max u w t,v} R).obj ((qValue R).obj X)
    let Y' := (liftD.{max u v t,w} R).obj ((qValue R).obj Y)
    let H := (rHomValue M).obj (op X', Y')
    ∃ (P I : compValue.{max u v w t} R) (p : P ⟶ A) (i : B ⟶ I),
      QuasiIso p ∧ QuasiIso i ∧ CochainComplex.IsKProjective P ∧
      CochainComplex.IsKInjective I ∧
      Nonempty ((qValue R).obj (internalHomValue P I) ≅ H) ∧
      Nonempty ((qValue R).obj (internalHomValue P B) ≅ H) ∧
      Nonempty ((qValue R).obj (internalHomValue A I) ≅ H)

end

end Specs.DerivedFormalization.DerivedHomModels
