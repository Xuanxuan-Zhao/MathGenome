import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.SquareZeroMaps
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Affine.DerivedHom

open CategoryTheory Opposite

universe u v

namespace Specs.DerivedFormalization.Affine.SquareZeroHomotopy

open _root_.DerivedFormalization
open _root_.DerivedFormalization.Affine
open CotangentComplex (Model)
open SquareZeroMaps (Extension IsNonpositive Maps PathTarget CycleComparison CoefficientMap)
open Tensor (ModuleTensor regular)
open PolynomialPath (ModulePathModel)
open DG.Basic (classOf cyclesZero zeroShort)
open DG.HomComplex (gradedHom homComplex homotopyClass)
open DG.KProjective (isKProjective)

noncomputable section

variable {k : Type u} [Field k] [CharZero k]
variable {A B : NonpositiveCDGA.{u,v} k} {b : A ⟶ B}

/-- The relation given by a single polynomial homotopy over the fixed augmentation. -/
def PolynomiallyHomotopic {R : Model b} {M : B.Module} {S : Extension M}
    {W : ModulePathModel M} {U : Extension W.obj} (P : PathTarget S W U)
    (f₀ f₁ : Maps R S.projection S.zeroSection) : Prop :=
  ∃ p : Maps R P.augmentation P.zeroSection, P.evalMap p 0 = f₀ ∧ P.evalMap p 1 = f₁

/-- The image of a degree-zero cocycle under the canonical quotient map to cohomology. -/
def cohomologyClass {C : ModuleCochain.{u,v} k} (z : cyclesZero C) : C.homology 0 :=
  ((zeroShort C).moduleCatHomologyIso.symm ≪≫
    (C.homologyIsoSc' (-1) 0 1
      (ComplexShape.prev_eq' _ (show (-1 : ℤ) + 1 = 0 from rfl))
      (ComplexShape.next_eq' _ (show (0 : ℤ) + 1 = 1 from rfl))).symm).hom (classOf z)

/-- For the actual truncated polynomial paths, joining two maps is equivalent
to their cocycles differing by a boundary. The quotient comparison sends
the class of a map to the cohomology class of its corresponding cocycle. -/
def PathQuotient : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A B : NonpositiveCDGA.{u,v} k}
    {b : A ⟶ B} (R : Model b) (T : ModuleTensor.{u,v} k)
    (_ : T.Formulas (R.augmentation : R.algebra.toCommDGAlgebra ⟶ B.toCommDGAlgebra)
      (regular B.toCommDGAlgebra))
    {M : B.Module} (_ : IsNonpositive M) (S : Extension M)
    (W : ModulePathModel M) (U : Extension W.obj),
    ∃ (P : PathTarget S W U) (E : CycleComparison R T S),
      (∀ f₀ f₁, PolynomiallyHomotopic P f₀ f₁ ↔
        ∃ h : gradedHom (R.module T) M (-1),
          (homComplex (R.module T) M).d (-1) 0 h = (E.equiv f₁).val - (E.equiv f₀).val) ∧
      ∃ q : Quot (PolynomiallyHomotopic (R := R) P) ≃ (homComplex (R.module T) M).homology 0,
        ∀ f, q (Quot.mk _ f) = cohomologyClass (E.equiv f)

/-- On representatives, coefficient maps act by postcomposition on the
cohomology classes of augmented maps. -/
def ClassNaturality : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A B : NonpositiveCDGA.{u,v} k}
    {b : A ⟶ B} (R : Model b) (T : ModuleTensor.{u,v} k)
    {M N : B.Module} (S : Extension M) (U : Extension N)
    (E : CycleComparison R T S) (E' : CycleComparison R T U)
    (J : DerivedHom.HomActions B.toCommDGAlgebra) (_ : DerivedHom.HomActionLaws _ J)
    (g : M ⟶ N),
    ∃ G : CoefficientMap S U g,
      ∀ f : Maps R S.projection S.zeroSection,
        HomologicalComplex.homologyMap ((J.post (R.module T) g).app ()) 0
          (cohomologyClass (E.equiv f)) =
        cohomologyClass (E'.equiv (G.postcompose f))

section Derived

variable (B : NonpositiveCDGA.{u,v} k)
variable (h : DG.Derived.HomotopyCategoryLaws (CotangentComplex.oneObject B))

variable [hLaw : Fact (DG.Derived.HomotopyCategoryLaws (CotangentComplex.oneObject B))]

local instance : Category (DerivedHom.K B.toCommDGAlgebra) :=
  DG.Derived.homotopyCategory _ hLaw.out
local instance : Category (DG.Derived.derivedCategory (CotangentComplex.oneObject B) h) :=
  DG.DerivedKProjective.derivedCategoryInstance _ h

abbrev D := DG.Derived.derivedCategory (CotangentComplex.oneObject B) h
abbrev Q := DG.Derived.quotient (CotangentComplex.oneObject B) h

/-- A derived Hom realization with the model factorization from ADerivedHom. -/
structure HomRealization where
  actions : DerivedHom.HomActions B.toCommDGAlgebra
  laws : DerivedHom.HomActionLaws _ actions
  onHomotopy : (DerivedHom.K B.toCommDGAlgebra)ᵒᵖ × DerivedHom.K B.toCommDGAlgebra ⥤
    DerivedHom.K B.toCommDGAlgebra
  onDerived : (D B h)ᵒᵖ × D B h ⥤ D B h
  model_obj (L M : B.Module) : onHomotopy.obj (op L, M) = DerivedHom.internalHom L M
  model_map {L L' M N : B.Module} (f : L' ⟶ L) (g : M ⟶ N) :
    let f₀ : @Quiver.Hom (DerivedHom.K B.toCommDGAlgebra) _ L' L := homotopyClass f
    let g₀ : @Quiver.Hom (DerivedHom.K B.toCommDGAlgebra) _ M N := homotopyClass g
    HEq (onHomotopy.map (CategoryTheory.Prod.mkHom f₀.op g₀))
      (homotopyClass (actions.pre M f ≫ actions.post L' g))
  factorization :
    (DG.DerivedKProjective.restrictedLocalization (CotangentComplex.oneObject B) h).op.prod
        (Q B h) ⋙ onDerived ≅
      ((DG.DerivedKProjective.kProjectiveObjects (CotangentComplex.oneObject B)).ι).op.prod
        (𝟭 (DerivedHom.K B.toCommDGAlgebra)) ⋙ onHomotopy ⋙ Q B h

/-- Cohomology on the localization agrees naturally with cohomology of strict modules. -/
structure CohomologyRealization (i : ℤ) where
  functor : D B h ⥤ ModuleCat.{v} k
  onStrict (M : B.Module) : functor.obj ((Q B h).obj M) ≅ (M.complex ()).homology i
  onStrict_natural {M N : B.Module} (g : M ⟶ N) :
    functor.map ((Q B h).map (homotopyClass g)) ≫ (onStrict N).hom =
      (onStrict M).hom ≫ HomologicalComplex.homologyMap (g.app ()) i

variable {B h}

/-- The coefficient arrow on a derived Hom with fixed first variable. -/
abbrev derivedPost {M N : B.Module} (F : HomRealization B h) (L : B.Module)
    (g : M ⟶ N) :=
  F.onDerived.map (CategoryTheory.Prod.mkHom (𝟙 (op ((Q B h).obj L)))
    ((Q B h).map (homotopyClass g)))

end Derived

/-- In every cochain degree the derived Hom out of the cotangent complex is
computed by the indicated Hom complex, naturally in the coefficient module. -/
def DerivedCalculation : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] (B : NonpositiveCDGA.{u,v} k)
    (h : DG.Derived.HomotopyCategoryLaws (CotangentComplex.oneObject B)),
    letI : Fact (DG.Derived.HomotopyCategoryLaws (CotangentComplex.oneObject B)) := ⟨h⟩
    letI := DG.Derived.homotopyCategory (CotangentComplex.oneObject B) h
    letI := DG.DerivedKProjective.derivedCategoryInstance (CotangentComplex.oneObject B) h
    (Nonempty (HomRealization B h)) ∧
    ∃ C : ∀ i : ℤ, CohomologyRealization B h i,
      ∀ (F : HomRealization B h) {A : NonpositiveCDGA.{u,v} k} {b : A ⟶ B}
        (R : Model b) (T : ModuleTensor.{u,v} k)
        (_ : T.Formulas (R.augmentation : R.algebra.toCommDGAlgebra ⟶ B.toCommDGAlgebra)
          (regular B.toCommDGAlgebra))
        (_ : ∀ N : B.Module, T.Formulas (𝟙 B.toCommDGAlgebra) N),
        let L := R.module T
        isKProjective L ∧
        ∃ e : ∀ (i : ℤ) (M : B.Module),
          (C i).functor.obj (F.onDerived.obj (op ((Q B h).obj L), (Q B h).obj M)) ≅
            (homComplex L M).homology i,
          ∀ (i : ℤ) {M N : B.Module} (g : M ⟶ N),
            (C i).functor.map (derivedPost F L g) ≫ (e i N).hom =
              (e i M).hom ≫ HomologicalComplex.homologyMap ((F.actions.post L g).app ()) i

/-- Polynomial homotopy classes give the degree-zero derived Hom, with the
representative formula and the naturality square for coefficient maps. -/
def TangentCalculation : Prop :=
  ∀ {k : Type u} [Field k] [CharZero k] {A B : NonpositiveCDGA.{u,v} k} {b : A ⟶ B}
    (R : Model b) (T : ModuleTensor.{u,v} k)
    (_ : T.Formulas (R.augmentation : R.algebra.toCommDGAlgebra ⟶ B.toCommDGAlgebra)
      (regular B.toCommDGAlgebra))
    (_ : ∀ N : B.Module, T.Formulas (𝟙 B.toCommDGAlgebra) N)
    (h : DG.Derived.HomotopyCategoryLaws (CotangentComplex.oneObject B)),
    letI : Fact (DG.Derived.HomotopyCategoryLaws (CotangentComplex.oneObject B)) := ⟨h⟩
    letI := DG.Derived.homotopyCategory (CotangentComplex.oneObject B) h
    letI := DG.DerivedKProjective.derivedCategoryInstance (CotangentComplex.oneObject B) h
    let L := R.module T
    ∃ (F : HomRealization B h) (C : CohomologyRealization B h 0),
      let V (M : B.Module) :=
        C.functor.obj (F.onDerived.obj (op ((Q B h).obj L), (Q B h).obj M))
      ∀ (S : ∀ M : B.Module, Extension M) (W : ∀ M : B.Module, ModulePathModel M)
        (U : ∀ M : B.Module, Extension (W M).obj),
        ∃ (P : ∀ M : B.Module, IsNonpositive M → PathTarget (S M) (W M) (U M))
          (E : ∀ M : B.Module, IsNonpositive M → CycleComparison R T (S M))
          (e : ∀ M : B.Module, V M ≅ (homComplex L M).homology 0)
          (q : ∀ (M : B.Module) (hm : IsNonpositive M),
            Quot (PolynomiallyHomotopic (R := R) (P M hm)) ≃ V M),
          (∀ (M : B.Module) (hm : IsNonpositive M) (f : Maps R (S M).projection (S M).zeroSection),
            (e M).hom (q M hm (Quot.mk _ f)) = cohomologyClass ((E M hm).equiv f)) ∧
          ∀ {M N : B.Module} (hm : IsNonpositive M) (hn : IsNonpositive N) (g : M ⟶ N),
            ∃ G : CoefficientMap (S M) (S N) g,
              ∀ f : Maps R (S M).projection (S M).zeroSection,
                C.functor.map (derivedPost F L g) (q M hm (Quot.mk _ f)) =
                  q N hn (Quot.mk _ (G.postcompose f))

end
end Specs.DerivedFormalization.Affine.SquareZeroHomotopy
