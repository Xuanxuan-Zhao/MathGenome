import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CoefficientLiftComparison

open CategoryTheory
open _root_.DerivedFormalization

universe u v w t

namespace Specs.DerivedFormalization.DG.AmbientDerived

open CoefficientLift (liftCategory liftFunctor)
open CoefficientLiftComparison (ComponentLaws MapProperties HomologyComparison)
open HomComplex (homotopyClass)

set_option linter.checkUnivs false

noncomputable section

variable {k : Type u} [CommRing k]

/-- Enlarge the coefficient level to include the objects and the extra parameter. -/
abbrev category (A : DGCategoryModel.{u,v,w} k) : DGCategoryModel.{u,max v w t,w} k :=
  liftCategory.{u,v,w,max w t} A

def CategoryType :=
  ∀ {k : Type u} [CommRing k], DGCategoryModel.{u,v,w} k → DGCategoryModel.{u,max v w t,w} k

/-- The entire module homotopy category at the adequate level. -/
abbrev homotopyCategory (A : DGCategoryModel.{u,v,w} k) :=
  HomComplex.homotopyCategory (category.{u,v,w,t} A)

def HomotopyCategoryType :=
  ∀ {k : Type u} [CommRing k], DGCategoryModel.{u,v,w} k → Type (max u (max v w t + 1))

/-- Localize at the homotopy classes of objectwise quasi-isomorphisms. -/
abbrev derivedCategory (A : DGCategoryModel.{u,v,w} k)
    (h : Derived.HomotopyCategoryLaws (category.{u,v,w,t} A)) :=
  Derived.derivedCategory (category.{u,v,w,t} A) h

def DerivedCategoryType :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
    Derived.HomotopyCategoryLaws (category.{u,v,w,t} A) → Type (max u (max v w t + 1))

abbrev quotient (A : DGCategoryModel.{u,v,w} k)
    (h : Derived.HomotopyCategoryLaws (category.{u,v,w,t} A)) :=
  Derived.quotient (category.{u,v,w,t} A) h

def QuotientType :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (h : Derived.HomotopyCategoryLaws (category.{u,v,w,t} A)),
    letI := Derived.homotopyCategory (category.{u,v,w,t} A) h
    letI : Category (derivedCategory.{u,v,w,t} A h) :=
      inferInstanceAs (Category (@MorphismProperty.Localization _
        (Derived.homotopyCategory (category.{u,v,w,t} A) h)
        (Derived.quasiIsomorphisms (category.{u,v,w,t} A))))
    homotopyCategory.{u,v,w,t} A ⥤ derivedCategory.{u,v,w,t} A h

def IsLocalization : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (h : Derived.HomotopyCategoryLaws (category.{u,v,w,t} A)),
    letI := Derived.homotopyCategory (category.{u,v,w,t} A) h
    (quotient A h).IsLocalization (Derived.quasiIsomorphisms (category.{u,v,w,t} A))

/-- The input of an original module is its coefficient lift, with its original action. -/
abbrev strictInput (A : DGCategoryModel.{u,v,w} k) :
    RightDGModuleModel A ⥤ RightDGModuleModel (category.{u,v,w,t} A) :=
  liftFunctor.{u,v,w,max w t} A

def StrictInputType :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
    RightDGModuleModel A ⥤ RightDGModuleModel (category.{u,v,w,t} A)

def InputCoefficients : Prop :=
  (∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k),
    ComponentLaws.{u,v,w,max w t} A) ∧
    MapProperties.{u,v,w,max w t} ∧ HomologyComparison.{u,v,max w t}

/-- The strict input on representatives induces the functor and the localization square. -/
def InputLocalization : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (h : Derived.HomotopyCategoryLaws A)
    (h' : Derived.HomotopyCategoryLaws (category.{u,v,w,t} A)),
    letI := Derived.homotopyCategory A h
    letI := Derived.homotopyCategory (category.{u,v,w,t} A) h'
    letI : Category (Derived.derivedCategory A h) :=
      inferInstanceAs (Category (@MorphismProperty.Localization _
        (Derived.homotopyCategory A h) (Derived.quasiIsomorphisms A)))
    letI : Category (derivedCategory.{u,v,w,t} A h') :=
      inferInstanceAs (Category (@MorphismProperty.Localization _
        (Derived.homotopyCategory (category.{u,v,w,t} A) h')
        (Derived.quasiIsomorphisms (category.{u,v,w,t} A))))
    ∃ H : HomComplex.homotopyCategory A ⥤ homotopyCategory.{u,v,w,t} A,
      Nonempty H.FullyFaithful ∧
      (∀ M : RightDGModuleModel A, H.obj M = (strictInput.{u,v,w,t} A).obj M) ∧
      (∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
        HEq (H.map (homotopyClass f)) (homotopyClass ((strictInput.{u,v,w,t} A).map f))) ∧
      ∃ G : Derived.derivedCategory A h ⥤ derivedCategory.{u,v,w,t} A h',
        Nonempty (Derived.quotient A h ⋙ G ≅ H ⋙ quotient A h')

section AdequateNative

open CoefficientLiftComparison (restrictModule restrictMap termDown)
open HomologicalComplex

variable {A : DGCategoryModel.{u,max v w t,w} k}

/-- At an unchanged coefficient level, the maps up and down are inverse dg maps. -/
def arrowIso (C : ModuleCochain.{u,max v w t} k) :
    (CoefficientLiftComparison.CUp.{u,max v w t,max w t} C) ≅ C :=
  Hom.isoOfComponents (fun i => (termDown.{u,max v w t,max w t} C i).toModuleIso)
    (fun _ _ _ => rfl)

@[reducible] def arrowDown (A : DGCategoryModel.{u,max v w t,w} k) :
    DGFunctorModel (category.{u,max v w t,w,t} A) A where
  obj := id
  map a b := (arrowIso.{u,v,w,t} (A.hom a b)).hom
  map_id _ := rfl
  map_comp _ _ _ _ _ _ := rfl

@[reducible] def arrowUp (A : DGCategoryModel.{u,max v w t,w} k) :
    DGFunctorModel A (category.{u,max v w t,w,t} A) where
  obj := id
  map a b := (arrowIso.{u,v,w,t} (A.hom a b)).inv
  map_id _ := rfl
  map_comp _ _ _ _ _ _ := rfl

private abbrev restriction {B C : DGCategoryModel.{u,max v w t,w} k} (F : DGFunctorModel B C) :
    RightDGModuleModel C ⥤ RightDGModuleModel B where
  obj M := restrictModule F M
  map f := restrictMap F f
  map_id _ := RightDGModuleModel.hom_ext (fun _ => rfl)
  map_comp _ _ := RightDGModuleModel.hom_ext (fun _ => rfl)

/-- Keep the term complexes and maps, and act by a lifted arrow via its original arrow. -/
abbrev transportToAmbient (A : DGCategoryModel.{u,max v w t,w} k) :
    RightDGModuleModel A ⥤ RightDGModuleModel (category.{u,max v w t,w,t} A) :=
  restriction.{u,v,w,t} (arrowDown.{u,v,w,t} A)

/-- Keep the term complexes and maps, and act by an original arrow via its lifted arrow. -/
abbrev transportToNative (A : DGCategoryModel.{u,max v w t,w} k) :
    RightDGModuleModel (category.{u,max v w t,w,t} A) ⥤ RightDGModuleModel A :=
  restriction.{u,v,w,t} (arrowUp.{u,v,w,t} A)

def TransportToAmbientType :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,max v w t,w} k),
    RightDGModuleModel A ⥤ RightDGModuleModel (category.{u,max v w t,w,t} A)

def TransportToNativeType :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,max v w t,w} k),
    RightDGModuleModel (category.{u,max v w t,w,t} A) ⥤ RightDGModuleModel A

/-- The two restrictions give an equivalence on the full strict module categories.
The pointwise coefficient lift identifies with this transport by down in every degree. -/
def NativeStrictComparison : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,max v w t,w} k),
    ∃ E : RightDGModuleModel A ≌ RightDGModuleModel (category.{u,max v w t,w,t} A),
      E.functor = transportToAmbient.{u,v,w,t} A ∧
      E.inverse = transportToNative.{u,v,w,t} A ∧
      ∃ alpha : strictInput.{u,max v w t,w,t} A ≅ transportToAmbient.{u,v,w,t} A,
        ∀ (M : RightDGModuleModel A) (a : A.Obj) (i : ℤ)
          (x : ((strictInput.{u,max v w t,w,t} A).obj M |>.complex a).X i),
          (((alpha.hom.app M).app a).f i) x = x.down

open HomComplex (gradedHom homComplex component compose ofStrict)

/-- Transport preserves each homogeneous map, the signed differential, and composition. -/
def NativeGradedComparison : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,max v w t,w} k),
    let F := transportToAmbient.{u,v,w,t} A
    ∃ E : ∀ (M N : RightDGModuleModel A) (r : ℤ),
        gradedHom M N r ≃ₗ[k] gradedHom (F.obj M) (F.obj N) r,
      (∀ (M N : RightDGModuleModel A) (r : ℤ) (f : gradedHom M N r)
        (a : A.Obj) (i j : ℤ) (e : i+r = j),
        component (E M N r f) a i j e = component f a i j e) ∧
      (∀ (M N : RightDGModuleModel A) (r q : ℤ) (f : gradedHom M N r),
        E M N q ((homComplex M N).d r q f) =
          (homComplex (F.obj M) (F.obj N)).d r q (E M N r f)) ∧
      (∀ (M N P : RightDGModuleModel A) (s r q : ℤ) (e : s+r = q)
        (g : gradedHom N P s) (f : gradedHom M N r),
        E M P q (compose M N P s r q e g f) =
          compose (F.obj M) (F.obj N) (F.obj P) s r q e (E N P s g) (E M N r f)) ∧
      (∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
        E M N 0 (ofStrict f) = ofStrict (F.map f))

def NativeHomotopyAndQuasiIso : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,max v w t,w} k),
    let F := transportToAmbient.{u,v,w,t} A
    let G := transportToNative.{u,v,w,t} A
    (∀ {M N : RightDGModuleModel A} (f g : M ⟶ N),
      homotopyClass (F.map f) = homotopyClass (F.map g) ↔ homotopyClass f = homotopyClass g) ∧
    (∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
      Module.quasiIsomorphism (F.map f) ↔ Module.quasiIsomorphism f) ∧
    (∀ {M N : RightDGModuleModel (category.{u,max v w t,w,t} A)} (f : M ⟶ N),
      Module.quasiIsomorphism (G.map f) ↔ Module.quasiIsomorphism f)

/-- The strict transport descends to equivalences on homotopy and derived categories. -/
def NativeLocalizationComparison : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,max v w t,w} k)
    (h : Derived.HomotopyCategoryLaws A)
    (h' : Derived.HomotopyCategoryLaws (category.{u,max v w t,w,t} A)),
    letI := Derived.homotopyCategory A h
    letI := Derived.homotopyCategory (category.{u,max v w t,w,t} A) h'
    letI : Category (Derived.derivedCategory A h) :=
      inferInstanceAs (Category (@MorphismProperty.Localization _
        (Derived.homotopyCategory A h) (Derived.quasiIsomorphisms A)))
    letI : Category (derivedCategory.{u,max v w t,w,t} A h') :=
      inferInstanceAs (Category (@MorphismProperty.Localization _
        (Derived.homotopyCategory (category.{u,max v w t,w,t} A) h')
        (Derived.quasiIsomorphisms (category.{u,max v w t,w,t} A))))
    ∃ E : HomComplex.homotopyCategory A ≌ homotopyCategory.{u,max v w t,w,t} A,
      (∀ M : RightDGModuleModel A, E.functor.obj M = (transportToAmbient.{u,v,w,t} A).obj M) ∧
      (∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
        HEq (E.functor.map (homotopyClass f))
          (homotopyClass ((transportToAmbient.{u,v,w,t} A).map f))) ∧
      (∀ {M N : HomComplex.homotopyCategory A} (f : M ⟶ N),
        Derived.quasiIsomorphisms (category.{u,max v w t,w,t} A) (E.functor.map f) ↔
          Derived.quasiIsomorphisms A f) ∧
      ∃ E' : Derived.derivedCategory A h ≌ derivedCategory.{u,max v w t,w,t} A h',
        Nonempty (Derived.quotient A h ⋙ E'.functor ≅ E.functor ⋙ quotient A h')

end AdequateNative

end

end Specs.DerivedFormalization.DG.AmbientDerived
