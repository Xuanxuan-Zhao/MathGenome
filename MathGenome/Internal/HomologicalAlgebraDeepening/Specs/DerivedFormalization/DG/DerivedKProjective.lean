import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.AmbientDerived
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.IndexedSemiFree
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.KProjective
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Preadditive.Basic

open CategoryTheory

universe u v w t

namespace Specs.DerivedFormalization.DG.DerivedKProjective

open _root_.DerivedFormalization

variable {k : Type u} [CommRing k]

/-- The objects of the full homotopy subcategory of K-projective modules. -/
abbrev kProjectiveObjects (A : DGCategoryModel.{u,v,w} k) :
    @ObjectProperty (HomComplex.homotopyCategory A) (Derived.homotopyCategoryStruct A) :=
  KProjective.isKProjective

noncomputable abbrev derivedCategoryInstance (A : DGCategoryModel.{u,v,w} k)
    (h : Derived.HomotopyCategoryLaws A) : Category (Derived.derivedCategory A h) :=
  inferInstanceAs
    (Category (@MorphismProperty.Localization _ (Derived.homotopyCategory A h)
      (Derived.quasiIsomorphisms A)))

/-- Restriction of the specified localization to the full subcategory. -/
noncomputable def restrictedLocalization (A : DGCategoryModel.{u,v,w} k)
    (h : Derived.HomotopyCategoryLaws A) :
    letI := Derived.homotopyCategory A h
    letI := derivedCategoryInstance A h
    (kProjectiveObjects A).FullSubcategory ⥤ Derived.derivedCategory A h := by
  letI := Derived.homotopyCategory A h
  letI := derivedCategoryInstance A h
  exact (kProjectiveObjects A).ι ⋙ Derived.quotient A h

/-- The smallness universe for the module terms contains the object universe, as
in the unbounded resolution theorem. The object sets and term modules may all
be taken in a common universe. -/
def LocalizationEquivalence : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,max v w,w} k)
    (h : Derived.HomotopyCategoryLaws A),
    letI := Derived.homotopyCategory A h
    letI := derivedCategoryInstance A h
    (restrictedLocalization A h).IsEquivalence

section

variable {A : DGCategoryModel.{u,v,w} k} (h : Derived.HomotopyCategoryLaws A)
variable {P M N : HomComplex.homotopyCategory A}

/-- The image of a replacement as an isomorphism in the localization. -/
noncomputable def replacementIso (p : RightDGModuleHomModel P M)
    (hp : Module.quasiIsomorphism p) :
    letI := Derived.homotopyCategory A h
    letI := derivedCategoryInstance A h
    (Derived.quotient A h).obj P ≅ (Derived.quotient A h).obj M := by
  letI := Derived.homotopyCategory A h
  letI := derivedCategoryInstance A h
  exact Localization.Construction.wIso (W := Derived.quasiIsomorphisms A)
    (HomComplex.homotopyClass p : P ⟶ M) ⟨p, rfl, hp⟩

/-- The canonical map from degree-zero cohomology sends a class `g` to
`Q(g) ∘ Q(p)⁻¹`. -/
noncomputable def homComparisonMap (p : RightDGModuleHomModel P M)
    (hp : Module.quasiIsomorphism p) (g : Basic.h0Hom (HomComplex.homComplex P N)) :
    letI := Derived.homotopyCategory A h
    letI := derivedCategoryInstance A h
    (Derived.quotient A h).obj M ⟶ (Derived.quotient A h).obj N := by
  letI := Derived.homotopyCategory A h
  letI := derivedCategoryInstance A h
  exact (replacementIso h p hp).inv ≫ (Derived.quotient A h).map (g : P ⟶ N)

end

/-- The comparison with degree-zero cohomology for every K-projective replacement. -/
def HomComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    (h : Derived.HomotopyCategoryLaws A) {P M N : HomComplex.homotopyCategory A}
    (p : RightDGModuleHomModel P M) (hp : Module.quasiIsomorphism p), KProjective.isKProjective P →
    Function.Bijective (homComparisonMap (N := N) h p hp)

/-- Postcomposition by a homotopy class in the target commutes with the comparison. -/
def HomComparisonNaturality : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    (h : Derived.HomotopyCategoryLaws A) {P M N N' : HomComplex.homotopyCategory A}
    (p : RightDGModuleHomModel P M) (hp : Module.quasiIsomorphism p),
    letI := Derived.homotopyCategory A h
    letI := derivedCategoryInstance A h
    ∀ (g : P ⟶ N) (a : N ⟶ N'),
      homComparisonMap (N := N') h p hp (g ≫ a) =
        homComparisonMap (N := N) h p hp g ≫ (Derived.quotient A h).map a

/-- Two K-projective replacements admit a unique comparison over the resolved object,
and that comparison is invertible in the homotopy category. -/
def ReplacementComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    (h : Derived.HomotopyCategoryLaws A) {P P' M : HomComplex.homotopyCategory A}
    (p : RightDGModuleHomModel P M) (p' : RightDGModuleHomModel P' M),
    Module.quasiIsomorphism p → Module.quasiIsomorphism p' →
    KProjective.isKProjective P → KProjective.isKProjective P' →
    letI := Derived.homotopyCategory A h
    (∃! t : P' ⟶ P, t ≫ HomComplex.homotopyClass p = HomComplex.homotopyClass p') ∧
      ∀ (t : P' ⟶ P), t ≫ HomComplex.homotopyClass p = HomComplex.homotopyClass p' → IsIso t

/-- Changing the replacement over the same module is precomposition on degree-zero
cohomology. -/
def HomComparisonChange : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    (h : Derived.HomotopyCategoryLaws A) {P P' M N : HomComplex.homotopyCategory A}
    (p : RightDGModuleHomModel P M) (p' : RightDGModuleHomModel P' M)
    (hp : Module.quasiIsomorphism p) (hp' : Module.quasiIsomorphism p'),
    letI := Derived.homotopyCategory A h
    letI := derivedCategoryInstance A h
    ∀ (t : P' ⟶ P), t ≫ HomComplex.homotopyClass p = HomComplex.homotopyClass p' →
    ∀ (g : P ⟶ N), homComparisonMap (N := N) h p' hp' (t ≫ g) =
      homComparisonMap (N := N) h p hp g

section Ambient

open AmbientDerived (category strictInput transportToAmbient)
open HomComplex (homotopyClass)

set_option maxHeartbeats 800000

/-- Restriction of the common localization on the entire adequately sized module
category of an original dg category, for every additional bound. -/
def AmbientLocalizationEquivalence : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (h : Derived.HomotopyCategoryLaws (category.{u,v,w,t} A)),
    letI := Derived.homotopyCategory (category.{u,v,w,t} A) h
    letI := derivedCategoryInstance (category.{u,v,w,t} A) h
    (restrictedLocalization (category.{u,v,w,t} A) h).IsEquivalence

/-- The canonical derived Hom comparison at every adequate bound, natural in
all targets of the ambient homotopy category. -/
def AmbientHomComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    (h : Derived.HomotopyCategoryLaws (category.{u,v,w,t} A))
    {P M : AmbientDerived.homotopyCategory.{u,v,w,t} A}
    (p : RightDGModuleHomModel P M) (hp : Module.quasiIsomorphism p),
    KProjective.isKProjective P →
    letI := Derived.homotopyCategory (category.{u,v,w,t} A) h
    letI := derivedCategoryInstance (category.{u,v,w,t} A) h
    (∀ N : AmbientDerived.homotopyCategory.{u,v,w,t} A,
      Function.Bijective (homComparisonMap (N := N) h p hp)) ∧
    (∀ {N N' : AmbientDerived.homotopyCategory.{u,v,w,t} A} (g : P ⟶ N) (a : N ⟶ N'),
      homComparisonMap h p hp (g ≫ a) =
        homComparisonMap h p hp g ≫ (AmbientDerived.quotient.{u,v,w,t} A h).map a)

/-- At an adequate bound the comparison of two replacements is the unique
homotopy class over the input module, and precomposition by it identifies the
two formulas for derived Hom. -/
def AmbientReplacementComparison : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    (h : Derived.HomotopyCategoryLaws (category.{u,v,w,t} A))
    {P P' M : AmbientDerived.homotopyCategory.{u,v,w,t} A}
    (p : RightDGModuleHomModel P M) (p' : RightDGModuleHomModel P' M)
    (hp : Module.quasiIsomorphism p) (hp' : Module.quasiIsomorphism p'),
    KProjective.isKProjective P → KProjective.isKProjective P' →
    letI := Derived.homotopyCategory (category.{u,v,w,t} A) h
    (∃! s : P' ⟶ P, s ≫ homotopyClass p = homotopyClass p') ∧
    ∀ (s : P' ⟶ P), s ≫ homotopyClass p = homotopyClass p' →
      IsIso s ∧ ∀ (N : AmbientDerived.homotopyCategory.{u,v,w,t} A) (g : P ⟶ N),
        homComparisonMap h p' hp' (s ≫ g) = homComparisonMap h p hp g

/-- A map of resolved modules has a unique lift between their replacements in
the homotopy category. The Hom comparison takes precomposition by this lift
to precomposition by the given map in the localization. -/
def AmbientHomComparisonSourceNaturality : Prop :=
  ∀ {k : Type u} [CommRing k] {A : DGCategoryModel.{u,v,w} k}
    (h : Derived.HomotopyCategoryLaws (category.{u,v,w,t} A))
    {P P' M M' : AmbientDerived.homotopyCategory.{u,v,w,t} A}
    (p : RightDGModuleHomModel P M) (p' : RightDGModuleHomModel P' M')
    (hp : Module.quasiIsomorphism p) (hp' : Module.quasiIsomorphism p'),
    KProjective.isKProjective P → KProjective.isKProjective P' →
    letI := Derived.homotopyCategory (category.{u,v,w,t} A) h
    letI := derivedCategoryInstance (category.{u,v,w,t} A) h
    ∀ (a : M' ⟶ M),
      (∃! s : P' ⟶ P, s ≫ homotopyClass p = homotopyClass p' ≫ a) ∧
      ∀ (s : P' ⟶ P), s ≫ homotopyClass p = homotopyClass p' ≫ a →
        ∀ (N : AmbientDerived.homotopyCategory.{u,v,w,t} A) (g : P ⟶ N),
          homComparisonMap h p' hp' (s ≫ g) =
            (AmbientDerived.quotient.{u,v,w,t} A h).map a ≫ homComparisonMap h p hp g

/-- At each adequate bound the canonical comparison is an isomorphism of
abelian groups for a preadditive structure on the common localization. -/
def AmbientHomComparisonAdditive : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (h : Derived.HomotopyCategoryLaws (category.{u,v,w,t} A)),
    let B := category.{u,v,w,t} A
    letI := Derived.homotopyCategory B h
    letI := derivedCategoryInstance B h
    let Q : HomComplex.homotopyCategory B ⥤ Derived.derivedCategory B h :=
      AmbientDerived.quotient.{u,v,w,t} A h
    ∃ S : Preadditive (Derived.derivedCategory B h),
      letI := S
      ∀ {P M N : AmbientDerived.homotopyCategory.{u,v,w,t} A}
        (p : RightDGModuleHomModel P M) (hp : Module.quasiIsomorphism p),
        KProjective.isKProjective P →
        ∃ e : Basic.h0Hom (HomComplex.homComplex P N) ≃+ (Q.obj M ⟶ Q.obj N),
          ∀ g, e g = homComparisonMap (N := N) h p hp g

/-- An original module is resolved at each adequate bound through the canonical
input. The augmentation maps into the original terms and cohomology via the
coefficient comparisons. The resulting Hom formula is natural for original
strict maps, represented by their canonical lifts. -/
def OriginalInputComparison : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,v,w} k)
    (h : Derived.HomotopyCategoryLaws (category.{u,v,w,t} A)) (M : RightDGModuleModel A),
    letI := Derived.homotopyCategory (category.{u,v,w,t} A) h
    letI := derivedCategoryInstance (category.{u,v,w,t} A) h
    let F := strictInput.{u,v,w,t} A
    ∃ (P : RightDGModuleModel (category.{u,v,w,t} A)) (p : RightDGModuleHomModel P (F.obj M))
      (hp : Module.quasiIsomorphism p),
      IndexedSemiFree.semiFree P ∧ KProjective.isKProjective P ∧
      Module.degreewiseSurjective p ∧ CoefficientLiftComparison.EvaluationLaws p ∧
      (∀ N : RightDGModuleModel A,
        Function.Bijective (homComparisonMap (N := F.obj N) h p hp)) ∧
      (∀ {N N' : RightDGModuleModel A}
        (g : @Quiver.Hom (AmbientDerived.homotopyCategory.{u,v,w,t} A) _ P (F.obj N))
        (a : N ⟶ N'),
        let a' : @Quiver.Hom (AmbientDerived.homotopyCategory.{u,v,w,t} A) _
          (F.obj N) (F.obj N') := homotopyClass (F.map a)
        homComparisonMap h p hp (g ≫ a') =
          homComparisonMap h p hp g ≫ (AmbientDerived.quotient.{u,v,w,t} A h).map a')

/-- At an already adequate bound the native and ambient comparisons correspond
under transport of the arrow actions and the commuting localization square. -/
def AdequateNativeComparison : Prop :=
  ∀ {k : Type u} [CommRing k] (A : DGCategoryModel.{u,max v w t,w} k)
    (h : Derived.HomotopyCategoryLaws A)
    (h' : Derived.HomotopyCategoryLaws (category.{u,max v w t,w,t} A)),
    let B := category.{u,max v w t,w,t} A
    letI := Derived.homotopyCategory A h
    letI := Derived.homotopyCategory B h'
    letI := derivedCategoryInstance A h
    letI := derivedCategoryInstance B h'
    let Q := Derived.quotient A h
    let Q' := AmbientDerived.quotient.{u,max v w t,w,t} A h'
    let F := transportToAmbient.{u,v,w,t} A
    ∃ E : HomComplex.homotopyCategory A ≌ AmbientDerived.homotopyCategory.{u,max v w t,w,t} A,
      ∃ G : Derived.derivedCategory A h ≌ AmbientDerived.derivedCategory.{u,max v w t,w,t} A h',
        ∃ σ : Q ⋙ G.functor ≅ E.functor ⋙ Q',
          (∀ M : RightDGModuleModel A, E.functor.obj M = F.obj M) ∧
          (∀ {M N : RightDGModuleModel A} (f : M ⟶ N),
            HEq (E.functor.map (homotopyClass f)) (homotopyClass (F.map f))) ∧
          (∀ P : RightDGModuleModel A,
            KProjective.isKProjective (E.functor.obj P) ↔ KProjective.isKProjective P) ∧
          ∀ {P M N : HomComplex.homotopyCategory A}
            (p : RightDGModuleHomModel P M) (hp : Module.quasiIsomorphism p) (g : P ⟶ N),
            let e := (σ.app P).symm ≪≫ G.functor.mapIso (replacementIso h p hp) ≪≫ σ.app M
            e.hom = Q'.map (E.functor.map (homotopyClass p)) ∧
            G.functor.map (homComparisonMap h p hp g) ≫ σ.hom.app N =
              σ.hom.app M ≫ e.inv ≫ Q'.map (E.functor.map g)

end Ambient

end Specs.DerivedFormalization.DG.DerivedKProjective
