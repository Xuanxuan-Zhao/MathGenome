import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.Derived
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFreeResolution
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.SemiFreeKProjective
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedHomFromKProjective
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.AmbientDerived
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.DerivedKProjective
import Mathlib.CategoryTheory.Preadditive.Transfer

open CategoryTheory

universe u v w t

namespace DerivedFormalization.RightDGModule

open Specs.DerivedFormalization.DG.DerivedKProjective

noncomputable section

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}

/-- Postcomposition by a quasi-isomorphism acts bijectively on maps in the homotopy
category out of a K-projective module. -/
theorem IsKProjective.homotopyPostcomp_bijective {P X Y : K A} (hP : IsKProjective P)
    (f : X ⟶ Y) (hf : quasiIsomorphisms A f) :
    Function.Bijective (fun g : P ⟶ X => g ≫ f) :=
  hP.postcomp_bijective ⟨instCategoryK A, rfl⟩ f hf

/-- Localization preserves the homotopy classes of maps from a K-projective source. -/
theorem IsKProjective.localizationMap_bijective {P N : K A} (hP : IsKProjective P) :
    Function.Bijective ((Q A).map : (P ⟶ N) → ((Q A).obj P ⟶ (Q A).obj N)) :=
  hP.Q_map_bijective ⟨instCategoryK A, rfl⟩

open Specs.DerivedFormalization.DG.Derived (HomotopyCategoryLaws)

local instance (A : DGCategory.{u,v,w} k) :
    Category (Specs.DerivedFormalization.DG.HomComplex.homotopyCategory A) :=
  inferInstanceAs (Category (K A))

local instance (A : DGCategory.{u,v,w} k) : Preadditive (K A) :=
  inferInstanceAs (Preadditive ((dgCategory A).H0))

local instance (A : DGCategory.{u,v,w} k) :
    Preadditive (Specs.DerivedFormalization.DG.HomComplex.homotopyCategory A) :=
  inferInstanceAs (Preadditive (K A))

/-- The isomorphism of native derived objects induced by a strict quasi-isomorphism. -/
private def nativeReplacementIso (h : HomotopyCategoryLaws A) {P M : K A}
    (p : RightDGModuleHomModel P M) (hp : IsQuasiIso p) : (Q A h).obj P ≅ (Q A h).obj M :=
  replacementIso h p hp

/-- The canonical localization restricts to an equivalence on K-projectives. -/
theorem kProjectiveLocalization_isEquivalence : LocalizationEquivalence.{u,v,w} := by
  intro k _ A h
  change ((kProjectiveObjects A).ι ⋙ Q A h).IsEquivalence
  refine ⟨⟨?_⟩, ⟨?_⟩, ⟨?_⟩⟩
  · intro P N
    exact ((IsKProjective.localizationMap_bijective P.property).injective).comp
      ((kProjectiveObjects A).fullyFaithfulι.map_bijective P N).injective
  · intro P N
    exact ((IsKProjective.localizationMap_bijective P.property).surjective).comp
      ((kProjectiveObjects A).fullyFaithfulι.map_bijective P N).surjective
  · intro X
    have := Localization.essSurj (Q A h) (quasiIsomorphisms A)
    let M := (Q A h).objPreimage X
    obtain ⟨P, p, hP, _, hp⟩ := unboundedSemiFreeResolutionInUniverse.{u,v,w} k A M
    exact ⟨⟨P, IsSemiFree.isKProjective hP⟩,
      ⟨nativeReplacementIso h p hp ≪≫ (Q A h).objObjPreimageIso X⟩⟩

/-- The equivalence whose functor is localization on the full subcategory of
K-projective modules. -/
def kProjectiveLocalizationEquivalence (A : DGCategory.{u,max v w,w} k)
    (h : HomotopyCategoryLaws A := ⟨instCategoryK A, rfl⟩) :
    (kProjectiveObjects A).FullSubcategory ≌ D A h := by
  let F : (kProjectiveObjects A).FullSubcategory ⥤ D A h := restrictedLocalization A h
  have : F.IsEquivalence := kProjectiveLocalization_isEquivalence.{u,v,w} A h
  exact F.asEquivalence

/-- Applying the localization and inverting the replacement gives the Hom bijection. -/
theorem derivedHomComparison_bijective : HomComparison.{u,v,w} := by
  intro k _ A h P M N p hp hP
  let e := nativeReplacementIso h p hp
  change Function.Bijective (fun g : P ⟶ N => e.inv ≫ (Q A h).map g)
  exact e.homFromEquiv.bijective.comp (IsKProjective.localizationMap_bijective hP)

/-- Compute the derived morphisms using degree-zero cohomology out of any
K-projective replacement. -/
def derivedHomEquiv {P M N : K A} (p : RightDGModuleHomModel P M)
    (hp : IsQuasiIso p) (hP : IsKProjective P)
    (h : HomotopyCategoryLaws A := ⟨instCategoryK A, rfl⟩) :
    ((Q A h).obj M ⟶ (Q A h).obj N) ≃
      Specs.DerivedFormalization.DG.Basic.h0Hom (homComplex P N) :=
  (Equiv.ofBijective (homComparisonMap (N := N) h p hp)
    (derivedHomComparison_bijective.{u,v,w} h p hp hP)).symm

/-- The Hom comparison commutes with postcomposition in the target. -/
theorem derivedHomComparison_naturality : HomComparisonNaturality.{u,v,w} := by
  intro k _ A h P M N N' p hp g a
  let e := nativeReplacementIso h p hp
  change e.inv ≫ (Q A h).map (g ≫ a) = (e.inv ≫ (Q A h).map g) ≫ (Q A h).map a
  rw [Functor.map_comp, Category.assoc]

/-- The unique comparison over the original module between two replacements is an
isomorphism in the homotopy category. -/
theorem kProjectiveReplacementComparison : ReplacementComparison.{u,v,w} := by
  intro k _ A h P P' M p p' hp hp' hP hP'
  let p₀ : P ⟶ M := homotopyClass p
  let p₁ : P' ⟶ M := homotopyClass p'
  have b₀ := IsKProjective.homotopyPostcomp_bijective hP' p₀ ⟨p, rfl, hp⟩
  have b₁ := IsKProjective.homotopyPostcomp_bijective hP p₁ ⟨p', rfl, hp'⟩
  change (∃! t : P' ⟶ P, t ≫ p₀ = p₁) ∧ ∀ (t : P' ⟶ P), t ≫ p₀ = p₁ → IsIso t
  constructor
  · obtain ⟨t, ht⟩ := b₀.surjective p₁
    exact ⟨t, ht, fun s hs => b₀.injective (hs.trans ht.symm)⟩
  · intro t ht
    obtain ⟨s, hs⟩ := b₁.surjective p₀
    change s ≫ p₁ = p₀ at hs
    have id₀ := IsKProjective.homotopyPostcomp_bijective hP p₀ ⟨p, rfl, hp⟩
    have id₁ := IsKProjective.homotopyPostcomp_bijective hP' p₁ ⟨p', rfl, hp'⟩
    refine ⟨s, id₁.injective ?_, id₀.injective ?_⟩
    · change (t ≫ s) ≫ p₁ = 𝟙 P' ≫ p₁
      rw [Category.assoc, hs, ht, Category.id_comp]
    · change (s ≫ t) ≫ p₀ = 𝟙 P ≫ p₀
      rw [Category.assoc, ht, hs, Category.id_comp]

/-- Precomposing by the comparison of replacements gives the same localized map. -/
theorem derivedHomComparison_change : HomComparisonChange.{u,v,w} := by
  intro k _ A h P P' M N p p' hp hp' t ht g
  let L := Q A h
  let e := nativeReplacementIso h p hp
  let e' := nativeReplacementIso h p' hp'
  have he : L.map t ≫ e.hom = e'.hom := ((L.map_comp _ _).symm).trans (congrArg L.map ht)
  have he' : e'.inv ≫ L.map t = e.inv := by
    apply (cancel_mono e.hom).mp
    rw [Category.assoc, he, e'.inv_hom_id, e.inv_hom_id]
  change e'.inv ≫ L.map (t ≫ g) = e.inv ≫ L.map g
  rw [L.map_comp, ← Category.assoc, he']


section Ambient

open DerivedFormalization.DG.AmbientDerived (category strictInput)
open Specs.DerivedFormalization.DG.CoefficientLiftComparison (EvaluationLaws)

/-- Localization on all adequately sized K-projectives is an equivalence. -/
theorem ambientKProjectiveLocalization_isEquivalence : AmbientLocalizationEquivalence.{u,v,w,t} :=
  fun A h => kProjectiveLocalization_isEquivalence.{u,max v t,w} (category.{u,v,w,t} A) h

/-- A given ambient K-projective replacement computes derived Hom, naturally in
the target. -/
theorem ambientDerivedHomComparison : AmbientHomComparison.{u,v,w,t} := by
  intro k _ A h P M p hp hP
  exact ⟨fun _ => derivedHomComparison_bijective.{u,max v w t,w} h p hp hP,
    fun g a => derivedHomComparison_naturality.{u,max v w t,w} h p hp g a⟩

/-- Unique comparison of replacements in the adequate homotopy category. -/
theorem ambientKProjectiveReplacementComparison : AmbientReplacementComparison.{u,v,w,t} := by
  intro k _ A h P P' M p p' hp hp' hP hP'
  obtain ⟨hex, hiso⟩ := kProjectiveReplacementComparison.{u,max v w t,w} h p p' hp hp' hP hP'
  exact ⟨hex, fun s hs => ⟨hiso s hs, fun _ g =>
    derivedHomComparison_change.{u,max v w t,w} h p p' hp hp' s hs g⟩⟩

/-- Lifting a map between resolved modules is compatible with precomposition
in the common derived category. -/
theorem ambientDerivedHomComparison_sourceNaturality :
    AmbientHomComparisonSourceNaturality.{u,v,w,t} := by
  intro k _ A h P P' M M' p p' hp hp' _ hP' a
  let B := category.{u,v,w,t} A
  let L := Q B h
  let p₀ : @Quiver.Hom (K B) inferInstance P M := homotopyClass p
  let p₁ : @Quiver.Hom (K B) inferInstance P' M' := homotopyClass p'
  change (∃! s : P' ⟶ P, s ≫ p₀ = p₁ ≫ a) ∧ _
  have b := IsKProjective.homotopyPostcomp_bijective hP' p₀ ⟨p, rfl, hp⟩
  obtain ⟨s, hs⟩ := b.surjective (p₁ ≫ a)
  refine ⟨⟨s, hs, fun r hr => b.injective (hr.trans hs.symm)⟩, ?_⟩
  intro r hr N g
  let e := nativeReplacementIso h p hp
  let e' := nativeReplacementIso h p' hp'
  have h₁ : L.map r ≫ e.hom = e'.hom ≫ L.map a :=
    (L.map_comp r p₀).symm.trans ((congrArg L.map hr).trans (L.map_comp p₁ a))
  have h₂ : e'.inv ≫ L.map r = L.map a ≫ e.inv := by
    apply (cancel_mono e.hom).mp
    simp only [Category.assoc, h₁, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  change e'.inv ≫ L.map (r ≫ g) = L.map a ≫ e.inv ≫ L.map g
  rw [L.map_comp, ← Category.assoc, h₂, Category.assoc]

/-- Original inputs are compared to their ambient resolutions by the canonical
coefficient evaluation maps. -/
theorem originalInputDerivedHomComparison : OriginalInputComparison.{u,v,w,t} := by
  intro k _ A h M
  let B := category.{u,v,w,t} A
  let M' := (strictInput.{u,v,w,t} A).obj M
  obtain ⟨P, p, hP, hs, hp⟩ := unboundedSemiFreeResolutionInUniverse.{u,max v t,w} k B M'
  have hKP := IsSemiFree.isKProjective hP
  have he : EvaluationLaws p := DG.CoefficientLift.evaluation.{u,v,w,max w t} p
  have hc := ambientDerivedHomComparison.{u,v,w,t} (A := A) h p hp hKP
  exact ⟨P, p, hp, hP, hKP, hs, he, fun N => hc.1 ((strictInput.{u,v,w,t} A).obj N),
    fun g a => hc.2 g (homotopyClass ((strictInput.{u,v,w,t} A).map a))⟩

open DerivedFormalization.DG.AmbientDerived
  (transportToAmbient transportToNative gradedEquivalence homotopyEquivalence
    homotopyTransport_map_class derivedEquivalence transportSquare)

/-- Transport of the arrow action carries the whole complex of right-linear maps. -/
private def transportedHomComplexIso {A : DGCategory.{u,max v w t,w} k}
    (P N : RightDGModule A) :
    homComplex P N ≅ homComplex ((transportToAmbient.{u,v,w,t} A).obj P)
      ((transportToAmbient.{u,v,w,t} A).obj N) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun r => (gradedEquivalence.{u,v,w,t} P N r).toModuleIso) (by
      intro i j _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact Subtype.ext rfl)

/-- The K-projectivity test is identical in the two categories at the same coefficient level. -/
theorem isKProjective_transportToAmbient_iff {A : DGCategory.{u,max v w t,w} k}
    (P : RightDGModule A) :
    IsKProjective ((transportToAmbient.{u,v,w,t} A).obj P) ↔ IsKProjective P := by
  constructor
  · intro h N hN i
    exact (h ((transportToAmbient.{u,v,w,t} A).obj N) hN i).of_iso
      (transportedHomComplexIso.{u,v,w,t} P N).symm
  · intro h N hN i
    let N₀ := (transportToNative.{u,v,w,t} A).obj N
    exact (h N₀ hN i).of_iso (transportedHomComplexIso.{u,v,w,t} P N₀)

/-- The comparison on an adequate native category is identified with the ambient
comparison by the equivalences that transport the arrow actions. -/
theorem adequateNativeDerivedHomComparison : AdequateNativeComparison.{u,v,w,t} := by
  intro k _ A h h'
  let B := category.{u,max v w t,w,t} A
  let E : K A ≌ K B := homotopyEquivalence.{u,v,w,t} A
  let G : D A h ≌ D B h' := derivedEquivalence.{u,v,w,t} A
  let H := Q B h'
  let σ : Q A h ⋙ G.functor ≅ E.functor ⋙ H := transportSquare.{u,v,w,t} A
  refine ⟨E, G, σ, fun _ => rfl,
    fun f => heq_of_eq (homotopyTransport_map_class.{u,v,w,t} f),
    isKProjective_transportToAmbient_iff.{u,v,w,t}, ?_⟩
  intro P M N p hp g
  let e₀ := nativeReplacementIso h p hp
  let p₀ : @Quiver.Hom (K A) inferInstance P M := homotopyClass p
  have hpσ : G.functor.map e₀.hom ≫ σ.hom.app M =
      σ.hom.app P ≫ H.map (E.functor.map p₀) :=
    σ.hom.naturality p₀
  have hgσ : G.functor.map ((Q A h).map g) ≫ σ.hom.app N =
      σ.hom.app P ≫ H.map (E.functor.map g) :=
    σ.hom.naturality g
  constructor
  · change σ.inv.app P ≫ G.functor.map e₀.hom ≫ σ.hom.app M =
      H.map (E.functor.map p₀)
    rw [hpσ, Iso.inv_hom_id_app_assoc]
  · change G.functor.map (e₀.inv ≫ (Q A h).map g) ≫ σ.hom.app N =
      σ.hom.app M ≫ ((σ.inv.app M ≫ G.functor.map e₀.inv) ≫ σ.hom.app P) ≫
        H.map (E.functor.map g)
    rw [Functor.map_comp, Category.assoc, hgσ]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

end Ambient

/-- The preadditive structure on the localization transported from the full
subcategory of K-projective modules. -/
@[instance_reducible]
def derivedPreadditive (A : DGCategory.{u,max v w,w} k)
    (h : HomotopyCategoryLaws A := ⟨instCategoryK A, rfl⟩) : Preadditive (D A h) :=
  Preadditive.ofFullyFaithful (kProjectiveLocalizationEquivalence A h).fullyFaithfulInverse

private theorem map_add_on_kProjectives {A : DGCategory.{u,max v w,w} k}
    (h : HomotopyCategoryLaws A) {P R : Specs.DerivedFormalization.DG.HomComplex.homotopyCategory A}
    (hP : IsKProjective P) (hR : IsKProjective R) (f g : P ⟶ R) :
    letI := derivedPreadditive A h
    (Q A h).map (f + g) = (Q A h).map f + (Q A h).map g := by
  let _ := derivedPreadditive A h
  let E := kProjectiveLocalizationEquivalence A h
  have : E.functor.Additive := Equivalence.additive_inverse_of_FullyFaithful E.symm
  let X : (kProjectiveObjects A).FullSubcategory := ⟨P, hP⟩
  let Y : (kProjectiveObjects A).FullSubcategory := ⟨R, hR⟩
  let f' : X ⟶ Y := ObjectProperty.homMk f
  let g' : X ⟶ Y := ObjectProperty.homMk g
  exact E.functor.map_add (f := f') (g := g')

/-- The localization is additive for the transported structure. -/
theorem derivedLocalization_additive (A : DGCategory.{u,max v w,w} k)
    (h : HomotopyCategoryLaws A := ⟨instCategoryK A, rfl⟩) :
    letI := derivedPreadditive A h
    (Q A h).Additive := by
  let _ := derivedPreadditive A h
  constructor
  intro M N f g
  let L := Q A h
  obtain ⟨P, p, hP, _, hp⟩ := unboundedSemiFreeResolutionInUniverse.{u,v,w} k A M
  obtain ⟨R, r, hR, _, hr⟩ := unboundedSemiFreeResolutionInUniverse.{u,v,w} k A N
  let e := nativeReplacementIso h p hp
  let p₀ : @Quiver.Hom (K A) inferInstance P M := homotopyClass p
  let r₀ : @Quiver.Hom (K A) inferInstance R N := homotopyClass r
  have b := IsKProjective.homotopyPostcomp_bijective (IsSemiFree.isKProjective hP) r₀
    ⟨r, rfl, hr⟩
  obtain ⟨f', hf'⟩ := b.surjective (p₀ ≫ f)
  obtain ⟨g', hg'⟩ := b.surjective (p₀ ≫ g)
  change f' ≫ r₀ = p₀ ≫ f at hf'
  change g' ≫ r₀ = p₀ ≫ g at hg'
  have hfg : (f' + g') ≫ r₀ = p₀ ≫ (f + g) := by
    rw [Preadditive.add_comp, Preadditive.comp_add, hf', hg']
  apply (cancel_epi e.hom).mp
  change L.map p₀ ≫ L.map (f + g) = L.map p₀ ≫ (L.map f + L.map g)
  rw [← L.map_comp, ← hfg, L.map_comp,
    map_add_on_kProjectives h (IsSemiFree.isKProjective hP) (IsSemiFree.isKProjective hR),
    Preadditive.add_comp, Preadditive.comp_add]
  rw [← L.map_comp f' r₀, ← L.map_comp g' r₀, hf', hg', L.map_comp, L.map_comp]

/-- The canonical comparison is an additive isomorphism for the preadditive
structure on the localization. -/
def derivedHomAddEquiv {A : DGCategory.{u,max v w,w} k} {P M N : K A}
    (p : RightDGModuleHomModel P M) (hp : IsQuasiIso p) (hP : IsKProjective P)
    (h : HomotopyCategoryLaws A := ⟨instCategoryK A, rfl⟩) :
    letI := derivedPreadditive A h
    ((Q A h).obj M ⟶ (Q A h).obj N) ≃+
      Specs.DerivedFormalization.DG.Basic.h0Hom (homComplex P N) := by
  letI := derivedPreadditive A h
  have := derivedLocalization_additive A h
  let e := nativeReplacementIso h p hp
  refine AddEquiv.symm { toEquiv := (derivedHomEquiv (N := N) p hp hP h).symm, map_add' := ?_ }
  intro f g
  change e.inv ≫ (Q A h).map ((f : P ⟶ N) + (g : P ⟶ N)) =
    (e.inv ≫ (Q A h).map f) + (e.inv ≫ (Q A h).map g)
  let f₀ : P ⟶ N := f
  let g₀ : P ⟶ N := g
  exact (congrArg (fun z => e.inv ≫ z) ((Q A h).map_add (f := f₀) (g := g₀))).trans
    (Preadditive.comp_add _ _ _ _ _ _)

/-- Degree-zero Hom cohomology computes the derived morphism group at
any adequate bound. -/
theorem ambientDerivedHomComparison_additive : AmbientHomComparisonAdditive.{u,v,w,t} := by
  intro k _ A h
  let B := DG.AmbientDerived.category.{u,v,w,t} A
  let S := derivedPreadditive.{u,max v t,w} B h
  refine ⟨S, ?_⟩
  intro P M N p hp hP
  let _ := S
  let e : ((Q B h).obj M ⟶ (Q B h).obj N) ≃+
      Specs.DerivedFormalization.DG.Basic.h0Hom (homComplex P N) :=
    derivedHomAddEquiv (A := B) (N := N) p hp hP h
  exact ⟨e.symm, fun _ => rfl⟩



end

end DerivedFormalization.RightDGModule
