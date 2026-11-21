import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.FilteredColimitDescent
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Étale descent from filtered colimits (ET-15)

Choose a finite type integer coefficient ring C and an étale C-algebra D
whose base change is B. Since the integers are Noetherian, C is finitely
presented. Its map to the filtered colimit therefore factors through a stage;
base changing D to that stage supplies the required model. Finite presentation
accounts for coefficient equalities which hold only after a later transition.
This is also the proof of Stacks Tag 00U2(9).

For the localization assertion we construct, and prove the universal property
of, the filtered diagram of principal localizations indexed by finite subsets
of the multiplicative set. We then apply the general result to its colimit.
-/

namespace AdvCommAlg.Etale

open CategoryTheory Limits
open scoped TensorProduct

universe u v
noncomputable section

/-- Maps out of a finite type integer algebra factor through a filtered stage.
Finite type suffices here because the integers are Noetherian. -/
theorem finiteType_integer_factor
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (C : Type u) [CommRing C] [Algebra.FiniteType ℤ C] (g : C →+* c.pt) :
    ∃ (i : J) (gᵢ : C →+* F.obj i), (c.ι.app i).hom.comp gᵢ = g := by
  let Z : CommRingCat.{u} := CommRingCat.of (ULift.{u} ℤ)
  let z (T : CommRingCat.{u}) : Z ⟶ T :=
    CommRingCat.ofHom ((Int.castRingHom T).comp ULift.ringEquiv.toRingHom)
  let α : (Functor.const J).obj Z ⟶ F :=
    { app i := z (F.obj i)
      naturality i j f := by ext x; simp [z] }
  have hfp : (z (CommRingCat.of C)).hom.FinitePresentation := by
    apply RingHom.FinitePresentation.comp
    · rw [← show algebraMap ℤ C = Int.castRingHom C from rfl,
        RingHom.finitePresentation_algebraMap]
      exact (Algebra.FinitePresentation.of_finiteType (R := ℤ) (A := C)).mp inferInstance
    · exact RingHom.FinitePresentation.of_bijective ULift.ringEquiv.bijective
  obtain ⟨i, gi, _, hgi⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit Z F α
      (z (CommRingCat.of C)) c hc hfp (CommRingCat.ofHom g) (by
        intro i; ext x; simp [z, α])
  exact ⟨i, gi.hom, congrArg CommRingCat.Hom.hom hgi.symm⟩

/-- ET-15 for arbitrary filtered categories, using a finite type integer model
and finite presentation to factor its coefficient map through the diagram. -/
theorem filtered_colimit_descent :
    Specs.AdvCommAlg.Etale.filteredColimitDescent.{u,v} := by
  intro J _ _ F c hc B _ _ hB
  let := hB
  obtain ⟨C, D, hD, hCD, hC, hE, ⟨e⟩⟩ :=
    Algebra.Etale.exists_subalgebra_fg ℤ c.pt B
  let := hD
  let := hCD
  let := hE
  have : Algebra.FiniteType ℤ C := ⟨C.fg_top.mpr hC⟩
  obtain ⟨i, gi, hgi⟩ := finiteType_integer_factor F c hc C (algebraMap C c.pt)
  let : Algebra C (F.obj i) := gi.toAlgebra
  let : Algebra (F.obj i) c.pt := (c.ι.app i).hom.toAlgebra
  have : IsScalarTower C (F.obj i) c.pt :=
    IsScalarTower.of_algebraMap_eq (fun x => congrArg (fun f : C →+* c.pt => f x) hgi.symm)
  refine ⟨i, F.obj i ⊗[C] D, inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨e.trans (Algebra.TensorProduct.cancelBaseChange C (F.obj i) c.pt c.pt D).symm⟩

namespace PrincipalLocalizationDiagram

variable {R : Type u} [CommRing R] (S : Submonoid R)

/-- The product of a finite set of denominators. -/
def denominator (t : Finset S) : R := ∏ s ∈ t, (s : R)

lemma denominator_mem (t : Finset S) : denominator S t ∈ S :=
  S.prod_mem fun s _ => s.property

/-- A finite set of denominators is inverted by inverting their product. -/
abbrev stage (t : Finset S) : CommRingCat.{u} :=
  CommRingCat.of (Localization.Away (denominator S t))

/-- The canonical transition between principal localizations. -/
def transition {t t' : Finset S} (h : t ⊆ t') : stage S t ⟶ stage S t' :=
  CommRingCat.ofHom (IsLocalization.Away.lift (denominator S t)
    (IsLocalization.Away.isUnit_of_dvd (S := Localization.Away (denominator S t'))
      (denominator S t') (Finset.prod_dvd_prod_of_subset t t' (fun s : S => (s : R)) h)))

@[simp]
lemma transition_algebraMap {t t' : Finset S} (h : t ⊆ t') (r : R) :
    transition S h (algebraMap R (stage S t) r) = algebraMap R (stage S t') r := by
  simp [transition]

/-- The filtered diagram of principal localizations at finite products from S. -/
abbrev diagram : Finset S ⥤ CommRingCat.{u} where
  obj := stage S
  map f := transition S (leOfHom f)
  map_id t := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers (denominator S t))
    ext r
    simp [transition]
  map_comp {t t' t''} f g := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers (denominator S t))
    ext r
    simp [transition]

variable (A : Type u) [CommRing A] [Algebra R A] [IsLocalization S A]

/-- The canonical cocone into S⁻¹R. -/
abbrev cocone : Cocone (diagram S) where
  pt := CommRingCat.of A
  ι :=
    { app t := CommRingCat.ofHom
        (IsLocalization.Away.lift (denominator S t)
          (IsLocalization.map_units A ⟨_, denominator_mem S t⟩))
      naturality {t t'} f := by
        apply CommRingCat.hom_ext
        apply IsLocalization.ringHom_ext (Submonoid.powers (denominator S t))
        ext r
        simp [diagram, transition] }

@[simp]
lemma cocone_algebraMap (t : Finset S) (r : R) :
    (cocone S A).ι.app t (algebraMap R (stage S t) r) = algebraMap R A r := by
  simp [cocone]

/-- Any cocone is given on the base ring by its component at the empty set. -/
def coconeBaseMap (q : Cocone (diagram S)) : R →+* q.pt :=
  (q.ι.app ∅).hom.comp (algebraMap R (stage S ∅))

lemma coconeBaseMap_eq (q : Cocone (diagram S)) (t : Finset S) (r : R) :
    coconeBaseMap S q r = q.ι.app t (algebraMap R (stage S t) r) := by
  have h := congrArg (fun f : stage S ∅ ⟶ q.pt =>
    f (algebraMap R (stage S ∅) r)) (q.w (homOfLE (Finset.empty_subset t)))
  simpa [coconeBaseMap, diagram, transition] using h.symm

lemma coconeBaseMap_isUnit (q : Cocone (diagram S)) (s : S) :
    IsUnit (coconeBaseMap S q s) := by
  classical
  rw [coconeBaseMap_eq S q {s}]
  apply IsUnit.map (q.ι.app {s}).hom
  have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (denominator S {s}))
    (denominator S {s})
  simpa [denominator] using h

/-- An arbitrary localization is the filtered colimit of these principal localizations. -/
def isColimit : IsColimit (cocone S A) where
  desc q := CommRingCat.ofHom (IsLocalization.lift (S := A) (coconeBaseMap_isUnit S q))
  fac q t := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers (denominator S t))
    ext r
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom, IsLocalization.Away.lift_eq, IsLocalization.lift_eq]
    exact coconeBaseMap_eq S q t r
  uniq q m hm := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext S
    ext r
    have h := congrArg (fun f : stage S ∅ ⟶ q.pt =>
      f (algebraMap R (stage S ∅) r)) (hm ∅)
    simpa [coconeBaseMap, IsLocalization.lift_eq] using h

end PrincipalLocalizationDiagram

/-- The localization assertion of ET-15. -/
theorem principal_localization_descent :
    Specs.AdvCommAlg.Etale.principalLocalizationDescent.{u,v} := by
  intro R A _ _ _ S _ B _ _ hB
  obtain ⟨t, D, hD, hAD, hE, he⟩ := filtered_colimit_descent
    (Finset S) (PrincipalLocalizationDiagram.diagram S)
      (PrincipalLocalizationDiagram.cocone S A)
      (PrincipalLocalizationDiagram.isColimit S A) B hB
  exact ⟨⟨PrincipalLocalizationDiagram.denominator S t,
    PrincipalLocalizationDiagram.denominator_mem S t⟩, D, hD, hAD, hE, he⟩

end
end AdvCommAlg.Etale
