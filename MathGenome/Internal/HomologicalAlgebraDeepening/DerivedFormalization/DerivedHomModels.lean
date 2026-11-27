import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedHomModels
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.ModelQuasiIsoInvariance
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.SemifreeReplacement
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.KInjectiveReplacementTransport
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainCoefficientLift

/-! The ordinary internal derived Hom on an adequate coefficient universe. -/

namespace DerivedFormalization.DerivedHomModels

open CategoryTheory Opposite
open Specs.DerivedFormalization.DerivedHomModels
open Specs.DerivedFormalization.Cochains (qhValue quotientValue qValue)
open Specs.DerivedFormalization.CochainModels (internalHomMapValue)

universe u a v w t

noncomputable section

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.checkUnivs false

variable {R : Type u} [CommRing R]

private theorem homotopyAction_congr
    {A A' B B' : Comp.{a} R} {f f' : A' ⟶ A} {g g' : B ⟶ B'}
    (hf : (homotopyQuotient R).map f = (homotopyQuotient R).map f')
    (hg : (homotopyQuotient R).map g = (homotopyQuotient R).map g') :
    (Q R).map (internalHomMap f g) = (Q R).map (internalHomMap f' g') :=
  DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{a} R) (internalHomMapHomotopy
    (HomotopyCategory.homotopyOfEq f f' hf) (HomotopyCategory.homotopyOfEq g g' hg))

private def homotopyHomFunctor (R : Type u) [CommRing R] :
    (K.{a} R)ᵒᵖ × K.{a} R ⥤ D.{a} R where
  obj X := (Q R).obj (internalHom X.1.unop.as X.2.as)
  map f := (Q R).map (internalHomMap f.1.unop.out f.2.out)
  map_id X := by
    change (Q R).map (internalHomMap (𝟙 X.1.unop : X.1.unop ⟶ _).out
      (𝟙 X.2 : X.2 ⟶ _).out) = _
    rw [homotopyAction_congr (f' := 𝟙 X.1.unop.as) (g' := 𝟙 X.2.as), internalHomMap_id]
    · exact (Q R).map_id _
    all_goals (simp; rfl)
  map_comp f g := by
    change (Q R).map (internalHomMap (g.1.unop ≫ f.1.unop).out (f.2 ≫ g.2).out) =
      (Q R).map (internalHomMap f.1.unop.out f.2.out) ≫
      (Q R).map (internalHomMap g.1.unop.out g.2.out)
    rw [← Functor.map_comp, internalHomMap_comp]
    apply homotopyAction_congr
    all_goals simp

/-- Descent of the signed chain model to homotopy classes followed by localization. -/
def signedHom (R : Type u) [CommRing R] : SignedHom.{u,a} R where
  functor := homotopyHomFunctor R
  obj_eq _ _ := rfl
  map_eq f g := by
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change (Q R).map (internalHomMap ((homotopyQuotient R).map f).out
      ((homotopyQuotient R).map g).out) = (Q R).map (internalHomMap f g)
    apply homotopyAction_congr
    · exact HomotopyCategory.quotient_map_out ((homotopyQuotient R).map f)
    · exact HomotopyCategory.quotient_map_out ((homotopyQuotient R).map g)

private def localizedIso {A B : Comp.{a} R} (f : A ⟶ B) (hf : QuasiIso f) :
    (Q R).obj A ≅ (Q R).obj B := by
  letI := hf
  exact asIso ((Q R).map f)

/-- A strict quasi-isomorphism to a complex supplies a representative of its
localized object. Use the inverse orientation for an injective coaugmentation. -/
def representative {A : Comp.{a} R} {X : D.{a} R} (e : (Q R).obj A ≅ X) :
    Representative X where
  obj := (homotopyQuotient R).obj A
  iso := (homotopyQuotientCompQhIso R).app A ≪≫ e

private theorem existsProjective (X : D.{max u v} R) :
    ∃ A : Representative X, CochainComplex.IsKProjective A.obj.as := by
  letI : Small.{max u v} R :=
    small_of_injective (f := (ULift.up : R → ULift.{v} R)) ULift.up_injective
  let Y := (Q.{max u v} R).objPreimage X
  obtain ⟨P, p, hp, _, _, hP, _⟩ := SemifreeReplacement.nativeReplacement.{u,max u v} R Y
  exact ⟨representative (localizedIso p hp ≪≫ (Q R).objObjPreimageIso X), hP⟩

private theorem existsInjective (X : D.{max u v} R) :
    ∃ A : Representative X, CochainComplex.IsKInjective A.obj.as := by
  let Y := (Q.{max u v} R).objPreimage X
  obtain ⟨I, i, _, hi, hI, _⟩ := kInjectiveReplacement (R := R) Y
  exact ⟨representative ((localizedIso i hi).symm ≪≫ (Q R).objObjPreimageIso X), hI⟩

/-- Choose models in the same cochain universe in which the two K-tests are made. -/
def models (R : Type u) [CommRing R] : Models.{u,max u v} R where
  hom := signedHom R
  projective X := (existsProjective X).choose
  injective X := (existsInjective X).choose
  isProjective X := (existsProjective X).choose_spec
  isInjective X := (existsInjective X).choose_spec

/-- Derived Hom computed with any simultaneous choice of good models. -/
def rHomUsing : rHomUsingType.{u,a} := rHomUsingValue

/-- Internal derived Hom over the original ring at the adequate coefficient level. -/
def rHom (R : Type u) [CommRing R] :
    (D.{max u v} R)ᵒᵖ × D.{max u v} R ⥤ D.{max u v} R :=
  rHomUsing R (models.{u,v} R)

theorem canonicalDerivedHom : canonicalDerivedHomType.{u,v} :=
  fun R _ => ⟨models.{u,v} R, rHom.{u,v} R, rfl⟩

theorem modelMap_natural : modelMapNaturalType.{u,a} := by
  intro R _ M X X' Y Y' A A' B B' f g α β hα hβ
  let α₁ := projectiveLift (M.projective X) A (M.isProjective X) (𝟙 X)
  let α₂ := projectiveLift (M.projective X') A' (M.isProjective X') (𝟙 X')
  let β₁ := injectiveLift B (M.injective Y) (M.isInjective Y) (𝟙 Y)
  let β₂ := injectiveLift B' (M.injective Y') (M.isInjective Y') (𝟙 Y')
  have h₁ : α₂ ≫ α = (projectiveSection M).map f ≫ α₁ := by
    letI := M.isProjective X'
    apply (CochainComplex.IsKProjective.Qh_map_bijective (M.projective X').obj.as _).injective
    change (qhValue.{a} R).map (α₂ ≫ α) = (qhValue.{a} R).map
      (projectiveLift (M.projective X') (M.projective X) (M.isProjective X') f ≫ α₁)
    have h₂ := projectiveLift_over (M.projective X') A' (M.isProjective X') (𝟙 X')
    have h₃ := projectiveLift_over (M.projective X) A (M.isProjective X) (𝟙 X)
    have h₄ := projectiveLift_over (M.projective X') (M.projective X) (M.isProjective X') f
    unfold Representative.Over at hα h₂ h₃ h₄
    change (qhValue.{a} R).map α₂ = _ at h₂
    change (qhValue.{a} R).map α₁ = _ at h₃
    rw [Functor.map_comp, Functor.map_comp, h₂, hα, h₄, h₃]
    simp
  have h₂ : β ≫ β₂ = β₁ ≫ (injectiveSection M).map g := by
    letI := M.isInjective Y'
    apply (CochainComplex.IsKInjective.Qh_map_bijective _ (M.injective Y').obj.as).injective
    change (qhValue.{a} R).map (β ≫ β₂) = (qhValue.{a} R).map
      (β₁ ≫ injectiveLift (M.injective Y) (M.injective Y') (M.isInjective Y') g)
    have h₂ := injectiveLift_over B' (M.injective Y') (M.isInjective Y') (𝟙 Y')
    have h₃ := injectiveLift_over B (M.injective Y) (M.isInjective Y) (𝟙 Y)
    have h₄ := injectiveLift_over (M.injective Y) (M.injective Y') (M.isInjective Y') g
    unfold Representative.Over at hβ h₂ h₃ h₄
    change (qhValue.{a} R).map β₂ = _ at h₂
    change (qhValue.{a} R).map β₁ = _ at h₃
    rw [Functor.map_comp, Functor.map_comp, hβ, h₂, h₃, h₄]
    simp
  change M.hom.functor.map (Prod.mkHom α.op β) ≫
      M.hom.functor.map (Prod.mkHom α₂.op β₂) =
    M.hom.functor.map (Prod.mkHom α₁.op β₁) ≫
      M.hom.functor.map (Prod.mkHom ((projectiveSection M).map f).op ((injectiveSection M).map g))
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  exact Prod.ext (congrArg Quiver.Hom.op h₁) h₂

private theorem out_quasiIso {A B : K.{a} R} (f : A ⟶ B)
    (hf : IsIso ((Qh R).map f)) : QuasiIso f.out := by
  apply (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1
  rw [HomotopyCategory.quotient_map_out]
  exact (DerivedCategory.isIso_Qh_map_iff f).1 hf

private theorem isIso_quotient_projective {A B : K.{a} R} (f : A ⟶ B)
    (hA : IsKProjective A.as) (hB : IsKProjective B.as)
    (hf : IsIso ((Qh R).map f)) : IsIso f := by
  letI := hA
  letI := hB
  have h := (CochainComplex.IsKProjective.quasiIso_iff f.out).1 (out_quasiIso f hf)
  rw [← HomotopyCategory.inverseImage_quotient_isomorphisms,
    MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff,
    HomotopyCategory.quotient_map_out] at h
  exact h

private theorem isIso_quotient_injective {A B : K.{a} R} (f : A ⟶ B)
    (hA : IsKInjective A.as) (hB : IsKInjective B.as)
    (hf : IsIso ((Qh R).map f)) : IsIso f := by
  letI := hA
  letI := hB
  have h := (CochainComplex.IsKInjective.quasiIso_iff f.out).1 (out_quasiIso f hf)
  rw [← HomotopyCategory.inverseImage_quotient_isomorphisms,
    MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff,
    HomotopyCategory.quotient_map_out] at h
  exact h

private theorem signedHom_map_isIso (H : SignedHom.{u,a} R)
    {A A' B B' : Comp.{a} R} (f : A' ⟶ A) (g : B ⟶ B')
    (h : QuasiIso (internalHomMap f g)) :
    IsIso (H.functor.map (Prod.mkHom ((homotopyQuotient R).map f).op
      ((homotopyQuotient R).map g))) := by
  change IsIso (H.functor.map (Prod.mkHom ((quotientValue R).map f).op
    ((quotientValue R).map g)))
  rw [H.map_eq f g]
  letI : QuasiIso (internalHomMapValue f g) := h
  infer_instance

private theorem homPost_isIso (H : SignedHom.{u,a} R) (P : K.{a} R)
    (hP : IsKProjective P.as) {B B' : K.{a} R} (g : B ⟶ B')
    (hg : IsIso ((Qh R).map g)) :
    IsIso (H.functor.map (Prod.mkHom (𝟙 (op P)) g)) := by
  have h := signedHom_map_isIso H (𝟙 P.as) g.out
    (internalHomMap_quasiIso_of_isKProjective P.as hP g.out (out_quasiIso g hg))
  rw [(homotopyQuotient R).map_id P.as,
    HomotopyCategory.quotient_map_out g, op_id] at h
  exact h

private theorem homPre_isIso (H : SignedHom.{u,a} R) (I : K.{a} R)
    (hI : IsKInjective I.as) {A A' : K.{a} R} (f : A' ⟶ A)
    (hf : IsIso ((Qh R).map f)) :
    IsIso (H.functor.map (Prod.mkHom f.op (𝟙 I))) := by
  have h := signedHom_map_isIso H f.out (𝟙 I.as)
    (internalHomMap_quasiIso_of_isKInjective I.as hI f.out (out_quasiIso f hf))
  rw [(homotopyQuotient R).map_id I.as, HomotopyCategory.quotient_map_out f] at h
  exact h

theorem modelMap_isIso : modelMapIsIsoType.{u,a} := by
  intro R _ M X Y A B h
  let p := projectiveLift (M.projective X) A (M.isProjective X) (𝟙 X)
  let i := injectiveLift B (M.injective Y) (M.isInjective Y) (𝟙 Y)
  have hp : IsIso ((Qh R).map p) := by
    have ho := projectiveLift_over (M.projective X) A (M.isProjective X) (𝟙 X)
    change (Qh R).map p = _ at ho
    rw [ho]
    infer_instance
  have hi : IsIso ((Qh R).map i) := by
    have ho := injectiveLift_over B (M.injective Y) (M.isInjective Y) (𝟙 Y)
    change (Qh R).map i = _ at ho
    rw [ho]
    infer_instance
  change IsIso (M.hom.functor.map (Prod.mkHom p.op i))
  rcases h with hA | hB
  · letI := isIso_quotient_projective p (M.isProjective X) hA hp
    letI : IsIso (M.hom.functor.map (Prod.mkHom p.op (𝟙 B.obj))) :=
      inferInstanceAs (IsIso (M.hom.functor.map (Iso.prod (asIso p.op) (Iso.refl B.obj)).hom))
    letI := homPost_isIso M.hom (M.projective X).obj (M.isProjective X) i hi
    have he : Prod.mkHom p.op i =
        Prod.mkHom p.op (𝟙 B.obj) ≫ Prod.mkHom (𝟙 (op (M.projective X).obj)) i := by
      ext <;> simp
    rw [he, Functor.map_comp]
    infer_instance
  · letI := isIso_quotient_injective i hB (M.isInjective Y) hi
    letI : IsIso (M.hom.functor.map (Prod.mkHom (𝟙 (op A.obj)) i)) :=
      inferInstanceAs
        (IsIso (M.hom.functor.map (Iso.prod (Iso.refl (op A.obj)) (asIso i)).hom))
    letI := homPre_isIso M.hom (M.injective Y).obj (M.isInjective Y) p hp
    have he : Prod.mkHom p.op i =
        Prod.mkHom (𝟙 (op A.obj)) i ≫ Prod.mkHom p.op (𝟙 (M.injective Y).obj) := by
      ext <;> simp
    rw [he, Functor.map_comp]
    infer_instance

/-- Comparison of the signed Hom on either good representative with derived Hom. -/
def modelIso (M : Models.{u,a} R) {X Y : D.{a} R}
    (A : Representative X) (B : Representative Y)
    (h : IsKProjective A.obj.as ∨ IsKInjective B.obj.as) :
    (Q R).obj (internalHom A.obj.as B.obj.as) ≅ (rHomValue M).obj (op X, Y) := by
  letI := modelMap_isIso M A B h
  exact (eqToIso (M.hom.obj_eq A.obj B.obj)).symm ≪≫ asIso (modelMap M A B)

private def signedHomIso (H H' : SignedHom.{u,a} R) : H.functor ≅ H'.functor :=
  NatIso.ofComponents
    (fun Z => eqToIso (H.obj_eq Z.1.unop Z.2) ≪≫ (eqToIso (H'.obj_eq Z.1.unop Z.2)).symm)
    (by
      rintro ⟨⟨A⟩, B⟩ ⟨⟨A'⟩, B'⟩ f
      obtain ⟨a, rfl⟩ := HomotopyCategory.quotient_obj_surjective A
      obtain ⟨a', rfl⟩ := HomotopyCategory.quotient_obj_surjective A'
      obtain ⟨b, rfl⟩ := HomotopyCategory.quotient_obj_surjective B
      obtain ⟨b', rfl⟩ := HomotopyCategory.quotient_obj_surjective B'
      let q := quotientValue.{a} R
      letI : q.Full := inferInstanceAs (homotopyQuotient.{a} R).Full
      obtain ⟨α, hα⟩ := q.map_surjective f.1.unop
      obtain ⟨β, hβ⟩ := q.map_surjective f.2
      have hf : f = Prod.mkHom (q.map α).op (q.map β) :=
        Prod.ext (congrArg Quiver.Hom.op hα).symm hβ.symm
      subst f
      dsimp only [q, unop_op, Iso.trans_hom, Iso.symm_hom, eqToIso.hom, eqToIso.inv]
      rw [H.map_eq α β, H'.map_eq α β]
      simp)

/-- The natural isomorphism between any two choices of models, induced by
the unique homotopy-class comparisons over the identity maps. -/
def compareModels (M N : Models.{u,a} R) : rHomValue M ≅ rHomValue N := by
  let F := (projectiveSection M).op.prod (injectiveSection M)
  refine Functor.isoWhiskerLeft F (signedHomIso M.hom N.hom) ≪≫ NatIso.ofComponents
    (fun Z => ?_) ?_
  · let A := M.projective Z.1.unop
    let B := M.injective Z.2
    letI := modelMap_isIso N A B (Or.inl (M.isProjective Z.1.unop))
    exact asIso (modelMap N A B)
  · intro Z Z' f
    exact modelMap_natural N (M.projective Z.1.unop) (M.projective Z'.1.unop)
      (M.injective Z.2) (M.injective Z'.2) f.1.unop f.2
      ((projectiveSection M).map f.1.unop) ((injectiveSection M).map f.2)
      (projectiveLift_over _ _ (M.isProjective Z'.1.unop) f.1.unop)
      (injectiveLift_over _ _ (M.isInjective Z'.2) f.2)

theorem modelChoiceIndependence : modelChoiceIndependenceType.{u,a} :=
  fun M N => ⟨compareModels M N⟩

private theorem representative_over {A B : Comp.{a} R} {X Y : D.{a} R}
    (eA : (Q R).obj A ≅ X) (eB : (Q R).obj B ≅ Y) (f : X ⟶ Y)
    (g : A ⟶ B) (h : (Q R).map g = eA.hom ≫ f ≫ eB.inv) :
    (representative eA).Over (representative eB) f ((homotopyQuotient R).map g) := by
  let e := homotopyQuotientCompQhIso.{a} R
  have hn := e.hom.naturality g
  change (Qh R).map ((homotopyQuotient R).map g) ≫ e.hom.app B =
    e.hom.app A ≫ (Q R).map g at hn
  change (Qh R).map ((homotopyQuotient R).map g) =
    (e.app A ≪≫ eA).hom ≫ f ≫ (e.app B ≪≫ eB).inv
  calc
    _ = ((Qh R).map ((homotopyQuotient R).map g) ≫ e.hom.app B) ≫ e.inv.app B := by simp
    _ = _ := by
      rw [hn, h]
      simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
      rfl

/-- The model isomorphisms intertwine the signed chain action on any
representatives of the given pair of derived morphisms. -/
theorem modelIso_chain_natural (M : Models.{u,a} R) {X X' Y Y' : D.{a} R}
    {A A' B B' : Comp.{a} R} (eA : (Q R).obj A ≅ X) (eA' : (Q R).obj A' ≅ X')
    (eB : (Q R).obj B ≅ Y) (eB' : (Q R).obj B' ≅ Y')
    (h : IsKProjective A ∨ IsKInjective B) (h' : IsKProjective A' ∨ IsKInjective B')
    (f : X' ⟶ X) (g : Y ⟶ Y') (α : A' ⟶ A) (β : B ⟶ B')
    (hα : (Q R).map α = eA'.hom ≫ f ≫ eA.inv)
    (hβ : (Q R).map β = eB.hom ≫ g ≫ eB'.inv) :
    (Q R).map (internalHomMap α β) ≫
      (modelIso M (representative eA') (representative eB') h').hom =
        (modelIso M (representative eA) (representative eB) h).hom ≫
          (rHomValue M).map (Prod.mkHom f.op g) := by
  let q := quotientValue.{a} R
  let x := eqToHom (M.hom.obj_eq (q.obj A) (q.obj B)).symm
  let x' := eqToHom (M.hom.obj_eq (q.obj A') (q.obj B')).symm
  have hn := modelMap_natural M (representative eA) (representative eA')
    (representative eB) (representative eB') f g (q.map α) (q.map β)
    (representative_over eA' eA f α hα) (representative_over eB eB' g β hβ)
  change (qValue R).map (internalHomMapValue α β) ≫
    (x' ≫ modelMap M (representative eA') (representative eB')) =
      (x ≫ modelMap M (representative eA) (representative eB)) ≫
        (rHomValue M).map (Prod.mkHom f.op g)
  calc
    _ = x ≫ (M.hom.functor.map (Prod.mkHom (q.map α).op (q.map β)) ≫
        modelMap M (representative eA') (representative eB')) := by
      dsimp only [q]
      rw [M.hom.map_eq α β]
      simp [x, x']
    _ = _ := by
      rw [hn]
      simp only [Category.assoc]

theorem strictComparisons : strictComparisonsType.{u,a} := by
  intro R _ M X Y P I p i hp hi hP hI
  let p' := localizedIso p hp
  let i' := (localizedIso i hi).symm
  let x := Iso.refl ((Q R).obj X)
  let y := Iso.refl ((Q R).obj Y)
  refine ⟨modelIso M (representative p') (representative i') (Or.inl hP),
    modelIso M (representative p') (representative y) (Or.inl hP),
    modelIso M (representative x) (representative i') (Or.inr hI), ?_, ?_⟩
  · have h := modelIso_chain_natural M p' p' y i' (Or.inl hP) (Or.inl hP)
        (𝟙 _) (𝟙 _) (𝟙 P) i (by rw [(Q R).map_id]; simp)
        (by simp [i', y, localizedIso])
    change _ = _ ≫ (rHomValue M).map (𝟙 _) at h
    rw [(rHomValue M).map_id, Category.comp_id] at h
    exact h
  · have h := modelIso_chain_natural M x p' i' i' (Or.inr hI) (Or.inl hP)
        (𝟙 _) (𝟙 _) p (𝟙 I) (by simp [p', x, localizedIso])
        (by rw [(Q R).map_id]; simp)
    change _ = _ ≫ (rHomValue M).map (𝟙 _) at h
    rw [(rHomValue M).map_id, Category.comp_id] at h
    exact h

open CochainComplex.HomComplex (Cochain)
open CochainCoefficientLift (termEquiv lift_d lift_f)

/-- Conjugate homogeneous maps by the linear equivalences of the original
terms with their actual lifts. -/
def mixedProduct (X : Comp.{v} R) (Y : Comp.{w} R) (n : ℤ) :
    (internalHom (liftSource.{u,v,w,t} X) (liftTarget.{u,v,w,t} Y)).X n
      ≃ₗ[R] MixedProduct X Y n where
  toFun z := fun ⟨(i,j), h⟩ => (termEquiv.{max u v t} Y j).symm.toLinearMap.comp
    ((z.v i j h).hom.comp (termEquiv.{max u w t} X i).toLinearMap)
  invFun z := Cochain.mk fun i j h => ModuleCat.ofHom <|
    (termEquiv.{max u v t} Y j).toLinearMap.comp
      ((z ⟨(i,j), h⟩).comp (termEquiv.{max u w t} X i).symm.toLinearMap)
  left_inv z := by
    apply Cochain.ext
    intro i j h
    rw [Cochain.mk_v]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let ex := termEquiv.{max u w t} X i
    let ey := termEquiv.{max u v t} Y j
    change ey (ey.symm (z.v i j h (ex (ex.symm x)))) = z.v i j h x
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  right_inv z := by
    funext ij
    obtain ⟨⟨i, j⟩, h⟩ := ij
    apply LinearMap.ext
    intro x
    dsimp only
    rw [Cochain.mk_v]
    simp only [LinearMap.comp_apply, ModuleCat.hom_ofHom, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem mixedProduct_eval (X : Comp.{v} R) (Y : Comp.{w} R) (n i j : ℤ) (h : i + n = j)
    (z : Cochain (liftSource.{u,v,w,t} X) (liftTarget.{u,v,w,t} Y) n) (x : X.X i) :
    z.v i j h (termEquiv.{max u w t} X i x) =
      termEquiv.{max u v t} Y j (mixedProduct.{u,v,w,t} X Y n z ⟨(i,j), h⟩ x) :=
  ((termEquiv.{max u v t} Y j).apply_symm_apply _).symm

theorem mixedProductComparison : mixedProductComparisonType.{u,v,w,t} := by
  intro R _
  refine ⟨mixedProduct.{u,v,w,t}, mixedProduct_eval.{u,v,w,t}, ?_, ?_⟩
  · intro X Y n i z x
    apply (termEquiv.{max u v t} Y (i + n + 1)).injective
    rw [← mixedProduct_eval.{u,v,w,t}, internalHom_d_apply]
    rw [mixedProduct_eval.{u,v,w,t} X Y n i (i + n) rfl, lift_d, lift_d, mixedProduct_eval.{u,v,w,t}]
    simp only [map_sub, Units.smul_def, map_zsmul]
  · intro X X' Y Y' f g n i j h z x
    apply (termEquiv.{max u v t} Y' j).injective
    rw [← mixedProduct_eval.{u,v,w,t}]
    change (((internalHomMap ((CochainCoefficientLift.lift.{max u w t,v} R).map f)
      ((CochainCoefficientLift.lift.{max u v t,w} R).map g)).f n z).v i j h)
      (termEquiv.{max u w t} X' i x) = _
    rw [internalHomMap_apply, lift_f, mixedProduct_eval.{u,v,w,t}, lift_f]

theorem originalComparison : originalComparisonType.{u,v,w,t} := by
  intro R _ M X Y
  dsimp only
  obtain ⟨P, p, hp, _, _, hP, _, _, _⟩ :=
    SemifreeReplacement.adequateReplacement.{u,v,max w t} R X
  obtain ⟨_, _, _, _, _, _, _, _, _, _, J, _, _, _, i, _, _, hi, hI, _, _, _, _⟩ :=
    KInjectiveReplacementTransport.replacementTransport.{w,u,max v t}.1 (R := R) Y
  let eX := (CochainCoefficientLift.liftDFactors.{max u w t,v} R).symm.app X
  let eY := (CochainCoefficientLift.liftDFactors.{max u v t,w} R).symm.app Y
  exact ⟨P, Limits.limit J, p, i, hp, hi, hP, hI,
    ⟨modelIso M (representative (localizedIso p hp ≪≫ eX))
      (representative ((localizedIso i hi).symm ≪≫ eY)) (Or.inl hP)⟩,
    ⟨modelIso M (representative (localizedIso p hp ≪≫ eX)) (representative eY)
      (Or.inl hP)⟩,
    ⟨modelIso M (representative eX) (representative ((localizedIso i hi).symm ≪≫ eY))
      (Or.inr hI)⟩⟩

end

end DerivedFormalization.DerivedHomModels
