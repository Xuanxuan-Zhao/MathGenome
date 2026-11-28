import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.JetEquivariantRestriction
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedPullbackPasting
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedEquivarianceExtension
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace RepTheorySurvey.Geometric.JetEquivariantRestriction

open Analytic AnalyticAction JetEquivariantRestrictionSpecs
open Analytic.DerivedPullbackPasting.Expected (squareValue)
open ClosedEquivarianceExtensionSpecs (parameterInclusion projectionSquare)

open private compositionAt compositionAt_inv pullbackMorphism_eq restrictionComparison
  RestrictsTo RestrictsTo.pullback RestrictsTo.comp
  restrictsTo_id pasteActionSquare
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedEquivarianceExtension

open private square_hom from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedPullbackPasting

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 250000
set_option linter.style.haveILetI false

/-- The inverse-image arrow of a coefficient morphism, with its target written
using the parameter pullback. -/
private def coefficientArrow {U X V W : TopCat.{0}} {i : U ⟶ X} {j : V ⟶ W}
    {e : W ⟶ X} {b : V ⟶ U} (h : j ≫ e = b ≫ i)
    {G : Derived U} {F : Derived X} (v : G ⟶ (derivedInverseImage i).obj F) :
    (derivedInverseImage b).obj G ⟶ (derivedInverseImage j).obj ((derivedInverseImage e).obj F) :=
  (derivedInverseImage b).map v ≫ (squareValue h).inv.app F

private theorem commutes_iff {H : AnalyticGroup.{0}} {U X : TopCat.{0}}
    {B : AnalyticAction H U} {A : AnalyticAction H X} {i : U ⟶ X}
    (he : ActionSquare B A i) {G : Derived U} {F : Derived X}
    (β : B.Equivariance G) (α : A.Equivariance F)
    (v : G ⟶ (derivedInverseImage i).obj F) :
    Commutes he β α v ↔
      coefficientArrow he v ≫ (derivedInverseImage (parameterInclusion H i)).map α.iso.hom =
        β.iso.hom ≫ coefficientArrow (projectionSquare H i) v := by
  let p := (squareValue (projectionSquare H i)).app F
  let a := coefficientArrow he v ≫ (derivedInverseImage (parameterInclusion H i)).map α.iso.hom
  let b := β.iso.hom ≫ (derivedInverseImage (projection H U)).map v
  have h := p.symm.comp_inv_eq (f := a) (g := b)
  change a ≫ (squareValue (projectionSquare H i)).hom.app F = b ↔
    a = b ≫ (squareValue (projectionSquare H i)).inv.app F at h
  simpa only [a, b, Commutes, coefficientArrow, Category.assoc] using h

/-- The coefficient comparison at the source end of a restriction square. -/
private def coefficientIso {U X V W : TopCat.{0}} {i : U ⟶ X} {j : V ⟶ W}
    {e : W ⟶ X} {b : V ⟶ U} (he : j ≫ e = b ≫ i)
    {F : Derived X} {G : Derived U} (v : G ≅ (derivedInverseImage i).obj F) :
    (derivedInverseImage j).obj ((derivedInverseImage e).obj F) ≅
      (derivedInverseImage b).obj G :=
  (squareValue he).app F ≪≫ (derivedInverseImage b).mapIso v.symm

private theorem coefficientIso_hom {U X V W : TopCat.{0}} {i : U ⟶ X} {j : V ⟶ W}
    {e : W ⟶ X} {b : V ⟶ U} (he : j ≫ e = b ≫ i)
    {F : Derived X} {G : Derived U} (v : G ≅ (derivedInverseImage i).obj F) :
    (coefficientIso he v).hom =
      (compositionAt j e he F).inv ≫ restrictionComparison i b v.inv := by
  rw [compositionAt_inv, Category.assoc]
  change (squareValue he).hom.app F ≫ (derivedInverseImage b).map v.inv = _
  rw [square_hom, Category.assoc, Category.assoc]
  rfl

private theorem restrictsTo_iff {U X V W : TopCat.{0}} {i : U ⟶ X} {j : V ⟶ W}
    {e p : W ⟶ X} {b q : V ⟶ U} (he : j ≫ e = b ≫ i) (hp : j ≫ p = q ≫ i)
    {F : Derived X} {G : Derived U} (v : G ≅ (derivedInverseImage i).obj F)
    (a : (derivedInverseImage e).obj F ⟶ (derivedInverseImage p).obj F)
    (d : (derivedInverseImage b).obj G ⟶ (derivedInverseImage q).obj G) :
    RestrictsTo i j he hp v.inv a d ↔
      (derivedInverseImage j).map a ≫ (coefficientIso hp v).hom =
        (coefficientIso he v).hom ≫ d := by
  unfold RestrictsTo
  rw [pullbackMorphism_eq, coefficientIso_hom, coefficientIso_hom]
  simp only [Category.assoc]
  exact (compositionAt j e he F).symm.inv_comp_eq

private theorem restriction_injective {U X V W : TopCat.{0}} {i : U ⟶ X} {j : V ⟶ W}
    {e p : W ⟶ X} {b q : V ⟶ U} (he : j ≫ e = b ≫ i) (hp : j ≫ p = q ≫ i)
    {F : Derived X} {G : Derived U} (v : G ≅ (derivedInverseImage i).obj F)
    (inj : Function.Injective ((derivedInverseImage j).map :
      ((derivedInverseImage e).obj F ⟶ (derivedInverseImage p).obj F) → _))
    {a a' : (derivedInverseImage e).obj F ⟶ (derivedInverseImage p).obj F}
    {d : (derivedInverseImage b).obj G ⟶ (derivedInverseImage q).obj G}
    (h : RestrictsTo i j he hp v.inv a d) (h' : RestrictsTo i j he hp v.inv a' d) : a = a' :=
  inj ((cancel_mono (coefficientIso hp v).hom).mp
    (((restrictsTo_iff he hp v a d).mp h).trans ((restrictsTo_iff he hp v a' d).mp h').symm))

private theorem commutes_iff_restrictsTo {H : AnalyticGroup.{0}} {U X : TopCat.{0}}
    {B : AnalyticAction H U} {A : AnalyticAction H X} {i : U ⟶ X}
    (he : ActionSquare B A i) {G : Derived U} {F : Derived X}
    (β : B.Equivariance G) (α : A.Equivariance F)
    (v : G ≅ (derivedInverseImage i).obj F) :
    Commutes he β α v.hom ↔
      RestrictsTo i (parameterInclusion H i) he (projectionSquare H i) v.inv
        α.iso.hom β.iso.hom := by
  let r := coefficientIso he v
  let s := coefficientIso (projectionSquare H i) v
  rw [commutes_iff he β α v.hom, restrictsTo_iff he (projectionSquare H i) v]
  change (r.inv ≫ _ = _ ≫ s.inv) ↔ (_ ≫ s.hom = r.hom ≫ _)
  rw [r.inv_comp_eq, ← Category.assoc r.hom, s.eq_comp_inv]

private theorem exists_iso_mapIso_eq {C D : Type*} [Category C] [Category D]
    (K : C ⥤ D) {Q P : C}
    (hom : Function.Surjective (K.map : (Q ⟶ P) → _))
    (inv : Function.Surjective (K.map : (P ⟶ Q) → _))
    (left : Function.Injective (K.map : (Q ⟶ Q) → _))
    (right : Function.Injective (K.map : (P ⟶ P) → _))
    (δ : K.obj Q ≅ K.obj P) :
    ∃ a : Q ≅ P, K.map a.hom = δ.hom := by
  obtain ⟨f, hf⟩ := hom δ.hom
  obtain ⟨g, hg⟩ := inv δ.inv
  refine ⟨⟨f, g, left ?_, right ?_⟩, hf⟩
  · rw [K.map_comp, hf, hg, δ.hom_inv_id, K.map_id]
  · rw [K.map_comp, hg, hf, δ.inv_hom_id, K.map_id]

/-- Lift the operator and inverse using only Hom maps between the two pullbacks. -/
private theorem exists_restricting_iso {U X V W : TopCat.{0}} {i : U ⟶ X} {j : V ⟶ W}
    {e p : W ⟶ X} {b q : V ⟶ U} (he : j ≫ e = b ≫ i) (hp : j ≫ p = q ≫ i)
    {F : Derived X} {G : Derived U} (v : G ≅ (derivedInverseImage i).obj F)
    (δ : (derivedInverseImage b).obj G ≅ (derivedInverseImage q).obj G)
    (bij : ∀ (S T : Derived W),
      (S = (derivedInverseImage e).obj F ∨ S = (derivedInverseImage p).obj F) →
      (T = (derivedInverseImage e).obj F ∨ T = (derivedInverseImage p).obj F) →
      Function.Bijective ((derivedInverseImage j).map : (S ⟶ T) → _)) :
    ∃ a : (derivedInverseImage e).obj F ≅ (derivedInverseImage p).obj F,
      RestrictsTo i j he hp v.inv a.hom δ.hom := by
  obtain ⟨a, ha⟩ := exists_iso_mapIso_eq (derivedInverseImage j)
    (bij _ _ (Or.inl rfl) (Or.inr rfl)).2 (bij _ _ (Or.inr rfl) (Or.inl rfl)).2
    (bij _ _ (Or.inl rfl) (Or.inl rfl)).1 (bij _ _ (Or.inr rfl) (Or.inr rfl)).1
    (coefficientIso he v ≪≫ δ ≪≫ (coefficientIso hp v).symm)
  refine ⟨a, (restrictsTo_iff he hp v a.hom δ.hom).mpr ?_⟩
  rw [ha]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem exists_restricting_datum {H : AnalyticGroup.{0}} {U X : TopCat.{0}}
    {B : AnalyticAction H U} {A : AnalyticAction H X} {i : U ⟶ X}
    (he : ActionSquare B A i) {G : Derived U} {F : Derived X}
    (v : G ≅ (derivedInverseImage i).obj F) (β : B.Equivariance G)
    (idInj : Function.Injective ((derivedInverseImage i).map :
      ((derivedInverseImage (𝟙 X)).obj F ⟶ (derivedInverseImage (𝟙 X)).obj F) → _))
    (bij : ∀ (S T : Derived (Parameters H X)),
      (S = (derivedInverseImage A.act).obj F ∨ S = (derivedInverseImage (projection H X)).obj F) →
      (T = (derivedInverseImage A.act).obj F ∨ T = (derivedInverseImage (projection H X)).obj F) →
      Function.Bijective ((derivedInverseImage (parameterInclusion H i)).map : (S ⟶ T) → _))
    (mulInj : Function.Injective
      ((derivedInverseImage (parameterInclusion H (parameterInclusion H i))).map :
        ((derivedInverseImage (multiplyParameters H X ≫ A.act)).obj F ⟶
          (derivedInverseImage (multiplyParameters H X ≫ projection H X)).obj F) → _)) :
    ∃ α : A.Equivariance F,
      RestrictsTo i (parameterInclusion H i) he (projectionSquare H i) v.inv
        α.iso.hom β.iso.hom := by
  let j := parameterInclusion H i
  let hp := projectionSquare H i
  obtain ⟨a, ha⟩ := exists_restricting_iso he hp v β.iso bij
  refine ⟨{ iso := a, identity := ?_, multiplication := ?_ }, ha⟩
  · have hi : i ≫ identitySection H X = identitySection H U ≫ j :=
      TopCat.ext (fun _ => rfl)
    have hid : i ≫ 𝟙 X = 𝟙 U ≫ i := rfl
    have h := RestrictsTo.pullback (identitySection H X) (identitySection H U)
      hi (identity_act A) identity_projection (identity_act B) identity_projection hid hid ha
    rw [β.identity] at h
    exact restriction_injective hid hid v idInj h (restrictsTo_id i i hid v.inv)
  · let j₂ := parameterInclusion H j
    let mx := multiplyParameters H X
    let mu := multiplyParameters H U
    let sx := secondParameter H X
    let su := secondParameter H U
    let fx := firstAfterSecond A
    let fu := firstAfterSecond B
    have hm : j₂ ≫ mx = mu ≫ j := TopCat.ext (fun _ => rfl)
    have hs : j₂ ≫ sx = su ≫ j := TopCat.ext (fun _ => rfl)
    have hf : j₂ ≫ fx = fu ≫ j := TopCat.ext (fun ⟨g, h, x⟩ =>
      congrArg (g, ·) (congrArg (fun f : Parameters H U ⟶ X => f (h, x)) he))
    have hme : j₂ ≫ (mx ≫ A.act) = (mu ≫ B.act) ≫ i := pasteActionSquare hm he
    have hmp : j₂ ≫ (mx ≫ projection H X) = (mu ≫ projection H U) ≫ i :=
      pasteActionSquare hm hp
    have hse : j₂ ≫ (sx ≫ A.act) = (su ≫ B.act) ≫ i := pasteActionSquare hs he
    have hm' := RestrictsTo.pullback mx mu hm rfl rfl rfl rfl hme hmp ha
    have hf' := RestrictsTo.pullback fx fu hf (multiply_act A) (first_projection A)
      (multiply_act B) (first_projection B) hme hse ha
    have hs' := RestrictsTo.pullback sx su hs rfl (multiply_projection (H := H) (X := X))
      rfl (multiply_projection (H := H) (X := U)) hse hmp ha
    have hcomp := RestrictsTo.comp hf' hs'
    rw [← β.multiplication] at hcomp
    exact restriction_injective hme hmp v mulInj hm' hcomp

private theorem jetEquivariance_ext {J : JetSystem.{0}} {X : TopCat.{0}}
    {A : JetAction J X} {F : Derived X} {α α' : A.Equivariance F}
    (h : α.datum = α'.datum) : α = α' := by
  cases α
  cases α'
  cases h
  rfl

theorem equivarianceLifting : Expected.EquivarianceLifting := by
  intro J U X B A i hc h G F v β idInj bij mulInj
  have hex (k : ℕ) (hk : A.cutoff ≤ k) :=
    exists_restricting_datum (h k hk) v (β.datum k (hc.trans hk)) idInj
      (bij k hk) (mulInj k hk)
  choose δ hr using hex
  let α : A.Equivariance F :=
    { datum := δ
      compatibility := by
        intro k l hk hkl
        let hl := hk.trans hkl
        let kx := J.parameterMap hkl (𝟙 X)
        let ku := J.parameterMap hkl (𝟙 U)
        let j (n : ℕ) := parameterInclusion (J.group n) i
        have htr : j l ≫ kx = ku ≫ j k := TopCat.ext (fun _ => rfl)
        have hpx : kx ≫ projection (J.group k) X = projection (J.group l) X :=
          TopCat.ext (fun _ => rfl)
        have hpu : ku ≫ projection (J.group k) U = projection (J.group l) U :=
          TopCat.ext (fun _ => rfl)
        have hres := RestrictsTo.pullback kx ku htr (A.factors hk hkl) hpx
          (B.factors (hc.trans hk) hkl) hpu (h l hl) (projectionSquare _ i) (hr k hk)
        rw [β.compatibility (hc.trans hk) hkl] at hres
        exact restriction_injective (h l hl) (projectionSquare _ i) v
          (bij l hl _ _ (Or.inl rfl) (Or.inr rfl)).1 hres (hr l hl) }
  refine ⟨α, fun k hk => (commutes_iff_restrictsTo (h k hk) _ _ v).mpr (hr k hk), ?_⟩
  intro α' hα'
  have hdatum : α'.datum = α.datum := by
    funext k hk
    have hres := (commutes_iff_restrictsTo (h k hk) _ _ v).mp (hα' k hk)
    have hh := restriction_injective (h k hk) (projectionSquare _ i) v
      (bij k hk _ _ (Or.inl rfl) (Or.inr rfl)).1 hres (hr k hk)
    have hiso : (α'.datum k hk).iso = (α.datum k hk).iso := Iso.ext hh
    generalize α'.datum k hk = a at hiso ⊢
    generalize α.datum k hk = b at hiso ⊢
    cases a
    cases b
    cases hiso
    rfl
  exact jetEquivariance_ext hdatum

set_option maxHeartbeats 800000 in
private theorem square_inv_paste {V W T U X Y : TopCat.{0}}
    {j : V ⟶ W} {j' : W ⟶ T} {i : U ⟶ X} {i' : X ⟶ Y}
    {b : V ⟶ U} {a : W ⟶ X} {c : T ⟶ Y}
    (h : j ≫ a = b ≫ i) (h' : j' ≫ c = a ≫ i')
    (hh : (j ≫ j') ≫ c = b ≫ (i ≫ i')) (E : Derived Y) :
    (squareValue hh).inv.app E =
      (derivedInverseImage b).map ((derivedInverseImageComposition i i').hom.app E) ≫
        (squareValue h).inv.app ((derivedInverseImage i').obj E) ≫
        (derivedInverseImage j).map ((squareValue h').inv.app E) ≫
        (derivedInverseImageComposition j j').inv.app ((derivedInverseImage c).obj E) := by
  let d₁ := (derivedInverseImageComposition j j').app ((derivedInverseImage c).obj E)
  let d₂ := (derivedInverseImage j).mapIso ((squareValue h').app E)
  let d₃ := (squareValue h).app ((derivedInverseImage i').obj E)
  let d₄ := (derivedInverseImage b).mapIso ((derivedInverseImageComposition i i').app E).symm
  have hcomp : (squareValue hh).app E = d₁ ≪≫ d₂ ≪≫ d₃ ≪≫ d₄ :=
    Iso.ext (DerivedPullbackPasting.squareHorizontalPasting h h' E)
  have hinv := congrArg Iso.inv hcomp
  change ((squareValue hh).app E).inv = d₄.inv ≫ d₃.inv ≫ d₂.inv ≫ d₁.inv
  simpa only [Iso.trans_inv, Category.assoc] using hinv

@[reassoc]
private theorem coefficientArrow_paste {V W T U X Y : TopCat.{0}}
    {j : V ⟶ W} {j' : W ⟶ T} {i : U ⟶ X} {i' : X ⟶ Y}
    {b : V ⟶ U} {a : W ⟶ X} {c : T ⟶ Y}
    (h : j ≫ a = b ≫ i) (h' : j' ≫ c = a ≫ i')
    (hh : (j ≫ j') ≫ c = b ≫ (i ≫ i')) {G : Derived U} {F : Derived X} {E : Derived Y}
    (v : G ⟶ (derivedInverseImage i).obj F) (w : F ⟶ (derivedInverseImage i').obj E) :
    coefficientArrow hh (v ≫ (derivedInverseImage i).map w ≫
        (derivedInverseImageComposition i i').inv.app E) =
      coefficientArrow h v ≫ (derivedInverseImage j).map (coefficientArrow h' w) ≫
        (derivedInverseImageComposition j j').inv.app ((derivedInverseImage c).obj E) := by
  have hn := (squareValue h).inv.naturality w
  change (derivedInverseImage b).map ((derivedInverseImage i).map w) ≫
      (squareValue h).inv.app ((derivedInverseImage i').obj E) =
    (squareValue h).inv.app F ≫ (derivedInverseImage j).map ((derivedInverseImage a).map w) at hn
  simp only [coefficientArrow, square_inv_paste h h' hh E, Functor.map_comp, Category.assoc]
  rw [← (derivedInverseImage b).map_comp_assoc
    ((derivedInverseImageComposition i i').inv.app E)
    ((derivedInverseImageComposition i i').hom.app E)]
  rw [Iso.inv_hom_id_app]
  erw [(derivedInverseImage b).map_id, Category.id_comp, reassoc_of% hn]

/-- Pasting and reflection use the same compatibility calculation, with
cancellation in the reflection direction. -/
theorem equivariancePasting : Expected.EquivariancePasting := by
  intro H U X Y B A C i i' hi hi' hii' G F E β α γ v w
  let j := parameterInclusion H i
  let j' := parameterInclusion H i'
  let z := v ≫ (derivedInverseImage i).map w ≫ (derivedInverseImageComposition i i').inv.app E
  change Commutes hi β α v →
    (Commutes hi' α γ w → Commutes hii' β γ z) ∧
      (IsIso v → (derivedInverseImage j).Faithful → Commutes hii' β γ z → Commutes hi' α γ w)
  change j ≫ A.act = B.act ≫ i at hi
  change j' ≫ C.act = A.act ≫ i' at hi'
  have he : (j ≫ j') ≫ C.act = B.act ≫ (i ≫ i') := hii'
  have hp : (j ≫ j') ≫ projection H Y = projection H U ≫ (i ≫ i') :=
    projectionSquare H (i ≫ i')
  intro h
  have h₁ := (commutes_iff hi β α v).mp h
  change coefficientArrow hi v ≫ (derivedInverseImage j).map α.iso.hom =
    β.iso.hom ≫ coefficientArrow (projectionSquare H i) v at h₁
  have hc : Commutes hii' β γ z ↔
      coefficientArrow hi v ≫
        (derivedInverseImage j).map
          (coefficientArrow hi' w ≫ (derivedInverseImage j').map γ.iso.hom) =
      coefficientArrow hi v ≫
        (derivedInverseImage j).map (α.iso.hom ≫ coefficientArrow (projectionSquare H i') w) := by
    rw [commutes_iff]
    have hn := (derivedInverseImageComposition j j').inv.naturality γ.iso.hom
    change (derivedInverseImage j).map ((derivedInverseImage j').map γ.iso.hom) ≫
        (derivedInverseImageComposition j j').inv.app ((derivedInverseImage (projection H Y)).obj E) =
      (derivedInverseImageComposition j j').inv.app ((derivedInverseImage C.act).obj E) ≫
        (derivedInverseImage (j ≫ j')).map γ.iso.hom at hn
    change (coefficientArrow he z ≫ (derivedInverseImage (j ≫ j')).map γ.iso.hom =
      β.iso.hom ≫ coefficientArrow hp z) ↔ _
    dsimp only [z]
    rw [coefficientArrow_paste_assoc hi hi' he, coefficientArrow_paste
      (projectionSquare H i) (projectionSquare H i') hp, ← hn]
    rw [← reassoc_of% h₁, ← (derivedInverseImage j).map_comp_assoc,
      ← (derivedInverseImage j).map_comp_assoc]
    exact cancel_mono_assoc_iff
      ((derivedInverseImageComposition j j').inv.app ((derivedInverseImage (projection H Y)).obj E))
  constructor
  · intro hw
    exact hc.mpr (congrArg (fun f => coefficientArrow hi v ≫ (derivedInverseImage j).map f)
      ((commutes_iff hi' α γ w).mp hw))
  · intro hv hf hz
    letI : IsIso v := hv
    letI : (derivedInverseImage j).Faithful := hf
    haveI : IsIso (coefficientArrow hi v) := by unfold coefficientArrow; infer_instance
    apply (commutes_iff hi' α γ w).mpr
    exact (derivedInverseImage j).map_injective
      ((cancel_epi (coefficientArrow hi v)).mp (hc.mp hz))

end RepTheorySurvey.Geometric.JetEquivariantRestriction
