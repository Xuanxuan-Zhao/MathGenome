import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SupportIntersectionEquivariance
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedSupportPullbackPasting
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace RepTheorySurvey.Geometric.SupportIntersectionEquivariance

open Analytic Analytic.AnalyticAction
open ClosedEquivarianceExtensionSpecs (parameterInclusion projectionSquare)
open EquivariantIntersectionComplexesSpecs (Intertwines restrictedArrow)
open FiniteStageClosedExtensionSpecs (SupportIntersections)

open private RestrictsTo RestrictsTo.comp RestrictsTo.pullback restrictsTo_id restrictionComparison
  restrictionComparison_isIso compComparison pasteActionSquare compositionAt pullbackMorphism_paste pullbackMorphism_congr from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedEquivarianceExtension
open private pullbackMorphismThroughSquare
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedSupportPullbackPasting
open Analytic.DerivedPullbackPasting.Expected (squareValue)

set_option allowUnsafeReducibility true in
attribute [local reducible] Analytic.DerivedPullbackPasting.Expected.SquareType

private theorem derivedIsZeroOfIsEmpty {X : TopCat.{0}} [IsEmpty X] (F : Derived X) : IsZero F := by
  let f : F ⟶ 0 := 0
  have : IsIso f := (DerivedCategory.isIso_iff (Sheaves X) f).mpr fun n => by
    apply isIso_of_source_target_iso_zero
    all_goals
      apply IsZero.isoZero
      apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr
      exact fun x => isEmptyElim x
  exact (isZero_zero _).of_iso (asIso f)

private def emptyDatum {H : AnalyticGroup.{0}} {U : TopCat.{0}} [IsEmpty U]
    (A : AnalyticAction H U) (F : Derived U) : A.Equivariance F where
  iso := (derivedIsZeroOfIsEmpty _).iso (derivedIsZeroOfIsEmpty _)
  identity := (derivedIsZeroOfIsEmpty _).eq_of_src _ _
  multiplication := (derivedIsZeroOfIsEmpty _).eq_of_src _ _

/-- Conjugate the pulled-back isomorphism by the two commutative squares. -/
private def squareIso {U X V W : TopCat.{0}} {i : U ⟶ X} {j : V ⟶ W}
    {e p : W ⟶ X} {v q : V ⟶ U} (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    {F : Derived X} (α : (derivedInverseImage e).obj F ≅ (derivedInverseImage p).obj F) :
    (derivedInverseImage v).obj ((derivedInverseImage i).obj F) ≅
      (derivedInverseImage q).obj ((derivedInverseImage i).obj F) :=
  ((squareValue he).app F).symm ≪≫ (derivedInverseImage j).mapIso α ≪≫ (squareValue hp).app F

private theorem squareIso_hom {U X V W : TopCat.{0}} {i : U ⟶ X} {j : V ⟶ W}
    {e p : W ⟶ X} {v q : V ⟶ U} (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    {F : Derived X} (α : (derivedInverseImage e).obj F ≅ (derivedInverseImage p).obj F) :
    (squareIso he hp α).hom =
      (derivedInverseImageComposition v i).inv.app F ≫ pullbackMorphism j he hp α.hom ≫
        (derivedInverseImageComposition q i).hom.app F := by
  exact (pullbackMorphismThroughSquare he hp α.hom).symm

private theorem squareIso_restrictsTo {U X V W : TopCat.{0}} {i : U ⟶ X} {j : V ⟶ W}
    {e p : W ⟶ X} {v q : V ⟶ U} (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    {F : Derived X} (α : (derivedInverseImage e).obj F ≅ (derivedInverseImage p).obj F) :
    RestrictsTo i j he hp (𝟙 ((derivedInverseImage i).obj F)) α.hom (squareIso he hp α).hom := by
  unfold RestrictsTo restrictionComparison compComparison
  rw [squareIso_hom]
  rw [(derivedInverseImage v).map_id, (derivedInverseImage q).map_id]
  erw [Category.comp_id ((derivedInverseImageComposition q i).hom.app F),
    Category.comp_id ((derivedInverseImageComposition v i).hom.app F),
    Iso.hom_inv_id_app_assoc]

private theorem restriction_unique {U X V W : TopCat.{0}} {i : U ⟶ X} {j : V ⟶ W}
    {e p : W ⟶ X} {v q : V ⟶ U} {he : j ≫ e = v ≫ i} {hp : j ≫ p = q ≫ i}
    {F : Derived X} {α : (derivedInverseImage e).obj F ⟶ (derivedInverseImage p).obj F}
    {β γ : (derivedInverseImage v).obj ((derivedInverseImage i).obj F) ⟶
      (derivedInverseImage q).obj ((derivedInverseImage i).obj F)}
    (hβ : RestrictsTo i j he hp (𝟙 _) α β) (hγ : RestrictsTo i j he hp (𝟙 _) α γ) : β = γ := by
  let ε := 𝟙 ((derivedInverseImage i).obj F)
  haveI := restrictionComparison_isIso i v ε
  exact (cancel_epi (restrictionComparison i v ε)).mp (hβ.symm.trans hγ)

private def restrictDatum {H : AnalyticGroup.{0}} {U X : TopCat.{0}} {i : U ⟶ X}
    (A : AnalyticAction H X) (B : AnalyticAction H U)
    (hA : parameterInclusion H i ≫ A.act = B.act ≫ i)
    {F : Derived X} (α : A.Equivariance F) :
    B.Equivariance ((derivedInverseImage i).obj F) where
  iso := squareIso hA (projectionSquare H i) α.iso
  identity := by
    let j := parameterInclusion H i
    have h := squareIso_restrictsTo hA (projectionSquare H i) α.iso
    have hi : i ≫ identitySection H X = identitySection H U ≫ j :=
      TopCat.ext (fun _ => rfl)
    have hId : i ≫ 𝟙 X = 𝟙 U ≫ i := (Category.comp_id i).trans (Category.id_comp i).symm
    have hr := RestrictsTo.pullback (identitySection H X) (identitySection H U) hi (identity_act A)
      identity_projection (identity_act B) identity_projection hId hId h
    rw [α.identity] at hr
    exact restriction_unique hr (restrictsTo_id i i hId (𝟙 ((derivedInverseImage i).obj F)))
  multiplication := by
    let j := parameterInclusion H i
    let j₂ := parameterInclusion H j
    let mx := multiplyParameters H X
    let mu := multiplyParameters H U
    let sx := secondParameter H X
    let su := secondParameter H U
    let fx := firstAfterSecond A
    let fu := firstAfterSecond B
    let px := projection H X
    let pu := projection H U
    have hm : j₂ ≫ mx = mu ≫ j := TopCat.ext (fun _ => rfl)
    have hs : j₂ ≫ sx = su ≫ j := TopCat.ext (fun _ => rfl)
    have hf : j₂ ≫ fx = fu ≫ j := TopCat.ext (fun ⟨g, h, z⟩ =>
      congrArg (g, ·) (congrArg (fun f : Parameters H U ⟶ X => f (h, z)) hA))
    have he : j₂ ≫ (mx ≫ A.act) = (mu ≫ B.act) ≫ i := pasteActionSquare hm hA
    have hp : j₂ ≫ (mx ≫ px) = (mu ≫ pu) ≫ i := pasteActionSquare hm (projectionSquare H i)
    have ht : j₂ ≫ (sx ≫ A.act) = (su ≫ B.act) ≫ i := pasteActionSquare hs hA
    have h := squareIso_restrictsTo hA (projectionSquare H i) α.iso
    have hm' := RestrictsTo.pullback mx mu hm rfl rfl rfl rfl he hp h
    have hf' := RestrictsTo.pullback fx fu hf (multiply_act A) (first_projection A)
      (multiply_act B) (first_projection B) he ht h
    have hs' := RestrictsTo.pullback sx su hs rfl (multiply_projection (H := H) (X := X))
      rfl (multiply_projection (H := H) (X := U)) ht hp h
    have hc := RestrictsTo.comp hf' hs'
    rw [← α.multiplication] at hc
    exact restriction_unique hm' hc

section Jets

variable {J : JetSystem.{0}} {U X : TopCat.{0}} {i : U ⟶ X}
variable {A : JetAction J U} {B : JetAction J X}
variable (h : Intertwines A B i)
variable (levels : ∀ (k : ℕ), A.cutoff ≤ k → B.cutoff ≤ k ∨ IsEmpty U)
variable {F : Derived X} (α : B.Equivariance F)

include levels in
private theorem emptyBelowCutoff (k : ℕ) (hk : A.cutoff ≤ k) (hb : ¬ B.cutoff ≤ k) :
    IsEmpty U :=
  (levels k hk).resolve_left hb

private def restrictLevel (k : ℕ) (hk : A.cutoff ≤ k) :
    (A.action k hk).Equivariance ((derivedInverseImage i).obj F) :=
  if hb : B.cutoff ≤ k then
    restrictDatum (B.action k hb) (A.action k hk) (h k hk hb) (α.datum k hb)
  else
    letI := emptyBelowCutoff levels k hk hb
    emptyDatum (A.action k hk) ((derivedInverseImage i).obj F)

private theorem restrictLevel_hom (k : ℕ) (hk : A.cutoff ≤ k) (hb : B.cutoff ≤ k) :
    (restrictLevel h levels α k hk).iso.hom = restrictedArrow h α k hk hb := by
  rw [restrictLevel, dite_eq_left hb]
  exact squareIso_hom (h k hk hb) (projectionSquare (J.group k) i) (α.datum k hb).iso

private theorem restrictLevel_restrictsTo (k : ℕ) (hk : A.cutoff ≤ k) (hb : B.cutoff ≤ k) :
    RestrictsTo i (parameterInclusion (J.group k) i) (h k hk hb)
      (projectionSquare (J.group k) i) (𝟙 ((derivedInverseImage i).obj F))
      (α.datum k hb).iso.hom (restrictLevel h levels α k hk).iso.hom := by
  rw [restrictLevel, dite_eq_left hb]
  exact squareIso_restrictsTo (h k hk hb) (projectionSquare (J.group k) i) (α.datum k hb).iso

private def restrictJetEquivariance : A.Equivariance ((derivedInverseImage i).obj F) where
  datum := restrictLevel h levels α
  compatibility := by
    intro k l hk hkl
    by_cases hb : B.cutoff ≤ k
    · let j (s : ℕ) := parameterInclusion (J.group s) i
      let tx := J.parameterMap hkl (𝟙 X)
      let tu := J.parameterMap hkl (𝟙 U)
      have hj : j l ≫ tx = tu ≫ j k := TopCat.ext (fun _ => rfl)
      have hpx : tx ≫ projection (J.group k) X = projection (J.group l) X :=
        TopCat.ext (fun _ => rfl)
      have hpu : tu ≫ projection (J.group k) U = projection (J.group l) U :=
        TopCat.ext (fun _ => rfl)
      have hr := RestrictsTo.pullback tx tu hj
        (B.factors hb hkl) hpx (A.factors hk hkl) hpu
        (h l (hk.trans hkl) (hb.trans hkl)) (projectionSquare (J.group l) i)
        (restrictLevel_restrictsTo h levels α k hk hb)
      rw [α.compatibility hb hkl] at hr
      exact restriction_unique hr
        (restrictLevel_restrictsTo h levels α l (hk.trans hkl) (hb.trans hkl))
    · letI := emptyBelowCutoff levels k hk hb
      exact (derivedIsZeroOfIsEmpty _).eq_of_src _ _

end Jets


private theorem flatten_squareIso {U X V W : TopCat.{0}} {i : U ⟶ X} {j : V ⟶ W}
    {e p : W ⟶ X} {v q : V ⟶ U} (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    {F : Derived X} (α : (derivedInverseImage e).obj F ≅ (derivedInverseImage p).obj F) :
    ClosedSupportPullbackPastingSpecs.flatten i (squareIso he hp α).hom =
      pullbackMorphism j he hp α.hom := by
  rw [squareIso_hom]
  simp only [ClosedSupportPullbackPastingSpecs.flatten,
    Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app, Category.comp_id]

private theorem squareIso_transition {H : AnalyticGroup.{0}} {U V X : TopCat.{0}}
    {C : AnalyticAction H U} {B : AnalyticAction H V} {A : AnalyticAction H X}
    {t : U ⟶ V} {j : V ⟶ X} {i : U ⟶ X}
    (ht : t ≫ j = i)
    (he : parameterInclusion H t ≫ B.act = C.act ≫ t)
    (he' : parameterInclusion H j ≫ A.act = B.act ≫ j)
    (he'' : parameterInclusion H i ≫ A.act = C.act ≫ i)
    {F : Derived X} (α : A.Equivariance F) :
    let c := compositionAt t j ht F
    (derivedInverseImage C.act).map c.hom ≫
        (squareIso he (projectionSquare H t) (squareIso he' (projectionSquare H j) α.iso)).hom =
      (squareIso he'' (projectionSquare H i) α.iso).hom ≫
        (derivedInverseImage (projection H U)).map c.hom := by
  intro c
  let p := derivedInverseImage (projection H U)
  apply (cancel_mono (p.map c.inv)).mp
  rw [Category.assoc (f := (squareIso he'' _ α.iso).hom), ← p.map_comp, c.hom_inv_id, p.map_id,
    Category.comp_id]
  apply ClosedSupportPullbackPasting.flattenInjective i C.act (projection H U) F
  have hj : parameterInclusion H t ≫ parameterInclusion H j = parameterInclusion H i :=
    TopCat.ext (fun z => Prod.ext rfl (congrArg (fun f : U ⟶ X => f z.2) ht))
  have heFlat : parameterInclusion H t ≫ (B.act ≫ j) = C.act ≫ i := by
    rw [← Category.assoc, he, Category.assoc, ht]
  have hpFlat : parameterInclusion H t ≫ (projection H V ≫ j) = projection H U ≫ i := by
    rw [← Category.assoc, projectionSquare H t, Category.assoc, ht]
  rw [flatten_squareIso, squareIso_hom he (projectionSquare H t)]
  have hpaste := ClosedSupportPullbackPasting.flattenRestriction
    he (projectionSquare H t) ht heFlat hpFlat (squareIso he' (projectionSquare H j) α.iso).hom
  simp only [Category.assoc]
  refine hpaste.trans ?_
  rw [flatten_squareIso]
  have hA : (parameterInclusion H t ≫ parameterInclusion H j) ≫ A.act = C.act ≫ i :=
    (congrArg (· ≫ A.act) hj).trans he''
  have hP : (parameterInclusion H t ≫ parameterInclusion H j) ≫ projection H X =
      projection H U ≫ i :=
    (congrArg (· ≫ projection H X) hj).trans (projectionSquare H i)
  rw [pullbackMorphism_paste _ _ he' (projectionSquare H j) heFlat hpFlat hA hP]
  exact pullbackMorphism_congr hj _ _ _ _ _

private theorem squareIso_naturality {U X V W : TopCat.{0}} {i : U ⟶ X} {j : V ⟶ W}
    {e p : W ⟶ X} {v q : V ⟶ U} (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    {F G : Derived X} (f : F ⟶ G)
    (α : (derivedInverseImage e).obj F ≅ (derivedInverseImage p).obj F)
    (β : (derivedInverseImage e).obj G ≅ (derivedInverseImage p).obj G)
    (hf : (derivedInverseImage e).map f ≫ β.hom = α.hom ≫ (derivedInverseImage p).map f) :
    (derivedInverseImage v).map ((derivedInverseImage i).map f) ≫ (squareIso he hp β).hom =
      (squareIso he hp α).hom ≫ (derivedInverseImage q).map ((derivedInverseImage i).map f) := by
  have ha := (squareValue he).inv.naturality f
  have hp' := (squareValue hp).hom.naturality f
  change (derivedInverseImage v).map ((derivedInverseImage i).map f) ≫
      (squareValue he).inv.app G =
    (squareValue he).inv.app F ≫ (derivedInverseImage j).map ((derivedInverseImage e).map f) at ha
  change (derivedInverseImage j).map ((derivedInverseImage p).map f) ≫
      (squareValue hp).hom.app G =
    (squareValue hp).hom.app F ≫ (derivedInverseImage q).map ((derivedInverseImage i).map f) at hp'
  simp only [squareIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% ha, ← Functor.map_comp_assoc, hf, Functor.map_comp_assoc, hp']

section Intersections

variable {X Y : TopCat.{0}} {J : JetSystem.{0}} {A : ClosedStages X}
variable {B : StageJetActions J A} {i : Y ⟶ X} {S : JetAction J Y}
variable (D : SupportIntersections B i S)
variable (levels : ∀ (n k : ℕ), (D.action n).cutoff ≤ k → S.cutoff ≤ k ∨ IsEmpty (D.space n))

private theorem intersectionComparison_underlying (F : BoundedBelow Y) {n m : ℕ} (h : n ≤ m) :
    (DerivedCategory.Plus.ι (C := Sheaves (D.space n))).mapIso
      (D.intersectionRestrictionComparison F h) =
    compositionAt (D.transition h) (D.intoSupport m) (D.transition_support h) F.obj :=
  ClosedSupportPullbackPasting.pullbackComparisonAtUnderlying
    (D.transition h) (D.intoSupport m) (D.transition_support h) F

private def localEquivariance (F : BoundedBelow Y) (α : S.Equivariance F.obj) :
    D.LocalEquivariance F α where
  datum n := restrictJetEquivariance (D.supportActionSquare n) (levels n) α
  onSupport := by
    intro n k hn hs
    have h := restrictLevel_hom (D.supportActionSquare n) (levels n) α k hn hs
    let a := derivedInverseImage ((D.action n).action k hn).act
    let p := derivedInverseImage (projection (J.group k) (D.space n))
    change a.map (𝟙 _) ≫ restrictedArrow (D.supportActionSquare n) α k hn hs =
      (restrictLevel (D.supportActionSquare n) (levels n) α k hn).iso.hom ≫ p.map (𝟙 _)
    rw [a.map_id, p.map_id,
      Category.id_comp (restrictedArrow (D.supportActionSquare n) α k hn hs),
      Category.comp_id (restrictLevel (D.supportActionSquare n) (levels n) α k hn).iso.hom]
    exact h.symm
  onTransitions := by
    intro n m h k hn hm
    by_cases hs : S.cutoff ≤ k
    · let H := J.group k
      let an := (D.action n).action k hn
      let v := D.transition h
      let j := D.intoSupport m
      let u := D.intoSupport n
      let c := compositionAt v j (D.transition_support h) F.obj
      let e := D.transitionActionSquare h k hn hm
      let em := D.supportActionSquare m k hm hs
      let en := D.supportActionSquare n k hn hs
      have hc : (D.intersectionRestrictionComparison F h).hom.hom = c.hom :=
        congrArg Iso.hom (intersectionComparison_underlying D F h)
      change (derivedInverseImage an.act).map (D.intersectionRestrictionComparison F h).hom.hom ≫
          restrictedArrow (D.transitionActionSquare h)
            (restrictJetEquivariance (D.supportActionSquare m) (levels m) α) k hn hm =
        (restrictLevel (D.supportActionSquare n) (levels n) α k hn).iso.hom ≫
          (derivedInverseImage (projection H (D.space n))).map
            (D.intersectionRestrictionComparison F h).hom.hom
      rw [hc, restrictLevel_hom (D.supportActionSquare n) (levels n) α k hn hs]
      unfold restrictedArrow
      change (derivedInverseImage an.act).map c.hom ≫
          ((derivedInverseImageComposition an.act v).inv.app
              ((derivedInverseImage j).obj F.obj) ≫
            pullbackMorphism (parameterInclusion H v) e (projectionSquare H v)
              (restrictLevel (D.supportActionSquare m) (levels m) α k hm).iso.hom ≫
            (derivedInverseImageComposition (projection H (D.space n)) v).hom.app
              ((derivedInverseImage j).obj F.obj)) =
        _ ≫ (derivedInverseImage (projection H (D.space n))).map c.hom
      rw [restrictLevel, dite_eq_left hs]
      have he := squareIso_hom e (projectionSquare H v)
        (squareIso em (projectionSquare H j) (α.datum k hs).iso)
      have hu := squareIso_hom en (projectionSquare H u) (α.datum k hs).iso
      exact (congrArg ((derivedInverseImage an.act).map c.hom ≫ ·) he.symm).trans
        ((squareIso_transition (D.transition_support h) e em en (α.datum k hs)).trans
          (congrArg (· ≫ (derivedInverseImage (projection H (D.space n))).map c.hom) hu))
    · letI := emptyBelowCutoff (levels n) k hn hs
      exact (derivedIsZeroOfIsEmpty _).eq_of_src _ _

end Intersections

/-- The canonical local equivariance on every support intersection is natural
in equivariant maps of bounded-below coefficient complexes. -/
theorem supportIntersectionEquivariance :
    SupportIntersectionEquivarianceSpecs.Expected.SupportIntersectionEquivariance := by
  intro X Y J A B i S D levels
  refine ⟨localEquivariance D levels, ?_, ?_, ?_⟩
  · intro F α n k hn hs
    exact restrictLevel_hom (D.supportActionSquare n) (levels n) α k hn hs
  · intro F n k hn hs
    letI := emptyBelowCutoff (levels n) k hn (Nat.not_le_of_lt hs)
    exact ⟨derivedIsZeroOfIsEmpty _, derivedIsZeroOfIsEmpty _⟩
  · intro F G α γ f hf n k hk
    by_cases hs : S.cutoff ≤ k
    · let e := D.supportActionSquare n k hk hs
      let p := projectionSquare (J.group k) (D.intoSupport n)
      change (derivedInverseImage ((D.action n).action k hk).act).map
            ((boundedBelowInverseImage (D.intoSupport n)).map f).hom ≫
          (restrictLevel (D.supportActionSquare n) (levels n) γ k hk).iso.hom =
        (restrictLevel (D.supportActionSquare n) (levels n) α k hk).iso.hom ≫
          (derivedInverseImage (projection (J.group k) (D.space n))).map
            ((boundedBelowInverseImage (D.intoSupport n)).map f).hom
      rw [restrictLevel, dite_eq_left hs, restrictLevel, dite_eq_left hs]
      exact squareIso_naturality e p f.hom (α.datum k hs).iso (γ.datum k hs).iso (hf k hs)
    · letI := emptyBelowCutoff (levels n) k hk hs
      exact (derivedIsZeroOfIsEmpty _).eq_of_src _ _

end RepTheorySurvey.Geometric.SupportIntersectionEquivariance
