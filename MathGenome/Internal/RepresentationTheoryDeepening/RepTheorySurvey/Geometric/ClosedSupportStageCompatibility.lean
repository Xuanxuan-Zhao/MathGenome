import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ClosedSupportStageCompatibility
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedSupportBaseChange
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedSupportPullbackPasting
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.FullSupportCounitComparison
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.FullSupportMateTransport
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Topology

namespace RepTheorySurvey.Geometric.ClosedSupportStageCompatibility

open Analytic Analytic.IntersectionComplex LocalSheaf
open Analytic.DerivedPullbackPasting.Expected (identityValue squareValue)
open AnalyticAction (projection)
open ClosedEquivarianceExtensionSpecs (DerivedAdjunctions parameterInclusion projectionSquare)
open ClosedSupportBaseChangeSpecs (MateCommutes SquareRestriction)
open EquivariantIntersectionComplexesSpecs (Intertwines)
open FullSupportCounitComparisonSpecs (fullSupportComparison)
open ClosedSupportStageCompatibilitySpecs.Expected

open private derivedClosedImage_supported derivedClosedImageCounit_isIso pullback_supported
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes
open private parameter_range squareRestrictionOfCommutes mateCommutesAtJet
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedSupportBaseChange

private theorem fullSupportComparison_isIso {X Y V : TopCat.{0}}
    {i : Y ⟶ X} {j : Y ⟶ V} {t : V ⟶ X}
    (hi : IsClosedEmbedding i) (hj : IsClosedEmbedding j)
    (h : j ≫ t = i) (hr : Set.range j = t ⁻¹' Set.range i)
    (a : DerivedAdjunctions.{0}) (F : BoundedBelow Y) :
    IsIso (fullSupportComparison h a F) := by
  let d : (boundedBelowInverseImage (𝟙 Y)).obj F ⟶ F :=
    ObjectProperty.homMk ((identityValue Y).hom.app F.obj)
  have : IsIso ((DerivedCategory.Plus.ι (C := Sheaves Y)).map d) :=
    inferInstanceAs (IsIso ((identityValue Y).hom.app F.obj))
  have : IsIso d := isIso_of_reflects_iso d (DerivedCategory.Plus.ι (C := Sheaves Y))
  let hs := h.trans (Category.id_comp i).symm
  have : IsIso (directImageComparison hs (a j) (a i) F) :=
    ClosedSupportBaseChange.closedBaseChange hi hj hs hr a F
  change IsIso (directImageComparison hs (a j) (a i) F ≫ (derivedDirectImage j).map d)
  infer_instance

/-- On a stage containing all of the support, the datum on the closed intersection
agrees with the datum on the original support through the canonical mates. -/
theorem fullSupportCompatibility : FullSupportCompatibility := by
  intro X Y U V i u v t hi hu ht hs hr J C S E hCutoff hStage hSupport
    a F α γ β hLocal hAgrees j h hAction
  let G := (boundedBelowInverseImage t).obj ((derivedDirectImage i).obj F)
  let c := fullSupportComparison h a F
  let d := directImageComparison hs (a u) (a i) F
  have hj : IsClosedEmbedding j :=
    ht.of_comp_iff.mp (show IsClosedEmbedding (j ≫ t) from h.symm ▸ hi)
  have hrj : Set.range j = t ⁻¹' Set.range i := by
    rw [← h]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, ht.isEmbedding.injective hy⟩
  have hFactor : v ≫ j = u := by
    apply TopCat.ext
    intro x
    apply ht.isEmbedding.injective
    have h₁ := congrArg (fun m : Y ⟶ X => m (v x)) h
    have h₂ := congrArg (fun m : U ⟶ X => m x) hs
    exact h₁.trans h₂.symm
  have hc : IsIso c := fullSupportComparison_isIso hi hj h hrj a F
  have hd : IsIso d := ClosedSupportBaseChange.closedBaseChange hi hu hs hr a F
  have hMates := ClosedSupportBaseChange.actionProjectionMatesAreIso hj hAction a F
  have hSupportAtJet (H : AnalyticGroup.{0}) :
      DerivedSupportedOn (Set.range (parameterInclusion H u))
        ((boundedBelowInverseImage (projection H V)).obj G) := by
    rw [parameter_range, hr]
    exact pullback_supported (projection H V) _ G
      (pullback_supported t _ _ (derivedClosedImage_supported hi F))
  obtain ⟨hPull, hSquare⟩ := FullSupportCounitComparison.intersectionCounit h hFactor hs a F
  have hCoeff := hSquare.symm.trans hPull.symm
  refine ⟨(DerivedCategory.Plus.ι (C := Sheaves V)).map_isIso c, hMates, ?_⟩
  apply mateCommutesAtJet hAction a c α β
  intro k hkS hkE
  let H := J.group k
  have hkC := hCutoff.trans hkE
  have hLocalCommutes := (EquivariantIntersectionComplexes.commutes_iff
    hSupport γ α (𝟙 _) k hkC hkS).mpr (hLocal k hkC hkS)
  have hLocalSquare := squareRestrictionOfCommutes (hSupport k hkC hkS)
    (γ.datum k hkC) (α.datum k hkS) (Iso.refl _) hLocalCommutes
  have hStageMate : MateCommutes (hStage k hkC hkE) (projectionSquare H u)
      (a (parameterInclusion H u)) (a u) d (β.datum k hkE).iso.hom (γ.datum k hkC).iso.hom := by
    simp only [MateCommutes, ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
    exact hAgrees k hkC hkE
  exact FullSupportMateTransport.fullSupportMateTransport hFactor hu
    (C.action k hkC) (S.action k hkS) (E.action k hkE)
    (hSupport k hkC hkS) (hAction k hkS hkE) (hStage k hkC hkE)
    a c d hc hd (hMates k hkS hkE).2 (hSupportAtJet H)
    (β.datum k hkE).iso.hom (α.datum k hkS).iso.hom (γ.datum k hkC).iso.hom
    hCoeff hLocalSquare hStageMate

section StageTransition

open ClosedSupportPullbackPastingSpecs (flatten pullbackComparisonAt)
open EquivariantIntersectionComplexesSpecs (restrictedArrow)
open private verticalCommutes from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.DerivedPullbackPasting
open private parameterInclusion_closed from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedEquivarianceExtension
open private directImageComparisonCounit from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.FullSupportCounitComparison
open private square_restriction_injective from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.FullSupportMateTransport

private theorem squareRestriction_iff {U X V W : TopCat.{0}}
    {i : U ⟶ X} {j : V ⟶ W} {e p : W ⟶ X} {v q : V ⟶ U}
    {he : j ≫ e = v ≫ i} {hp : j ≫ p = q ≫ i}
    {G : Derived X} {F : Derived U} {ε : (derivedInverseImage i).obj G ⟶ F}
    {α : (derivedInverseImage e).obj G ⟶ (derivedInverseImage p).obj G}
    {β : (derivedInverseImage v).obj F ⟶ (derivedInverseImage q).obj F} :
    SquareRestriction he hp ε α β ↔
      ClosedSupportPullbackPastingSpecs.SquareRestriction he hp ε α β :=
  Iff.rfl

private theorem flattenSquareRestriction {U V Y X P Q : TopCat.{0}}
    {i : Y ⟶ X} {j : U ⟶ V} {v : U ⟶ Y} {t : V ⟶ X}
    {k : P ⟶ Q} {e p : Q ⟶ V} {f q : P ⟶ U}
    (hs : j ≫ t = v ≫ i) (he : k ≫ e = f ≫ j) (hp : k ≫ p = q ≫ j)
    {G : Derived X} {F : Derived Y} (ε : (derivedInverseImage i).obj G ⟶ F)
    {α : (derivedInverseImage f).obj ((derivedInverseImage v).obj F) ⟶
      (derivedInverseImage q).obj ((derivedInverseImage v).obj F)}
    {β : (derivedInverseImage e).obj ((derivedInverseImage t).obj G) ⟶
      (derivedInverseImage p).obj ((derivedInverseImage t).obj G)}
    (h : SquareRestriction he hp
      ((squareValue hs).hom.app G ≫ (derivedInverseImage v).map ε) β α) :
    ClosedSupportPullbackPastingSpecs.SquareRestriction
      (verticalCommutes he hs) (verticalCommutes hp hs) ε (flatten t β) (flatten v α) :=
  (ClosedSupportPullbackPasting.squareRestrictionFlatten hs he hp
    (verticalCommutes he hs) (verticalCommutes hp hs) ε β α).mpr (squareRestriction_iff.mp h)

section StageMate

variable {U V Y X : TopCat.{0}} {i : Y ⟶ X} {j : U ⟶ V} {v : U ⟶ Y} {t : V ⟶ X}
  {H : AnalyticGroup.{0}} {C : AnalyticAction H U} {E : AnalyticAction H V}

variable
    (hs : j ≫ t = v ≫ i) (he : parameterInclusion H j ≫ E.act = C.act ≫ j)
    (a : DerivedAdjunctions.{0}) (F : BoundedBelow Y)
    (α : (derivedInverseImage C.act).obj ((derivedInverseImage v).obj F.obj) ⟶
      (derivedInverseImage (projection H U)).obj ((derivedInverseImage v).obj F.obj))
    (β : (derivedInverseImage E.act).obj
        ((derivedInverseImage t).obj ((derivedDirectImage i).obj F).obj) ⟶
      (derivedInverseImage (projection H V)).obj
        ((derivedInverseImage t).obj ((derivedDirectImage i).obj F).obj))
    (hm : MateCommutes he (projectionSquare H j) (a (parameterInclusion H j)) (a j)
      (directImageComparison hs (a j) (a i) F) β α)

include hm

private theorem transposeStageMate :
    SquareRestriction he (projectionSquare H j)
      ((squareValue hs).hom.app ((derivedDirectImage i).obj F).obj ≫
        (derivedInverseImage v).map ((a i).counit.app F).hom) β α := by
  let d := directImageComparison hs (a j) (a i) F
  have h := (ClosedSupportBaseChange.derivedDirectImageMateEquationIff he
    (projectionSquare H j) a d β α).mp hm
  exact (directImageComparisonCounit hs a F) ▸ h

private theorem flattenedStageMate :
    ClosedSupportPullbackPastingSpecs.SquareRestriction
      (verticalCommutes he hs) (verticalCommutes (projectionSquare H j) hs)
      ((a i).counit.app F).hom (flatten t β) (flatten v α) :=
  flattenSquareRestriction (G := ((derivedDirectImage i).obj F).obj) (F := F.obj)
    (α := α) (β := β) hs he (projectionSquare H j) ((a i).counit.app F).hom
    (transposeStageMate hs he a F α β hm)

end StageMate

private theorem comp_eq_of_square {K : Type*} [Category* K] {A B C D T : K}
    {a : A ⟶ B} {b : B ⟶ C} {c : C ⟶ D} {f : A ⟶ T} {g : T ⟶ C} {h : T ⟶ D}
    (h₁ : a ≫ b = f ≫ g) (h₂ : g ≫ c = h) : a ≫ (b ≫ c) = f ≫ h := by
  rw [← Category.assoc, h₁, Category.assoc, h₂]

private theorem flattenLocalRestriction {U₀ U₁ Y : TopCat.{0}}
    {r : U₀ ⟶ U₁} {v₀ : U₀ ⟶ Y} {v₁ : U₁ ⟶ Y}
    {J : JetSystem.{0}} {C₀ : JetAction J U₀} {C₁ : JetAction J U₁}
    (hr : r ≫ v₁ = v₀) (hLocal : Intertwines C₀ C₁ r) (F : BoundedBelow Y)
    (α₀ : C₀.Equivariance ((boundedBelowInverseImage v₀).obj F).obj)
    (α₁ : C₁.Equivariance ((boundedBelowInverseImage v₁).obj F).obj)
    (k : ℕ) (hk₀ : C₀.cutoff ≤ k) (hk₁ : C₁.cutoff ≤ k)
    (he : parameterInclusion (J.group k) r ≫ ((C₁.action k hk₁).act ≫ v₁) =
      (C₀.action k hk₀).act ≫ v₀)
    (hp : parameterInclusion (J.group k) r ≫ (projection (J.group k) U₁ ≫ v₁) =
      projection (J.group k) U₀ ≫ v₀)
    (h : let c := (pullbackComparisonAt r v₁ hr F).hom.hom
      (derivedInverseImage (C₀.action k hk₀).act).map c ≫ restrictedArrow hLocal α₁ k hk₀ hk₁ =
        (α₀.datum k hk₀).iso.hom ≫ (derivedInverseImage (projection (J.group k) U₀)).map c) :
    flatten v₀ (α₀.datum k hk₀).iso.hom =
      pullbackMorphism (parameterInclusion (J.group k) r) he hp
        (flatten v₁ (α₁.datum k hk₁).iso.hom) := by
  let e := derivedInverseImage (C₀.action k hk₀).act
  let p := derivedInverseImage (projection (J.group k) U₀)
  let c := (DerivedCategory.Plus.ι (C := Sheaves U₀)).mapIso (pullbackComparisonAt r v₁ hr F)
  have hCommutes : e.map c.hom ≫ restrictedArrow hLocal α₁ k hk₀ hk₁ =
      (α₀.datum k hk₀).iso.hom ≫ p.map c.hom := h
  have hConjugated := congrArg (fun f => f ≫ p.map c.inv) hCommutes
  simp only [restrictedArrow, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id] at hConjugated
  rw [p.map_id, Category.comp_id] at hConjugated
  have hc := ClosedSupportPullbackPasting.pullbackComparisonAtUnderlying r v₁ hr F
  change c = _ at hc
  rw [hc] at hConjugated
  exact (congrArg (flatten v₀) hConjugated).symm.trans
    (ClosedSupportPullbackPasting.flattenRestriction (hLocal k hk₀ hk₁)
      (projectionSquare (J.group k) r) hr he hp (α₁.datum k hk₁).iso.hom)

/-- The ambient restriction of the larger stage datum gives the smaller stage
datum at the common jet. -/
theorem stageTransitionCompatibility : StageTransitionCompatibility := by
  intro X Y U₀ U₁ V₀ V₁ i j₀ j₁ v₀ v₁ t₀ t₁ r s hi hj₀ _ h₀ h₁ hr₀ _
    hStage hSupport hAmbient J C₀ C₁ E₀ E₁ hAct₀ hAct₁ hLocal a F α₀ α₁ β₀ β₁
    k hc₀ hc₁ he₀ he₁ hAction H hMate₀ hMate₁ coeff hLocalEq G G₁ e₀ p₀ σ
  let e₁ := (E₁.action k he₁).act
  let p₁ := projection H V₁
  let f₀ := (C₀.action k hc₀).act
  let f₁ := (C₁.action k hc₁).act
  let q₀ := projection H U₀
  let q₁ := projection H U₁
  let T := J.parameterMap (le_refl k) s
  let R := parameterInclusion H r
  let Tproj : T ≫ p₁ = p₀ ≫ s := TopCat.ext fun _ => rfl
  have hT : T = parameterInclusion H s := by
    apply TopCat.ext
    intro p
    change (J.truncate k k (le_refl k) p.1, s p.2) = (p.1, s p.2)
    rw [J.truncate_id]
    rfl
  have hParameter : parameterInclusion H j₀ ≫ T = R ≫ parameterInclusion H j₁ := by
    rw [hT]
    exact TopCat.ext fun p => Prod.ext rfl (congrArg (fun f : U₀ ⟶ V₁ => f p.2) hStage.symm)
  have he : T ≫ (e₁ ≫ t₁) = e₀ ≫ t₀ := comp_eq_of_square hAction hAmbient
  have hp : T ≫ (p₁ ≫ t₁) = p₀ ≫ t₀ := comp_eq_of_square Tproj hAmbient
  have hf : R ≫ (f₁ ≫ v₁) = f₀ ≫ v₀ := comp_eq_of_square (hLocal k hc₀ hc₁) hSupport
  have hq : R ≫ (q₁ ≫ v₁) = q₀ ≫ v₀ := comp_eq_of_square (projectionSquare H r) hSupport
  have hFlatLocal := flattenLocalRestriction hSupport hLocal F α₀ α₁ k hc₀ hc₁ hf hq hLocalEq
  let b := (derivedInverseImage e₀).map σ.hom ≫
    (derivedInverseImageComposition e₀ s).inv.app G₁ ≫
    pullbackMorphism T hAction Tproj (β₁.datum k he₁).iso.hom ≫
    (derivedInverseImageComposition p₀ s).hom.app G₁ ≫
    (derivedInverseImage p₀).map σ.inv
  have hFlatAmbient : flatten t₀ b =
      pullbackMorphism T he hp (flatten t₁ (β₁.datum k he₁).iso.hom) :=
    ClosedSupportPullbackPasting.flattenRestriction hAction Tproj hAmbient he hp (β₁.datum k he₁).iso.hom
  let ha₀ := hAct₀ k hc₀ he₀
  let ha₁ := hAct₁ k hc₁ he₁
  let hp₀ := projectionSquare H j₀
  let hp₁ := projectionSquare H j₁
  have hSmall := flattenedStageMate h₀ ha₀ a F
    (α₀.datum k hc₀).iso.hom (β₀.datum k he₀).iso.hom hMate₀
  have hLarge := flattenedStageMate h₁ ha₁ a F
    (α₁.datum k hc₁).iso.hom (β₁.datum k he₁).iso.hom hMate₁
  have hRestr := ClosedSupportPullbackPasting.squareRestrictionParameterChange T R hParameter
    (verticalCommutes ha₁ h₁) (verticalCommutes hp₁ h₁) he hp hf hq
    (verticalCommutes ha₀ h₀) (verticalCommutes hp₀ h₀) hLarge
  rw [← hFlatAmbient, ← hFlatLocal] at hRestr
  have hTarget : DerivedSupportedOn (Set.range (parameterInclusion H j₀))
      ((boundedBelowInverseImage (p₀ ≫ t₀)).obj ((derivedDirectImage i).obj F)) := by
    rw [parameter_range, hr₀]
    exact pullback_supported (p₀ ≫ t₀) _ _ (derivedClosedImage_supported hi F)
  have hCounit : IsIso ((a i).counit.app F).hom := by
    have := derivedClosedImageCounit_isIso hi (a i) F
    exact (DerivedCategory.Plus.ι (C := Sheaves Y)).map_isIso _
  have hEq := square_restriction_injective a (parameterInclusion_closed H hj₀)
    hCounit hTarget (squareRestriction_iff.mpr hRestr) (squareRestriction_iff.mpr hSmall)
  exact ClosedSupportPullbackPasting.flattenInjective t₀ e₀ p₀ G hEq

end StageTransition

end RepTheorySurvey.Geometric.ClosedSupportStageCompatibility
