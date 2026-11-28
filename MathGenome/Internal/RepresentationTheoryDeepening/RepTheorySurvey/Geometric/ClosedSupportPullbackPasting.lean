import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ClosedSupportPullbackPasting
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedPullbackPasting
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedEquivarianceExtension
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option Elab.async false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u

namespace RepTheorySurvey.Geometric.ClosedSupportPullbackPasting

open Analytic Analytic.IntersectionComplex
open Analytic.DerivedPullbackPasting.Expected (squareValue)
open ClosedSupportPullbackPastingSpecs

set_option allowUnsafeReducibility true in
attribute [local reducible] Analytic.DerivedPullbackPasting.Expected.SquareType

open private adjointSquareMap_counit compositionAt compositionAt_paste compositionAt_inv
  compComparison pullbackMorphism_eq restrictionComparison RestrictsTo RestrictsTo.pullback
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedEquivarianceExtension
open private comparison_transport_left_assoc square_hom
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedPullbackPasting
open private verticalCommutes from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.DerivedPullbackPasting
open private directImageComparisonNaturality
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

abbrev pullbackComparisonAt := @ClosedSupportPullbackPastingSpecs.pullbackComparisonAt
abbrev flatten := @ClosedSupportPullbackPastingSpecs.flatten
abbrev SquareRestriction := @ClosedSupportPullbackPastingSpecs.SquareRestriction

theorem pullbackComparisonAtUnderlying : Expected.PullbackComparisonAtUnderlying.{u} := by
  intro W X Y s t f h F
  subst f
  rw [ClosedSupportPullbackPastingSpecs.pullbackComparisonAt]
  simp only [eqToIso_refl, Iso.refl_trans]
  rfl

private theorem adjointSquareMapPasting
    {X₀ X₁ X₂ U₀ U₁ U₂ : Type*}
    [Category* X₀] [Category* X₁] [Category* X₂]
    [Category* U₀] [Category* U₁] [Category* U₂]
    {J₀ : X₀ ⥤ U₀} {J₁ : X₁ ⥤ U₁} {J₂ : X₂ ⥤ U₂}
    {R₀ : U₀ ⥤ X₀} {R₁ : U₁ ⥤ X₁} {R₂ : U₂ ⥤ X₂}
    {E : X₀ ⥤ X₂} {E₁ : X₀ ⥤ X₁} {E₂ : X₁ ⥤ X₂}
    {V : U₀ ⥤ U₂} {V₁ : U₀ ⥤ U₁} {V₂ : U₁ ⥤ U₂}
    (a₀ : J₀ ⊣ R₀) (a₁ : J₁ ⊣ R₁) (a₂ : J₂ ⊣ R₂)
    (s₁ : E₁ ⋙ J₁ ≅ J₀ ⋙ V₁) (s₂ : E₂ ⋙ J₂ ≅ J₁ ⋙ V₂)
    (s : E ⋙ J₂ ≅ J₀ ⋙ V) (σ : E ≅ E₁ ⋙ E₂) (τ : V ≅ V₁ ⋙ V₂) (F : U₀)
    (hs : s.hom.app (R₀.obj F) =
      J₂.map (σ.hom.app (R₀.obj F)) ≫ s₂.hom.app (E₁.obj (R₀.obj F)) ≫
      V₂.map (s₁.hom.app (R₀.obj F)) ≫ τ.inv.app (J₀.obj (R₀.obj F))) :
    adjointSquareMap s a₂ a₀ F =
      σ.hom.app (R₀.obj F) ≫ E₂.map (adjointSquareMap s₁ a₁ a₀ F) ≫
        adjointSquareMap s₂ a₂ a₁ (V₁.obj F) ≫ R₂.map (τ.inv.app F) := by
  apply (cancel_mono (R₂.map (τ.hom.app F))).mp
  simp only [Functor.comp_obj, Category.assoc, ← R₂.map_comp, Iso.inv_hom_id_app]
  rw [R₂.map_id (V₂.obj (V₁.obj F)), Category.comp_id (adjointSquareMap s₂ a₂ a₁ (V₁.obj F))]
  apply (a₂.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_left_symm]
  simp only [Adjunction.homEquiv_counit, adjointSquareMap_counit, hs, Category.assoc]
  have hc : V.map (a₀.counit.app F) ≫ τ.hom.app F =
      τ.hom.app (J₀.obj (R₀.obj F)) ≫ V₂.map (V₁.map (a₀.counit.app F)) :=
    τ.hom.naturality (a₀.counit.app F)
  have hn : J₂.map (E₂.map (adjointSquareMap s₁ a₁ a₀ F)) ≫
      s₂.hom.app (R₁.obj (V₁.obj F)) =
      s₂.hom.app (E₁.obj (R₀.obj F)) ≫ V₂.map (J₁.map (adjointSquareMap s₁ a₁ a₀ F)) :=
    s₂.hom.naturality (adjointSquareMap s₁ a₁ a₀ F)
  rw [hc, Iso.inv_hom_id_app_assoc, reassoc_of% hn,
    ← V₂.map_comp (J₁.map (adjointSquareMap s₁ a₁ a₀ F)) (a₁.counit.app (V₁.obj F)),
    adjointSquareMap_counit, V₂.map_comp]

private theorem pullbackComparisonAtRefl {W X Y : TopCat.{u}}
    (s : W ⟶ X) (t : X ⟶ Y) (F : BoundedBelow Y) :
    ClosedSupportPullbackPastingSpecs.pullbackComparisonAt s t rfl F =
      (boundedBelowPullbackComposition s t).app F :=
  Iso.refl_trans _

set_option linter.auxLemma false in
private theorem boundedBelowSquareVerticalComponent {U₀ X₀ U₁ X₁ U₂ X₂ : TopCat.{u}}
    {j₀ : U₀ ⟶ X₀} {j₁ : U₁ ⟶ X₁} {j₂ : U₂ ⟶ X₂}
    {e₁ : X₁ ⟶ X₀} {e₂ : X₂ ⟶ X₁} {v₁ : U₁ ⟶ U₀} {v₂ : U₂ ⟶ U₁}
    (h₁ : j₁ ≫ e₁ = v₁ ≫ j₀) (h₂ : j₂ ≫ e₂ = v₂ ≫ j₁)
    (F : BoundedBelow X₀) :
    (pullbackSquare (verticalCommutes h₂ h₁)).hom.app F =
      (boundedBelowInverseImage j₂).map ((boundedBelowPullbackComposition e₂ e₁).hom.app
        F) ≫
      (pullbackSquare h₂).hom.app ((boundedBelowInverseImage e₁).obj F) ≫
      (boundedBelowInverseImage v₂).map ((pullbackSquare h₁).hom.app F) ≫
      (boundedBelowPullbackComposition v₂ v₁).inv.app
        ((boundedBelowInverseImage j₀).obj F) := by
  -- Align the propositional instances retained by the imported statement with
  -- the instances in the bounded-below functors. This avoids unfolding the
  -- derived category construction during the kernel conversion.
  have hs := @DerivedPullbackPasting.boundedBelowSquareVerticalPasting U₂ X₂ U₁ X₁ U₀ X₀
    j₂ j₁ j₀ v₂ e₂ v₁ e₁ h₂ h₁ F
  have hzero (X : TopCat.{u}) :
      @Analytic.DerivedPullbackPasting.Expected.SquareBoundedBelowCompatibility._proof_1 X =
        (@DerivedCategory.instHasZeroObject (Sheaves X) _
          (@TopCat.Sheaf.instAbelian X Coeff _ (Analytic.instHasDerivedCategorySheaves._proof_1 X) _)
          (Analytic.instHasDerivedCategorySheaves X)) := Subsingleton.elim _ _
  have hadd (X : TopCat.{u}) :
      @Analytic.DerivedPullbackPasting.Expected.SquareBoundedBelowCompatibility._proof_2 X =
        (@DerivedCategory.instAdditiveShiftFunctorInt (Sheaves X) _
          (@TopCat.Sheaf.instAbelian X Coeff _ (Analytic.instHasDerivedCategorySheaves._proof_1 X) _)
          (Analytic.instHasDerivedCategorySheaves X)) := Subsingleton.elim _ _
  rw [hzero U₂] at hs
  rw [hzero X₂, hzero U₁, hzero X₁, hzero U₀, hzero X₀] at hs
  rw [hadd U₂, hadd X₂, hadd U₁, hadd X₁, hadd U₀, hadd X₀] at hs
  exact hs

private theorem mateVerticalPastingComposite {U₀ X₀ U₁ X₁ U₂ X₂ : TopCat.{u}}
    {j₀ : U₀ ⟶ X₀} {j₁ : U₁ ⟶ X₁} {j₂ : U₂ ⟶ X₂}
    {e₁ : X₁ ⟶ X₀} {e₂ : X₂ ⟶ X₁} {v₁ : U₁ ⟶ U₀} {v₂ : U₂ ⟶ U₁}
    (h₁ : j₁ ≫ e₁ = v₁ ≫ j₀) (h₂ : j₂ ≫ e₂ = v₂ ≫ j₁)
    (a₀ : boundedBelowInverseImage j₀ ⊣ derivedDirectImage j₀)
    (a₁ : boundedBelowInverseImage j₁ ⊣ derivedDirectImage j₁)
    (a₂ : boundedBelowInverseImage j₂ ⊣ derivedDirectImage j₂) (F : BoundedBelow U₀) :
    directImageComparison (verticalCommutes h₂ h₁) a₂ a₀ F =
      (boundedBelowPullbackComposition e₂ e₁).hom.app ((derivedDirectImage j₀).obj F) ≫
        (boundedBelowInverseImage e₂).map (directImageComparison h₁ a₁ a₀ F) ≫
        directImageComparison h₂ a₂ a₁ ((boundedBelowInverseImage v₁).obj F) ≫
        (derivedDirectImage j₂).map ((boundedBelowPullbackComposition v₂ v₁).inv.app F) := by
  unfold directImageComparison
  exact adjointSquareMapPasting a₀ a₁ a₂ (pullbackSquare h₁) (pullbackSquare h₂)
    (pullbackSquare (verticalCommutes h₂ h₁)) (boundedBelowPullbackComposition e₂ e₁)
    (boundedBelowPullbackComposition v₂ v₁) F
    (boundedBelowSquareVerticalComponent h₁ h₂ ((derivedDirectImage j₀).obj F))

theorem mateVerticalPasting : Expected.MateVerticalPasting.{u} := by
  intro U₀ X₀ U₁ X₁ U₂ X₂ j₀ j₁ j₂ e₁ e₂ v₁ v₂ h₁ h₂ e v he hv h a₀ a₁ a₂ F
  subst e v
  rw [pullbackComparisonAtRefl, pullbackComparisonAtRefl, Iso.app_hom, Iso.app_inv]
  exact mateVerticalPastingComposite h₁ h₂ a₀ a₁ a₂ F

theorem mateNaturality : Expected.MateNaturality.{u} := by
  intro U X V Y j i e v h a b F G q P Q f cF cG hc
  rw [← Functor.map_comp_assoc, hc, Functor.map_comp, Category.assoc,
    directImageComparisonNaturality h a b q, Category.assoc]

theorem flattenInjective : Expected.FlattenInjective.{u} := by
  intro W X Y t e p G r s h
  unfold ClosedSupportPullbackPastingSpecs.flatten at h
  exact (cancel_mono _).mp ((cancel_epi _).mp h)

private theorem conjugatedSquare {K : Type*} [Category K]
    {A₀ B₀ C₀ D₀ A₁ B₁ C₁ D₁ : K}
    (u : A₀ ≅ A₁) (v : B₀ ≅ B₁) (w : C₀ ≅ C₁) (z : D₀ ≅ D₁)
    {a : A₁ ⟶ B₁} {b : C₁ ⟶ D₁}
    {p₀ : A₀ ⟶ C₀} {q₀ : B₀ ⟶ D₀} {p₁ : A₁ ⟶ C₁} {q₁ : B₁ ⟶ D₁}
    (hp : p₀ ≫ w.hom = u.hom ≫ p₁) (hq : q₀ ≫ z.hom = v.hom ≫ q₁) :
    (u.hom ≫ a ≫ v.inv) ≫ q₀ = p₀ ≫ (w.hom ≫ b ≫ z.inv) ↔
      a ≫ q₁ = p₁ ≫ b := by
  rw [← cancel_mono z.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, reassoc_of% hp, hq,
    Iso.inv_hom_id_assoc, cancel_epi]

set_option maxHeartbeats 900000 in
theorem squareRestrictionFlatten : Expected.SquareRestrictionFlatten.{u} := by
  intro U X V Y U' X' j j' i t v e p s q h he hp he' hp' G F ε α β
  let u (f : X' ⟶ X) := (derivedInverseImage j').mapIso ((derivedInverseImageComposition f t).app G)
  let w (f : U' ⟶ U) := (derivedInverseImageComposition f v).app F
  have hs (f : X' ⟶ X) (b : U' ⟶ U) (hc : j' ≫ f = b ≫ j)
      (hc' : j' ≫ (f ≫ t) = (b ≫ v) ≫ i) :
      ((squareValue hc').hom.app G ≫ (derivedInverseImage (b ≫ v)).map ε) ≫ (w b).hom =
        (u f).hom ≫ ((squareValue hc).hom.app ((derivedInverseImage t).obj G) ≫
          (derivedInverseImage b).map ((squareValue h).hom.app G ≫ (derivedInverseImage v).map ε)) := by
    have hc'' := DerivedPullbackPasting.squareVerticalPasting hc h G
    have hn := (derivedInverseImageComposition b v).hom.naturality ε
    change (derivedInverseImage (b ≫ v)).map ε ≫ (w b).hom =
      (derivedInverseImageComposition b v).hom.app _ ≫
        (derivedInverseImage b).map ((derivedInverseImage v).map ε) at hn
    rw [Category.assoc, hn, show (squareValue hc').hom.app G = _ from hc'']
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp, u,
      Functor.mapIso_hom, Iso.app_hom]
  unfold ClosedSupportPullbackPastingSpecs.SquareRestriction
  simp only [ClosedSupportPullbackPastingSpecs.flatten, Functor.map_comp]
  simpa only [Category.assoc, u, w, Functor.mapIso_hom, Functor.mapIso_inv,
    Iso.app_hom, Iso.app_inv, Functor.map_comp] using!
    (conjugatedSquare (u e) (u p) (w s) (w q) (a := (derivedInverseImage j').map α)
      (b := β) (hs e s he he') (hs p q hp hp'))

private theorem comparisonAcrossSquare {W X W' X' Y : TopCat.{u}}
    {r' : W' ⟶ W} {r : X' ⟶ X} {e : W ⟶ X} {e' : W' ⟶ X'}
    {t : X ⟶ Y} {t' : X' ⟶ Y} (h : r' ≫ e = e' ≫ r) (ht : r ≫ t = t')
    (h' : r' ≫ (e ≫ t) = e' ≫ t') (F : Derived Y) :
    (compositionAt r' (e ≫ t) h' F) ≪≫
      (derivedInverseImage r').mapIso ((derivedInverseImageComposition e t).app F) =
    (derivedInverseImageComposition e' t').app F ≪≫
      (derivedInverseImage e').mapIso (compositionAt r t ht F) ≪≫
      ((squareValue h).app ((derivedInverseImage t).obj F)).symm := by
  subst t'
  apply Iso.ext
  have h₀ : (r' ≫ e) ≫ t = e' ≫ (r ≫ t) :=
    (congrArg (· ≫ t) h).trans (Category.assoc _ _ _)
  have h₁ : (e' ≫ r) ≫ t = e' ≫ (r ≫ t) := Category.assoc _ _ _
  have hc := compositionAt_paste r' e t rfl h' h₀ F
  have hc₀ : (compositionAt e t rfl F).hom =
      (derivedInverseImageComposition e t).hom.app F := by
    simp only [compositionAt, eqToIso_refl, Iso.refl_trans, Iso.app_hom]
  rw [hc₀] at hc
  change (compositionAt r' (e ≫ t) h' F).hom ≫
    (derivedInverseImage r').map ((derivedInverseImageComposition e t).hom.app F) =
    (compositionAt (r' ≫ e) t h₀ F).hom ≫
      (derivedInverseImageComposition r' e).hom.app ((derivedInverseImage t).obj F) at hc
  simp only [Iso.trans_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Iso.symm_hom]
  rw [hc]
  dsimp only [compositionAt, Iso.trans_hom, eqToIso.hom, Iso.app_hom]
  have hright := DerivedPullbackPasting.compositionAssociativity e' r t F
  have hcancel : (derivedInverseImageComposition e' (r ≫ t)).hom.app F ≫
      (derivedInverseImage e').map ((derivedInverseImageComposition r t).hom.app F) =
    eqToHom (congrArg (fun f => (derivedInverseImage f).obj F) h₁.symm) ≫
      (derivedInverseImageComposition (e' ≫ r) t).hom.app F ≫
      (derivedInverseImageComposition e' r).hom.app ((derivedInverseImage t).obj F) := by
    rw [hright]
    simp only [eqToHom_refl, Category.id_comp]
  simp only [eqToHom_refl, Category.id_comp]
  have hinv : (squareValue h).inv.app ((derivedInverseImage t).obj F) =
      (derivedInverseImageComposition e' r).inv.app ((derivedInverseImage t).obj F) ≫
        eqToHom (congrArg (fun f => (derivedInverseImage f).obj ((derivedInverseImage t).obj F)) h.symm) ≫
        (derivedInverseImageComposition r' e).hom.app ((derivedInverseImage t).obj F) := by
    simp only [squareValue, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
      eqToIso.inv, eqToHom_app, Category.assoc]
  rw [hinv, ← Category.assoc (f := (derivedInverseImageComposition e' (r ≫ t)).hom.app F), hcancel]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [comparison_transport_left_assoc t h.symm F, eqToHom_trans_assoc]

theorem flattenPullback : Expected.FlattenPullback.{u} := by
  intro W X W' X' Y r' r e p e' p' t t' he hp ht he' hp' F α c a
  rw [pullbackMorphism_eq]
  let er := congrArg Iso.hom (comparisonAcrossSquare he ht he' F)
  let pr := congrArg Iso.inv (comparisonAcrossSquare hp ht hp' F)
  have heq : (compositionAt r' (e ≫ t) he' F).hom ≫
      (derivedInverseImage r').map ((derivedInverseImageComposition e t).hom.app F) =
    (derivedInverseImageComposition e' t').hom.app F ≫ (derivedInverseImage e').map c.hom ≫
      (squareValue he).inv.app ((derivedInverseImage t).obj F) := by
    exact er
  have hpq : (derivedInverseImage r').map ((derivedInverseImageComposition p t).inv.app F) ≫
      (compositionAt r' (p ≫ t) hp' F).inv =
    (squareValue hp).hom.app ((derivedInverseImage t).obj F) ≫
      (derivedInverseImage p').map c.inv ≫ (derivedInverseImageComposition p' t').inv.app F := by
    simpa only [Iso.trans_inv, Category.assoc] using! pr
  simp only [ClosedSupportPullbackPastingSpecs.flatten, a, Functor.map_comp, Category.assoc]
  rw [← Category.assoc (f := (compositionAt r' (e ≫ t) he' F).hom), heq, hpq]
  simp only [Category.assoc]

private theorem squareComponentHom {U X V W : TopCat.{u}}
    {i : U ⟶ X} {j : V ⟶ W} {e : W ⟶ X} {v : V ⟶ U}
    (h : j ≫ e = v ≫ i) (G : Derived X) :
    (squareValue h).hom.app G =
      (compositionAt j e h G).inv ≫ (derivedInverseImageComposition v i).hom.app G := by
  rw [square_hom, compositionAt_inv]
  exact (Category.assoc _ _ _).symm

private theorem squareComponentInv {U X V W : TopCat.{u}}
    {i : U ⟶ X} {j : V ⟶ W} {e : W ⟶ X} {v : V ⟶ U}
    (h : j ≫ e = v ≫ i) (G : Derived X) :
    (squareValue h).inv.app G =
      (derivedInverseImageComposition v i).inv.app G ≫ (compositionAt j e h G).hom := by
  apply (cancel_mono ((squareValue h).hom.app G)).mp
  rw [Iso.inv_hom_id_app, squareComponentHom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_app]

private theorem pullbackMorphismThroughSquare {W X W' X' : TopCat.{u}}
    {r' : W' ⟶ W} {r : X' ⟶ X} {e p : W ⟶ X} {e' p' : W' ⟶ X'}
    (he : r' ≫ e = e' ≫ r) (hp : r' ≫ p = p' ≫ r)
    {K : Derived X} (α : (derivedInverseImage e).obj K ⟶ (derivedInverseImage p).obj K) :
    (derivedInverseImageComposition e' r).inv.app K ≫ pullbackMorphism r' he hp α ≫
        (derivedInverseImageComposition p' r).hom.app K =
    (squareValue he).inv.app K ≫ (derivedInverseImage r').map α ≫ (squareValue hp).hom.app K := by
  rw [pullbackMorphism_eq, squareComponentHom hp, squareComponentInv he]
  simp only [Category.assoc]

theorem flattenRestriction : Expected.FlattenRestriction.{u} := by
  intro W X W' X' Y r' r e p e' p' t t' he hp ht he' hp' F α c
  refine Eq.trans ?_ (flattenPullback he hp ht he' hp' α)
  have h := pullbackMorphismThroughSquare he hp α
  simpa only [Category.assoc] using
    congrArg (fun f => flatten t' ((derivedInverseImage e').map c.hom ≫ f ≫
      (derivedInverseImage p').map c.inv)) h

private theorem squareRestrictionIffRestrictsTo {U X V W : TopCat.{u}}
    {i : U ⟶ X} {j : V ⟶ W} {e p : W ⟶ X} {v q : V ⟶ U}
    (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    {G : Derived X} {F : Derived U} (ε : (derivedInverseImage i).obj G ⟶ F)
    (α : (derivedInverseImage e).obj G ⟶ (derivedInverseImage p).obj G)
    (β : (derivedInverseImage v).obj F ⟶ (derivedInverseImage q).obj F) :
    ClosedSupportPullbackPastingSpecs.SquareRestriction he hp ε α β ↔
      RestrictsTo i j he hp ε α β := by
  have hs (f : W ⟶ X) (w : V ⟶ U) (hh : j ≫ f = w ≫ i) :
      (squareValue hh).hom.app G ≫ (derivedInverseImage w).map ε =
        (compositionAt j f hh G).inv ≫ restrictionComparison i w ε := by
    rw [squareComponentHom, restrictionComparison, compComparison, Category.assoc]
  unfold ClosedSupportPullbackPastingSpecs.SquareRestriction RestrictsTo
  rw [← Category.assoc ((squareValue he).hom.app G), hs e v he,
    hs p q hp, pullbackMorphism_eq]
  simp only [Category.assoc]
  exact ((compositionAt j e he G).symm.inv_comp_eq).symm

theorem squareRestrictionPullbackForm : Expected.SquareRestrictionPullbackForm.{u} := by
  intro U X V W i j e p v q he hp G F ε α β
  simpa only [RestrictsTo, restrictionComparison, compComparison, Category.assoc] using
    squareRestrictionIffRestrictsTo he hp ε α β

theorem squareRestrictionParameterChange : Expected.SquareRestrictionParameterChange.{u} := by
  intro U X V W V' W' i j j' k l hl e p v q e' p' v' q' he hp hke hkp hlv hlq he' hp'
    G F ε α β h
  apply (squareRestrictionIffRestrictsTo he' hp' ε _ _).mpr
  exact RestrictsTo.pullback k l hl hke hkp hlv hlq he' hp'
    ((squareRestrictionIffRestrictsTo he hp ε α β).mp h)

private theorem pasteCoefficientMap {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (J : C ⥤ E) (V : D ⥤ E) {A₀ A₁ A₂ : C} {B₀ B₁ B₂ B₃ : D} {T : E}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : B₀ ≅ B₁) (f : B₁ ⟶ B₂) (g : B₂ ⟶ B₃)
    (d : J.obj A₁ ⟶ V.obj B₁) (e : J.obj A₂ ⟶ V.obj B₂)
    (s : T ⟶ J.obj A₀) (h : T ⟶ V.obj B₀)
    (hn : J.map b ≫ e = d ≫ V.map f)
    (hs : h = s ≫ J.map a ≫ d ≫ V.map c.inv) :
    h ≫ V.map (c.hom ≫ f ≫ g) = s ≫ J.map (a ≫ b) ≫ e ≫ V.map g := by
  rw [hs]
  simp only [Category.assoc, Functor.map_comp]
  rw [← V.map_comp_assoc c.inv c.hom, Iso.inv_hom_id, V.map_id, Category.id_comp,
    reassoc_of% hn]

set_option maxHeartbeats 1000000 in
theorem squareRestrictionHorizontalPasting : Expected.SquareRestrictionHorizontalPasting.{u} := by
  intro U X Z V Y W j j' i i' v q e p e' p' h k h' k' G F K ε η α β γ hr hs
  let u (z : Z ⟶ W) := (derivedInverseImageComposition j j').hom.app ((derivedInverseImage z).obj G)
  let c (z : X ⟶ Y) (z' : Z ⟶ W) (hz : j' ≫ z' = z ≫ i') :=
    (squareValue hz).hom.app G ≫ (derivedInverseImage z).map ε
  let d (z : U ⟶ V) (z' : X ⟶ Y) (hz : j ≫ z' = z ≫ i) :=
    (squareValue hz).hom.app F ≫ (derivedInverseImage z).map η
  have hbridge {z : U ⟶ V} {z' : X ⟶ Y} {z'' : Z ⟶ W}
      (hz : j ≫ z' = z ≫ i) (hz' : j' ≫ z'' = z' ≫ i') :
      (squareValue (horizontalSquare hz hz')).hom.app G ≫
        (derivedInverseImage z).map
          ((derivedInverseImageComposition i i').hom.app G ≫ (derivedInverseImage i).map ε ≫ η) =
      u z'' ≫ (derivedInverseImage j).map (c z' z'' hz') ≫ d z z' hz := by
    have hn : (derivedInverseImage j).map ((derivedInverseImage z').map ε) ≫
        (squareValue hz).hom.app F = (squareValue hz).hom.app ((derivedInverseImage i').obj G) ≫
          (derivedInverseImage z).map ((derivedInverseImage i).map ε) :=
      (squareValue hz).hom.naturality ε
    have hh := DerivedPullbackPasting.squareHorizontalPasting hz hz' G
    exact pasteCoefficientMap (derivedInverseImage j) (derivedInverseImage z)
      ((squareValue hz').hom.app G) ((derivedInverseImage z').map ε)
      ((derivedInverseImageComposition i i').app G) ((derivedInverseImage i).map ε) η
      ((squareValue hz).hom.app ((derivedInverseImage i').obj G)) ((squareValue hz).hom.app F)
      (u z'') ((squareValue (horizontalSquare hz hz')).hom.app G) hn hh
  unfold ClosedSupportPullbackPastingSpecs.SquareRestriction
  rw [hbridge k k', reassoc_of% (hbridge h h')]
  change (derivedInverseImage (j ≫ j')).map α ≫ u p' ≫
    (derivedInverseImage j).map (c p p' k') ≫ d q p k =
      u e' ≫ (derivedInverseImage j).map (c e e' h') ≫ d v e h ≫ γ
  have hn : (derivedInverseImage (j ≫ j')).map α ≫ u p' =
      u e' ≫ (derivedInverseImage j).map ((derivedInverseImage j').map α) :=
    (derivedInverseImageComposition j j').hom.naturality α
  have hr' : (derivedInverseImage j').map α ≫ c p p' k' = c e e' h' ≫ β := by
    simpa only [c, Category.assoc] using! hr
  have hs' : (derivedInverseImage j).map β ≫ d q p k = d v e h ≫ γ := by
    simpa only [d, Category.assoc] using! hs
  rw [reassoc_of% hn, ← Functor.map_comp_assoc, hr', Functor.map_comp]
  simp only [Category.assoc, hs']


theorem squareRestrictionNaturality : Expected.SquareRestrictionNaturality.{u} := by
  intro U X V W i j e p v q he hp G G' F F' c d ε ε' hc α α' β β' hd h h'
  have he' : (derivedInverseImage j).map ((derivedInverseImage e).map c) ≫
      (squareValue he).hom.app G' = (squareValue he).hom.app G ≫
        (derivedInverseImage v).map ((derivedInverseImage i).map c) :=
    (squareValue he).hom.naturality c
  have hp' : (derivedInverseImage j).map ((derivedInverseImage p).map c) ≫
      (squareValue hp).hom.app G' = (squareValue hp).hom.app G ≫
        (derivedInverseImage q).map ((derivedInverseImage i).map c) :=
    (squareValue hp).hom.naturality c
  unfold ClosedSupportPullbackPastingSpecs.SquareRestriction at h h'
  simp only [Functor.map_comp, Category.assoc]
  rw [h', reassoc_of% he', ← (derivedInverseImage v).map_comp_assoc, hc,
    Functor.map_comp, Category.assoc, hd, reassoc_of% hp',
    ← (derivedInverseImage q).map_comp, hc, Functor.map_comp, reassoc_of% h]

end RepTheorySurvey.Geometric.ClosedSupportPullbackPasting
