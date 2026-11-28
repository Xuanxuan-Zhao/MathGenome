import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.PointMatesOnSupportIntersections
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedPointExtensionComposition
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedSupportPullbackPasting
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedSupportBaseChange
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace RepTheorySurvey.Geometric.PointMatesOnSupportIntersections

open Analytic Analytic.AnalyticAction Analytic.IntersectionComplex LocalSheaf
open ClosedEquivarianceExtensionSpecs (parameterInclusion projectionSquare)
open ClosedSupportBaseChangeSpecs (MateCommutes)
open ClosedSupportPullbackPastingSpecs (SquareRestriction flatten)
open EquivariantIntersectionComplexesSpecs (Intertwines IntertwinesPullback restrictedArrow)
open FiniteStageClosedExtensionSpecs
open PointMatesOnSupportIntersectionsSpecs
open Analytic.DerivedPullbackPasting.Expected (squareValue)
open private mateCommutesAtJet from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedSupportBaseChange
open private squareTranspose from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedPointExtensionComposition
open private derivedIsZero from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension
open private verticalCommutes from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.DerivedPullbackPasting

private theorem parameter_square {H : AnalyticGroup.{0}} {U X V Y : TopCat.{0}}
    {j : U ⟶ X} {t : X ⟶ Y} {v : U ⟶ V} {i : V ⟶ Y}
    (h : j ≫ t = v ≫ i) :
    parameterInclusion H j ≫ parameterInclusion H t =
      parameterInclusion H v ≫ parameterInclusion H i := by
  exact TopCat.ext fun z => Prod.ext rfl (congrArg (fun f : U ⟶ Y => f z.2) h)

private theorem flatten_on_support {U X : TopCat.{0}} {J : JetSystem.{0}} {t : U ⟶ X}
    {C : JetAction J U} {E : JetAction J X} (h : Intertwines C E t)
    {G : Derived X} (α : E.Equivariance G)
    (β : C.Equivariance ((derivedInverseImage t).obj G))
    (hβ : IntertwinesPullback h β α (𝟙 _))
    (k : ℕ) (hu : C.cutoff ≤ k) (hx : E.cutoff ≤ k)
    (he : parameterInclusion (J.group k) t ≫ ((E.action k hx).act) =
        (C.action k hu).act ≫ t)
    (hp : parameterInclusion (J.group k) t ≫ projection (J.group k) X =
        projection (J.group k) U ≫ t) :
    flatten t (β.datum k hu).iso.hom =
      pullbackMorphism (parameterInclusion (J.group k) t) he hp (α.datum k hx).iso.hom := by
  have hEq := hβ k hu hx
  change (derivedInverseImage (C.action k hu).act).map (𝟙 _) ≫ restrictedArrow h α k hu hx =
    (β.datum k hu).iso.hom ≫ (derivedInverseImage (projection (J.group k) U)).map (𝟙 _) at hEq
  rw [(derivedInverseImage (C.action k hu).act).map_id,
    (derivedInverseImage (projection (J.group k) U)).map_id,
    Category.id_comp, Category.comp_id] at hEq
  rw [← hEq]
  simp only [flatten, restrictedArrow, Category.assoc, Iso.hom_inv_id_app_assoc,
    Iso.hom_inv_id_app, Category.comp_id]

private theorem restriction_on_empty {U X V W : TopCat.{0}} [IsEmpty V]
    {i : U ⟶ X} {j : V ⟶ W} {e p : W ⟶ X} {v q : V ⟶ U}
    (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    {G : Derived X} (F : BoundedBelow U) (ε : (derivedInverseImage i).obj G ⟶ F.obj)
    (α : (derivedInverseImage e).obj G ⟶ (derivedInverseImage p).obj G)
    (β : (derivedInverseImage v).obj F.obj ⟶ (derivedInverseImage q).obj F.obj) :
    ClosedSupportBaseChangeSpecs.SquareRestriction he hp ε α β := by
  let Q := (boundedBelowInverseImage q).obj F
  have hQ : IsZero Q := derivedIsZero Q fun n =>
    (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero _).mpr fun z => isEmptyElim z
  have hQobj : IsZero ((derivedInverseImage q).obj F.obj) :=
    (DerivedCategory.Plus.ι (C := Sheaves V)).map_isZero hQ
  exact hQobj.eq_of_tgt _ _

/-- The transpose of the support comparison at the identity is the counit equation. -/
private theorem transpose_support_mate {U X V W : TopCat.{0}}
    {i : U ⟶ X} {j : V ⟶ W} {e p : W ⟶ X} {v q : V ⟶ U}
    (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    (a : boundedBelowInverseImage j ⊣ derivedDirectImage j)
    {R : BoundedBelow U ⥤ BoundedBelow X} (b : boundedBelowInverseImage i ⊣ R)
    {F : BoundedBelow U}
    {α : (derivedInverseImage e).obj (R.obj F).obj ⟶ (derivedInverseImage p).obj (R.obj F).obj}
    {β : (derivedInverseImage v).obj F.obj ⟶ (derivedInverseImage q).obj F.obj}
    (h : MateCommutes he hp a b (𝟙 (R.obj F)) α β) :
    SquareRestriction he hp (b.counit.app F).hom α β := by
  have ht := (ClosedSupportBaseChange.mateEquationIff he hp a b (𝟙 (R.obj F)) α β).mp h
  let L := boundedBelowInverseImage i
  let K := L.obj (R.obj F)
  have hc : L.map (𝟙 (R.obj F)) ≫ b.counit.app F = b.counit.app F :=
    (congrArg (fun f : K ⟶ K => f ≫ b.counit.app F) (L.map_id (R.obj F))).trans
      (Category.id_comp (b.counit.app F))
  exact (congrArg (fun f : K ⟶ F => SquareRestriction he hp f.hom α β) hc).mp ht

/-- Restrict both parameter spaces, then express the result on the restricted coefficients. -/
private theorem restrict_support_square {U X V Y : TopCat.{0}} {H : AnalyticGroup.{0}}
    {j : U ⟶ X} {i : V ⟶ Y} {t : X ⟶ Y} {v : U ⟶ V}
    {e : Parameters H Y ⟶ Y} {f : Parameters H V ⟶ V}
    {e₀ : Parameters H X ⟶ X} {f₀ : Parameters H U ⟶ U}
    (h : j ≫ t = v ≫ i)
    (he : parameterInclusion H i ≫ e = f ≫ i)
    (he₀ : parameterInclusion H j ≫ e₀ = f₀ ≫ j)
    (ht : parameterInclusion H t ≫ e = e₀ ≫ t)
    (hv : parameterInclusion H v ≫ f = f₀ ≫ v)
    {G : Derived Y} {F : Derived V} {ε : (derivedInverseImage i).obj G ⟶ F}
    {α : (derivedInverseImage e).obj G ⟶ (derivedInverseImage (projection H Y)).obj G}
    {β : (derivedInverseImage f).obj F ⟶ (derivedInverseImage (projection H V)).obj F}
    {α₀ : (derivedInverseImage e₀).obj ((derivedInverseImage t).obj G) ⟶
      (derivedInverseImage (projection H X)).obj ((derivedInverseImage t).obj G)}
    {β₀ : (derivedInverseImage f₀).obj ((derivedInverseImage v).obj F) ⟶
      (derivedInverseImage (projection H U)).obj ((derivedInverseImage v).obj F)}
    (hα : flatten t α₀ = pullbackMorphism (parameterInclusion H t) ht (projectionSquare H t) α)
    (hβ : flatten v β₀ = pullbackMorphism (parameterInclusion H v) hv (projectionSquare H v) β)
    (hs : SquareRestriction he (projectionSquare H i) ε α β) :
    SquareRestriction he₀ (projectionSquare H j)
      ((squareValue h).hom.app G ≫ (derivedInverseImage v).map ε) α₀ β₀ := by
  let he' := verticalCommutes he₀ h
  let hp' := verticalCommutes (projectionSquare H j) h
  apply (ClosedSupportPullbackPasting.squareRestrictionFlatten
    h he₀ (projectionSquare H j) he' hp' ε α₀ β₀).mp
  rw [hα, hβ]
  exact ClosedSupportPullbackPasting.squareRestrictionParameterChange
    (parameterInclusion H t) (parameterInclusion H v) (parameter_square (H := H) h)
    he (projectionSquare H i) ht (projectionSquare H t) hv (projectionSquare H v) he' hp' hs

set_option maxHeartbeats 1000000 in
private theorem mate_of_restriction {U X V W : TopCat.{0}}
    {i : U ⟶ X} {j : V ⟶ W} {e p : W ⟶ X} {v q : V ⟶ U}
    (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    (a : boundedBelowInverseImage j ⊣ derivedDirectImage j)
    (b : boundedBelowInverseImage i ⊣ derivedDirectImage i)
    {F : BoundedBelow U} {G : BoundedBelow X} (c : G ⟶ (derivedDirectImage i).obj F)
    (α : (derivedInverseImage e).obj G.obj ⟶ (derivedInverseImage p).obj G.obj)
    (β : (derivedInverseImage v).obj F.obj ⟶ (derivedInverseImage q).obj F.obj)
    (ε : (derivedInverseImage i).obj G.obj ⟶ F.obj)
    (hε : ((boundedBelowInverseImage i).map c ≫ b.counit.app F).hom = ε)
    (h : SquareRestriction he hp ε α β) :
    MateCommutes he hp a b c α β := by
  have h' := (congrArg (fun f : (derivedInverseImage i).obj G.obj ⟶ F.obj =>
    SquareRestriction he hp f α β) hε.symm).mp h
  exact (ClosedSupportBaseChange.mateEquationIff he hp a b c α β).mpr h'

set_option maxHeartbeats 1000000 in
theorem pointMatesOnIntersections : Expected.PointMatesOnIntersections := by
  intro X Y J A B i x S T hx D P I hPoint a b F α γ Lₚ L hMates hLevel n
  let j := I.inclusion n
  let c := adjointSquareMap (pullbackSquare (I.support n)) (a j) b F
  apply mateCommutesAtJet (I.actionSquare n) a c (Lₚ.datum n) (L.datum n)
  intro k hu hv
  let H := J.group k
  let hAction := I.actionSquare n k hu hv
  let α₀ := ((Lₚ.datum n).datum k hu).iso.hom
  let γ₀ := ((L.datum n).datum k hv).iso.hom
  rcases hLevel n k hu hv with ⟨ht, hs⟩ | hEmpty
  · have hSupport := transpose_support_mate (hPoint k ht hs)
      (projectionSquare H (closedInclusion ({x} : Set Y)))
      (a (parameterInclusion H (closedInclusion ({x} : Set Y)))) b (hMates k ht hs)
    have hγ := flatten_on_support (D.supportActionSquare n) γ (L.datum n) (L.onSupport n)
      k hv hs (D.supportActionSquare n k hv hs) (projectionSquare H (D.intoSupport n))
    have hα := flatten_on_support (P.supportActionSquare n) α (Lₚ.datum n) (Lₚ.onSupport n)
      k hu ht (P.supportActionSquare n k hu ht) (projectionSquare H (P.intoSupport n))
    have hLocal := restrict_support_square (I.support n) (hPoint k ht hs) hAction
      (D.supportActionSquare n k hv hs) (P.supportActionSquare n k hu ht) hγ hα hSupport
    exact mate_of_restriction hAction (projectionSquare H j)
      (a (parameterInclusion H j)) (a j) c γ₀ α₀ _
      (squareTranspose (I.support n) (a j) b F) hLocal
  · let : IsEmpty (P.space n) := hEmpty
    have hMate := ClosedSupportBaseChange.mateEquationIff hAction (projectionSquare H j)
      (a (parameterInclusion H j)) (a j) c γ₀ α₀
    exact hMate.mpr (restriction_on_empty hAction (projectionSquare H j)
      (P.intersectionRestriction F n) _ γ₀ α₀)

end RepTheorySurvey.Geometric.PointMatesOnSupportIntersections
