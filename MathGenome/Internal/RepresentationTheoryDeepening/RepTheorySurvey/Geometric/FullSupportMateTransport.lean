import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.FullSupportMateTransport
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedSupportBaseChange
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedPullbackPasting
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option autoImplicit false
set_option Elab.async false

open CategoryTheory Topology

namespace RepTheorySurvey.Geometric.FullSupportMateTransport

open Analytic Analytic.IntersectionComplex LocalSheaf
open Analytic.DerivedPullbackPasting.Expected (squareValue)
open AnalyticAction (projection)
open ClosedEquivarianceExtensionSpecs (DerivedAdjunctions parameterInclusion projectionSquare)
open ClosedSupportBaseChangeSpecs (MateCommutes SquareRestriction)

set_option allowUnsafeReducibility true in
attribute [local reducible] Analytic.DerivedPullbackPasting.Expected.SquareType

open private horizontalCommutes from MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.DerivedPullbackPasting
open private parameterInclusion_closed from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedEquivarianceExtension
open private derivedClosedImageCounit_isIso
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes

private theorem exists_mate_commutes {U X S T : TopCat.{0}} {i : U ⟶ X} {k : S ⟶ T}
    {e p : T ⟶ X} {s q : S ⟶ U} (he : k ≫ e = s ≫ i) (hp : k ≫ p = q ≫ i)
    (a : DerivedAdjunctions.{0}) {G : BoundedBelow X} {F : BoundedBelow U}
    (c : G ⟶ (derivedDirectImage i).obj F)
    (β : (derivedInverseImage s).obj F.obj ⟶ (derivedInverseImage q).obj F.obj)
    [IsIso c] [IsIso (directImageComparison hp (a k) (a i) F)] :
    ∃ α, MateCommutes he hp (a k) (a i) c α β := by
  let cP := (boundedBelowInverseImage p).map c ≫ directImageComparison hp (a k) (a i) F
  let cA := (boundedBelowInverseImage e).map c ≫ directImageComparison he (a k) (a i) F
  let βPlus : (boundedBelowInverseImage s).obj F ⟶ (boundedBelowInverseImage q).obj F :=
    ObjectProperty.homMk β
  have : IsIso cP := by
    dsimp only [cP]
    infer_instance
  let m := cA ≫ (derivedDirectImage k).map βPlus
  let α := m ≫ inv cP
  have h : α ≫ cP = m := by
    simp only [α, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  refine ⟨α.hom, ?_⟩
  change (α ≫ cP).hom = m.hom
  exact congrArg (fun f => f.hom) h

private theorem square_restriction_injective {U X S T : TopCat.{0}} {i : U ⟶ X} {k : S ⟶ T}
    {e p : T ⟶ X} {s q : S ⟶ U} {he : k ≫ e = s ≫ i} {hp : k ≫ p = q ≫ i}
    (a : DerivedAdjunctions.{0}) (hk : IsClosedEmbedding k)
    {G : BoundedBelow X} {F : Derived U} {ε : (derivedInverseImage i).obj G.obj ⟶ F}
    (hε : IsIso ε) (hG : DerivedSupportedOn (Set.range k) ((boundedBelowInverseImage p).obj G))
    {α α' : (derivedInverseImage e).obj G.obj ⟶ (derivedInverseImage p).obj G.obj}
    {β : (derivedInverseImage s).obj F ⟶ (derivedInverseImage q).obj F}
    (h : SquareRestriction he hp ε α β) (h' : SquareRestriction he hp ε α' β) :
    α = α' := by
  let comparison := (squareValue hp).hom.app G.obj ≫ (derivedInverseImage q).map ε
  have : IsIso comparison := by
    dsimp only [comparison]
    infer_instance
  have heq : (derivedInverseImage k).map α ≫ comparison =
      (derivedInverseImage k).map α' ≫ comparison := h.trans h'.symm
  exact (ClosedSupportBaseChange.supportedRestrictionBijective hk a
    ((boundedBelowInverseImage e).obj G) ((boundedBelowInverseImage p).obj G) hG).injective
      ((cancel_mono comparison).mp heq)

private theorem transpose_isIso {U X : TopCat.{0}} {i : U ⟶ X} (hi : IsClosedEmbedding i)
    (a : DerivedAdjunctions.{0}) {G : BoundedBelow X} {F : BoundedBelow U}
    (d : G ⟶ (derivedDirectImage i).obj F) [IsIso d] :
    IsIso (((boundedBelowInverseImage i).map d ≫ (a i).counit.app F).hom) := by
  have : IsIso ((a i).counit.app F) := derivedClosedImageCounit_isIso hi (a i) F
  exact (DerivedCategory.Plus.ι (C := Sheaves U)).map_isIso
    ((boundedBelowInverseImage i).map d ≫ (a i).counit.app F)

private theorem restriction_horizontal {U X Z V Y W : TopCat.{0}}
    {j : U ⟶ X} {j' : X ⟶ Z} {i : V ⟶ Y} {i' : Y ⟶ W}
    {v q : U ⟶ V} {e p : X ⟶ Y} {e' p' : Z ⟶ W}
    (h : j ≫ e = v ≫ i) (k : j ≫ p = q ≫ i)
    (h' : j' ≫ e' = e ≫ i') (k' : j' ≫ p' = p ≫ i')
    {G : Derived W} {F : Derived Y} {K : Derived V}
    (ε : (derivedInverseImage i').obj G ⟶ F) (η : (derivedInverseImage i).obj F ⟶ K)
    {α : (derivedInverseImage e').obj G ⟶ (derivedInverseImage p').obj G}
    {β : (derivedInverseImage e).obj F ⟶ (derivedInverseImage p).obj F}
    {γ : (derivedInverseImage v).obj K ⟶ (derivedInverseImage q).obj K}
    (hr : SquareRestriction h' k' ε α β) (hs : SquareRestriction h k η β γ) :
    SquareRestriction (horizontalCommutes h h') (horizontalCommutes k k')
      ((derivedInverseImageComposition i i').hom.app G ≫ (derivedInverseImage i).map ε ≫ η)
      α γ := by
  let u (z : Z ⟶ W) := (derivedInverseImageComposition j j').hom.app ((derivedInverseImage z).obj G)
  let c (z : X ⟶ Y) (z' : Z ⟶ W) (hz : j' ≫ z' = z ≫ i') :=
    (squareValue hz).hom.app G ≫ (derivedInverseImage z).map ε
  let d (z : U ⟶ V) (z' : X ⟶ Y) (hz : j ≫ z' = z ≫ i) :=
    (squareValue hz).hom.app F ≫ (derivedInverseImage z).map η
  have hbridge {z : U ⟶ V} {z' : X ⟶ Y} {z'' : Z ⟶ W}
      (hz : j ≫ z' = z ≫ i) (hz' : j' ≫ z'' = z' ≫ i') :
      (squareValue (horizontalCommutes hz hz')).hom.app G ≫
        (derivedInverseImage z).map
          ((derivedInverseImageComposition i i').hom.app G ≫ (derivedInverseImage i).map ε ≫ η) =
      u z'' ≫ (derivedInverseImage j).map (c z' z'' hz') ≫ d z z' hz := by
    have hn : (derivedInverseImage j).map ((derivedInverseImage z').map ε) ≫
        (squareValue hz).hom.app F = (squareValue hz).hom.app ((derivedInverseImage i').obj G) ≫
          (derivedInverseImage z).map ((derivedInverseImage i).map ε) :=
      (squareValue hz).hom.naturality ε
    have hh := DerivedPullbackPasting.squareHorizontalPasting hz hz' G
    rw [show (squareValue (horizontalCommutes hz hz')).hom.app G = _ from hh]
    simp only [u, c, d, Functor.map_comp, Category.assoc]
    rw [← (derivedInverseImage z).map_comp_assoc ((derivedInverseImageComposition i i').inv.app G)
      ((derivedInverseImageComposition i i').hom.app G), Iso.inv_hom_id_app,
      (derivedInverseImage z).map_id, Category.id_comp, reassoc_of% hn]
  unfold SquareRestriction
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

private theorem paste_parameter_restriction {U Y V : TopCat.{0}}
    {v : U ⟶ Y} {j : Y ⟶ V} {H : AnalyticGroup.{0}}
    {A_U : AnalyticAction H U} {A_Y : AnalyticAction H Y} {A_V : AnalyticAction H V}
    (hv : parameterInclusion H v ≫ A_Y.act = A_U.act ≫ v)
    (hj : parameterInclusion H j ≫ A_V.act = A_Y.act ≫ j)
    (hu : parameterInclusion H (v ≫ j) ≫ A_V.act = A_U.act ≫ (v ≫ j))
    {G : Derived V} {F : Derived Y}
    (ε : (derivedInverseImage j).obj G ⟶ F)
    {α : (derivedInverseImage A_V.act).obj G ⟶ (derivedInverseImage (projection H V)).obj G}
    {β : (derivedInverseImage A_Y.act).obj F ⟶ (derivedInverseImage (projection H Y)).obj F}
    {γ : (derivedInverseImage A_U.act).obj ((derivedInverseImage v).obj F) ⟶
      (derivedInverseImage (projection H U)).obj ((derivedInverseImage v).obj F)}
    (hY : SquareRestriction hj (projectionSquare H j) ε α β)
    (hU : SquareRestriction hv (projectionSquare H v) (𝟙 _) β γ) :
    SquareRestriction hu (projectionSquare H (v ≫ j))
      ((derivedInverseImageComposition v j).hom.app G ≫ (derivedInverseImage v).map ε) α γ := by
  let comparison := (derivedInverseImageComposition v j).hom.app G ≫ (derivedInverseImage v).map ε
  have pasted := restriction_horizontal hv (projectionSquare H v) hj (projectionSquare H j)
    ε (𝟙 _) hY hU
  rw [Category.comp_id] at pasted
  have transport (k : AnalyticAction.Parameters H U ⟶ AnalyticAction.Parameters H V)
      (hk : parameterInclusion H v ≫ parameterInclusion H j = k)
      (he : k ≫ A_V.act = A_U.act ≫ (v ≫ j))
      (hp : k ≫ projection H V = projection H U ≫ (v ≫ j)) :
      SquareRestriction he hp comparison α γ := by
    subst k
    exact pasted
  exact transport _ (TopCat.ext (fun _ => rfl)) hu (projectionSquare H (v ≫ j))

/-- Agreement with the mates on a closed intersection implies agreement with the
mates on the full support when the coefficient transposes compose. -/
theorem fullSupportMateTransport :
    FullSupportMateTransportSpecs.Expected.FullSupportMateTransport := by
  intro U Y V v j u factor huClosed H A_U A_Y A_V hv hj hu a G F c K d hc hd hp hsupport
    α β γ εj εu hε hlocal hα
  subst u
  have hε' : εu = (derivedInverseImageComposition v j).hom.app G.obj ≫
      (derivedInverseImage v).map εj := by
    simpa only [eqToHom_refl, Category.id_comp] using hε
  obtain ⟨α', hα'⟩ := exists_mate_commutes hj (projectionSquare H j) a c β
  have hY : SquareRestriction hj (projectionSquare H j) εj α' β :=
    (ClosedSupportBaseChange.derivedDirectImageMateEquationIff hj
      (projectionSquare H j) a c α' β).mp hα'
  have hU : SquareRestriction hu (projectionSquare H (v ≫ j)) εu α γ :=
    (ClosedSupportBaseChange.derivedDirectImageMateEquationIff hu
      (projectionSquare H (v ≫ j)) a d α γ).mp hα
  have hU' : SquareRestriction hu (projectionSquare H (v ≫ j)) εu α' γ := by
    rw [hε']
    exact paste_parameter_restriction hv hj hu εj hY hlocal
  have hεu : IsIso εu := transpose_isIso huClosed a d
  have hEq : α = α' := square_restriction_injective a
    (parameterInclusion_closed H huClosed) hεu hsupport hU hU'
  exact hEq.symm ▸ hα'

end RepTheorySurvey.Geometric.FullSupportMateTransport
