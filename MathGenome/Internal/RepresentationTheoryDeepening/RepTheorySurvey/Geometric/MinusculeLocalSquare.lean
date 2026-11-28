import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.MinusculeLocalSquare
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedEquivarianceExtension
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.DerivedPullbackPasting
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionActionComparisons
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionPointCoefficients
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeAndTwoStep
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RankTwoSchubertStrata
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000

open CategoryTheory

namespace RepTheorySurvey.Geometric.MinusculeLocalSquare

open Analytic AnalyticAction LocalSheaf
open Analytic.IntersectionComplex (point complex DimensionFiltration shiftedConstant
  adjointSquareMap pullbackSquare directImageComparison)
open ClosedEquivarianceExtensionSpecs (DerivedAdjunctions parameterInclusion projectionSquare)
open ConvolutionAnalyticChartsSpecs (surface)
open ConvolutionEquivariantSplittingSpecs (SplittingData)
open ConvolutionUnitConeSpecs (convolution pointSkyscraper unit)
open EquivariantIntersectionComplexesSpecs
open FiniteStageClosedExtensionSpecs (AgreesWithMates MatesAreIso)
open LatticeModelSpecs (BoundedLattice boundedSubspace OrbitBound)
open MinusculeAndTwoStepSpecs (scalarPair scalarPoint)
open RankTwoSchubertStrataSpecs
open SchubertIntersectionConstructibilitySpecs
open TwoStepICNormalizationSpecs (TerminalComparison)
open MinusculeLocalSquareSpecs
open ConvolutionConstantDescentSpec (shiftedConstantPullback)

open private pullbackMorphism_id pullbackMorphism_paste pullbackMorphism_congr
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedEquivarianceExtension
open private orbit_mem_of_small from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RankTwoSchubertStrata

private def trivialJetAction (J : JetSystem.{0}) (Y : TopCat.{0}) (n : ℕ) : JetAction J Y where
  cutoff := n
  action k _ := ⟨projection (J.group k) Y, fun _ ↦ rfl, fun _ _ _ ↦ rfl⟩
  factors _ _ := TopCat.ext (fun _ ↦ rfl)

private def trivialJetDatum (J : JetSystem.{0}) (Y : TopCat.{0}) (n : ℕ) (F : Derived Y) :
    (trivialJetAction J Y n).Equivariance F where
  datum k _ :=
    { iso := Iso.refl _
      identity := pullbackMorphism_id _ _
      multiplication := by
        simp only [Iso.refl_hom, pullbackMorphism_id, Category.id_comp]
        rfl }
  compatibility _ _ := pullbackMorphism_id _ _

private theorem scalarModel (x : surface) (hN : OrbitBound scalarPair 2) :
    ∃ (e : TopCat.of ({x} : Set surface) ≅ SchubertSpace scalarPair 2 hN)
      (L : BoundedLattice 2 2),
      L.val = scalarPoint ∧
      (∀ p, schubertPointSubspace (e.hom p) = boundedSubspace L) ∧
      Subsingleton (SchubertSpace scalarPair 2 hN) := by
  obtain ⟨C, hC, -⟩ := RankTwoSchubertStrata.schubertStratification scalarPair 2 hN
  let Q := schubertLatticeSet scalarPair 2
  let L := diagonalBounded scalarPair 2 hN
  have scalar (p : Q) : p.val.val = scalarPoint := by
    have hp := orbit_mem_of_small (ab := scalarPair) (by decide) p.property
    rw [MinusculeAndTwoStep.twoStepOrbits.2.1] at hp
    exact hp
  have hQ : Subsingleton Q := ⟨fun p q ↦ Subtype.ext (Subtype.ext ((scalar p).trans (scalar q).symm))⟩
  have hmodel : Subsingleton (SchubertSpace scalarPair 2 hN) :=
    ⟨fun p q ↦ C.injective (Subsingleton.elim (C p) (C q))⟩
  let q : Q := ⟨L, ⟨scalarPair, (RankTwoSchubertStrata.below_iff scalarPair scalarPair).mpr
    ⟨rfl, le_rfl, le_rfl⟩, MulAction.mem_orbit_self _⟩⟩
  let e : TopCat.of ({x} : Set surface) ≃ₜ SchubertSpace scalarPair 2 hN :=
    { toFun := fun _ ↦ C.symm q
      invFun := fun _ ↦ ⟨x, rfl⟩
      left_inv := fun p ↦ Subtype.ext p.property.symm
      right_inv := fun _ ↦ Subsingleton.elim _ _
      continuous_toFun := continuous_const
      continuous_invFun := continuous_const }
  refine ⟨TopCat.isoOfHomeo e, L, scalar q, ?_, hmodel⟩
  intro p
  change schubertPointSubspace (C.symm q) = boundedSubspace L
  rw [hC, C.apply_symm_apply]

private theorem filtrationAtDepthZero {ab : LatticeModelSpecs.DominantPair} {N : ℕ}
    {hN : OrbitBound ab N} {Y : TopCat.{0}} {f : Y ⟶ SchubertSpace ab N hN}
    {P : Stratification Y} {s k : ℕ} {D : DimensionFiltration Y s}
    (h : IsNormalizedOrbitIC ab N hN f k P D) (hk : k = 0) :
    HEq D (DimensionFiltration.top Y (difference ab)) := by
  cases h with
  | top => rfl
  | attach => omega

private theorem constantOnTrivialAction {H : AnalyticGroup.{0}} {Y : TopCat.{0}}
    (d : ℕ) {f : Parameters H Y ⟶ Y} (h : f = projection H Y) :
    (shiftedConstantPullback f d ≪≫ (shiftedConstantPullback (projection H Y) d).symm).hom =
      eqToHom (congrArg (fun t => (derivedInverseImage t).obj (shiftedConstant Y d).obj) h) := by
  subst f
  simp

private theorem pullbackActionTransport {W Y X : TopCat.{0}}
    {f g f' : Y ⟶ X} {s t : W ⟶ X} (p : W ⟶ Y)
    (h : f' = f) (hs : p ≫ f' = s) (ht : p ≫ g = t) {F : Derived X}
    (v : (derivedInverseImage f).obj F ⟶ (derivedInverseImage g).obj F) :
    pullbackMorphism p hs ht
        (eqToHom (congrArg (fun u => (derivedInverseImage u).obj F) h) ≫ v) =
      pullbackMorphism p ((congrArg (p ≫ ·) h.symm).trans hs) ht v := by
  subst f'
  simp

private theorem scalarCoefficients {c : ContinuousJets} (a : DerivedAdjunctions.{0})
    (x : surface) {hN : OrbitBound scalarPair 2}
    (C : SchubertJetAction c scalarPair 2 hN) {P : Stratification (SchubertSpace scalarPair 2 hN)}
    {E : DimensionFiltration (SchubertSpace scalarPair 2 hN) 0}
    (hE : IsNormalizedOrbitIC scalarPair 2 hN (𝟙 _) 0 P E)
    (γ : C.action.Equivariance (complex E).obj) (hγ : NormalizedICDatum (@a) C.action E γ)
    [Subsingleton (SchubertSpace scalarPair 2 hN)]
    (e : TopCat.of ({x} : Set surface) ≅ SchubertSpace scalarPair 2 hN)
    (h : Intertwines (trivialJetAction (jetSystem c) _ 1) C.action e.hom) :
    ∃ v : (point x).obj ≅ (derivedInverseImage e.hom).obj (complex E).obj,
      IntertwinesPullback h (trivialJetDatum (jetSystem c) _ 1 (point x).obj) γ v.hom := by
  have htop : E = .top (SchubertSpace scalarPair 2 hN) 0 := eq_of_heq (filtrationAtDepthZero hE rfl)
  subst E
  let t : (shiftedConstant (TopCat.of ({x} : Set surface)) 0).obj ≅ (point x).obj :=
    (shiftFunctorZero (Derived (TopCat.of ({x} : Set surface))) ℤ).app _
  refine ⟨t.symm ≪≫ (shiftedConstantPullback e.hom 0).symm, ?_⟩
  unfold Intertwines at h
  intro k hp hm
  let H := (jetSystem c).group k
  let p := projection H (TopCat.of ({x} : Set surface))
  have he : (C.action.action k hm).act = projection H (SchubertSpace scalarPair 2 hN) :=
    TopCat.ext (fun _ ↦ Subsingleton.elim _ _)
  have hcoeff : (γ.datum k hm).iso.hom =
      eqToHom (congrArg (fun f => (derivedInverseImage f).obj (complex (.top _ 0)).obj) he) := by
    have hn := EquivariantIntersectionComplexes.normalizedConstantDatum_iso (@a) hγ k hm
    change (γ.datum k hm).iso = (EquivariantIntersectionComplexes.constantDatum (C.action.action k hm) 0).iso at hn
    exact congrArg Iso.hom (hn.trans (EquivariantIntersectionComplexes.constantDatum_iso _ _)) |>.trans
      (constantOnTrivialAction 0 he)
  have hrestrict : restrictedArrow h γ k hp hm =
      𝟙 ((derivedInverseImage p).obj ((derivedInverseImage e.hom).obj (complex (.top _ 0)).obj)) := by
    dsimp only [restrictedArrow]
    rw [hcoeff]
    have hid := pullbackActionTransport (parameterInclusion H e.hom) he
      (h k hp hm) (projectionSquare H e.hom)
        (𝟙 ((derivedInverseImage (projection H (SchubertSpace scalarPair 2 hN))).obj
          (complex (.top _ 0)).obj))
    rw [Category.comp_id, pullbackMorphism_id] at hid
    rw [hid]
    rw [Category.id_comp]
    exact Iso.inv_hom_id_app (derivedInverseImageComposition p e.hom) _
  rw [hrestrict]
  change _ ≫ 𝟙 _ = 𝟙 _ ≫ (derivedInverseImage p).map _
  rw [Category.comp_id, Category.id_comp]
  rfl

section JetExtension

open private restrictEquivariance from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ConvolutionActionComparisons

private theorem analyticAction_ext {H : AnalyticGroup.{0}} {Y : TopCat.{0}}
    {A B : AnalyticAction H Y} (h : A.act = B.act) : A = B := by
  cases A
  cases B
  cases h
  rfl

private def changeActionDatum {H : AnalyticGroup.{0}} {Y : TopCat.{0}}
    {A B : AnalyticAction H Y} {F : Derived Y} (h : A.act = B.act) (β : B.Equivariance F) :
    A.Equivariance F := (analyticAction_ext h).symm ▸ β

private theorem changeActionDatum_hom {H : AnalyticGroup.{0}} {Y : TopCat.{0}}
    {A B : AnalyticAction H Y} {F : Derived Y} (h : A.act = B.act) (β : B.Equivariance F) :
    (changeActionDatum h β).iso.hom =
      eqToHom (congrArg (fun f => (derivedInverseImage f).obj F) h) ≫ β.iso.hom := by
  cases A
  cases B
  cases h
  simp [changeActionDatum]

private def truncationHom (J : JetSystem.{0}) {n k : ℕ} (h : n ≤ k) :
    (J.group k).space →* (J.group n).space where
  toFun := J.truncate n k h
  map_one' := J.truncate_one h
  map_mul' := J.truncate_mul h

private def datumAtJetLevel {J : JetSystem.{0}} {Y : TopCat.{0}} {n k : ℕ} {h : n ≤ k}
    {A : AnalyticAction (J.group n) Y} {B : AnalyticAction (J.group k) Y} {F : Derived Y}
    (hs : J.parameterMap h (𝟙 Y) ≫ A.act = B.act) (α : A.Equivariance F) :
    B.Equivariance F :=
  let φ := truncationHom J h
  let hφ : Continuous φ := (J.truncate n k h).hom.continuous
  changeActionDatum hs.symm (restrictEquivariance φ hφ A α)

private theorem datumAtJetLevel_hom {J : JetSystem.{0}} {Y : TopCat.{0}} {n k : ℕ} {h : n ≤ k}
    {A : AnalyticAction (J.group n) Y} {B : AnalyticAction (J.group k) Y} {F : Derived Y}
    (hs : J.parameterMap h (𝟙 Y) ≫ A.act = B.act) (α : A.Equivariance F) :
    (datumAtJetLevel hs α).iso.hom =
      pullbackMorphism (J.parameterMap h (𝟙 Y)) hs (TopCat.ext (fun _ ↦ rfl)) α.iso.hom := by
  let φ := truncationHom J h
  let hφ : Continuous φ := (J.truncate n k h).hom.continuous
  change (changeActionDatum hs.symm (restrictEquivariance φ hφ A α)).iso.hom = _
  rw [changeActionDatum_hom]
  simp only [restrictEquivariance, asIso_hom, pullbackMorphism, eqToHom_refl, Category.id_comp]
  simp only [← Category.assoc]
  rfl

private theorem parameterMap_comp {J : JetSystem.{0}} {Y : TopCat.{0}} {n k l : ℕ}
    (hn : n ≤ k) (hk : k ≤ l) :
    J.parameterMap hk (𝟙 Y) ≫ J.parameterMap hn (𝟙 Y) = J.parameterMap (hn.trans hk) (𝟙 Y) := by
  apply TopCat.ext
  rintro ⟨g, x⟩
  change ((J.truncate n k hn (J.truncate k l hk g)), x) = (J.truncate n l (hn.trans hk) g, x)
  exact Prod.ext (congrArg (fun f : (J.group l).space ⟶ (J.group n).space ↦ f g)
    (J.truncate_comp hn hk)) rfl

private theorem parameterMap_id (J : JetSystem.{0}) (n : ℕ) (Y : TopCat.{0}) :
    J.parameterMap (le_refl n) (𝟙 Y) = 𝟙 (Parameters (J.group n) Y) := by
  apply TopCat.ext
  rintro ⟨g, x⟩
  change (J.truncate n n (le_refl n) g, x) = (g, x)
  rw [J.truncate_id]
  rfl

/-- Pull the datum at the cutoff back along each actual jet truncation. -/
private def datumFromCutoff {J : JetSystem.{0}} {Y : TopCat.{0}} {F : Derived Y}
    {A : JetAction J Y} (α : (A.action A.cutoff le_rfl).Equivariance F) : A.Equivariance F where
  datum _ hk := datumAtJetLevel (A.factors le_rfl hk) α
  compatibility {k l} hk h := by
    simp only [datumAtJetLevel_hom]
    rw [pullbackMorphism_paste]
    · exact pullbackMorphism_congr (parameterMap_comp hk h) _ _ _ _ α.iso.hom
    · rw [parameterMap_comp]
      exact A.factors le_rfl (hk.trans h)
    · rfl

private theorem datumFromCutoff_hom {J : JetSystem.{0}} {Y : TopCat.{0}} {F : Derived Y}
    {A : JetAction J Y} (α : (A.action A.cutoff le_rfl).Equivariance F) :
    ((datumFromCutoff α).datum A.cutoff le_rfl).iso.hom = α.iso.hom := by
  change (datumAtJetLevel (A.factors le_rfl le_rfl) α).iso.hom = _
  rw [datumAtJetLevel_hom]
  exact (pullbackMorphism_congr (parameterMap_id J A.cutoff Y) _ _ _ _ α.iso.hom).trans
    (DerivedPullbackPasting.pullbackIdentityMap α.iso.hom)

private def datumFromLevel {J : JetSystem.{0}} {Y : TopCat.{0}} {F : Derived Y}
    {A : JetAction J Y} {n : ℕ} (h : A.cutoff = n)
    (α : (A.action n h.le).Equivariance F) : A.Equivariance F := by
  subst n
  exact datumFromCutoff α

private theorem datumFromLevel_hom {J : JetSystem.{0}} {Y : TopCat.{0}} {F : Derived Y}
    {A : JetAction J Y} {n : ℕ} (h : A.cutoff = n)
    (α : (A.action n h.le).Equivariance F) :
    ((datumFromLevel h α).datum n h.le).iso.hom = α.iso.hom := by
  subst n
  exact datumFromCutoff_hom α

private theorem intertwinesFromLevel {J : JetSystem.{0}} {Y : TopCat.{0}}
    {A : JetAction J Y} {F G : Derived Y} {f : F ⟶ G}
    (α : A.Equivariance F) (β : A.Equivariance G) {n : ℕ} (hn : A.cutoff = n)
    (h : ConvolutionEquivariantSplittingSpecs.Intertwines
      (α.datum n hn.le) (β.datum n hn.le) f) :
    ∀ k hk, ConvolutionEquivariantSplittingSpecs.Intertwines (α.datum k hk) (β.datum k hk) f := by
  intro k hk
  let hnk : n ≤ k := hn ▸ hk
  have ht := DerivedPullbackPasting.pullbackNaturality (J.parameterMap hnk (𝟙 Y))
    (A.factors hn.le hnk) (TopCat.ext (fun _ ↦ rfl)) f _ _ h
  rwa [α.compatibility, β.compatibility] at ht

end JetExtension

section PointExtension

open ClosedEquivarianceExtensionSpecs (ActionSquares above ComparisonsAreIso MatchesComparisons
  actionComparison projectionComparison)
open ConvolutionPointCoefficients (twoJetPointUniqueness)
open ConvolutionUnitConeSpecs (jetGroup)

private abbrev PointSpace (x : surface) := TopCat.of ({x} : Set surface)

private theorem pointInclusionCommutes {c : ContinuousJets} {d : SplittingData}
    (A : JetAction (jetSystem c) surface) (h : A.cutoff = 1)
    (hact : (A.action 1 h.le).act = d.terminalAction.act) :
    Intertwines (trivialJetAction (jetSystem c) (PointSpace d.point) 1) A
      (closedInclusion ({d.point} : Set surface)) := by
  intro k hp ht
  apply TopCat.ext
  rintro ⟨g, x⟩
  have hx : x.val = d.point := x.property
  have h1 : 1 ≤ k := hp
  have he := (A.factors h.le h1).symm.trans
    (congrArg (fun f => (jetSystem c).parameterMap h1 (𝟙 surface) ≫ f) hact)
  have hv := congrArg (fun f : Parameters ((jetSystem c).group k) surface ⟶ surface =>
    f (g, x.val)) he
  change (A.action k ht).act (g, x.val) = x.val
  rw [hx] at hv ⊢
  exact hv.trans (d.fixes (jetTruncation h1 g))

private def datumOfAbove {J : JetSystem.{0}} {X : TopCat.{0}} {A : JetAction J X}
    {n : ℕ} (hn : n ≤ A.cutoff) {F : Derived X} (α : (above A n).Equivariance F) :
    A.Equivariance F where
  datum k hk := α.datum k (max_le hk (hn.trans hk))
  compatibility hk h := α.compatibility (max_le hk (hn.trans hk)) h

private theorem pointAtTwo (d : SplittingData) {A : AnalyticAction (jetGroup d.topologicalGroup) surface}
    (h : A.act = d.terminalAction.act) (α : A.Equivariance (pointSkyscraper d.point d.closed)) :
    α.iso.hom =
      eqToHom (congrArg (fun f => (derivedInverseImage f).obj (pointSkyscraper d.point d.closed)) h) ≫
        d.pointEq.iso.hom := by
  obtain rfl := analyticAction_ext h
  simp only [eqToHom_refl, Category.id_comp]
  exact congrArg Iso.hom
    (twoJetPointUniqueness d.topologicalGroup d.scalar d.fixes d.point_normalized α.iso α.identity)

/-- Replacing the right adjoint on the horizontal side changes the mate by the
inverse of the right-adjoint uniqueness isomorphism. -/
private theorem mateChangeRightAdjoint {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    {E : B ⥤ A} {V : D ⥤ C} {J : A ⥤ C} {K : B ⥤ D}
    {S : C ⥤ A} {R R' : D ⥤ B}
    (σ : E ⋙ J ≅ K ⋙ V) (a : J ⊣ S) (b : K ⊣ R) (b' : K ⊣ R') (F : D) :
    adjointSquareMap σ a b' F =
      E.map ((b.rightAdjointUniq b').inv.app F) ≫ adjointSquareMap σ a b F := by
  let p := (b.rightAdjointUniq b').inv.app F
  have hp : K.map p ≫ b.counit.app F = b'.counit.app F := by
    dsimp only [p]
    rw [Adjunction.rightAdjointUniq_inv_app, Adjunction.rightAdjointUniq_hom_app_counit]
  unfold adjointSquareMap
  rw [← Adjunction.homEquiv_naturality_left, ← Functor.comp_map, ← Category.assoc,
    σ.hom.naturality, Functor.comp_map, Category.assoc, ← Functor.map_comp, hp]

private theorem mateEquationChangeRightAdjoint
    {U V X Y : TopCat.{0}} {j : U ⟶ X} {i : V ⟶ Y}
    {e p : X ⟶ Y} {v q : U ⟶ V} (he : j ≫ e = v ≫ i) (hp : j ≫ p = q ≫ i)
    {R : BoundedBelow V ⥤ BoundedBelow Y}
    (a : boundedBelowInverseImage j ⊣ derivedDirectImage j)
    (b : boundedBelowInverseImage i ⊣ derivedDirectImage i) (b' : boundedBelowInverseImage i ⊣ R)
    (F : BoundedBelow V)
    (δ : (derivedInverseImage e).obj (R.obj F).obj ⟶ (derivedInverseImage p).obj (R.obj F).obj)
    (w : (boundedBelowInverseImage v).obj F ⟶ (boundedBelowInverseImage q).obj F)
    (h : δ ≫ (adjointSquareMap (pullbackSquare hp) a b' F).hom =
      (adjointSquareMap (pullbackSquare he) a b' F).hom ≫ ((derivedDirectImage j).map w).hom) :
    let τ := ((b.rightAdjointUniq b').inv.app F).hom
    δ ≫ (derivedInverseImage p).map τ ≫ (directImageComparison hp a b F).hom =
      (derivedInverseImage e).map τ ≫ (directImageComparison he a b F).hom ≫
        ((derivedDirectImage j).map w).hom := by
  let f := (b.rightAdjointUniq b').inv.app F
  let ea := (boundedBelowInverseImage e).map f
  let ep := (boundedBelowInverseImage p).map f
  let d : (boundedBelowInverseImage e).obj (R.obj F) ⟶
      (boundedBelowInverseImage p).obj (R.obj F) := ObjectProperty.homMk δ
  let va := directImageComparison he a b F
  let vp := directImageComparison hp a b F
  let u := (derivedDirectImage j).map w
  have hm : d ≫ adjointSquareMap (pullbackSquare hp) a b' F =
      adjointSquareMap (pullbackSquare he) a b' F ≫ u := ObjectProperty.hom_ext _ h
  have ha : adjointSquareMap (pullbackSquare he) a b' F = ea ≫ va :=
    mateChangeRightAdjoint (pullbackSquare he) a b b' F
  have hp' : adjointSquareMap (pullbackSquare hp) a b' F = ep ≫ vp :=
    mateChangeRightAdjoint (pullbackSquare hp) a b b' F
  have equation : d ≫ ep ≫ vp = ea ≫ va ≫ u :=
    (congrArg (d ≫ ·) hp'.symm).trans
      (hm.trans ((congrArg (· ≫ u) ha).trans (Category.assoc _ _ _)))
  exact congrArg (fun t => t.hom) equation

private theorem inclusionActionSquares {J : JetSystem.{0}} {X : TopCat.{0}} {Z : Set X}
    {A : JetAction J X} {B : JetAction J (TopCat.of Z)}
    (h : EquivariantIntersectionComplexesSpecs.Intertwines B A (closedInclusion Z)) :
    ActionSquares A B :=
  fun k hx hz ↦ h k hz hx

private theorem transferPointMates {J : JetSystem.{0}} {X : TopCat.{0}} {Z : Set X}
    (hZ : IsClosed Z) (A : JetAction J X) (B : JetAction J (TopCat.of Z))
    (h : Intertwines B A (closedInclusion Z)) (a : DerivedAdjunctions.{0})
    (b : boundedBelowInverseImage (closedInclusion Z) ⊣ closedExtensionPlus hZ)
    (F : BoundedBelow (TopCat.of Z)) (β : B.Equivariance F.obj)
    (α : (above A B.cutoff).Equivariance ((closedExtensionPlus hZ).obj F).obj)
    (hcut : B.cutoff ≤ A.cutoff)
    (hisos : ComparisonsAreIso hZ (inclusionActionSquares h) (@a) b F)
    (hmates : MatchesComparisons hZ (inclusionActionSquares h) (@a) b F β α) :
    MatesAreIso h (@a) F ∧
      AgreesWithMates h (@a) β (datumOfAbove hcut α)
        (((a (closedInclusion Z)).rightAdjointUniq b).inv.app F).hom := by
  let i := closedInclusion Z
  let τ := (a i).rightAdjointUniq b
  have mate (k : ℕ) (hk : max A.cutoff B.cutoff ≤ k) :
      let H := J.group k
      let iH := parameterInclusion H i
      let hx := (le_max_left A.cutoff B.cutoff).trans hk
      let hz := (le_max_right A.cutoff B.cutoff).trans hk
      actionComparison hZ (inclusionActionSquares h) (@a) b F k hk =
        (boundedBelowInverseImage (A.action k hx).act).map (τ.inv.app F) ≫
          directImageComparison (h k hz hx) (a iH) (a i) F ∧
      projectionComparison hZ (@a) b F H =
        (boundedBelowInverseImage (projection H X)).map (τ.inv.app F) ≫
          directImageComparison (projectionSquare H i) (a iH) (a i) F := by
    intro H iH hx hz
    exact ⟨mateChangeRightAdjoint (pullbackSquare (h k hz hx)) (a iH) (a i) b F,
      mateChangeRightAdjoint (pullbackSquare (projectionSquare H i)) (a iH) (a i) b F⟩
  constructor
  · intro k hz hx
    let hk : max A.cutoff B.cutoff ≤ k := max_le hx hz
    let H := J.group k
    let iH := parameterInclusion H i
    obtain ⟨ha, hp⟩ := mate k hk
    obtain ⟨hA, hP⟩ := hisos k hk
    rw [ha] at hA
    rw [hp] at hP
    let := hA
    let := hP
    exact ⟨IsIso.of_isIso_comp_left ((boundedBelowInverseImage (A.action k hx).act).map (τ.inv.app F))
        (directImageComparison (h k hz hx) (a iH) (a i) F),
      IsIso.of_isIso_comp_left ((boundedBelowInverseImage (projection H X)).map (τ.inv.app F))
        (directImageComparison (projectionSquare H i) (a iH) (a i) F)⟩
  · intro k hz hx
    let hk : max A.cutoff B.cutoff ≤ k := max_le hx hz
    let H := J.group k
    let iH := parameterInclusion H i
    exact mateEquationChangeRightAdjoint (h k hz hx) (projectionSquare H i)
      (a iH) (a i) b F (α.datum k hk).iso.hom
      (ObjectProperty.homMk (β.datum k hz).iso.hom) (hmates k hk)

end PointExtension

section LocalSplitting

private theorem intertwinesOfActionEq {H : AnalyticGroup.{0}} {X : TopCat.{0}}
    {A A' : AnalyticAction H X} (h : A.act = A'.act)
    {F G : Derived X} {α : A.Equivariance F} {β : A.Equivariance G}
    {α' : A'.Equivariance F} {β' : A'.Equivariance G} {f : F ⟶ G}
    (hα : α.iso.hom = eqToHom (congrArg (fun p => (derivedInverseImage p).obj F) h) ≫ α'.iso.hom)
    (hβ : β.iso.hom = eqToHom (congrArg (fun p => (derivedInverseImage p).obj G) h) ≫ β'.iso.hom)
    (hf : ConvolutionEquivariantSplittingSpecs.Intertwines α' β' f) :
    ConvolutionEquivariantSplittingSpecs.Intertwines α β f := by
  obtain rfl := analyticAction_ext h
  simp only [eqToHom_refl, Category.id_comp] at hα hβ
  unfold ConvolutionEquivariantSplittingSpecs.Intertwines at hf ⊢
  rwa [hα, hβ]

private theorem intertwinesInverse {H : AnalyticGroup.{0}} {X : TopCat.{0}}
    {A : AnalyticAction H X} {F G : Derived X} {α : A.Equivariance F}
    {β : A.Equivariance G} (e : F ≅ G) (h : ConvolutionEquivariantSplittingSpecs.Intertwines α β e.hom) :
    ConvolutionEquivariantSplittingSpecs.Intertwines β α e.inv := by
  unfold ConvolutionEquivariantSplittingSpecs.Intertwines at h ⊢
  have hh := congrArg (fun v => (derivedInverseImage A.act).map e.inv ≫ v ≫
    (derivedInverseImage (projection H X)).map e.inv) h
  simp only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
    Iso.inv_hom_id, Iso.hom_inv_id] at hh
  rw [(derivedInverseImage A.act).map_id G, (derivedInverseImage (projection H X)).map_id F,
    Category.id_comp, Category.comp_id] at hh
  exact hh.symm

end LocalSplitting

/-- The local scalar model and the equivariance of the fixed splitting. -/
theorem minusculeLocalSquare : Expected.MinusculeLocalSquare := by
  intro c a d terminalBound B D β T b scalarBound C P E hE γ hγ
  let F := point d.point
  let Y := PointSpace d.point
  let A := T.action
  let S := trivialJetAction (jetSystem c) Y 1
  let η := trivialJetDatum (jetSystem c) Y 1 F.obj
  obtain ⟨e, L, hL, hcoordinates, hsingleton⟩ := scalarModel d.point scalarBound
  let : Subsingleton (SchubertSpace scalarPair 2 scalarBound) := hsingleton
  have hmodel : EquivariantIntersectionComplexesSpecs.Intertwines S C.action e.hom :=
    fun _ _ _ ↦ TopCat.ext (fun _ ↦ Subsingleton.elim _ _)
  obtain ⟨v, hv⟩ := scalarCoefficients (@a) d.point C hE γ hγ e hmodel
  have hpoint := pointInclusionCommutes (d := d) A T.cutoff T.actsAtTwo
  have hcut : S.cutoff ≤ A.cutoff := T.cutoff.ge
  obtain ⟨hmateIso, ξ, hmate⟩ := EquivariantIntersectionComplexes.closedExtensionCompatibility
    (jetSystem c) d.closed A S (inclusionActionSquares hpoint) (@a) b F η
  let δ := datumOfAbove hcut ξ
  have hδ : (δ.datum 1 T.cutoff.le).iso.hom =
      eqToHom (congrArg (fun f => (derivedInverseImage f).obj (pointSkyscraper d.point d.closed))
        T.actsAtTwo) ≫ d.pointEq.iso.hom :=
    pointAtTwo d T.actsAtTwo (δ.datum 1 T.cutoff.le)
  let θ := datumFromLevel T.cutoff (changeActionDatum T.actsAtTwo d.convolutionEq)
  have hθ : (θ.datum 1 T.cutoff.le).iso.hom =
      eqToHom (congrArg (fun f => (derivedInverseImage f).obj convolution.obj) T.actsAtTwo) ≫
        d.convolutionEq.iso.hom := by
    exact (datumFromLevel_hom T.cutoff _).trans (changeActionDatum_hom _ _)
  obtain ⟨hDirectIso, hDirect⟩ :=
    transferPointMates d.closed A S hpoint (@a) b F η ξ hcut hmateIso hmate
  have hsection := intertwinesFromLevel δ θ T.cutoff
    (intertwinesOfActionEq T.actsAtTwo hδ hθ d.section_equivariant)
  have hunit := intertwinesFromLevel T.constantDatum θ T.cutoff
    (intertwinesOfActionEq T.actsAtTwo T.constantAtTwo hθ d.unit_equivariant)
  refine ⟨{
    pointAction := S
    pointCutoff := rfl
    pointActs := fun _ _ ↦ rfl
    pointDatum := η
    pointCoefficients := fun _ _ ↦ rfl
    model := e
    lattice := fun _ ↦ L
    latticeScalar := fun _ ↦ hL
    modelCoordinates := hcoordinates
    modelAction := hmodel
    modelIdentification := v
    modelIntertwines := hv
    convolutionDatum := θ
    convolutionAtTwo := hθ
    skyscraperDatum := δ
    skyscraperAtTwo := hδ
    pointInclusionAction := hpoint
    exactExtensionMates := ?_
    directImageMatesAreIso := hDirectIso
    directImageMates := hDirect
    sectionIntertwines := hsection
    unitIntertwines := ?_ }⟩
  · intro k hp ht
    exact hmate k (max_le ht hp)
  · intro k hk
    have hi := intertwinesInverse T.constantIdentification (T.constantIntertwines k hk)
    have hu := hunit k hk
    unfold ConvolutionEquivariantSplittingSpecs.Intertwines at hi hu ⊢
    simp only [Functor.map_comp, Category.assoc, hu, reassoc_of% hi]

end RepTheorySurvey.Geometric.MinusculeLocalSquare
