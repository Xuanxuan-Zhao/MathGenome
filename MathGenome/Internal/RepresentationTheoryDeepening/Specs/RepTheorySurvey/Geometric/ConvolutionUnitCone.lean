import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TransverseCone
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConstantSheafComparison
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionAnalyticCharts
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionFrameQuotient
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionConstantDescent
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionUnitLocality
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.ComplexProjectiveHomology

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace Topology
open LinearAlgebraicGroups (Points)

namespace RepTheorySurvey.Geometric.ConvolutionUnitConeSpecs

open Analytic LocalSheaf
open LatticeModelSpecs BoundedLatticeSpecs MinusculeAndTwoStepSpecs ConvolutionBundleSpecs
open ConvolutionSurfaceSpecs TransverseConeSpecs NilpotentConeChartSpecs

export ConvolutionAnalyticChartsSpecs (surfacePointTopology surface ordered)
export ConvolutionFrameQuotientSpecs (minuscule FrameRepresentative representativeSpace Jets
  constantJetLinear twoTermJetLinear)
export ConvolutionConstantDescentSpec (scalars constantAdj constantPullback shiftedConstantPullback
  pulledBackTensor shiftedTensor MultipliesCoefficients NormalizedCoefficients)
export ConvolutionUnitLocalitySpecs (coefficientComplex)

attribute [instance] ConvolutionAnalyticChartsSpecs.surfacePointTopology

/-- Analytification of the actual terminal-lattice projection. -/
def convolutionMap : ordered ⟶ surface :=
  TopCat.ofHom ⟨fun q => q ≫ terminalProjection, by
    apply continuous_induced_rng.mpr
    exact continuous_snd.comp (show Continuous incidenceCoordinates from continuous_induced_dom)⟩

/-- Analytification of the first-lattice projection. -/
def firstStageMap : ordered ⟶ minuscule :=
  TopCat.ofHom ⟨fun q => q ≫ firstProjection,
    continuous_fst.comp (show Continuous incidenceCoordinates from continuous_induced_dom)⟩

/-- The derived unit with the adjunction identification of pulled-back constants. -/
abbrev derivedConstantUnit {Y X : TopCat.{u}} (m : Y ⟶ X) (n : ℤ) :=
  ConvolutionUnitLocalitySpecs.derivedConstantUnit m n (constantPullback m)

/-- The constant coefficient complex for each minuscule factor. -/
abbrev minusculeFactor : BoundedBelow minuscule := IntersectionComplex.shiftedConstant minuscule 1

/-- The constant coefficient model on the ordered surface. -/
abbrev orderedFactor : BoundedBelow ordered := IntersectionComplex.shiftedConstant ordered 2

/-- The direct image of the descended shifted coefficient model. -/
abbrev convolution : BoundedBelow surface :=
  (derivedDirectImage convolutionMap).obj orderedFactor

/-- Single degree `-d` and degree-zero shifted by `d` are the same
normalization, via the comparison for single complexes. -/
def coefficientShiftIso (Z : TopCat.{u}) (d : ℕ) :
    DerivedCategory.Plus.Q.obj (coefficientComplex Z (-(d : ℤ))) ≅
      IntersectionComplex.shiftedConstant Z d := by
  apply DerivedCategory.Plus.ι.preimageIso
  exact ((DerivedCategory.singleFunctors (Sheaves Z)).shiftIso
    (d : ℤ) (-(d : ℤ)) 0 (add_neg_cancel _)).app (rational Z) |>.symm

/-- The specific shifted derived unit whose cone is split in the next result. -/
def unit : (IntersectionComplex.shiftedConstant surface 2).obj ⟶ convolution.obj :=
  (coefficientShiftIso surface 2).inv.hom ≫ derivedConstantUnit convolutionMap (-2) ≫
    ((derivedDirectImage convolutionMap).map (coefficientShiftIso ordered 2).hom).hom

private theorem unitCocone :
    ∃ (C : Derived surface) (v : convolution.obj ⟶ C)
      (δ : C ⟶ (IntersectionComplex.shiftedConstant surface 2).obj⟦(1 : ℤ)⟧),
      Triangle.mk unit v δ ∈ distTriang (Derived surface) :=
  distinguished_cocone_triangle unit

/-- A fixed completion of the actual unit to a distinguished triangle.
The first two objects and the first arrow are fixed before choosing its cone. -/
def unitTriangle : Triangle (Derived surface) :=
  Triangle.mk unit (Classical.choose unitCocone.choose_spec)
    (Classical.choose (Classical.choose_spec unitCocone.choose_spec))

abbrev unitCone : Derived surface := unitTriangle.obj₃

/-- The constant object on the closed point pushed to the Schubert surface. -/
abbrev pointSkyscraper (x : surface) (hx : IsClosed ({x} : Set surface)) : Derived surface :=
  (closedExtension hx).obj (IntersectionComplex.point x).obj

abbrev stalkCohomology (x : surface) (n : ℤ) :=
  Analytic.cohomology surface n ⋙ stalk x

/-- The stalk of the convolution at the exceptional point, with the specified shift. -/
def StalkProfile (x : surface) : Prop :=
  (∀ (n : ℤ), (n = -2 ∨ n = 0) →
    Nonempty ((stalkCohomology x n).obj convolution.obj ≅ scalars)) ∧
  (∀ (n : ℤ), n ≠ -2 → n ≠ 0 → IsZero ((stalkCohomology x n).obj convolution.obj)) ∧
  IsIso ((stalkCohomology x (-2)).map unit)

/-- Concentration and the skyscraper identification for the chosen cone of the unit.
The identification with its degree-zero cohomology induces the identity there
via the ordinary comparison for a single object. -/
def ConeProfile (x : surface) (hx : IsClosed ({x} : Set surface)) : Prop :=
  unitTriangle ∈ distTriang (Derived surface) ∧
  (∀ (n : ℤ), n ≠ 0 → IsZero ((Analytic.cohomology surface n).obj unitCone)) ∧
  let H := (Analytic.cohomology surface 0).obj unitCone
  SupportedOn ({x} : Set surface) H ∧
  (∃ e : unitCone ≅ (DerivedCategory.singleFunctor (Sheaves surface) 0).obj H,
    (Analytic.cohomology surface 0).map e.hom ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (Sheaves surface) 0).hom.app H =
        𝟙 H) ∧
  Nonempty (unitCone ≅ pointSkyscraper x hx)

def jetGroup (h : IsTopologicalGroup Jets) : AnalyticGroup where
  space := TopCat.of Jets
  topologicalGroup := h

/-- The exterior square on the actual twisted product descends through the
quotient by first-lattice basis change. On representatives its comparison is
the pullback of the degree-two model followed by the tensor comparison.
The factor and ordered-space data use their actual jet actions and the
normalized coefficient identifications. The tensor compatibilities are
specified in `Expected.EquivariantTwistedExteriorDescent`. -/
def TwistedExteriorDescent : Prop :=
  ∃ (h : StableStage (PositiveGL 2) (colength 1))
    (e : OrderedProduct h ≃ ordered)
    (b : representativeSpace ⟶ minuscule)
    (q : representativeSpace ⟶ ordered),
    IsQuotientMap q ∧
    (∀ p : FrameRepresentative,
      q p = e (Quotient.mk (twistRel (PositiveGL 2) firstStage (colength 1)) p) ∧
      firstPlane (firstStageMap (q p)) =
        (latticeSubspace 0 1 (p.val.1 • standardLattice 2)).map constantCoordinates.toLinearMap ∧
      firstPlane (b p) =
        (latticeSubspace 0 1 p.val.2).map constantCoordinates.toLinearMap ∧
      secondPlane (convolutionMap (q p)) =
        (latticeSubspace 0 2 (p.val.1 • p.val.2)).map twoStepCoordinates.toLinearMap) ∧
    let a := q ≫ firstStageMap
    (∃ (μ : pulledBackTensor a b ≅ rational representativeSpace)
      (d : (derivedInverseImage q).obj orderedFactor.obj ≅ shiftedTensor a b),
      let μ₂ : shiftedTensor a b ≅ (IntersectionComplex.shiftedConstant representativeSpace 2).obj :=
        (shiftFunctor (Derived representativeSpace) (2 : ℤ)).mapIso
          ((DerivedCategory.singleFunctor (Sheaves representativeSpace) 0).mapIso μ)
      MultipliesCoefficients a b μ ∧ d ≪≫ μ₂ = shiftedConstantPullback q 2 ∧
      ∀ (W : TopCat) (k : W ⟶ representativeSpace),
        (derivedInverseImageComposition k q).hom.app orderedFactor.obj ≫
          (derivedInverseImage k).map (d.hom ≫ μ₂.hom) ≫
          (shiftedConstantPullback k 2).hom =
        (shiftedConstantPullback (k ≫ q) 2).hom) ∧
    ∃ (hH : IsTopologicalGroup Jets)
      (A₁ : AnalyticAction (jetGroup hH) minuscule)
      (A₂ : AnalyticAction (jetGroup hH) ordered),
      (∀ g : Jets, ∀ p : ProjectivePoints,
        firstPlane (A₁.act (g, p)) = (firstPlane p).map (constantJetLinear g)) ∧
      (∀ g : Jets, ∀ p : ordered,
        firstStageMap (A₂.act (g, p)) = A₁.act (g, firstStageMap p) ∧
        secondPlane (convolutionMap (A₂.act (g, p))) =
          (secondPlane (convolutionMap p)).map (twoTermJetLinear g)) ∧
      NormalizedCoefficients A₁ 1 ∧ NormalizedCoefficients A₂ 2

section FrameDescent

open MonoidalCategory
open ConvolutionConstantDescentSpec (tensorPresheaf coefficientTensor)
open AnalyticAction (projection)
open scoped Matrix MatrixGroups TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

private def tensorPresheafIso {Z : TopCat} {F F' G G' : Sheaves Z}
    (f : F ≅ F') (g : G ≅ G') : tensorPresheaf F G ≅ tensorPresheaf F' G' :=
  let P := sheafToPresheaf (Opens.grothendieckTopology Z) Coeff.{0}
  NatIso.ofComponents (fun U => tensorIso ((P.mapIso f).app U) ((P.mapIso g).app U)) (by
    intro U V i
    change (_ ⊗ₘ _) ≫ (f.hom.hom.app V ⊗ₘ g.hom.hom.app V) =
      (f.hom.hom.app U ⊗ₘ g.hom.hom.app U) ≫ (_ ⊗ₘ _)
    have h := congrArg₂ (fun v w => v ⊗ₘ w) (f.hom.hom.naturality i) (g.hom.hom.naturality i)
    simpa only [tensorHom_comp_tensorHom] using h)

/-- On sheafified tensors this is induced by tensoring the two given maps on sections. -/
def coefficientTensorIso {Z : TopCat} {F F' G G' : Sheaves Z}
    (f : F ≅ F') (g : G ≅ G') : coefficientTensor F G ≅ coefficientTensor F' G' :=
  (presheafToSheaf (Opens.grothendieckTopology Z) Coeff.{0}).mapIso (tensorPresheafIso f g)

private abbrev sectionTensorUnit {Z : TopCat} (F G : Sheaves Z) :=
  (sheafificationAdjunction (Opens.grothendieckTopology Z) Coeff.{0}).unit.app (tensorPresheaf F G)

/-- The comparison on the two pullbacks of a rational coefficient sheaf. -/
def coefficientTransition {W X : TopCat} (f g : W ⟶ X) :
    (inverseImage f).obj (rational X) ≅ (inverseImage g).obj (rational X) :=
  constantPullback f ≪≫ (constantPullback g).symm

private def compositionUnit {W Z X : TopCat} (k : W ⟶ Z) (a : Z ⟶ X) :
    (inverseImage a).obj (rational X) ⟶
      (directImage k).obj ((inverseImage (k ≫ a)).obj (rational X)) :=
  (inverseDirectAdjunction k).homEquiv _ _ ((inverseImageComposition k a).inv.app (rational X))

private def pulledTensorSections {W Z X Y : TopCat} (k : W ⟶ Z) (a : Z ⟶ X) (b : Z ⟶ Y) :
    tensorPresheaf ((inverseImage a).obj (rational X)) ((inverseImage b).obj (rational Y)) ⟶
      ((directImage k).obj (pulledBackTensor (k ≫ a) (k ≫ b))).obj where
  app U := ((compositionUnit k a).hom.app U ⊗ₘ (compositionUnit k b).hom.app U) ≫
    (sectionTensorUnit ((inverseImage (k ≫ a)).obj (rational X))
      ((inverseImage (k ≫ b)).obj (rational Y))).app ((Opens.map k).op.obj U)
  naturality U V i := by
    let η := sectionTensorUnit ((inverseImage (k ≫ a)).obj (rational X))
      ((inverseImage (k ≫ b)).obj (rational Y))
    have hn := η.naturality ((Opens.map k).op.map i)
    change (_ ⊗ₘ _) ≫ η.app ((Opens.map k).op.obj V) =
      η.app ((Opens.map k).op.obj U) ≫
        ((directImage k).obj (pulledBackTensor (k ≫ a) (k ≫ b))).obj.map i at hn
    change (_ ⊗ₘ _) ≫ ((_ ⊗ₘ _) ≫ η.app _) = ((_ ⊗ₘ _) ≫ η.app _) ≫ _
    rw [Category.assoc, ← hn]
    have ha := (compositionUnit k a).hom.naturality i
    have hb := (compositionUnit k b).hom.naturality i
    have h := congrArg₂ (fun v w => v ⊗ₘ w) ha hb
    have ht := (tensorHom_comp_tensorHom _ _ _ _).trans
      (h.trans (tensorHom_comp_tensorHom _ _ _ _).symm)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ η.app ((Opens.map k).op.obj V)) ht).trans (Category.assoc _ _ _))

/-- The canonical pullback map of the sheafified tensor. The two adjunctions
send it to the tensor of the factor units on sections over each open. -/
def pullbackTensorMap {W Z X Y : TopCat} (k : W ⟶ Z) (a : Z ⟶ X) (b : Z ⟶ Y) :
    (inverseImage k).obj (pulledBackTensor a b) ⟶ pulledBackTensor (k ≫ a) (k ≫ b) :=
  ((inverseDirectAdjunction k).homEquiv (pulledBackTensor a b)
    (pulledBackTensor (k ≫ a) (k ≫ b))).symm
    (((sheafificationAdjunction (Opens.grothendieckTopology Z) Coeff.{0}).homEquiv
      (tensorPresheaf ((inverseImage a).obj (rational X)) ((inverseImage b).obj (rational Y)))
      ((directImage k).obj (pulledBackTensor (k ≫ a) (k ≫ b)))).symm
        (pulledTensorSections k a b))

/-- Place an ordinary sheaf in degree zero and then shift it. -/
abbrev singleShift (Z : TopCat) (d : ℕ) : Sheaves Z ⥤ Derived Z :=
  DerivedCategory.singleFunctor (Sheaves Z) 0 ⋙ shiftFunctor (Derived Z) (d : ℤ)

/-- Exact inverse image commutes with the single complex and the ordinary shift. -/
def shiftedSinglePullback {W Z : TopCat} (k : W ⟶ Z) (d : ℕ) :
    singleShift Z d ⋙ derivedInverseImage k ≅ inverseImage k ⋙ singleShift W d := by
  let F := inverseImage k
  let P := DerivedCategory.singleFunctor (Sheaves Z) 0
  let Q := DerivedCategory.singleFunctor (Sheaves W) 0
  let T := shiftFunctor (Derived W) (d : ℤ)
  let i : P ⋙ (shiftFunctor (Derived Z) (d : ℤ) ⋙ F.mapDerivedCategory) ≅
      (P ⋙ F.mapDerivedCategory) ⋙ T :=
    Functor.isoWhiskerLeft P (F.mapDerivedCategory.commShiftIso (d : ℤ))
  let j : (P ⋙ F.mapDerivedCategory) ⋙ T ≅ (F ⋙ Q) ⋙ T :=
    Functor.isoWhiskerRight (F.mapDerivedCategorySingleFunctor 0) T
  exact i ≪≫ j

/-- Tensor the two underlying maps of coefficient sheaves and take the total shift. -/
def shiftedTensorTransition {W X Y : TopCat} (a a' : W ⟶ X) (b b' : W ⟶ Y) :
    shiftedTensor a b ≅ shiftedTensor a' b' :=
  (singleShift W 2).mapIso
    (coefficientTensorIso (coefficientTransition a a') (coefficientTransition b b'))

def shiftedCoefficientTransition {W X : TopCat} (f g : W ⟶ X) (d : ℕ) :
    (derivedInverseImage f).obj (IntersectionComplex.shiftedConstant X d).obj ≅
      (derivedInverseImage g).obj (IntersectionComplex.shiftedConstant X d).obj :=
  shiftedConstantPullback f d ≪≫ (shiftedConstantPullback g d).symm

/-- The pullback of the descent comparison using the shifted tensor map. -/
def pullbackDescentMap {W Z X Y : TopCat} (k : W ⟶ Z)
    (a : Z ⟶ X) (b : Z ⟶ Y) (q : Z ⟶ ordered)
    (d : (derivedInverseImage q).obj orderedFactor.obj ≅ shiftedTensor a b) :
    (derivedInverseImage (k ≫ q)).obj orderedFactor.obj ⟶ shiftedTensor (k ≫ a) (k ≫ b) :=
  (derivedInverseImageComposition k q).hom.app orderedFactor.obj ≫
    (derivedInverseImage k).map d.hom ≫
    (shiftedSinglePullback k 2).hom.app (pulledBackTensor a b) ≫
    (singleShift W 2).map (pullbackTensorMap k a b)

abbrev FrameBasis := GL (Fin 2) O

def frameJet : FrameBasis →* Jets := reduceGL 2 2 (by decide)

/-- Positive loop parameters on a frame representative, with the two-jet
topology used by the action on the lattice windows. -/
structure FrameParameters where
  basis : FrameBasis
  representative : FrameRepresentative

instance : TopologicalSpace FrameParameters :=
  .induced (fun z => (frameJet z.basis, z.representative)) inferInstance

abbrev frameParameters : TopCat := TopCat.of FrameParameters

private theorem continuous_frameParameters :
    Continuous (fun z : FrameParameters => (frameJet z.basis, z.representative)) :=
  continuous_induced_dom

def frameProjection : frameParameters ⟶ representativeSpace :=
  TopCat.ofHom ⟨FrameParameters.representative, continuous_snd.comp continuous_frameParameters⟩

def frameActionParameter {X : TopCat} (f : representativeSpace ⟶ X) :
    frameParameters ⟶ TopCat.of (Jets × X) :=
  TopCat.ofHom ⟨fun z => (frameJet z.basis, f z.representative),
    (continuous_fst.comp continuous_frameParameters).prodMk
      (f.hom.continuous.comp (continuous_snd.comp continuous_frameParameters))⟩

def inverseFrameActionParameter (hG : IsTopologicalGroup Jets) {X : TopCat}
    (f : representativeSpace ⟶ X) : frameParameters ⟶ TopCat.of (Jets × X) := by
  let := hG
  exact TopCat.ofHom ⟨fun z => ((frameJet z.basis)⁻¹, f z.representative),
    (continuous_fst.comp continuous_frameParameters).inv.prodMk
      (f.hom.continuous.comp (continuous_snd.comp continuous_frameParameters))⟩

/-- Display a map of unshifted factors as a map between the pullbacks of the
single complexes in the minuscule normalization. -/
def shiftedFactorIso {W X : TopCat} (f g : W ⟶ X)
    (v : (inverseImage f).obj (rational X) ≅ (inverseImage g).obj (rational X)) :
    (derivedInverseImage f).obj (IntersectionComplex.shiftedConstant X 1).obj ≅
      (derivedInverseImage g).obj (IntersectionComplex.shiftedConstant X 1).obj :=
  (shiftedSinglePullback f 1).app (rational X) ≪≫
    (singleShift W 1).mapIso v ≪≫ ((shiftedSinglePullback g 1).app (rational X)).symm

/-- The tensor comparison on the actual frame overlaps, together with the
two positive-loop comparisons. The right change of basis acts on the relative
second line, and the left action acts on the first line and the quotient. -/
structure FrameDescentCompatibility
    (q : representativeSpace ⟶ ordered) (b : representativeSpace ⟶ minuscule)
    {hG : IsTopologicalGroup Jets}
    (A₁ : AnalyticAction (jetGroup hG) minuscule) (A₂ : AnalyticAction (jetGroup hG) ordered)
    (right left : frameParameters ⟶ representativeSpace)
    (E₁ : A₁.Equivariance minusculeFactor.obj) (E₂ : A₂.Equivariance orderedFactor.obj)
    (d : (derivedInverseImage q).obj orderedFactor.obj ≅ shiftedTensor (q ≫ firstStageMap) b)
    : Prop where
  basis_change : ∀ z : FrameParameters,
    (right z).val.1 = z.representative.val.1 * positiveGLMap 2 z.basis ∧
      (right z).val.2 = positiveGLMap 2 z.basis⁻¹ • z.representative.val.2
  left_multiplication : ∀ z : FrameParameters,
    (left z).val = (positiveGLMap 2 z.basis * z.representative.val.1, z.representative.val.2)
  covers_overlaps : ∀ p p' : FrameRepresentative,
    q p' = q p ↔ ∃ g : FrameBasis, right ⟨g, p⟩ = p'
  covers_jet_parameters : Function.Surjective (frameActionParameter q)
  right_quotient : right ≫ q = frameProjection ≫ q
  right_second : inverseFrameActionParameter hG b ≫ A₁.act = right ≫ b
  left_first : frameActionParameter (q ≫ firstStageMap) ≫ A₁.act =
    left ≫ (q ≫ firstStageMap)
  left_second : left ≫ b = frameProjection ≫ b
  left_quotient : frameActionParameter q ≫ A₂.act = left ≫ q
  right_first_coefficients :
    (coefficientTransition (right ≫ (q ≫ firstStageMap))
      (frameProjection ≫ (q ≫ firstStageMap))).hom =
        eqToHom (congrArg (fun f => (inverseImage f).obj (rational minuscule))
          (congrArg (· ≫ firstStageMap) right_quotient))
  right_second_coefficients :
    pullbackMorphism (inverseFrameActionParameter hG b) right_second rfl E₁.iso.hom =
      (shiftedFactorIso (right ≫ b) (frameProjection ≫ b)
        (coefficientTransition (right ≫ b) (frameProjection ≫ b))).hom
  left_first_coefficients :
    let a := q ≫ firstStageMap
    pullbackMorphism (frameActionParameter a) left_first rfl E₁.iso.hom =
      (shiftedFactorIso (left ≫ a) (frameProjection ≫ a)
        (coefficientTransition (left ≫ a) (frameProjection ≫ a))).hom
  left_second_coefficients :
    (coefficientTransition (left ≫ b) (frameProjection ≫ b)).hom =
      eqToHom (congrArg (fun f => (inverseImage f).obj (rational minuscule)) left_second)
  tensor_pullback_isIso :
    ∀ (W : TopCat) (k : W ⟶ representativeSpace),
      IsIso (pullbackTensorMap k (q ≫ firstStageMap) b)
  /-- The two projections from the fibre product give the descent square.
  The right basis change specializes this square via `right_quotient` and the
  two right coefficient comparisons. -/
  on_overlaps :
    let a := q ≫ firstStageMap
    ∀ (W : TopCat) (k₁ k₀ : W ⟶ representativeSpace) (hk : k₁ ≫ q = k₀ ≫ q),
      pullbackDescentMap k₁ a b q d ≫
        (shiftedTensorTransition (k₁ ≫ a) (k₀ ≫ a) (k₁ ≫ b) (k₀ ≫ b)).hom =
          eqToHom (congrArg (fun f => (derivedInverseImage f).obj orderedFactor.obj) hk) ≫
            pullbackDescentMap k₀ a b q d
  intertwines_ordered_action :
    let a := q ≫ firstStageMap
    let k₁ := left
    let k₀ := frameProjection
    pullbackDescentMap k₁ a b q d ≫
      (shiftedTensorTransition (k₁ ≫ a) (k₀ ≫ a) (k₁ ≫ b) (k₀ ≫ b)).hom =
        pullbackMorphism (frameActionParameter q) left_quotient rfl E₂.iso.hom ≫
          pullbackDescentMap k₀ a b q d

end FrameDescent

open P202Specs.CohomologyPairs in
/-- Rational singular cohomology with its ordinary pullback maps. -/
abbrev singularCohomology (n : ℤ) : TopCatᵒᵖ ⥤ Coeff.{0} :=
  ordinaryCohomologyFunctor ℚ Analytic.SingularCochains.Values.{0} n

abbrev projectiveLine : TopCat := TopCat.of (P202.ComplexProjective.Space 1)

/-- The complex projective line is compared with the first-stage space by
identifying each point with its actual homogeneous line. -/
def ProjectiveLineModel : Prop :=
  ∃ e : projectiveLine ≃ₜ minuscule,
    (∀ l : P202.ComplexProjective.Space 1, firstPlane (e l) = l.submodule) ∧
    (∀ n : ℤ, (n = 0 ∨ n = 2) →
      Nonempty ((singularCohomology n).obj (op projectiveLine) ≅ scalars)) ∧
    (∀ n : ℤ, n ≠ 0 → n ≠ 2 → IsZero ((singularCohomology n).obj (op projectiveLine)))

/-- The radial basis used for the stalk calculation consists of the same balls
in the transverse cone. The pullbacks to the closed fibre along the section
compute singular cohomology, so these maps commute with shrinking the balls. -/
def RadialFibreComparison (x : surface) : Prop :=
  ∃ (c : coneScheme ⟶ twoStepScheme) (s : projectiveScheme ⟶ incidenceScheme)
    (B : ∀ r : ℝ, 0 < r → Opens surface),
    IsTerminalConeChart c ∧ ExceptionalSection x s ∧ conePoint coneVertex ≫ c = x ∧
    (∀ (r : ℝ) (hr : 0 < r),
      x ∈ B r hr ∧ (B r hr : Set surface) =
        (fun z => conePoint z ≫ c) '' coneBall .radial r) ∧
    (∀ U : Opens surface, x ∈ U → ∃ (r : ℝ) (hr : 0 < r), B r hr ≤ U) ∧
    ∃ j : ∀ (r : ℝ) (hr : 0 < r),
      minuscule ⟶ TopCat.of ((Opens.map convolutionMap).obj (B r hr)),
      ∀ (r : ℝ) (hr : 0 < r),
        let Z := TopCat.of ((Opens.map convolutionMap).obj (B r hr))
        (∀ p : ProjectivePoints, (j r hr p).val = p ≫ s) ∧
        SecondCountableTopology Z ∧ LocallyCompactSpace Z ∧ T2Space Z ∧
        Analytic.SingularCochains.HasContractibleOpenBasis Z ∧
        ∀ n : ℤ, IsIso ((singularCohomology n).map (j r hr).op)

/-- The actual derived unit restricts to an isomorphism on the open orbit. -/
def OpenUnit (x : surface) (hx : IsClosed ({x} : Set surface)) : Prop :=
  let U := complementOpen {x} hx
  IsIso ((derivedInverseImage (openInclusion U)).map unit)

namespace Expected

open AnalyticAction (projection)

/-- Equivariant descent for the two normalized minuscule coefficient sheaves.
The isomorphism on representatives is compatible with the tensor maps induced
by basis change and with the normalized equivariance on the ordered space. -/
def EquivariantTwistedExteriorDescent : Prop :=
  ∃ (h : StableStage (PositiveGL 2) (colength 1))
    (e : OrderedProduct h ≃ ordered)
    (b : representativeSpace ⟶ minuscule) (q : representativeSpace ⟶ ordered),
    IsQuotientMap q ∧
    (∀ p : FrameRepresentative,
        q p = e (Quotient.mk (twistRel (PositiveGL 2) firstStage (colength 1)) p) ∧
        firstPlane (firstStageMap (q p)) =
          (latticeSubspace 0 1 (p.val.1 • standardLattice 2)).map constantCoordinates.toLinearMap ∧
        firstPlane (b p) = (latticeSubspace 0 1 p.val.2).map constantCoordinates.toLinearMap ∧
        secondPlane (convolutionMap (q p)) =
          (latticeSubspace 0 2 (p.val.1 • p.val.2)).map twoStepCoordinates.toLinearMap) ∧
    ∃ (μ : pulledBackTensor (q ≫ firstStageMap) b ≅ rational representativeSpace)
      (d : (derivedInverseImage q).obj orderedFactor.obj ≅ shiftedTensor (q ≫ firstStageMap) b),
      MultipliesCoefficients (q ≫ firstStageMap) b μ ∧
      d ≪≫ (singleShift representativeSpace 2).mapIso μ = shiftedConstantPullback q 2 ∧
      ∃ (hG : IsTopologicalGroup Jets)
        (A₁ : AnalyticAction (jetGroup hG) minuscule) (A₂ : AnalyticAction (jetGroup hG) ordered)
        (_ : ∀ (g : Jets) (p : ProjectivePoints),
          firstPlane (A₁.act (g, p)) = (firstPlane p).map (constantJetLinear g))
        (_ : ∀ (g : Jets) (p : ordered),
          firstStageMap (A₂.act (g, p)) = A₁.act (g, firstStageMap p) ∧
          secondPlane (convolutionMap (A₂.act (g, p))) =
            (secondPlane (convolutionMap p)).map (twoTermJetLinear g))
        (E₁ : A₁.Equivariance minusculeFactor.obj) (E₂ : A₂.Equivariance orderedFactor.obj)
        (right left : frameParameters ⟶ representativeSpace),
        E₁.iso = shiftedCoefficientTransition A₁.act (projection (jetGroup hG) minuscule) 1 ∧
        E₂.iso = shiftedCoefficientTransition A₂.act (projection (jetGroup hG) ordered) 2 ∧
        FrameDescentCompatibility q b A₁ A₂ right left E₁ E₂ d

/-- The normalized twisted exterior square, the stalks of its pushforward, and
the skyscraper cone of the pullback-pushforward unit for the two-step surface. -/
def ConvolutionUnitCone : Prop :=
  TwistedExteriorDescent ∧ ProjectiveLineModel ∧
    ∃ (x : surface) (hx : IsClosed ({x} : Set surface)),
      ScalarTerminalPoint x ∧ RadialFibreComparison x ∧ OpenUnit x hx ∧
      StalkProfile x ∧ ConeProfile x hx

end Expected
end RepTheorySurvey.Geometric.ConvolutionUnitConeSpecs
