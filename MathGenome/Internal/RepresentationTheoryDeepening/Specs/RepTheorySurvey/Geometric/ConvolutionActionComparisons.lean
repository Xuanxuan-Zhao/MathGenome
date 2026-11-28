import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionUnitCone
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.MiddleExtension

noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated

namespace RepTheorySurvey.Geometric.ConvolutionActionComparisonsSpecs

open Analytic ConvolutionUnitConeSpecs
open IntersectionComplex (shiftedConstant directImageComparison boundedBelowPullbackComposition)
open AnalyticAction (Parameters projection)

/-- The continuous product of the identity on the parameter space and the terminal map. -/
def productMap (T : TopCat.{0}) : TopCat.of (T × ordered) ⟶ TopCat.of (T × surface) :=
  TopCat.ofHom ⟨fun p => (p.1, convolutionMap p.2),
    continuous_fst.prodMk (convolutionMap.hom.continuous.comp continuous_snd)⟩

def productProjection (T Z : TopCat.{0}) : TopCat.of (T × Z) ⟶ Z :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

theorem projectionSquare (T : TopCat.{0}) :
    productMap T ≫ productProjection T surface =
      productProjection T ordered ≫ convolutionMap :=
  TopCat.ext (fun _ => rfl)

/-- The continuous change of coordinates that turns the action into the projection. -/
def actionTwist {H : AnalyticGroup.{0}} {Z : TopCat.{0}} (A : AnalyticAction H Z) :
    Parameters H Z ≃ₜ Parameters H Z where
  toFun p := (p.1, A.act p)
  invFun p := (p.1, A.act (p.1⁻¹, p.2))
  left_inv p := by
    change (p.1, A.act (p.1⁻¹, A.act p)) = p
    rw [← A.mul_act, inv_mul_cancel, A.one_act]
  right_inv p := by
    change (p.1, A.act (p.1, A.act (p.1⁻¹, p.2))) = p
    rw [← A.mul_act, mul_inv_cancel, A.one_act]
  continuous_toFun := continuous_fst.prodMk A.act.hom.continuous
  continuous_invFun := continuous_fst.prodMk
    (A.act.hom.continuous.comp ((continuous_inv.comp continuous_fst).prodMk continuous_snd))

abbrev twistMap {H : AnalyticGroup.{0}} {Z : TopCat.{0}} (A : AnalyticAction H Z) :
    Parameters H Z ⟶ Parameters H Z :=
  TopCat.ofHom ⟨actionTwist A, (actionTwist A).continuous⟩

theorem twist_projection {H : AnalyticGroup.{0}} {Z : TopCat.{0}} (A : AnalyticAction H Z) :
    twistMap A ≫ projection H Z = A.act :=
  TopCat.ext (fun _ => rfl)

/-- Commutation of the two analytic actions with the actual terminal map. -/
def Commutes {H : AnalyticGroup.{0}} (A : AnalyticAction H surface)
    (B : AnalyticAction H ordered) : Prop :=
  ∀ (h : H.space) (y : ordered), convolutionMap (B.act (h, y)) = A.act (h, convolutionMap y)

theorem actionSquare {H : AnalyticGroup.{0}} {A : AnalyticAction H surface}
    {B : AnalyticAction H ordered} (h : Commutes A B) :
    productMap H.space ≫ A.act = B.act ≫ convolutionMap :=
  TopCat.ext (fun p => (h p.1 p.2).symm)

theorem twistSquare {H : AnalyticGroup.{0}} {A : AnalyticAction H surface}
    {B : AnalyticAction H ordered} (h : Commutes A B) :
    productMap H.space ≫ twistMap A = twistMap B ≫ productMap H.space :=
  TopCat.ext (fun p => Prod.ext rfl (h p.1 p.2).symm)

abbrev DerivedAdjunction {Y X : TopCat.{0}} (m : Y ⟶ X) :=
  boundedBelowInverseImage m ⊣ derivedDirectImage m

/-- The ordinary cochain unit followed by the right derivation map computes
the unit of the chosen derived adjunction. -/
def IsDerivedDirectAdjunction {Y X : TopCat.{0}} (m : Y ⟶ X)
    (a : DerivedAdjunction m) : Prop :=
  let L := inverseImage m
  let R := directImage m
  ∀ K : CochainComplex.Plus (Sheaves X),
    let comparison : (boundedBelowInverseImage m).obj (DerivedCategory.Plus.Q.obj K) ⟶
        DerivedCategory.Plus.Q.obj (L.mapCochainComplexPlus.obj K) :=
      DerivedCategory.Plus.ι.preimage (L.mapDerivedCategoryFactors.hom.app K.obj)
    a.unit.app (DerivedCategory.Plus.Q.obj K) ≫ (derivedDirectImage m).map comparison =
      DerivedCategory.Plus.Q.map ((inverseDirectAdjunction m).unit.mapCochainComplexPlus.app K) ≫
        R.rightDerivedFunctorPlusUnit.app (L.mapCochainComplexPlus.obj K)

abbrev productFactor (T : TopCat.{0}) := shiftedConstant (TopCat.of (T × ordered)) 2

abbrev productConvolution (T : TopCat.{0}) :=
  (derivedDirectImage (productMap T)).obj (productFactor T)

/-- Apply the same single-degree construction as for the convolution unit to the product map. -/
def productUnit (T : TopCat.{0}) :
    (shiftedConstant (TopCat.of (T × surface)) 2).obj ⟶ (productConvolution T).obj :=
  (coefficientShiftIso (TopCat.of (T × surface)) 2).inv.hom ≫
    derivedConstantUnit (productMap T) (-2) ≫
    ((derivedDirectImage (productMap T)).map
      (coefficientShiftIso (TopCat.of (T × ordered)) 2).hom).hom

abbrev projectionMate (T : TopCat.{0}) (a : DerivedAdjunction (productMap T))
    (b : DerivedAdjunction convolutionMap) :=
  directImageComparison (projectionSquare T) a b orderedFactor

abbrev actionMate {H : AnalyticGroup.{0}} {A : AnalyticAction H surface}
    {B : AnalyticAction H ordered} (h : Commutes A B)
    (a : DerivedAdjunction (productMap H.space)) (b : DerivedAdjunction convolutionMap) :=
  directImageComparison (actionSquare h) a b orderedFactor

/-- The projection mate with the pulled-back coefficient complex identified on the source. -/
def projectionComparison (T : TopCat.{0}) (a : DerivedAdjunction (productMap T))
    (b : DerivedAdjunction convolutionMap) :
    (derivedInverseImage (productProjection T surface)).obj convolution.obj ⟶
      (productConvolution T).obj :=
  (projectionMate T a b).hom ≫
    ((derivedDirectImage (productMap T)).map
      (ObjectProperty.homMk (shiftedConstantPullback (productProjection T ordered) 2).hom)).hom

/-- The action mate with the pulled-back coefficient complex identified on the source. -/
def actionComparison {H : AnalyticGroup.{0}} {A : AnalyticAction H surface}
    {B : AnalyticAction H ordered} (h : Commutes A B)
    (a : DerivedAdjunction (productMap H.space)) (b : DerivedAdjunction convolutionMap) :
    (derivedInverseImage A.act).obj convolution.obj ⟶ (productConvolution H.space).obj :=
  (actionMate h a b).hom ≫
    ((derivedDirectImage (productMap H.space)).map
      (ObjectProperty.homMk (shiftedConstantPullback B.act 2).hom)).hom

def MatePasting {H : AnalyticGroup.{0}} {A : AnalyticAction H surface}
    {B : AnalyticAction H ordered} (h : Commutes A B)
    (a : DerivedAdjunction (productMap H.space)) (b : DerivedAdjunction convolutionMap) : Prop :=
  let q := projection H ordered
  let p := projection H surface
  (boundedBelowPullbackComposition (twistMap A) p).hom.app convolution ≫
      (boundedBelowInverseImage (twistMap A)).map (projectionMate H.space a b) ≫
      directImageComparison (twistSquare h) a a ((boundedBelowInverseImage q).obj orderedFactor) =
    eqToHom (congrArg (fun f => (boundedBelowInverseImage f).obj convolution)
      (twist_projection A)) ≫ actionMate h a b ≫
      (derivedDirectImage (productMap H.space)).map
        (eqToHom (congrArg (fun f => (boundedBelowInverseImage f).obj orderedFactor)
          (twist_projection B).symm) ≫
          (boundedBelowPullbackComposition (twistMap B) q).hom.app orderedFactor)

def parameterMap {K H : AnalyticGroup.{0}} (φ : K.space →* H.space)
    (hφ : Continuous φ) (Z : TopCat.{0}) : Parameters K Z ⟶ Parameters H Z :=
  TopCat.ofHom ⟨fun p => (φ p.1, p.2), (hφ.comp continuous_fst).prodMk continuous_snd⟩

def restrictAction {K H : AnalyticGroup.{0}} {Z : TopCat.{0}} (φ : K.space →* H.space)
    (hφ : Continuous φ) (A : AnalyticAction H Z) : AnalyticAction K Z where
  act := parameterMap φ hφ Z ≫ A.act
  one_act z := by
    change A.act (φ 1, z) = z
    rw [map_one, A.one_act]
  mul_act g h z := by
    change A.act (φ (g * h), z) = A.act (φ g, A.act (φ h, z))
    rw [map_mul, A.mul_act]

theorem restrict_commutes {K H : AnalyticGroup.{0}} {A : AnalyticAction H surface}
    {B : AnalyticAction H ordered} (h : Commutes A B) (φ : K.space →* H.space)
    (hφ : Continuous φ) : Commutes (restrictAction φ hφ A) (restrictAction φ hφ B) :=
  fun k y => h (φ k) y

namespace Expected

/-- Pasting gives the invertible action mate and the normalized datum with its
identity and multiplication laws. Both coefficient comparisons preserve the
actual unit, and the projection comparison identifies its distinguished triangle. -/
def ActionTransport : Prop :=
  ∀ {H : AnalyticGroup.{0}} {A : AnalyticAction H surface} {B : AnalyticAction H ordered}
    (h : Commutes A B)
    (a : DerivedAdjunction (productMap H.space)) (b : DerivedAdjunction convolutionMap)
    (a₂ : DerivedAdjunction (productMap (TopCat.of (H.space × H.space)))),
    IsDerivedDirectAdjunction (productMap H.space) a →
    IsDerivedDirectAdjunction convolutionMap b →
    IsDerivedDirectAdjunction (productMap (TopCat.of (H.space × H.space))) a₂ →
    IsIso (projectionMate H.space a b) →
    IsIso (projectionMate (TopCat.of (H.space × H.space)) a₂ b) →
    MatePasting h a b ∧ IsIso (actionMate h a b) ∧
    ∃ α : A.Equivariance convolution.obj,
      α.iso.hom ≫ projectionComparison H.space a b = actionComparison h a b ∧
      (derivedInverseImage A.act).map unit ≫ actionComparison h a b =
        (shiftedConstantPullback A.act 2).hom ≫ productUnit H.space ∧
      (derivedInverseImage A.act).map unit ≫ α.iso.hom =
        (shiftedConstantPullback A.act 2 ≪≫
          (shiftedConstantPullback (projection H surface) 2).symm).hom ≫
          (derivedInverseImage (projection H surface)).map unit ∧
      let p := projection H surface
      letI : (derivedInverseImage p).CommShift ℤ :=
        inferInstanceAs (((inverseImage p).mapDerivedCategory).CommShift ℤ)
      ∃ (C : Derived (Parameters H surface)) (v : (productConvolution H.space).obj ⟶ C)
        (δ : C ⟶ (shiftedConstant (Parameters H surface) 2).obj⟦(1 : ℤ)⟧)
        (e : (derivedInverseImage p).mapTriangle.obj unitTriangle ≅
          Triangle.mk (productUnit H.space) v δ),
        Triangle.mk (productUnit H.space) v δ ∈ distTriang (Derived (Parameters H surface)) ∧
        e.hom.hom₁ = (shiftedConstantPullback p 2).hom ∧
        e.hom.hom₂ = projectionComparison H.space a b ∧
        (derivedInverseImage p).map unit ≫ projectionComparison H.space a b =
          (shiftedConstantPullback p 2).hom ≫ productUnit H.space

/-- Restriction along a continuous group homomorphism carries the normalized
mate description at the larger parameter group to the one at its source. -/
def ParameterTransport : Prop :=
  ∀ {K H : AnalyticGroup.{0}} {A : AnalyticAction H surface} {B : AnalyticAction H ordered}
    (h : Commutes A B) (φ : K.space →* H.space) (hφ : Continuous φ)
    (a : DerivedAdjunction (productMap H.space)) (a' : DerivedAdjunction (productMap K.space))
    (b : DerivedAdjunction convolutionMap)
    (α : A.Equivariance convolution.obj),
    IsDerivedDirectAdjunction (productMap H.space) a →
    IsDerivedDirectAdjunction (productMap K.space) a' →
    IsDerivedDirectAdjunction convolutionMap b →
    IsIso (projectionMate H.space a b) →
    IsIso (projectionMate K.space a' b) →
    α.iso.hom ≫ projectionComparison H.space a b = actionComparison h a b →
    ∃ α' : (restrictAction φ hφ A).Equivariance convolution.obj,
      α'.iso.hom ≫ projectionComparison K.space a' b =
        actionComparison (restrict_commutes h φ hφ) a' b ∧
      pullbackMorphism (parameterMap φ hφ surface) rfl
        (show parameterMap φ hφ surface ≫ projection H surface = projection K surface from
          TopCat.ext (fun _ => rfl)) α.iso.hom = α'.iso.hom

end Expected
end RepTheorySurvey.Geometric.ConvolutionActionComparisonsSpecs
