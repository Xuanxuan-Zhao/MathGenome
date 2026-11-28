import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionUnitCone

noncomputable section

open CategoryTheory

namespace RepTheorySurvey.Geometric.ConvolutionPointCoefficientsSpecs

open Analytic AnalyticAction ConvolutionUnitConeSpecs
open ConvolutionSurfaceSpecs (ScalarTerminalPoint)

/-- The ordinary skyscraper whose single complex is the closed orbit summand. -/
abbrev pointSheaf (x : surface) : Sheaves surface :=
  (directImage (closedInclusion ({x} : Set surface))).obj
    (rational (TopCat.of ({x} : Set surface)))

/-- Any subspace mapping to the scalar point has a unique map to its singleton. -/
def toPoint {Y : TopCat.{0}} (W : Set Y) (x : surface) :
    TopCat.of W ⟶ TopCat.of ({x} : Set surface) :=
  TopCat.ofHom ⟨fun _ => ⟨x, rfl⟩, continuous_const⟩

/-- The mate of restriction to the closed preimage, followed by the counit on the
point and the canonical comparison of rational constant sheaves. -/
def ordinaryPointPullback {Y : TopCat.{0}} {f : Y ⟶ surface} {W : Set Y} {x : surface}
    (h : closedInclusion W ≫ f = toPoint W x ≫ closedInclusion ({x} : Set surface)) :
    (inverseImage f).obj (pointSheaf x) ⟶
      (directImage (closedInclusion W)).obj (rational (TopCat.of W)) :=
  let i := closedInclusion ({x} : Set surface)
  let j := closedInclusion W
  let r := toPoint W x
  let Q := rational (TopCat.of ({x} : Set surface))
  ((inverseDirectAdjunction j).homEquiv ((inverseImage f).obj (pointSheaf x))
    (rational (TopCat.of W)))
    ((inverseImageComposition j f).inv.app (pointSheaf x) ≫
      eqToHom (congrArg (fun k => (inverseImage k).obj (pointSheaf x)) h) ≫
      (inverseImageComposition r i).hom.app (pointSheaf x) ≫
      (inverseImage r).map ((inverseDirectAdjunction i).counit.app Q) ≫
      (constantPullback r).hom)

def pointSkyscraperSingle (x : surface) (hx : IsClosed ({x} : Set surface)) :
    pointSkyscraper x hx ≅ (DerivedCategory.singleFunctor (Sheaves surface) 0).obj (pointSheaf x) := by
  letI := (extraordinaryAdjunction hx).isLeftAdjoint
  exact ((directImage (closedInclusion ({x} : Set surface))).mapDerivedCategorySingleFunctor 0).app
    (rational (TopCat.of ({x} : Set surface)))

/-- The same coefficient map in degree zero, through the exact-functor comparisons
of the shared derived category model. -/
def derivedPointPullback {Y : TopCat.{0}} {f : Y ⟶ surface} {W : Set Y} {x : surface}
    (hx : IsClosed ({x} : Set surface))
    (h : closedInclusion W ≫ f = toPoint W x ≫ closedInclusion ({x} : Set surface)) :
    (derivedInverseImage f).obj (pointSkyscraper x hx) ⟶
      (DerivedCategory.singleFunctor (Sheaves Y) 0).obj
        ((directImage (closedInclusion W)).obj (rational (TopCat.of W))) :=
  (derivedInverseImage f).map (pointSkyscraperSingle x hx).hom ≫
    ((inverseImage f).mapDerivedCategorySingleFunctor 0).hom.app (pointSheaf x) ≫
    (DerivedCategory.singleFunctor (Sheaves Y) 0).map (ordinaryPointPullback h)

abbrev productPoint (H : AnalyticGroup.{0}) (x : surface) : Set (H.space × surface) :=
  (Prod.snd : H.space × surface → surface) ⁻¹' ({x} : Set surface)

theorem productPoint_closed (H : AnalyticGroup.{0}) {x : surface}
    (hx : IsClosed ({x} : Set surface)) : IsClosed (productPoint H x) :=
  hx.preimage continuous_snd

theorem projectionPointSquare (H : AnalyticGroup.{0}) (x : surface) :
    closedInclusion (productPoint H x) ≫ projection H surface =
      toPoint (Y := Parameters H surface) (productPoint H x) x ≫ closedInclusion ({x} : Set surface) :=
  TopCat.ext (fun z => z.property)

theorem actionPointSquare {H : AnalyticGroup.{0}} {A : AnalyticAction H surface} {x : surface}
    (fixes : ∀ g : H.space, A.act (g, x) = x) :
    closedInclusion (productPoint H x) ≫ A.act =
      toPoint (Y := Parameters H surface) (productPoint H x) x ≫ closedInclusion ({x} : Set surface) :=
  TopCat.ext (fun z => by
    change A.act z.val = x
    have hz : z.val = (z.val.1, x) := Prod.ext rfl z.property
    exact (congrArg (fun y : H.space × surface => A.act y) hz).trans (fixes z.val.1))

/-- The normalized comparison identifies both pullbacks with the degree-zero
closed extension of the same constant sheaf on the product. Its restriction
to that closed product is the identity under composition of inverse images. -/
def TrivialPointEquivariance {H : AnalyticGroup.{0}} {A : AnalyticAction H surface} {x : surface}
    {hx : IsClosed ({x} : Set surface)} (fixes : ∀ g : H.space, A.act (g, x) = x)
    (α : A.Equivariance (pointSkyscraper x hx)) : Prop :=
  let hp := projectionPointSquare H x
  let ha := actionPointSquare fixes
  α.iso.hom ≫ derivedPointPullback hx hp = derivedPointPullback hx ha ∧
    pullbackMorphism (closedInclusion (productPoint H x)) (ha.trans hp.symm) rfl α.iso.hom = 𝟙 _

/-- Map on parameters for pullback of an action along a continuous group homomorphism. -/
def groupParameterMap {K H : AnalyticGroup.{0}} (φ : K.space →* H.space) (hφ : Continuous φ) :
    Parameters K surface ⟶ Parameters H surface :=
  TopCat.ofHom ⟨fun z => (φ z.1, z.2),
    (hφ.comp continuous_fst).prodMk continuous_snd⟩

theorem groupParameterProjection {K H : AnalyticGroup.{0}} (φ : K.space →* H.space)
    (hφ : Continuous φ) :
    groupParameterMap φ hφ ≫ projection H surface = projection K surface :=
  TopCat.ext (fun _ => rfl)

namespace Expected

def ClosedPointPullback : Prop :=
  ∀ {Y : TopCat.{0}} {f : Y ⟶ surface} {W : Set Y} {x : surface}
    (hx : IsClosed ({x} : Set surface)) (_ : W = f ⁻¹' ({x} : Set surface))
    (h : closedInclusion W ≫ f = toPoint W x ≫ closedInclusion ({x} : Set surface)),
    IsIso (ordinaryPointPullback h) ∧ IsIso (derivedPointPullback hx h)

def TrivialPointCoefficients : Prop :=
  ∀ {H : AnalyticGroup.{0}} (A : AnalyticAction H surface) {x : surface}
    (hx : IsClosed ({x} : Set surface))
    (fixes : ∀ g : H.space, A.act (g, x) = x),
    ∃ α : A.Equivariance (pointSkyscraper x hx), TrivialPointEquivariance fixes α

def PointCoefficientFunctoriality : Prop :=
  ∀ {K H : AnalyticGroup.{0}} {B : AnalyticAction K surface} {A : AnalyticAction H surface}
    {x : surface} {hx : IsClosed ({x} : Set surface)}
    (fixesA : ∀ g : H.space, A.act (g, x) = x)
    (fixesB : ∀ g : K.space, B.act (g, x) = x)
    (φ : K.space →* H.space) (hφ : Continuous φ)
    (h : groupParameterMap φ hφ ≫ A.act = B.act)
    {α : A.Equivariance (pointSkyscraper x hx)} {β : B.Equivariance (pointSkyscraper x hx)},
    TrivialPointEquivariance fixesA α → TrivialPointEquivariance fixesB β →
    pullbackMorphism (groupParameterMap φ hφ) h (groupParameterProjection φ hφ) α.iso.hom =
      β.iso.hom

/-- A normalized comparison of the two pullbacks over the actual two-jet group
has no freedom on the rational line at the scalar terminal point. -/
def TwoJetPointUniqueness : Prop :=
  ∀ (hH : IsTopologicalGroup Jets) {A : AnalyticAction (jetGroup hH) surface}
    {x : surface} {hx : IsClosed ({x} : Set surface)} (_ : ScalarTerminalPoint x)
    (fixes : ∀ g : Jets, A.act (g, x) = x)
    {α : A.Equivariance (pointSkyscraper x hx)},
    TrivialPointEquivariance fixes α →
    ∀ e : (derivedInverseImage A.act).obj (pointSkyscraper x hx) ≅
      (derivedInverseImage (projection (jetGroup hH) surface)).obj (pointSkyscraper x hx),
    pullbackMorphism (identitySection (jetGroup hH) surface)
      (identity_act A) identity_projection e.hom = 𝟙 _ →
    e = α.iso

/-- Once the comparison for the actual cone is normalized, its transport through
the closed-orbit identification is the trivial coefficient comparison. -/
def NormalizedConeComparison : Prop :=
  ∀ (hH : IsTopologicalGroup Jets) {A : AnalyticAction (jetGroup hH) surface}
    {x : surface} {hx : IsClosed ({x} : Set surface)} (_ : ScalarTerminalPoint x)
    (fixes : ∀ g : Jets, A.act (g, x) = x)
    {α : A.Equivariance (pointSkyscraper x hx)},
    TrivialPointEquivariance fixes α →
    ∀ (c : unitCone ≅ pointSkyscraper x hx)
      (e : (derivedInverseImage A.act).obj unitCone ≅
        (derivedInverseImage (projection (jetGroup hH) surface)).obj unitCone),
    pullbackMorphism (identitySection (jetGroup hH) surface)
      (identity_act A) identity_projection e.hom = 𝟙 _ →
    ((derivedInverseImage A.act).mapIso c).symm ≪≫ e ≪≫
      (derivedInverseImage (projection (jetGroup hH) surface)).mapIso c = α.iso

end Expected
end RepTheorySurvey.Geometric.ConvolutionPointCoefficientsSpecs
