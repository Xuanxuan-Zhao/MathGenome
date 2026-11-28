import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.CentralLatticeTranslation
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.FiniteStageClosedExtensions
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.MinusculeConvolutionSquare

noncomputable section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology
open LinearAlgebraicGroups (Points testSpec)
open scoped MatrixGroups

namespace RepTheorySurvey.Geometric.CentralMinusculeRuleSpecs

open LatticeModelSpecs BoundedLatticeSpecs RankTwoSchubertStrataSpecs
open MinusculeAndTwoStepSpecs
open CentralLatticeTranslationSpecs
open MinusculeConvolutionSquareSpecs
open ConvolutionUnitConeSpecs
open ConvolutionFrameQuotientSpecs (FrameRepresentative)
open ConvolutionFrameOverlapSpecs (FrameOverlapIdentification FrameActionIdentification)
open LocalSheaf
open Analytic
open Analytic.IntersectionComplex (DimensionFiltration complex)
open EquivariantIntersectionComplexesSpecs SchubertIntersectionConstructibilitySpecs
open EquivariantHomeomorphismDirectImageSpecs
  (DirectImageIntertwines EquivariantDirectImageComparison)
open FiniteStageClosedExtensionSpecs (SupportIntersections RealizesStages)

/-- The two independently translated Schubert factors use the usual frame relation. -/
abbrev ShiftedOrdered (a b : ℤ) :=
  TwistedProduct (PositiveGL 2) (schubertFirst (shiftPair a minusculePair))
    (closureLattices (shiftPair b minusculePair)) (schubertStable _)

abbrev ShiftedRepresentative (a b : ℤ) :=
  Representatives (PositiveGL 2) (schubertFirst (shiftPair a minusculePair))
    (closureLattices (shiftPair b minusculePair))

abbrev shiftedTerminal (a b : ℤ) :
    ShiftedOrdered a b → GL2Lattice :=
  terminalMap (PositiveGL 2) (schubertStable (shiftPair b minusculePair))

/-- An algebraic and equivariant presentation of a translated normalized IC.
The translated scheme is in an actual occupied symmetric window. The two
pullback comparisons identify the factors with the same normalized ICs that
occur on the original and translated Schubert models. -/
structure TranslatedIC {c : ContinuousJets} {ab : DominantPair} {Y : TopCat.{0}}
    {A : JetAction (jetSystem c) Y} {F : BoundedBelow Y} {α : A.Equivariance F.obj}
    (C : ICComparison ab A F α) (s : ℤ) where
  bound : ℕ
  bounded : OrbitBound (shiftPair s ab) bound
  translation : SchubertTranslationData s ab 2 bound C.bound bounded
  targetAction : SchubertJetAction c (shiftPair s ab) bound bounded
  commutes : JetMapsCommute C.action targetAction.action translation.analyticIso.hom
  stratification : Stratification (SchubertSpace (shiftPair s ab) bound bounded)
  filtration : DimensionFiltration (SchubertSpace (shiftPair s ab) bound bounded)
    (orbitDimension (shiftPair s ab) (difference (shiftPair s ab) / 2))
  isIC : IsNormalizedOrbitIC (shiftPair s ab) bound bounded (𝟙 _)
    (difference (shiftPair s ab) / 2) stratification filtration
  datum : targetAction.action.Equivariance (complex filtration).obj
  normalized : NormalizedICDatum C.adjunctions targetAction.action filtration datum
  comparison : (complex C.filtration).obj ≅
    (derivedInverseImage translation.analyticIso.hom).obj (complex filtration).obj
  intertwines : IntertwinesPullback commutes C.datum datum comparison.hom
  composedCommutes : JetMapsCommute A targetAction.action (C.model.hom ≫ translation.analyticIso.hom)
  composedIntertwines : IntertwinesPullback composedCommutes α datum
    (C.comparison.hom ≫ (derivedInverseImage C.model.hom).map comparison.hom ≫
      (derivedInverseImageComposition C.model.hom translation.analyticIso.hom).inv.app
        (complex filtration).obj)
  directImage : EquivariantDirectImageComparison C.adjunctions A targetAction.action
    (C.model.hom ≫ translation.analyticIso.hom) composedCommutes F α (complex filtration) datum
  onCoordinates : ∀ y : Y,
    schubertPointSubspace (translation.analyticIso.hom (C.model.hom y)) =
      latticeSubspace (-(bound : ℤ)) (2 * bound) (translate s (C.lattice y).val)

/-- The translated flag diagram presented in the original jet coordinates.
The first coordinate is shifted by `a`, the frame-relative second
modification by `b`, and the terminal lattice by `a + b`. -/
structure TranslatedFlags {c : ContinuousJets} (S : LocalSquare c) (a b : ℤ) where
  frames : FrameRepresentative ≃ ShiftedRepresentative a b
  onFrames : ∀ p, (frames p).val =
    (scalarLoop a * p.val.1, translate b p.val.2)
  quotient : ShiftedOrdered a b ≃ ordered
  relative : representativeSpace ⟶ minuscule
  projection : representativeSpace ⟶ ordered
  quotientTopology : IsQuotientMap projection
  onQuotient : ∀ p : FrameRepresentative,
    projection p = quotient (Quotient.mk _ (frames p))
  coefficients :
    let x := projection ≫ firstStageMap
    ∃ (μ : pulledBackTensor x relative ≅ rational representativeSpace)
      (d : (derivedInverseImage projection).obj orderedFactor.obj ≅ shiftedTensor x relative),
      let μ₂ := (shiftFunctor (Derived representativeSpace) (2 : ℤ)).mapIso
        ((DerivedCategory.singleFunctor (Sheaves representativeSpace) 0).mapIso μ)
      MultipliesCoefficients x relative μ ∧ d ≪≫ μ₂ = shiftedConstantPullback projection 2 ∧
      FrameOverlapIdentification S.splitting.firstEq projection relative d ∧
      FrameActionIdentification S.splitting.firstEq S.splitting.orderedEq projection relative d
  firstLattice : ∀ p : FrameRepresentative,
    (S.minusculeIC.lattice (firstStageMap (projection p))).val =
      p.val.1 • standardLattice 2
  relativeLattice : ∀ p : FrameRepresentative,
    (S.minusculeIC.lattice (relative p)).val = p.val.2
  terminalLattice : ∀ p : ShiftedOrdered a b,
    shiftedTerminal a b p = translate (a + b)
      (S.twoStepIC.lattice (convolutionMap (quotient p))).val

/-- In the common frame coordinates the two exterior factors pull back from
the first translated lattice and the translated relative modification. -/
def TranslatedFactorMaps {c : ContinuousJets} (S : LocalSquare c) {a b : ℤ}
    (A : TranslatedIC S.minusculeIC a) (B : TranslatedIC S.minusculeIC b)
    (F : TranslatedFlags S a b) : Prop :=
  let f := firstStageMap ≫ S.minusculeIC.model.hom ≫ A.translation.analyticIso.hom
  let g := F.relative ≫ S.minusculeIC.model.hom ≫ B.translation.analyticIso.hom
  Nonempty ((singleShift representativeSpace 1).obj
    ((inverseImage (F.projection ≫ firstStageMap)).obj (rational minuscule)) ≅
    (derivedInverseImage (F.projection ≫ f)).obj (complex A.filtration).obj) ∧
  Nonempty ((singleShift representativeSpace 1).obj
    ((inverseImage F.relative).obj (rational minuscule)) ≅
    (derivedInverseImage g).obj (complex B.filtration).obj) ∧
  ∀ p : FrameRepresentative,
    schubertPointSubspace (f (F.projection p)) =
      latticeSubspace (-(A.bound : ℤ)) (2 * A.bound) ((F.frames p).val.1 • standardLattice 2) ∧
    schubertPointSubspace (g p) =
      latticeSubspace (-(B.bound : ℤ)) (2 * B.bound) (F.frames p).val.2

/-- The normalized comparison on a local model, with both pullbacks composed. -/
def TranslatedIC.localIso {c : ContinuousJets} {ab : DominantPair} {Y : TopCat.{0}}
    {A : JetAction (jetSystem c) Y} {F : BoundedBelow Y} {α : A.Equivariance F.obj}
    {C : ICComparison ab A F α} {s : ℤ} (K : TranslatedIC C s) :
    F.obj ≅ (derivedInverseImage (C.model.hom ≫ K.translation.analyticIso.hom)).obj
      (complex K.filtration).obj :=
  C.comparison ≪≫ (derivedInverseImage C.model.hom).mapIso K.comparison ≪≫
    ((derivedInverseImageComposition C.model.hom K.translation.analyticIso.hom).app
      (complex K.filtration).obj).symm

def pullbackAlong {W X Y : TopCat.{0}} {i : X ⟶ Y} {F : Derived X} {G : Derived Y}
    (u : F ≅ (derivedInverseImage i).obj G) (f : W ⟶ X) :
    (derivedInverseImage f).obj F ≅ (derivedInverseImage (f ≫ i)).obj G :=
  (derivedInverseImage f).mapIso u ≪≫ ((derivedInverseImageComposition f i).app G).symm

open ConvolutionFrameOverlapSpecs
  (pullbackFactorIso shiftedSingleMap tensorMap leftLeg rightLeg
    overlap commonImage quotientTransition orderedTransition)
open ClosedEquivarianceExtensionSpecs (parameterInclusion)
open AnalyticAction (Parameters)

/-- The degree minus one presentation of the actual translated IC pulled back
along a frame coordinate, or along a further map into the frame space. -/
def translatedFactorIso {c : ContinuousJets} {S : LocalSquare c} {s : ℤ}
    (K : TranslatedIC S.minusculeIC s) {W : TopCat.{0}} (f : W ⟶ minuscule) :=
  (pullbackFactorIso f 1).symm ≪≫ pullbackAlong K.localIso f

def TranslatedFactorTransition {c : ContinuousJets} {S : LocalSquare c} {s : ℤ}
    (K : TranslatedIC S.minusculeIC s) {W : TopCat.{0}} {f₁ f₀ : W ⟶ minuscule}
    (e : (inverseImage f₁).obj (rational minuscule) ⟶
      (inverseImage f₀).obj (rational minuscule))
    (u : (derivedInverseImage (f₁ ≫ S.minusculeIC.model.hom ≫
      K.translation.analyticIso.hom)).obj (complex K.filtration).obj ⟶
      (derivedInverseImage (f₀ ≫ S.minusculeIC.model.hom ≫
      K.translation.analyticIso.hom)).obj (complex K.filtration).obj) : Prop :=
  (translatedFactorIso K f₁).hom ≫ u =
    shiftedSingleMap 1 e ≫ (translatedFactorIso K f₀).hom

/-- At the two-jet level the arrow on the coefficient is the pullback of the
normalized translated IC equivariance along the same group parameter. -/
def TranslatedActionTransition {c : ContinuousJets} {S : LocalSquare c} {s : ℤ}
    (K : TranslatedIC S.minusculeIC s) {W : TopCat.{0}} {f₁ f₀ : W ⟶ minuscule}
    (γ : W ⟶ Parameters ((jetSystem c).group 1) minuscule)
    (_h₁ : γ ≫ S.splitting.firstAction.act = f₁)
    (_h₀ : γ ≫ AnalyticAction.projection ((jetSystem c).group 1) minuscule = f₀)
    (e : (inverseImage f₁).obj (rational minuscule) ⟶
      (inverseImage f₀).obj (rational minuscule)) : Prop :=
  let H := (jetSystem c).group 1
  let v := S.minusculeIC.model.hom ≫ K.translation.analyticIso.hom
  ∃ (hk : K.targetAction.action.cutoff ≤ 1)
    (ht : (γ ≫ parameterInclusion H v) ≫ (K.targetAction.action.action 1 hk).act = f₁ ≫ v)
    (hp : (γ ≫ parameterInclusion H v) ≫ AnalyticAction.projection H _ = f₀ ≫ v),
    TranslatedFactorTransition K e
      (pullbackMorphism (γ ≫ parameterInclusion H v) ht hp (K.datum.datum 1 hk).iso.hom)

/-- Equality of the two lattice maps contributes the identity comparison on
the unchanged translated IC factor. -/
def TranslatedUnchangedFactor {c : ContinuousJets} {S : LocalSquare c} {s : ℤ}
    (K : TranslatedIC S.minusculeIC s) {W : TopCat.{0}} {f₁ f₀ : W ⟶ minuscule}
    (h : f₁ = f₀) : Prop :=
  let v := S.minusculeIC.model.hom ≫ K.translation.analyticIso.hom
  TranslatedFactorTransition K
    (eqToHom (congrArg (fun f ↦ (inverseImage f).obj (rational minuscule)) h))
    (eqToHom (congrArg (fun f ↦ (derivedInverseImage (f ≫ v)).obj (complex K.filtration).obj) h))

/-- The tensor of the two normalized translated IC pullbacks, written using
their degree minus one presentations, descends to orderedFactor.
Both equations use the same descent comparison and the actual shifted frames. -/
def TranslatedTensorDescent {c : ContinuousJets} (S : LocalSquare c) {a b : ℤ}
    (A : TranslatedIC S.minusculeIC a) (B : TranslatedIC S.minusculeIC b)
    (F : TranslatedFlags S a b) : Prop :=
  let q := F.projection
  let x := q ≫ firstStageMap
  let y := F.relative
  let H := (jetSystem c).group 1
  ∃ (d : (derivedInverseImage q).obj orderedFactor.obj ≅ shiftedTensor x y),
    (let r₀ := leftLeg q
     let r₁ := rightLeg q
     let hx : r₁ ≫ x = r₀ ≫ x := by simp only [x, ← Category.assoc, r₀, r₁, commonImage]
     ∃ (γ : overlap q ⟶ Parameters H minuscule)
       (h₁ : γ ≫ S.splitting.firstAction.act = r₁ ≫ y)
       (h₀ : γ ≫ AnalyticAction.projection H minuscule = r₀ ≫ y),
       (∀ w : overlap q, ∃ g : GL (Fin 2) O,
         (F.frames (r₁ w)).val.1 = (F.frames (r₀ w)).val.1 * positiveGLMap 2 g ∧
         (F.frames (r₁ w)).val.2 = positiveGLMap 2 g⁻¹ • (F.frames (r₀ w)).val.2 ∧
         constantJetLinear (γ w).1 = constantJetLinear (reduceGL 2 2 (by decide) g⁻¹)) ∧
       IsIso (ConvolutionFrameOverlapSpecs.pullbackTensorMap r₁ x y) ∧ IsIso (ConvolutionFrameOverlapSpecs.pullbackTensorMap r₀ x y) ∧
       ∃ (e₂ : (inverseImage (r₁ ≫ y)).obj (rational minuscule) ⟶
           (inverseImage (r₀ ≫ y)).obj (rational minuscule)),
         TranslatedUnchangedFactor A hx ∧ TranslatedActionTransition B γ h₁ h₀ e₂ ∧
         let e₁ := eqToHom (congrArg (fun f ↦ (inverseImage f).obj (rational minuscule)) hx)
         ConvolutionFrameOverlapSpecs.pullbackTensorMap r₁ x y ≫ shiftedSingleMap 2 (tensorMap e₁ e₂) =
           quotientTransition d (commonImage q) ≫ ConvolutionFrameOverlapSpecs.pullbackTensorMap r₀ x y) ∧
    (let W := Parameters H representativeSpace
     let r₀ := AnalyticAction.projection H representativeSpace
     let γ₁ : W ⟶ Parameters H minuscule := parameterInclusion H x
     let γq : W ⟶ Parameters H ordered := parameterInclusion H q
     let h₀ : γ₁ ≫ AnalyticAction.projection H minuscule = r₀ ≫ x :=
       TopCat.ext (fun _ ↦ rfl)
     let hq₀ : γq ≫ AnalyticAction.projection H ordered = r₀ ≫ q :=
       TopCat.ext (fun _ ↦ rfl)
     ∃ (r₁ : W ⟶ representativeSpace)
       (hq₁ : γq ≫ S.splitting.orderedAction.act = r₁ ≫ q)
       (h₁ : γ₁ ≫ S.splitting.firstAction.act = r₁ ≫ x)
       (hy : r₁ ≫ y = r₀ ≫ y),
       (∀ w : W, ∃ g : GL (Fin 2) O,
         reduceGL 2 2 (by decide) g = w.1 ∧
         (F.frames (r₁ w)).val.1 = positiveGLMap 2 g * (F.frames (r₀ w)).val.1 ∧
         (F.frames (r₁ w)).val.2 = (F.frames (r₀ w)).val.2) ∧
       IsIso (ConvolutionFrameOverlapSpecs.pullbackTensorMap r₁ x y) ∧ IsIso (ConvolutionFrameOverlapSpecs.pullbackTensorMap r₀ x y) ∧
       ∃ (e₁ : (inverseImage (r₁ ≫ x)).obj (rational minuscule) ⟶
           (inverseImage (r₀ ≫ x)).obj (rational minuscule)),
         TranslatedActionTransition A γ₁ h₁ h₀ e₁ ∧ TranslatedUnchangedFactor B hy ∧
         let e₂ := eqToHom (congrArg (fun f ↦ (inverseImage f).obj (rational minuscule)) hy)
         ConvolutionFrameOverlapSpecs.pullbackTensorMap r₁ x y ≫ shiftedSingleMap 2 (tensorMap e₁ e₂) =
           orderedTransition S.splitting.orderedEq d γq hq₁ hq₀ ≫ ConvolutionFrameOverlapSpecs.pullbackTensorMap r₀ x y)

/-- The algebraic projection from the translated incidence presentation takes
values in the translated length-two stable window. Its coordinates agree with
the occupied symmetric Schubert window on the actual terminal lattice. -/
def TranslatedTerminalScheme {c : ContinuousJets} (S : LocalSquare c) {a b : ℤ}
    (K : TranslatedIC S.twoStepIC (a + b)) (F : TranslatedFlags S a b) : Prop :=
  ∃ (d : WindowDimension 2 (0 + (a + b)) 2)
    (m : ConvolutionBundleSpecs.incidenceScheme ⟶ windowStableScheme 2 (0 + (a + b)) 2 d),
    d.val = 2 ∧ IsProper m.left ∧
    ∀ p : ShiftedOrdered a b,
      windowSchemeSubspace (F.quotient p ≫ m) =
        latticeSubspace (0 + (a + b)) 2 (shiftedTerminal a b p) ∧
      schubertPointSubspace
        (K.translation.analyticIso.hom (S.twoStepIC.model.hom (convolutionMap (F.quotient p)))) =
        latticeSubspace (-(K.bound : ℤ)) (2 * K.bound) (shiftedTerminal a b p)

/-- Coordinate presentation of the finite closed windows after translation.
The same stage actions act on the translated points through these closed
embeddings. The final two inclusions give the same ind-space topology. -/
structure TranslatedStages {c : ContinuousJets} (D : GrassmannianStages c) (s : ℤ) where
  chart : Gr ≅ Gr
  onLattices : ∀ L, chart.hom L = translate s L
  onInverse : ∀ L, chart.inv L = translate (-s) L
  commutes : ∀ (g : GL (Fin 2) O) (L : Gr),
    chart.hom (positiveGLMap 2 g • L) = positiveGLMap 2 g • chart.hom L
  intoSymmetric : ∀ N, ∃ M, Set.range (D.stages.inclusion N ≫ chart.hom) ⊆ boundedSet M
  fromSymmetric : ∀ N, ∃ M, boundedSet N ⊆ Set.range (D.stages.inclusion M ≫ chart.hom)

/-- The finite-stage inclusion in the actual translated Grassmannian. Its
domain is a chart of the shifted closed subspace. -/
abbrev TranslatedStages.inclusion {c : ContinuousJets} {D : GrassmannianStages c} {s : ℤ}
    (T : TranslatedStages D s) (n : ℕ) : D.stages.space n ⟶ Gr :=
  D.stages.inclusion n ≫ T.chart.hom

/-- The shifted stages in chart coordinates carry the actual positive-loop
actions and the orbit stratifications with their original dimensions. -/
def TranslatedStageGeometry {c : ContinuousJets} {D : GrassmannianStages c} {s : ℤ}
    (T : TranslatedStages D s) : Prop :=
  (∀ n, IsClosedEmbedding (T.inclusion n)) ∧
  (∀ {n m : ℕ} (h : n ≤ m), D.stages.transition h ≫ T.inclusion m = T.inclusion n) ∧
  (∀ n k (hk : (D.actions.stageAction n).cutoff ≤ k)
    (g : GL (Fin 2) O) (p : D.stages.space n),
    T.inclusion n (((D.actions.stageAction n).action k hk).act
      (reduceGL 2 (k + 1) (Nat.succ_pos k) g, p)) =
      positiveGLMap 2 g • T.inclusion n p) ∧
  ∀ n (i : (D.stratification n).Index),
    ∃ ab : DominantPair,
      Set.range (((D.stratification n).stratum i).inclusion ≫ T.inclusion n) =
        gl2Orbit (shiftPair s ab) ∩ Set.range (T.inclusion n) ∧
      ((D.stratification n).stratum i).complexDimension = difference (shiftPair s ab)

/-- Realization on the Grassmannian of a complex written in the translated
stage coordinates. Pullback by the inverse homeomorphism is direct image
by the translation. -/
abbrev TranslatedStages.realize {c : ContinuousJets} {D : GrassmannianStages c} {s : ℤ}
    (T : TranslatedStages D s) : Derived Gr ⥤ Derived Gr :=
  derivedInverseImage T.chart.inv

/-- Restricting a realized complex to an actual shifted stage gives the
original chart restriction, naturally in the complex. -/
def TranslatedStages.restrictionIso {c : ContinuousJets} {D : GrassmannianStages c} {s : ℤ}
    (T : TranslatedStages D s) (n : ℕ) :
    T.realize ⋙ derivedInverseImage (T.inclusion n) ≅
      derivedInverseImage (D.stages.inclusion n) :=
  (derivedInverseImageComposition (T.inclusion n) T.chart.inv).symm ≪≫
    eqToIso (congrArg derivedInverseImage (by simp [TranslatedStages.inclusion]))

def TranslatedStages.coefficientIso {c : ContinuousJets} {D : GrassmannianStages c} {s : ℤ}
    (T : TranslatedStages D s) (P : D.actions.Object) {F : Derived Gr}
    (i : F ≅ T.realize.obj P.obj) (n : ℕ) :=
  (derivedInverseImage (T.inclusion n)).mapIso i ≪≫ (T.restrictionIso n).app P.obj

/-- The action-to-projection arrow for an actual complex identified with its
presentation in the translated atlas. -/
def TranslatedStages.stageArrow {c : ContinuousJets} {D : GrassmannianStages c} {s : ℤ}
    (T : TranslatedStages D s) (P : D.actions.Object) {F : Derived Gr}
    (i : F ≅ T.realize.obj P.obj) (n k : ℕ) (hk : (D.actions.stageAction n).cutoff ≤ k) :=
  let a := derivedInverseImage ((D.actions.stageAction n).action k hk).act
  let p := derivedInverseImage (AnalyticAction.projection ((jetSystem c).group k) (D.stages.space n))
  let e := T.coefficientIso P i n
  a.map e.hom ≫ ((P.equivariance.datum n).datum k hk).iso.hom ≫ p.map e.inv

/-- An actual map commutes with the realized action and projection arrows
on each shifted stage. -/
def TranslatedStages.Intertwines {c : ContinuousJets} {D : GrassmannianStages c} {s : ℤ}
    (T : TranslatedStages D s) (P Q : D.actions.Object) {F G : Derived Gr}
    (i : F ≅ T.realize.obj P.obj) (j : G ≅ T.realize.obj Q.obj) (f : F ⟶ G) : Prop :=
  ∀ n k (hk : (D.actions.stageAction n).cutoff ≤ k),
    let a := derivedInverseImage ((D.actions.stageAction n).action k hk).act
    let p := derivedInverseImage (AnalyticAction.projection ((jetSystem c).group k) (D.stages.space n))
    let r := derivedInverseImage (T.inclusion n)
    a.map (r.map f) ≫ T.stageArrow Q j n k hk = T.stageArrow P i n k hk ≫ p.map (r.map f)

/-- A shifted equivariant perverse extension, expressed in the atlas of
closed embeddings given by the translation. The chart morphisms are those
of StageJetActions, whose restrictions compare the same jet data across
all stage inclusions. The normalized support is identified by both mates
on each occupied stage. -/
structure TranslatedStageExtension {c : ContinuousJets} {D : GrassmannianStages c} {s : ℤ}
    (T : TranslatedStages D s) {Y : TopCat.{0}} (A : JetAction (jetSystem c) Y)
    (F : BoundedBelow Y) (α : A.Equivariance F.obj) (i : Y ⟶ Gr)
    (sheaf : D.actions.FiniteSupportPerverse D.stratification) where
  ordinary : ((derivedDirectImage i).obj F).obj ≅ T.realize.obj sheaf.obj.obj
  onPerverseStage : ∃ (n : ℕ) (P : MiddlePerverse (D.stratification n))
    (h : DerivedCategory.TStructure.t.plus P.obj),
    Nonempty (((derivedDirectImage (T.inclusion n)).obj ⟨P.obj, h⟩).obj ≅
      T.realize.obj sheaf.obj.obj)
  stagewise : ∀ n, 2 ≤ n →
    ∃ (j : Y ⟶ D.stages.space n) (a : DerivedAdjunctions.{0})
      (e : ((derivedDirectImage j).obj F).obj ≅
        (derivedInverseImage (T.inclusion n)).obj ((derivedDirectImage i).obj F).obj)
      (β : (D.actions.stageAction n).Equivariance
        ((derivedInverseImage (T.inclusion n)).obj ((derivedDirectImage i).obj F).obj)),
      j ≫ T.inclusion n = i ∧
      (∀ k hk, (β.datum k hk).iso.hom = T.stageArrow sheaf.obj ordinary n k hk) ∧
      ExtendsAtStage j a α β e

open ConvolutionActionComparisonsSpecs (Commutes restrictAction restrict_commutes parameterMap)
open ConvolutionEquivariantSplittingSpecs (UsesConvolutionMates)

/-- The normalized convolution arrow after pulling back the acting group
along a continuous homomorphism. -/
def TruncatedConvolutionMates {H K : AnalyticGroup.{0}}
    {A : AnalyticAction H surface} {B : AnalyticAction H ordered}
    (h : Commutes A B) (φ : K.space →* H.space) (hφ : Continuous φ)
    (η : A.Equivariance convolution.obj) : Prop :=
  ∃ η' : (restrictAction φ hφ A).Equivariance convolution.obj,
    UsesConvolutionMates (restrict_commutes h φ hφ) η' ∧
    pullbackMorphism (parameterMap φ hφ surface) rfl
      (TopCat.ext (fun _ ↦ rfl)) η.iso.hom = η'.iso.hom

/-- The terminal support datum agrees with the normalized mates at two jets.
All the higher comparisons are pulled back from that same arrow, along the
actual truncation that also determines the support datum by jet compatibility. -/
def TranslatedConvolutionMates {c : ContinuousJets} (S : LocalSquare c) : Prop :=
  let d := S.splitting
  UsesConvolutionMates d.commutes d.convolutionEq ∧
  (S.convolutionDatum.datum 1 S.terminalCutoff).iso.hom =
    eqToHom (congrArg (fun f ↦ (derivedInverseImage f).obj convolution.obj) S.terminalActs) ≫
      d.convolutionEq.iso.hom ∧
  ∀ k (hk : 1 ≤ k),
    let J := jetSystem c
    let φ : (J.group k).space →* (J.group 1).space := jetTruncation hk
    let hφ : Continuous φ := c.truncation hk
    TruncatedConvolutionMates d.commutes φ hφ d.convolutionEq

/-- The action on the ordered coefficient object is the one used on the
representative space. Its direct image by the terminal map carries the
normalized action and projection comparisons at every common jet level. -/
structure TranslatedConvolutionDatum {c : ContinuousJets} (S : LocalSquare c) where
  action : JetAction (jetSystem c) ordered
  datum : action.Equivariance orderedFactor.obj
  cutoff : action.cutoff = 1
  actsAtTwo : (action.action 1 cutoff.le).act = S.splitting.orderedAction.act
  datumAtTwo : (datum.datum 1 cutoff.le).iso.hom =
    eqToHom (congrArg (fun f ↦ (derivedInverseImage f).obj orderedFactor.obj) actsAtTwo) ≫
      S.splitting.orderedEq.iso.hom
  normalized : ∀ k hk, (datum.datum k hk).iso =
    shiftedConstantPullback (action.action k hk).act 2 ≪≫
      (shiftedConstantPullback (AnalyticAction.projection ((jetSystem c).group k) ordered) 2).symm
  terminalMates : TranslatedConvolutionMates S

/-- The two actual translated normalized ICs are the equivariant coproduct
summands of the convolution in the translated atlas. Its realization uses
the same maps in the ordinary decomposition. -/
def TranslatedExtension {c : ContinuousJets} (D : GrassmannianStages c) (S : LocalSquare c)
    {s : ℤ} (T : TranslatedStages D s)
    (K' : TranslatedIC S.twoStepIC s) (P' : TranslatedIC S.scalarIC s) : Prop :=
  let d := S.splitting
  let i := closedInclusion ({d.point} : Set surface)
  TranslatedStageGeometry T ∧ Nonempty (TranslatedConvolutionDatum S) ∧
  ∃ j₂ : surface ⟶ Gr,
    (∀ p, j₂ p = (S.twoStepIC.lattice p).val) ∧
    let k := (S.twoStepIC.model ≪≫ K'.translation.analyticIso).inv ≫ j₂ ≫ T.chart.hom
    let p := (S.scalarIC.model ≪≫ P'.translation.analyticIso).inv ≫ (i ≫ j₂) ≫ T.chart.hom
    let l := j₂ ≫ T.chart.hom
    IsClosedEmbedding k ∧ IsClosedEmbedding p ∧ IsClosedEmbedding l ∧
    ∃ (K P L : D.actions.FiniteSupportPerverse D.stratification)
      (eK : TranslatedStageExtension T K'.targetAction.action (complex K'.filtration) K'.datum k K)
      (eP : TranslatedStageExtension T P'.targetAction.action (complex P'.filtration) P'.datum p P)
      (eL : TranslatedStageExtension T S.terminalAction convolution S.convolutionDatum l L)
      (e : ((derivedDirectImage (convolutionMap ≫ l)).obj orderedFactor).obj ≅
        ((derivedDirectImage l).obj convolution).obj)
      (u : K ⟶ L) (v : P ⟶ L),
      Nonempty (IsColimit (BinaryCofan.mk u v)) ∧
      let r := e ≪≫ eL.ordinary
      let f := eK.ordinary.hom ≫ T.realize.map u.hom.hom ≫ r.inv
      let g := eP.ordinary.hom ≫ T.realize.map v.hom.hom ≫ r.inv
      T.Intertwines K.obj L.obj eK.ordinary r f ∧
      T.Intertwines P.obj L.obj eP.ordinary r g ∧
      IsIso (biprod.desc f g)

/-- The right-adjoint composition isomorphism for the terminal map. -/
def centralDirectImageComposition {X Y : TopCat.{0}} (adj : DerivedAdjunctions)
    (f : X ⟶ Y) (i : Y ⟶ Gr) :
    derivedDirectImage (f ≫ i) ≅ derivedDirectImage f ⋙ derivedDirectImage i :=
  let h := ((adj i).comp (adj f)).ofNatIsoLeft
    (Analytic.IntersectionComplex.boundedBelowPullbackComposition f i).symm
  (adj (f ≫ i)).rightAdjointUniq h

/-- The composite terminal comparison is the closed direct image of the
comparison on the ordered Schubert chart. -/
def centralComparisonOnUnion {X Y : TopCat.{0}} (adj : DerivedAdjunctions)
    (f : X ⟶ Y) (i : Y ⟶ Gr) {F : BoundedBelow X} {G : BoundedBelow Y}
    (e : (derivedDirectImage f).obj F ≅ G) :
    (derivedDirectImage (f ≫ i)).obj F ≅ (derivedDirectImage i).obj G :=
  (centralDirectImageComposition adj f i).app F ≪≫ (derivedDirectImage i).mapIso e

/-- The equivariant direct image along the composite is computed using the
right-adjoint composition isomorphism. On the translated Schubert support its
coefficient datum is determined by the mates for the ordered terminal map.
On the Grassmannian both closed images use the same support intersections. -/
def CentralStageTransport {c : ContinuousJets} (D : GrassmannianStages c)
    {X Y : TopCat.{0}} (A : JetAction (jetSystem c) X) (B : JetAction (jetSystem c) Y)
    (adj : DerivedAdjunctions) {f : X ⟶ Y} (i : Y ⟶ Gr) (h : JetMapsCommute A B f)
    {F : BoundedBelow X} {G : BoundedBelow Y}
    (α : A.Equivariance F.obj) (β : B.Equivariance G.obj) (e : (derivedDirectImage f).obj F ≅ G) : Prop :=
  let H := (derivedDirectImage f).obj F
  let C := ((derivedDirectImage (f ≫ i)).obj F).obj
  let K := ((derivedDirectImage i).obj G).obj
  A.cutoff ≤ B.cutoff ∧
  ∃ (θ : B.Equivariance H.obj) (I : SupportIntersections D.actions i B)
    (M : I.LocalEquivariance H θ) (L : I.LocalEquivariance G β)
    (γ' : D.actions.Equivariance ((derivedDirectImage i).obj H).obj)
    (γ : D.actions.Equivariance C) (δ : D.actions.Equivariance K)
    (hC : IsFiniteStagePerverse D.stages D.stratification C)
    (hK : IsFiniteStagePerverse D.stages D.stratification K),
    DirectImageIntertwines adj A B h F α H θ (Iso.refl H) ∧
    RealizesStages I adj M γ' ∧ RealizesStages I adj L δ ∧
    (∃ v : (⟨C, γ⟩ : D.actions.Object) ≅ ⟨((derivedDirectImage i).obj H).obj, γ'⟩,
      v.hom.hom = ((centralDirectImageComposition adj f i).hom.app F).hom) ∧
    (∃ w : (⟨((derivedDirectImage i).obj H).obj, γ'⟩ : D.actions.Object) ≅ ⟨K, δ⟩,
      w.hom.hom = ((derivedDirectImage i).map e.hom).hom) ∧
    let P : D.actions.FiniteSupportPerverse D.stratification := ⟨⟨C, γ⟩, hC⟩
    let Q : D.actions.FiniteSupportPerverse D.stratification := ⟨⟨K, δ⟩, hK⟩
    ∃ u : P ≅ Q, u.hom.hom.hom = (centralComparisonOnUnion adj f i e).hom.hom

/-- For the same local comparisons and ordered charts as in the central
convolution theorem, the terminal map lands in the actual translated Schubert
closure and the comparison extends over the symmetric stages. -/
def CentralPointAllStages : Prop :=
  ∀ c : ContinuousJets, ∃ D : GrassmannianStages c,
    ∀ {a : ℤ} {ab : DominantPair} {N M C : ℕ}
      {hN : OrbitBound ab N} {hM : OrbitBound (shiftPair a ab) M}
      {hC : OrbitBound (centralPair a) C}
      (A : SchubertJetAction c ab N hN) (B : SchubertJetAction c (shiftPair a ab) M hM)
      (T : SchubertTranslationData a ab N M hN hM) (W : OrderedCharts a ab)
      (point : occupiedSchubert (centralPair a) C hC ≅
        (testSpec ℂ).obj (Opposite.op complexAlgebra))
      (S : RealizesOrderedSchemes A T W point)
      (adj : DerivedAdjunctions)
      {P : Stratification (SchubertSpace ab N hN)}
      {Q : Stratification (SchubertSpace (shiftPair a ab) M hM)}
      {F : DimensionFiltration (SchubertSpace ab N hN) (orbitDimension ab (difference ab / 2))}
      {G : DimensionFiltration (SchubertSpace (shiftPair a ab) M hM)
        (orbitDimension (shiftPair a ab) (difference (shiftPair a ab) / 2))}
      (_ : IsNormalizedOrbitIC ab N hN (𝟙 _) (difference ab / 2) P F)
      (_ : IsNormalizedOrbitIC (shiftPair a ab) M hM (𝟙 _) (difference (shiftPair a ab) / 2) Q G)
      (α : A.action.Equivariance (complex F).obj) (β : B.action.Equivariance (complex G).obj)
      (_ : NormalizedICDatum adj A.action F α) (_ : NormalizedICDatum adj B.action G β)
      (h : JetMapsCommute A.action B.action T.analyticIso.hom)
      (e : (derivedDirectImage T.analyticIso.hom).obj (complex F) ≅ complex G),
      DirectImageIntertwines adj A.action B.action h (complex F) α (complex G) β e →
      ∃ i : SchubertSpace (shiftPair a ab) M hM ⟶ Gr,
        IsClosedEmbedding i ∧ Set.range i = closureLattices (shiftPair a ab) ∧
        (∀ p, schubertPointSubspace p = latticeSubspace (-(M : ℤ)) (2 * M) (i p)) ∧
        (∀ p, i (T.analyticIso.hom p) = leftTerminal a ab (S.left p) ∧
          i (T.analyticIso.hom p) = rightTerminal a ab (S.right p)) ∧
        CentralStageTransport D A.action B.action adj i h α β e

namespace Expected

/-- Convolution with the scalar point in either position is the normalized IC
of the translated Schubert closure in the equivariant perverse category. -/
def CentralPointRule : Prop := CentralConvolution ∧ CentralPointAllStages

/-- The two translated minuscule factors have the two stated shifted summands.
The quotient, factor descent, and proper terminal projection use the common
ordered incidence presentation, with the individual lattice shifts recorded
by `TranslatedFlags`. -/
def TranslatedMinusculeRule : Prop :=
  ∀ a b : ℤ,
    ∃ (c : ContinuousJets) (D : GrassmannianStages c) (S : LocalSquare c)
      (A : TranslatedIC S.minusculeIC a) (B : TranslatedIC S.minusculeIC b)
      (K : TranslatedIC S.twoStepIC (a + b)) (P : TranslatedIC S.scalarIC (a + b))
      (F : TranslatedFlags S a b) (T : TranslatedStages D (a + b)),
      TranslatedFactorMaps S A B F ∧ TranslatedTensorDescent S A B F ∧
      TranslatedTerminalScheme S K F ∧
      TranslatedExtension D S T K P

end Expected
end RepTheorySurvey.Geometric.CentralMinusculeRuleSpecs
