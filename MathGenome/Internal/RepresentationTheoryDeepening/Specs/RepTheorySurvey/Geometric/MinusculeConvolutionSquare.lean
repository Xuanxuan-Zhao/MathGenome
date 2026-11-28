import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionEquivariantSplitting
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TwoStepIntersectionComplex

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace Topology
open scoped MatrixGroups TensorProduct

namespace RepTheorySurvey.Geometric.ConvolutionFrameOverlapSpecs

open Analytic AnalyticAction ConvolutionUnitConeSpecs
open ConvolutionConstantDescentSpec (tensorPresheaf coefficientTensor)
open IntersectionComplex (shiftedConstant)
open LatticeModelSpecs BoundedLatticeSpecs MinusculeAndTwoStepSpecs
open ConvolutionBundleSpecs (firstPlane secondPlane firstStage OrderedProduct)

/-- The sheaf map induced by the tensor of the maps on sections. -/
def tensorMap {Z : TopCat.{0}} {F F' G G' : Sheaves Z} (u : F ⟶ F') (v : G ⟶ G') :
    coefficientTensor F G ⟶ coefficientTensor F' G' :=
  (presheafToSheaf (Opens.grothendieckTopology Z) Coeff.{0}).map {
    app U := u.hom.app U ⊗ₘ v.hom.app U
    naturality U V j := by
      change (F.obj.map j ⊗ₘ G.obj.map j) ≫ (u.hom.app V ⊗ₘ v.hom.app V) =
        (u.hom.app U ⊗ₘ v.hom.app U) ≫ (F'.obj.map j ⊗ₘ G'.obj.map j)
      calc
        _ = (F.obj.map j ≫ u.hom.app V) ⊗ₘ (G.obj.map j ≫ v.hom.app V) :=
          tensorHom_comp_tensorHom _ _ _ _
        _ = (u.hom.app U ≫ F'.obj.map j) ⊗ₘ (v.hom.app U ≫ G'.obj.map j) :=
          congrArg₂ (fun f g => f ⊗ₘ g) (u.hom.naturality j) (v.hom.naturality j)
        _ = _ := (tensorHom_comp_tensorHom _ _ _ _).symm }

/-- The maps on sections induced by the inverse-image adjunction units, then sheafified on the
source of the inverse image, define the canonical tensor comparison. -/
def inverseTensorMap {W Z : TopCat.{0}} (r : W ⟶ Z) (F G : Sheaves Z) :
    (inverseImage r).obj (coefficientTensor F G) ⟶
      coefficientTensor ((inverseImage r).obj F) ((inverseImage r).obj G) := by
  let FF := (inverseImage r).obj F
  let GG := (inverseImage r).obj G
  let P := tensorPresheaf FF GG
  let a := inverseDirectAdjunction r
  let s := sheafificationAdjunction (Opens.grothendieckTopology W) Coeff.{0}
  let s' := sheafificationAdjunction (Opens.grothendieckTopology Z) Coeff.{0}
  refine (a.homEquiv _ _).symm ((s'.homEquiv _ _).symm ?_)
  exact {
    app U := ((a.unit.app F).hom.app U ⊗ₘ (a.unit.app G).hom.app U) ≫
      (s.unit.app P).app ((Opens.map r).op.obj U)
    naturality U V j := by
      let j' := (Opens.map r).op.map j
      have hη : (FF.obj.map j' ⊗ₘ GG.obj.map j') ≫ (s.unit.app P).app ((Opens.map r).op.obj V) =
          (s.unit.app P).app ((Opens.map r).op.obj U) ≫
            ((sheafToPresheaf _ _).obj (coefficientTensor FF GG)).map j' :=
        (s.unit.app P).naturality j'
      have hu : F.obj.map j ≫ (a.unit.app F).hom.app V =
          (a.unit.app F).hom.app U ≫ FF.obj.map j' := (a.unit.app F).hom.naturality j
      have hv : G.obj.map j ≫ (a.unit.app G).hom.app V =
          (a.unit.app G).hom.app U ≫ GG.obj.map j' := (a.unit.app G).hom.naturality j
      change (F.obj.map j ⊗ₘ G.obj.map j) ≫
        ((a.unit.app F).hom.app V ⊗ₘ (a.unit.app G).hom.app V) ≫
          (s.unit.app P).app ((Opens.map r).op.obj V) =
        ((a.unit.app F).hom.app U ⊗ₘ (a.unit.app G).hom.app U) ≫
          (s.unit.app P).app ((Opens.map r).op.obj U) ≫
            ((sheafToPresheaf _ _).obj (coefficientTensor FF GG)).map j'
      calc
        _ = ((F.obj.map j ≫ (a.unit.app F).hom.app V) ⊗ₘ
            (G.obj.map j ≫ (a.unit.app G).hom.app V)) ≫
              (s.unit.app P).app ((Opens.map r).op.obj V) :=
          tensorHom_comp_tensorHom_assoc _ _ _ _ _
        _ = (((a.unit.app F).hom.app U ≫ FF.obj.map j') ⊗ₘ
            ((a.unit.app G).hom.app U ≫ GG.obj.map j')) ≫
              (s.unit.app P).app ((Opens.map r).op.obj V) :=
          congrArg (fun v => v ≫ _) (congrArg₂ (fun f g => f ⊗ₘ g) hu hv)
        _ = ((a.unit.app F).hom.app U ⊗ₘ (a.unit.app G).hom.app U) ≫
              (FF.obj.map j' ⊗ₘ GG.obj.map j') ≫ (s.unit.app P).app ((Opens.map r).op.obj V) :=
          (tensorHom_comp_tensorHom_assoc _ _ _ _ _).symm
        _ = _ := congrArg (fun v => _ ≫ v) hη
    }

/-- Shift an ordinary rational coefficient morphism into degree `-d`. -/
abbrev shiftedSingleMap {W : TopCat.{0}} (d : ℕ) {F G : Sheaves W} (u : F ⟶ G) :=
  (shiftFunctor (Derived W) (d : ℤ)).map ((DerivedCategory.singleFunctor (Sheaves W) 0).map u)

abbrev pulledFactor {W X : TopCat.{0}} (p : W ⟶ X) (d : ℕ) :=
  ((DerivedCategory.singleFunctor (Sheaves W) 0).obj ((inverseImage p).obj (rational X)))⟦(d : ℤ)⟧

def pullbackFactorIso {W X : TopCat.{0}} (p : W ⟶ X) (d : ℕ) :
    (derivedInverseImage p).obj (shiftedConstant X d).obj ≅ pulledFactor p d :=
  ((inverseImage p).mapDerivedCategory.commShiftIso (d : ℤ)).app _ ≪≫
    (shiftFunctor (Derived W) (d : ℤ)).mapIso
      (((inverseImage p).mapDerivedCategorySingleFunctor 0).app (rational X))

def pullbackTensorMap {W Z X Y : TopCat.{0}} (r : W ⟶ Z) (a : Z ⟶ X) (b : Z ⟶ Y) :
    (derivedInverseImage r).obj (shiftedTensor a b) ⟶ shiftedTensor (r ≫ a) (r ≫ b) :=
  ((inverseImage r).mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
    (shiftFunctor (Derived W) (2 : ℤ)).map
      (((inverseImage r).mapDerivedCategorySingleFunctor 0).hom.app (pulledBackTensor a b)) ≫
    shiftedSingleMap 2 (inverseTensorMap r _ _ ≫
      tensorMap ((inverseImageComposition r a).inv.app (rational X))
        ((inverseImageComposition r b).inv.app (rational Y)))

/-- The transition on the tensor induced by the descent comparison and a pair of maps with
the same image downstairs. -/
def quotientTransition {W Z X Y S : TopCat.{0}} {q : Z ⟶ S}
    {a : Z ⟶ X} {b : Z ⟶ Y}
    (d : (derivedInverseImage q).obj (shiftedConstant S 2).obj ≅ shiftedTensor a b)
    {r₀ r₁ : W ⟶ Z} (h : r₁ ≫ q = r₀ ≫ q) :
    (derivedInverseImage r₁).obj (shiftedTensor a b) ⟶
      (derivedInverseImage r₀).obj (shiftedTensor a b) :=
  (derivedInverseImage r₁).map d.inv ≫
    (derivedInverseImageComposition r₁ q).inv.app (shiftedConstant S 2).obj ≫
    eqToHom (congrArg (fun f => (derivedInverseImage f).obj (shiftedConstant S 2).obj) h) ≫
    (derivedInverseImageComposition r₀ q).hom.app (shiftedConstant S 2).obj ≫
    (derivedInverseImage r₀).map d.hom

abbrev overlap (q : representativeSpace ⟶ ordered) : TopCat.{0} :=
  TopCat.of {p : representativeSpace × representativeSpace // q p.1 = q p.2}

def leftLeg (q : representativeSpace ⟶ ordered) : overlap q ⟶ representativeSpace :=
  TopCat.ofHom ⟨fun w => w.val.1, continuous_fst.comp continuous_subtype_val⟩

def rightLeg (q : representativeSpace ⟶ ordered) : overlap q ⟶ representativeSpace :=
  TopCat.ofHom ⟨fun w => w.val.2, continuous_snd.comp continuous_subtype_val⟩

theorem commonImage (q : representativeSpace ⟶ ordered) : rightLeg q ≫ q = leftLeg q ≫ q :=
  TopCat.ext (fun w => w.property.symm)

/-- The two pullbacks of the frame comparison agree with the tensor transition induced by
the actual change of first-lattice frame. -/
def FrameOverlapIdentification {hH : IsTopologicalGroup Jets}
    {A : AnalyticAction (jetGroup hH) minuscule}
    (α : A.Equivariance minusculeFactor.obj)
    (q : representativeSpace ⟶ ordered) (b : representativeSpace ⟶ minuscule)
    (d : (derivedInverseImage q).obj orderedFactor.obj ≅ shiftedTensor (q ≫ firstStageMap) b) : Prop :=
  let a := q ≫ firstStageMap
  let r₀ := leftLeg q
  let r₁ := rightLeg q
  let ha : r₁ ≫ a = r₀ ≫ a := by simp only [a, ← Category.assoc, r₀, r₁, commonImage]
  ∃ (γ : overlap q ⟶ Parameters (jetGroup hH) minuscule)
    (hb₁ : γ ≫ A.act = r₁ ≫ b)
    (hb₀ : γ ≫ projection (jetGroup hH) minuscule = r₀ ≫ b),
    (∀ w : overlap q, ∃ g : GL (Fin 2) O,
      (r₁ w).val.1 = (r₀ w).val.1 * positiveGLMap 2 g ∧
      (r₁ w).val.2 = positiveGLMap 2 g⁻¹ • (r₀ w).val.2 ∧
      constantJetLinear (γ w).1 = constantJetLinear (reduceGL 2 2 (by decide) g⁻¹)) ∧
    IsIso (pullbackTensorMap r₁ a b) ∧ IsIso (pullbackTensorMap r₀ a b) ∧
    ∃ (e₂ : (inverseImage (r₁ ≫ b)).obj (rational minuscule) ⟶
      (inverseImage (r₀ ≫ b)).obj (rational minuscule)),
      (pullbackFactorIso (r₁ ≫ b) 1).hom ≫ shiftedSingleMap 1 e₂ ≫
          (pullbackFactorIso (r₀ ≫ b) 1).inv =
        pullbackMorphism γ hb₁ hb₀ α.iso.hom ∧
      let e₁ := eqToHom (congrArg (fun f => (inverseImage f).obj (rational minuscule)) ha)
      pullbackTensorMap r₁ a b ≫ shiftedSingleMap 2 (tensorMap e₁ e₂) =
        quotientTransition d (commonImage q) ≫ pullbackTensorMap r₀ a b

/-- Pull the ordered equivariance through the same comparison on the two frame legs. -/
def orderedTransition {H : AnalyticGroup.{0}} {B : AnalyticAction H ordered}
    (β : B.Equivariance orderedFactor.obj) {W : TopCat.{0}}
    {q : representativeSpace ⟶ ordered} {a b : representativeSpace ⟶ minuscule}
    (d : (derivedInverseImage q).obj orderedFactor.obj ≅ shiftedTensor a b)
    {r₀ r₁ : W ⟶ representativeSpace} (γ : W ⟶ Parameters H ordered)
    (h₁ : γ ≫ B.act = r₁ ≫ q) (h₀ : γ ≫ projection H ordered = r₀ ≫ q) :
    (derivedInverseImage r₁).obj (shiftedTensor a b) ⟶
      (derivedInverseImage r₀).obj (shiftedTensor a b) :=
  (derivedInverseImage r₁).map d.inv ≫
    (derivedInverseImageComposition r₁ q).inv.app orderedFactor.obj ≫
    pullbackMorphism γ h₁ h₀ β.iso.hom ≫
    (derivedInverseImageComposition r₀ q).hom.app orderedFactor.obj ≫
    (derivedInverseImage r₀).map d.hom

/-- Left multiplication acts on the first frame and fixes the relative second lattice.
The same descent comparison intertwines the first factor action with the ordered action. -/
def FrameActionIdentification {hH : IsTopologicalGroup Jets}
    {A : AnalyticAction (jetGroup hH) minuscule} {B : AnalyticAction (jetGroup hH) ordered}
    (α : A.Equivariance minusculeFactor.obj) (β : B.Equivariance orderedFactor.obj)
    (q : representativeSpace ⟶ ordered) (b : representativeSpace ⟶ minuscule)
    (d : (derivedInverseImage q).obj orderedFactor.obj ≅ shiftedTensor (q ≫ firstStageMap) b) : Prop :=
  let a := q ≫ firstStageMap
  let H := jetGroup hH
  let W := Parameters H representativeSpace
  let r₀ := projection H representativeSpace
  let γ₁ : W ⟶ Parameters H minuscule := TopCat.ofHom
    ⟨fun w => (w.1, a w.2), continuous_fst.prodMk (a.hom.continuous.comp continuous_snd)⟩
  let γq : W ⟶ Parameters H ordered := TopCat.ofHom
    ⟨fun w => (w.1, q w.2), continuous_fst.prodMk (q.hom.continuous.comp continuous_snd)⟩
  let h₀ : γ₁ ≫ projection H minuscule = r₀ ≫ a := TopCat.ext (fun _ => rfl)
  let hq₀ : γq ≫ projection H ordered = r₀ ≫ q := TopCat.ext (fun _ => rfl)
  ∃ (r₁ : W ⟶ representativeSpace)
    (hq₁ : γq ≫ B.act = r₁ ≫ q)
    (h₁ : γ₁ ≫ A.act = r₁ ≫ a)
    (hb : r₁ ≫ b = r₀ ≫ b),
    (∀ w : W, ∃ g : GL (Fin 2) O,
      reduceGL 2 2 (by decide) g = w.1 ∧
      (r₁ w).val.1 = positiveGLMap 2 g * (r₀ w).val.1 ∧
      (r₁ w).val.2 = (r₀ w).val.2) ∧
    IsIso (pullbackTensorMap r₁ a b) ∧ IsIso (pullbackTensorMap r₀ a b) ∧
    ∃ (e₁ : (inverseImage (r₁ ≫ a)).obj (rational minuscule) ⟶
      (inverseImage (r₀ ≫ a)).obj (rational minuscule)),
      (pullbackFactorIso (r₁ ≫ a) 1).hom ≫ shiftedSingleMap 1 e₁ ≫
          (pullbackFactorIso (r₀ ≫ a) 1).inv =
        pullbackMorphism γ₁ h₁ h₀ α.iso.hom ∧
      let e₂ := eqToHom (congrArg (fun f => (inverseImage f).obj (rational minuscule)) hb)
      pullbackTensorMap r₁ a b ≫ shiftedSingleMap 2 (tensorMap e₁ e₂) =
        orderedTransition β d γq hq₁ hq₀ ≫ pullbackTensorMap r₀ a b

/-- The normalized coefficient complex on the ordered lattice surface realizes descent
of the actual two minuscule factors for this same pair of equivariance data. -/
def ActualDescent {hH : IsTopologicalGroup Jets}
    {A : AnalyticAction (jetGroup hH) minuscule} {B : AnalyticAction (jetGroup hH) ordered}
    (α : A.Equivariance minusculeFactor.obj) (β : B.Equivariance orderedFactor.obj) : Prop :=
  ∃ (h : StableStage (PositiveGL 2) (colength 1))
    (e : OrderedProduct h ≃ ordered)
    (b : representativeSpace ⟶ minuscule) (q : representativeSpace ⟶ ordered),
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
    ∃ (μ : pulledBackTensor a b ≅ rational representativeSpace)
      (d : (derivedInverseImage q).obj orderedFactor.obj ≅ shiftedTensor a b),
      let μ₂ := (shiftFunctor (Derived representativeSpace) (2 : ℤ)).mapIso
          ((DerivedCategory.singleFunctor (Sheaves representativeSpace) 0).mapIso μ)
      MultipliesCoefficients a b μ ∧ d ≪≫ μ₂ = shiftedConstantPullback q 2 ∧
      FrameOverlapIdentification α q b d ∧ FrameActionIdentification α β q b d

end RepTheorySurvey.Geometric.ConvolutionFrameOverlapSpecs

namespace RepTheorySurvey.Geometric.MinusculeConvolutionSquareSpecs

open Analytic
open Analytic.IntersectionComplex
  (shiftedConstant DimensionFiltration complex attachmentι directImageComparison
    boundedBelowPullbackComposition)
open LatticeModelSpecs BoundedLatticeSpecs MinusculeAndTwoStepSpecs RankTwoSchubertStrataSpecs
open SchubertIntersectionConstructibilitySpecs
open EquivariantIntersectionComplexesSpecs
open ConvolutionUnitConeSpecs
open ConvolutionBundleSpecs (firstPlane secondPlane)
open ConvolutionFrameOverlapSpecs (ActualDescent)
open ConvolutionEquivariantSplittingSpecs (SplittingData)
open ClosedEquivarianceExtensionSpecs (parameterInclusion projectionSquare DerivedAdjunctions)

abbrev Gr : TopCat.{0} := TopCat.of GL2Lattice

/-- The symmetric bounds on lattices used for the closed stages of the affine Grassmannian. -/
def boundedSet (N : ℕ) : Set Gr :=
  {L | (scalarLattice 2 (N : ℤ)).val ≤ L.val ∧
    L.val ≤ (scalarLattice 2 (-(N : ℤ))).val}

/-- The common closed stages and their positive-loop actions, in the original coordinates. -/
structure GrassmannianStages (c : ContinuousJets) where
  stages : ClosedStages Gr
  isBoundedSet : ∀ N, stages.stage N = boundedSet N
  actions : StageJetActions (jetSystem c) stages
  actionCutoff : ∀ N, (actions.stageAction N).cutoff = 2 * N - 1
  actionOnLattices : ∀ N k (hk : (actions.stageAction N).cutoff ≤ k)
    (g : GL (Fin 2) O) (L : stages.space N),
    (((actions.stageAction N).action k hk).act
      (reduceGL 2 (k + 1) (Nat.succ_pos k) g, L)).val = positiveGLMap 2 g • L.val
  stratification : ∀ N, Stratification (stages.space N)
  orbitStrata : ∀ N (s : (stratification N).Index),
    ∃ ab : DominantPair,
      Set.range ((stratification N).stratum s).inclusion =
        {L | L.val ∈ gl2Orbit ab} ∧
      ((stratification N).stratum s).complexDimension = difference ab

/-- The actual Schubert model is identified with the short-window model on the
same lattices. Its sheaf comparison uses the normalized orbit IC. -/
structure ICComparison {c : ContinuousJets} (ab : DominantPair) {Y : TopCat.{0}}
    (A : JetAction (jetSystem c) Y) (F : BoundedBelow Y) (α : A.Equivariance F.obj) where
  bound : OrbitBound ab 2
  model : Y ≅ SchubertSpace ab 2 bound
  lattice : Y → BoundedLattice 2 2
  coordinates : ∀ y, schubertPointSubspace (model.hom y) = boundedSubspace (lattice y)
  stratification : Stratification (SchubertSpace ab 2 bound)
  filtration : DimensionFiltration (SchubertSpace ab 2 bound) (orbitDimension ab (difference ab / 2))
  isIC : IsNormalizedOrbitIC ab 2 bound (𝟙 _) (difference ab / 2) stratification filtration
  action : JetAction (jetSystem c) (SchubertSpace ab 2 bound)
  actionActual : ActualSchubertAction ab 2 bound action
  action_commutes : EquivariantIntersectionComplexesSpecs.Intertwines A action model.hom
  datum : action.Equivariance (complex filtration).obj
  adjunctions : DerivedAdjunctions.{0}
  normalized : NormalizedICDatum adjunctions action filtration datum
  comparison : F.obj ≅ (derivedInverseImage model.hom).obj (complex filtration).obj
  equivariant : IntertwinesPullback action_commutes α datum comparison.hom

/-- At a closed-stage inclusion the extension uses the action and projection
mates of the actual derived direct image. -/
def ExtendsAtStage {J : JetSystem.{0}} {X Y : TopCat.{0}} {A : JetAction J Y}
    {B : JetAction J X} {F : BoundedBelow Y} {G : Derived X} (i : Y ⟶ X)
    (a : DerivedAdjunctions.{0}) (α : A.Equivariance F.obj) (β : B.Equivariance G)
    (e : ((derivedDirectImage i).obj F).obj ≅ G) : Prop :=
  ∀ (k : ℕ) (hy : A.cutoff ≤ k) (hx : B.cutoff ≤ k),
    let H := J.group k
    let iH := parameterInclusion H i
    let p := AnalyticAction.projection H X
    ∃ h : iH ≫ (B.action k hx).act = (A.action k hy).act ≫ i,
      let bcA := directImageComparison h (a iH) (a i) F
      let bcP := directImageComparison (projectionSquare H i) (a iH) (a i) F
      IsIso bcA ∧ IsIso bcP ∧
      (derivedInverseImage (B.action k hx).act).map e.hom ≫ (β.datum k hx).iso.hom ≫
          (derivedInverseImage p).map e.inv ≫ bcP.hom =
        bcA.hom ≫ ((derivedDirectImage iH).map (ObjectProperty.homMk (α.datum k hy).iso.hom)).hom

/-- A finite-stage equivariant object on the union realizes the closed direct
image from its support. The same ordinary identifications determine the
equivariance on all sufficiently large stages. -/
structure GrassmannianExtension {c : ContinuousJets} (D : GrassmannianStages c)
    {Y : TopCat.{0}} (A : JetAction (jetSystem c) Y) (F : BoundedBelow Y)
    (α : A.Equivariance F.obj) (i : Y ⟶ Gr) where
  sheaf : D.actions.Object
  closed : IsClosedEmbedding i
  ordinary : ((derivedDirectImage i).obj F).obj ≅ sheaf.obj
  perverse : IsFiniteStagePerverse D.stages D.stratification sheaf.obj
  stagewise : ∀ N, 2 ≤ N →
    ∃ (j : Y ⟶ D.stages.space N) (a : DerivedAdjunctions.{0})
      (e : ((derivedDirectImage j).obj F).obj ≅
        (derivedInverseImage (D.stages.inclusion N)).obj sheaf.obj),
      j ≫ D.stages.inclusion N = i ∧ IsClosedEmbedding j ∧
        ExtendsAtStage j a α (sheaf.equivariance.datum N) e

/-- The comparison on the surface itself is the factorization of the
constant-coefficient restriction map through the middle truncation. -/
def IsGS10Identification (d : SplittingData)
    (e : (shiftedConstant surface 2).obj ≅ (IntersectionComplex.surface d.point d.closed).obj) :
    Prop :=
  let U := complementOpen {d.point} d.closed
  let j := openInclusion U
  let a := shiftedConstant surface 2
  let b := shiftedConstant (TopCat.of U) 2
  ∃ adj : boundedBelowInverseImage j ⊣ derivedDirectImage j,
    e.hom ≫ attachmentι j U.isOpenEmbedding 0 b =
      (adj.homEquiv a b (ObjectProperty.homMk (shiftedConstantPullback j 2).hom)).hom

/-- The fixed unit and section compare the convolution with the two canonical
summands. A point summand is carried to the surface by the closed inclusion. -/
structure LocalSquare (c : ContinuousJets) where
  splitting : SplittingData
  minAction : JetAction (jetSystem c) minuscule
  terminalAction : JetAction (jetSystem c) surface
  pointAction : JetAction (jetSystem c) (TopCat.of ({splitting.point} : Set surface))
  minCutoff : minAction.cutoff ≤ 1
  terminalCutoff : terminalAction.cutoff ≤ 1
  pointCutoff : pointAction.cutoff ≤ 1
  minActs : (minAction.action 1 minCutoff).act = splitting.firstAction.act
  terminalActs : (terminalAction.action 1 terminalCutoff).act = splitting.terminalAction.act
  pointActs : ∀ k (hk : pointAction.cutoff ≤ k),
    (pointAction.action k hk).act = AnalyticAction.projection _ _
  minDatum : minAction.Equivariance minusculeFactor.obj
  convolutionDatum : terminalAction.Equivariance convolution.obj
  constantDatum : terminalAction.Equivariance (shiftedConstant surface 2).obj
  intersectionDatum : terminalAction.Equivariance
    (IntersectionComplex.surface splitting.point splitting.closed).obj
  pointDatum : pointAction.Equivariance (IntersectionComplex.point splitting.point).obj
  minDatumAtTwo : (minDatum.datum 1 minCutoff).iso.hom =
    eqToHom (congrArg (fun f => (derivedInverseImage f).obj minusculeFactor.obj) minActs) ≫
      splitting.firstEq.iso.hom
  convolutionDatumAtTwo : (convolutionDatum.datum 1 terminalCutoff).iso.hom =
    eqToHom (congrArg (fun f => (derivedInverseImage f).obj convolution.obj) terminalActs) ≫
      splitting.convolutionEq.iso.hom
  constantDatumAtTwo : (constantDatum.datum 1 terminalCutoff).iso.hom =
    eqToHom (congrArg (fun f => (derivedInverseImage f).obj (shiftedConstant surface 2).obj)
      terminalActs) ≫ splitting.constantEq.iso.hom
  minusculeIC : ICComparison minusculePair minAction minusculeFactor minDatum
  twoStepIC : ICComparison twoStepPair terminalAction
    (IntersectionComplex.surface splitting.point splitting.closed) intersectionDatum
  scalarIC : ICComparison scalarPair pointAction (IntersectionComplex.point splitting.point) pointDatum
  minusculeCoordinates : ∀ p : minuscule,
    (minusculeIC.lattice p).val ∈ colength 1 ∧
    firstPlane p = (latticeSubspace 0 1 (minusculeIC.lattice p).val).map constantCoordinates.toLinearMap
  terminalCoordinates : ∀ p : surface,
    (twoStepIC.lattice p).val ∈ colength 2 ∧
    secondPlane p = (latticeSubspace 0 2 (twoStepIC.lattice p).val).map twoStepCoordinates.toLinearMap
  scalarCoordinates : ∀ p : TopCat.of ({splitting.point} : Set surface),
    (scalarIC.lattice p).val = scalarPoint ∧ (twoStepIC.lattice p.val).val = scalarPoint
  latticeChart : surface ≅ TwoStepIntersectionComplexSpecs.X
  latticeChartCoordinates : ∀ p : surface, (latticeChart.hom p).val = (twoStepIC.lattice p).val
  constantIdentification :
    (shiftedConstant surface 2).obj ≅ (IntersectionComplex.surface splitting.point splitting.closed).obj
  isGS10Identification : IsGS10Identification splitting constantIdentification
  constantIdentificationEquivariant : ∀ k (hk : terminalAction.cutoff ≤ k),
    ConvolutionEquivariantSplittingSpecs.Intertwines
      (constantDatum.datum k hk) (intersectionDatum.datum k hk) constantIdentification.hom
  pointAsSkyscraper : terminalAction.Equivariance
    (pointSkyscraper splitting.point splitting.closed)
  pointAsSkyscraperAtTwo : (pointAsSkyscraper.datum 1 terminalCutoff).iso.hom =
    eqToHom (congrArg (fun f => (derivedInverseImage f).obj
      (pointSkyscraper splitting.point splitting.closed)) terminalActs) ≫ splitting.pointEq.iso.hom
  pointExtension :
    let i := closedInclusion ({splitting.point} : Set surface)
    let F := IntersectionComplex.point splitting.point
    ∃ (a : DerivedAdjunctions.{0})
      (b : boundedBelowInverseImage i ⊣ LocalSheaf.closedExtensionPlus splitting.closed),
      let e := ((a i).rightAdjointUniq b).app F
      ExtendsAtStage i a pointDatum pointAsSkyscraper
        (DerivedCategory.Plus.ι.mapIso e)

/-- Compose the two actual direct images and use exact closed extension for
the closed inclusion of the point in the terminal surface. -/
def closedPointComposition (d : SplittingData) (j : surface ⟶ Gr)
    (a : DerivedAdjunctions.{0})
    (b : boundedBelowInverseImage (closedInclusion ({d.point} : Set surface)) ⊣
      LocalSheaf.closedExtensionPlus d.closed) :
    derivedDirectImage (closedInclusion ({d.point} : Set surface) ≫ j) ≅
      LocalSheaf.closedExtensionPlus d.closed ⋙ derivedDirectImage j :=
  let i := closedInclusion ({d.point} : Set surface)
  let c := ((a j).comp (a i)).ofNatIsoLeft (boundedBelowPullbackComposition i j).symm
  (a (i ≫ j)).rightAdjointUniq c ≪≫
    Functor.isoWhiskerRight ((a i).rightAdjointUniq b) (derivedDirectImage j)

/-- Global direct images of the same local maps give an isomorphism in the
positive-loop-equivariant perverse category. -/
def ExtendsSquare {c : ContinuousJets} (D : GrassmannianStages c)
    (S : LocalSquare c) : Prop :=
  let d := S.splitting
  let i := closedInclusion ({d.point} : Set surface)
  ∃ (j₁ : minuscule ⟶ Gr) (j₂ : surface ⟶ Gr),
    (∀ p : minuscule, j₁ p = (S.minusculeIC.lattice p).val) ∧
    (∀ p : surface, j₂ p = (S.twoStepIC.lattice p).val) ∧
    ∃ (_ : GrassmannianExtension D S.minAction minusculeFactor S.minDatum j₁)
      (K : GrassmannianExtension D S.terminalAction (IntersectionComplex.surface d.point d.closed)
        S.intersectionDatum j₂)
      (P : GrassmannianExtension D S.pointAction (IntersectionComplex.point d.point) S.pointDatum (i ≫ j₂))
      (L : GrassmannianExtension D S.terminalAction convolution S.convolutionDatum j₂)
      (u : K.sheaf ⟶ L.sheaf) (v : P.sheaf ⟶ L.sheaf)
      (a : DerivedAdjunctions.{0})
      (b : boundedBelowInverseImage i ⊣ LocalSheaf.closedExtensionPlus d.closed),
      u.hom = K.ordinary.inv ≫
        ((derivedDirectImage j₂).map (ObjectProperty.homMk (S.constantIdentification.inv ≫ unit))).hom ≫
        L.ordinary.hom ∧
      v.hom = P.ordinary.inv ≫ ((closedPointComposition d j₂ a b).hom.app
        (IntersectionComplex.point d.point)).hom ≫
        ((derivedDirectImage j₂).map (ObjectProperty.homMk d.sectionMap)).hom ≫ L.ordinary.hom ∧
      IsIso (biprod.desc u.hom v.hom) ∧
      Nonempty (IsColimit (BinaryCofan.mk u v))

namespace Expected

/-- The minuscule intersection complex convolved with itself on the actual
ordered lattice surface splits into the two indicated intersection complexes,
with their normalized rational coefficients and extension to the affine
Grassmannian. The maps respect the positive-loop equivariance at every stage. -/
def MinusculeConvolutionSquare : Prop :=
  ∃ (c : ContinuousJets) (D : GrassmannianStages c) (S : LocalSquare c),
    ActualDescent S.splitting.firstEq S.splitting.orderedEq ∧ ExtendsSquare D S

end Expected
end RepTheorySurvey.Geometric.MinusculeConvolutionSquareSpecs
