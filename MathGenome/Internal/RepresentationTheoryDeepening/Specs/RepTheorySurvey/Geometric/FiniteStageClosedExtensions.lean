import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.DerivedPullbackPasting

noncomputable section

set_option autoImplicit false

open CategoryTheory Topology

namespace RepTheorySurvey.Geometric.FiniteStageClosedExtensionSpecs

open Analytic Analytic.IntersectionComplex LocalSheaf
open ClosedEquivarianceExtensionSpecs (DerivedAdjunctions parameterInclusion projectionSquare)
open EquivariantIntersectionComplexesSpecs (Intertwines IntertwinesPullback)
open Analytic.DerivedPullbackPasting.Expected (identityValue)

/-- Each square presents the actual closed intersection with the support.
The intersection can be given in any homeomorphic coordinates. -/
structure SupportIntersections {X Y : TopCat.{0}} {J : JetSystem.{0}} {A : ClosedStages X}
    (B : StageJetActions J A) (i : Y ⟶ X) (S : JetAction J Y) where
  space : ℕ → TopCat.{0}
  intoStage : ∀ n, space n ⟶ A.space n
  intoSupport : ∀ n, space n ⟶ Y
  closed : ∀ n, IsClosedEmbedding (intoStage n)
  square : ∀ n, intoStage n ≫ A.inclusion n = intoSupport n ≫ i
  range_eq : ∀ n, Set.range (intoStage n) = (A.inclusion n) ⁻¹' Set.range i
  transition : ∀ {n m : ℕ}, n ≤ m → (space n ⟶ space m)
  transition_stage : ∀ {n m : ℕ} (h : n ≤ m),
    transition h ≫ intoStage m = intoStage n ≫ A.transition h
  transition_support : ∀ {n m : ℕ} (h : n ≤ m),
    transition h ≫ intoSupport m = intoSupport n
  action : ∀ n, JetAction J (space n)
  cutoff_le : ∀ n, (action n).cutoff ≤ (B.stageAction n).cutoff
  stageActionSquare : ∀ n, Intertwines (action n) (B.stageAction n) (intoStage n)
  supportActionSquare : ∀ n, Intertwines (action n) S (intoSupport n)
  transitionActionSquare : ∀ {n m : ℕ} (h : n ≤ m),
    Intertwines (action n) (action m) (transition h)

namespace SupportIntersections

variable {X Y : TopCat.{0}} {J : JetSystem.{0}} {A : ClosedStages X}
variable {B : StageJetActions J A} {i : Y ⟶ X} {S : JetAction J Y}
variable (D : SupportIntersections B i S)

def intersectionRestriction (F : BoundedBelow Y) (n : ℕ) : BoundedBelow (D.space n) :=
  (boundedBelowInverseImage (D.intoSupport n)).obj F

/-- The composition comparison for restriction from one support intersection
to another. -/
def intersectionRestrictionComparison (F : BoundedBelow Y) {n m : ℕ} (h : n ≤ m) :
    D.intersectionRestriction F n ≅
      (boundedBelowInverseImage (D.transition h)).obj (D.intersectionRestriction F m) :=
  eqToIso (congrArg (fun f => (boundedBelowInverseImage f).obj F) (D.transition_support h).symm) ≪≫
    (boundedBelowPullbackComposition (D.transition h) (D.intoSupport m)).app F

/-- Only local equivariance on the restricted coefficient complexes is input.
The stage and support restriction laws are imposed on those complexes. -/
structure LocalEquivariance (F : BoundedBelow Y) (α : S.Equivariance F.obj) where
  datum : ∀ n, (D.action n).Equivariance (D.intersectionRestriction F n).obj
  onSupport : ∀ n, IntertwinesPullback (D.supportActionSquare n) (datum n) α (𝟙 _)
  onTransitions : ∀ {n m : ℕ} (h : n ≤ m),
    IntertwinesPullback (D.transitionActionSquare h) (datum n) (datum m)
      (D.intersectionRestrictionComparison F h).hom.hom

/-- The ordinary comparison at a stage is the mate of the intersection square. -/
def stageComparison (a : DerivedAdjunctions.{0}) (F : BoundedBelow Y) (n : ℕ) :=
  directImageComparison (D.square n) (a (D.intoStage n)) (a i) F

end SupportIntersections

/-- The transport equation for an action arrow and a comparison to a closed
direct image. This is the equation using the two actual adjunction mates. -/
def AgreesWithMates {J : JetSystem.{0}} {U V : TopCat.{0}}
    {C : JetAction J U} {E : JetAction J V} {F : BoundedBelow U} {G : Derived V}
    {j : U ⟶ V} (h : Intertwines C E j) (a : DerivedAdjunctions.{0})
    (α : C.Equivariance F.obj) (β : E.Equivariance G)
    (c : G ⟶ ((derivedDirectImage j).obj F).obj) : Prop :=
  ∀ (k : ℕ) (hu : C.cutoff ≤ k) (hv : E.cutoff ≤ k),
    let H := J.group k
    let jH := parameterInclusion H j
    let bcA := directImageComparison (h k hu hv) (a jH) (a j) F
    let bcP := directImageComparison (projectionSquare H j) (a jH) (a j) F
    (β.datum k hv).iso.hom ≫ (derivedInverseImage (AnalyticAction.projection H V)).map c ≫
        bcP.hom =
      (derivedInverseImage (E.action k hv).act).map c ≫ bcA.hom ≫
        ((derivedDirectImage jH).map (ObjectProperty.homMk (α.datum k hu).iso.hom)).hom

def MatesAreIso {J : JetSystem.{0}} {U V : TopCat.{0}}
    {C : JetAction J U} {E : JetAction J V} {j : U ⟶ V}
    (h : Intertwines C E j) (a : DerivedAdjunctions.{0}) (F : BoundedBelow U) : Prop :=
  ∀ (k : ℕ) (hu : C.cutoff ≤ k) (hv : E.cutoff ≤ k),
    let H := J.group k
    let jH := parameterInclusion H j
    IsIso (directImageComparison (h k hu hv) (a jH) (a j) F) ∧
      IsIso (directImageComparison (projectionSquare H j) (a jH) (a j) F)

/-- Ordinary and equivariant realization at every intersection, with a single
global datum on the actual direct image. -/
def RealizesStages {X Y : TopCat.{0}} {J : JetSystem.{0}} {A : ClosedStages X}
    {B : StageJetActions J A} {i : Y ⟶ X} {S : JetAction J Y}
    (D : SupportIntersections B i S) (a : DerivedAdjunctions.{0})
    {F : BoundedBelow Y} {α : S.Equivariance F.obj} (L : D.LocalEquivariance F α)
    (β : B.Equivariance ((derivedDirectImage i).obj F).obj) : Prop :=
  ∀ n : ℕ,
    IsIso (D.stageComparison a F n) ∧
      MatesAreIso (D.stageActionSquare n) a (D.intersectionRestriction F n) ∧
      AgreesWithMates (D.stageActionSquare n) a (L.datum n) (β.datum n)
        (D.stageComparison a F n).hom

/-- The full-support stage comparison uses the identity pullback on the
support, so the complex carried from the support is the original one. -/
def fullSupportComparison {X Y V : TopCat.{0}} {i : Y ⟶ X} {t : V ⟶ X} {j : Y ⟶ V}
    (h : j ≫ t = i) (a : DerivedAdjunctions.{0}) (F : BoundedBelow Y) :
    (derivedInverseImage t).obj ((derivedDirectImage i).obj F).obj ⟶
      ((derivedDirectImage j).obj F).obj :=
  (directImageComparison (h.trans (Category.id_comp i).symm) (a j) (a i) F).hom ≫
    ((derivedDirectImage j).map (ObjectProperty.homMk ((identityValue Y).hom.app F.obj))).hom

/-- The source stratifies a closed union of strata, with the same dimensions
and the same subspace for every matched pair of strata. -/
structure ClosedStrata {Y X : TopCat.{0}} (i : Y ⟶ X)
    (P : Stratification Y) (Q : Stratification X) where
  index : P.Index ≃ {q : Q.Index // Set.range (Q.stratum q).inclusion ⊆ Set.range i}
  range_eq : ∀ p, Set.range (Q.stratum (index p).val).inclusion =
    i '' Set.range (P.stratum p).inclusion
  dimension_eq : ∀ p,
    (Q.stratum (index p).val).complexDimension = (P.stratum p).complexDimension
  disjoint : ∀ q : Q.Index,
    ¬ Set.range (Q.stratum q).inclusion ⊆ Set.range i →
      Disjoint (Set.range (Q.stratum q).inclusion) (Set.range i)

/-- The right adjoint comparison for the composite from a closed point, using
the exact closed extension for its inclusion in the intermediate space. -/
def closedPointComposition {X Y : TopCat.{0}} {x : Y}
    (hx : IsClosed ({x} : Set Y)) (i : Y ⟶ X) (a : DerivedAdjunctions.{0})
    (b : boundedBelowInverseImage (closedInclusion ({x} : Set Y)) ⊣ closedExtensionPlus hx) :
    derivedDirectImage (closedInclusion ({x} : Set Y) ≫ i) ≅
      closedExtensionPlus hx ⋙ derivedDirectImage i :=
  let p := closedInclusion ({x} : Set Y)
  let c := ((a i).comp (a p)).ofNatIsoLeft (boundedBelowPullbackComposition p i).symm
  (a (p ≫ i)).rightAdjointUniq c ≪≫
    Functor.isoWhiskerRight ((a p).rightAdjointUniq b) (derivedDirectImage i)

section Composition

variable {X Y : TopCat.{0}} {J : JetSystem.{0}} {A : ClosedStages X}
variable {B : StageJetActions J A} {i : Y ⟶ X} {x : Y}
variable {S : JetAction J Y} {T : JetAction J (TopCat.of ({x} : Set Y))}
variable (D : SupportIntersections B i S)
variable (P : SupportIntersections B (closedInclusion ({x} : Set Y) ≫ i) T)

/-- The inclusions of the point intersections in the surface intersections.
Their ranges allow a singleton or the empty subspace, according to the stage. -/
structure PointIntersectionMaps where
  inclusion : ∀ n, P.space n ⟶ D.space n
  stage : ∀ n, inclusion n ≫ D.intoStage n = P.intoStage n
  support : ∀ n, inclusion n ≫ D.intoSupport n =
    P.intoSupport n ≫ closedInclusion ({x} : Set Y)
  actionSquare : ∀ n, Intertwines (P.action n) (D.action n) (inclusion n)

/-- At the intersections, the given local equivariance of the point extension
is the transport of the point datum by the actual action and projection mates. -/
def LocalPointCompatibility (I : PointIntersectionMaps D P)
    (hx : IsClosed ({x} : Set Y)) (a : DerivedAdjunctions.{0})
    (b : boundedBelowInverseImage (closedInclusion ({x} : Set Y)) ⊣ closedExtensionPlus hx)
    {F : BoundedBelow (TopCat.of ({x} : Set Y))} {α : T.Equivariance F.obj}
    {γ : S.Equivariance ((closedExtensionPlus hx).obj F).obj}
    (Lₚ : P.LocalEquivariance F α) (L : D.LocalEquivariance ((closedExtensionPlus hx).obj F) γ) :
    Prop :=
  ∀ n, AgreesWithMates (I.actionSquare n) a (Lₚ.datum n) (L.datum n)
    (adjointSquareMap (pullbackSquare (I.support n)) (a (I.inclusion n)) b F).hom

end Composition

namespace Expected

/-- Closed base change holds for the actual mate and arbitrary closed
embeddings, including a pullback with empty source. -/
def ClosedBaseChange : Prop :=
  ∀ {U X V Y : TopCat.{0}} {j : U ⟶ X} {i : V ⟶ Y} {e : X ⟶ Y} {v : U ⟶ V}
    (_hi : IsClosedEmbedding i) (_hj : IsClosedEmbedding j) (h : j ≫ e = v ≫ i),
    Set.range j = e ⁻¹' Set.range i →
    ∀ (a : DerivedAdjunctions.{0}) (F : BoundedBelow V),
      IsIso (directImageComparison h (a j) (a i) F)

/-- The stage comparisons paste through the actual transition maps, with the
canonical pullback composition isomorphisms on both sides. -/
def StageComparisonPasting : Prop :=
  ∀ {X Y : TopCat.{0}} {J : JetSystem.{0}} {A : ClosedStages X}
    {B : StageJetActions J A} {i : Y ⟶ X} {S : JetAction J Y}
    (D : SupportIntersections B i S) (a : DerivedAdjunctions.{0}) (F : BoundedBelow Y)
    {n m : ℕ} (h : n ≤ m),
    let E := (derivedDirectImage i).obj F
    let σ := eqToIso (congrArg (fun f => (boundedBelowInverseImage f).obj E)
      (A.transition_inclusion h).symm) ≪≫
        (boundedBelowPullbackComposition (A.transition h) (A.inclusion m)).app E
    D.stageComparison a F n =
      σ.hom ≫ (boundedBelowInverseImage (A.transition h)).map (D.stageComparison a F m) ≫
        directImageComparison (D.transition_stage h).symm
          (a (D.intoStage n)) (a (D.intoStage m)) (D.intersectionRestriction F m) ≫
        (derivedDirectImage (D.intoStage n)).map (D.intersectionRestrictionComparison F h).inv

/-- Extend the local data to a single compatible equivariance on the union.
Where the whole support is contained in a stage, the same datum is realized
by the full-support comparison and the original two mates. -/
def ClosedExtensionAtStages : Prop :=
  ∀ {X Y : TopCat.{0}} {J : JetSystem.{0}} {A : ClosedStages X}
    {B : StageJetActions J A} {i : Y ⟶ X} {S : JetAction J Y}
    (_hi : IsClosedEmbedding i) (D : SupportIntersections B i S)
    (a : DerivedAdjunctions.{0}) (F : BoundedBelow Y)
    (α : S.Equivariance F.obj) (L : D.LocalEquivariance F α),
    ∃ β : B.Equivariance ((derivedDirectImage i).obj F).obj,
      RealizesStages D a L β ∧
        ∀ (n : ℕ) (j : Y ⟶ A.space n) (h : j ≫ A.inclusion n = i)
          (commutes : Intertwines S (B.stageAction n) j),
          IsIso (fullSupportComparison h a F) ∧ MatesAreIso commutes a F ∧
            AgreesWithMates commutes a α (β.datum n) (fullSupportComparison h a F)

/-- The ordinary stage comparisons are natural and the direct image of
a local equivariant map intertwines the global data. -/
def ClosedExtensionNaturality : Prop :=
  ∀ {X Y : TopCat.{0}} {J : JetSystem.{0}} {A : ClosedStages X}
    {B : StageJetActions J A} {i : Y ⟶ X} {S : JetAction J Y}
    (D : SupportIntersections B i S) (a : DerivedAdjunctions.{0})
    {F G : BoundedBelow Y} (f : F ⟶ G),
    (∀ n, (boundedBelowInverseImage (A.inclusion n)).map ((derivedDirectImage i).map f) ≫
        D.stageComparison a G n = D.stageComparison a F n ≫
          (derivedDirectImage (D.intoStage n)).map ((boundedBelowInverseImage (D.intoSupport n)).map f)) ∧
    ∀ {α : S.Equivariance F.obj} {γ : S.Equivariance G.obj}
      (L : D.LocalEquivariance F α) (M : D.LocalEquivariance G γ)
      {β : B.Equivariance ((derivedDirectImage i).obj F).obj}
      {δ : B.Equivariance ((derivedDirectImage i).obj G).obj},
      RealizesStages D a L β → RealizesStages D a M δ →
      (∀ n, ∀ (k : ℕ) (hk : (D.action n).cutoff ≤ k),
        let qf := ((boundedBelowInverseImage (D.intoSupport n)).map f).hom
        (derivedInverseImage ((D.action n).action k hk).act).map qf ≫
            ((M.datum n).datum k hk).iso.hom =
          ((L.datum n).datum k hk).iso.hom ≫
            (derivedInverseImage (AnalyticAction.projection (J.group k) (D.space n))).map qf) →
      ∃ g : (⟨((derivedDirectImage i).obj F).obj, β⟩ : B.Object) ⟶
          (⟨((derivedDirectImage i).obj G).obj, δ⟩ : B.Object),
        g.hom = ((derivedDirectImage i).map f).hom

/-- Perversity is preserved under the closed direct image into the containing
stage and gives finite-stage perversity on the union. -/
def ClosedExtensionPerverse : Prop :=
  ∀ {Y X : TopCat.{0}} (A : ClosedStages X)
    (P : Stratification Y) (Q : ∀ n, Stratification (A.space n)) (n : ℕ)
    (j : Y ⟶ A.space n) (_ : IsClosedEmbedding j) (_ : ClosedStrata j P (Q n))
    (F : BoundedBelow Y),
    IsMiddlePerverse P F.obj →
      IsMiddlePerverse (Q n) ((derivedDirectImage j).obj F).obj ∧
        IsFiniteStagePerverse A Q ((derivedDirectImage (j ≫ A.inclusion n)).obj F).obj

/-- The right-adjoint comparison through the closed point intertwines all
stagewise arrows whenever the input local point diagrams commute. -/
def ClosedPointCompositionEquivariant : Prop :=
  ∀ {X Y : TopCat.{0}} {J : JetSystem.{0}} {A : ClosedStages X}
    {B : StageJetActions J A} {i : Y ⟶ X} {x : Y}
    {S : JetAction J Y} {T : JetAction J (TopCat.of ({x} : Set Y))}
    (_hi : IsClosedEmbedding i) (hx : IsClosed ({x} : Set Y))
    (D : SupportIntersections B i S)
    (P : SupportIntersections B (closedInclusion ({x} : Set Y) ≫ i) T)
    (I : PointIntersectionMaps D P) (a : DerivedAdjunctions.{0})
    (b : boundedBelowInverseImage (closedInclusion ({x} : Set Y)) ⊣ closedExtensionPlus hx)
    {F : BoundedBelow (TopCat.of ({x} : Set Y))} {α : T.Equivariance F.obj}
    {γ : S.Equivariance ((closedExtensionPlus hx).obj F).obj}
    (Lₚ : P.LocalEquivariance F α) (L : D.LocalEquivariance ((closedExtensionPlus hx).obj F) γ)
    (β : B.Equivariance ((derivedDirectImage (closedInclusion ({x} : Set Y) ≫ i)).obj F).obj)
    (δ : B.Equivariance ((derivedDirectImage i).obj ((closedExtensionPlus hx).obj F)).obj),
    RealizesStages P a Lₚ β → RealizesStages D a L δ →
      LocalPointCompatibility D P I hx a b Lₚ L →
      ∃ g : (⟨((derivedDirectImage (closedInclusion ({x} : Set Y) ≫ i)).obj F).obj, β⟩ :
            B.Object) ⟶
          (⟨((derivedDirectImage i).obj ((closedExtensionPlus hx).obj F)).obj, δ⟩ : B.Object),
        g.hom = ((closedPointComposition hx i a b).hom.app F).hom

end Expected
end RepTheorySurvey.Geometric.FiniteStageClosedExtensionSpecs
