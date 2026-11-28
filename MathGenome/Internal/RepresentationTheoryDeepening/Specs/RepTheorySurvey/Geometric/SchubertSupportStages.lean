import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.MinusculeConvolutionSquare
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.MinusculeSupportIntersections

noncomputable section

set_option autoImplicit false

open CategoryTheory Topology

namespace RepTheorySurvey.Geometric.SchubertSupportStagesSpecs

open Analytic Analytic.IntersectionComplex
open LatticeModelSpecs BoundedLatticeSpecs RankTwoSchubertStrataSpecs
open SchubertIntersectionConstructibilitySpecs EquivariantIntersectionComplexesSpecs
open MinusculeConvolutionSquareSpecs (Gr GrassmannianStages)
open MinusculeSupportIntersectionsSpecs (SupportInStage)
open FiniteStageClosedExtensionSpecs (SupportIntersections ClosedStrata)

/-- Each stage stratum is the orbit of a label whose diagonal representative lies in
the stage's symmetric window. -/
structure StageOrbitLabels {c : ContinuousJets} (D : GrassmannianStages c) where
  label : ∀ n, (D.stratification n).Index → DominantPair
  bounded : ∀ n s, OrbitBound (label n s) n
  range_eq : ∀ n s, Set.range ((D.stratification n).stratum s).inclusion =
    {L | L.val ∈ gl2Orbit (label n s)}
  dimension_eq : ∀ n s, ((D.stratification n).stratum s).complexDimension =
    difference (label n s)

/-- The literal inverse-image subspace in a symmetric stage. -/
def intersectionSet (T : ClosedStages Gr) {Y : TopCat.{0}} (i : Y ⟶ Gr) (n : ℕ) :
    Set (T.space n) :=
  T.inclusion n ⁻¹' Set.range i

/-- Send the lattice of a stage intersection back to its unique point of the support. -/
def intersectionToSupport (T : ClosedStages Gr) {Y : TopCat.{0}} (i : Y ⟶ Gr)
    (hi : IsClosedEmbedding i) (n : ℕ) : TopCat.of (intersectionSet T i n) ⟶ Y :=
  let e := hi.isEmbedding.toHomeomorph.symm
  TopCat.ofHom ⟨fun x => e ⟨T.inclusion n x.val, x.property⟩,
    e.continuous.comp
      (((T.inclusion n).hom.continuous.comp continuous_subtype_val).subtype_mk
        (fun x : intersectionSet T i n => x.property))⟩

/-- The Schubert support in the union and its closed intersections with all symmetric stages. -/
structure SchubertStageSupport {c : ContinuousJets} (D : GrassmannianStages c)
    {ab : DominantPair} {M : ℕ} {hM : OrbitBound ab M} (A : SchubertJetAction c ab M hM) where
  inclusion : SchubertSpace ab M hM ⟶ Gr
  closed : IsClosedEmbedding inclusion
  range_eq : Set.range inclusion = closureLattices ab
  coordinates : ∀ p, schubertPointSubspace p =
    latticeSubspace (-(M : ℤ)) (2 * M) (inclusion p)
  intersections : SupportIntersections D.actions inclusion A.action
  space_eq : ∀ n, intersections.space n = TopCat.of (intersectionSet D.stages inclusion n)
  intoStage_eq : ∀ n, intersections.intoStage n =
    eqToHom (space_eq n) ≫ closedInclusion (intersectionSet D.stages inclusion n)
  intoSupport_eq : ∀ n, intersections.intoSupport n =
    eqToHom (space_eq n) ≫ intersectionToSupport D.stages inclusion closed n
  cutoff_eq : ∀ n, (intersections.action n).cutoff = (D.actions.stageAction n).cutoff
  fullSupport : SupportInStage D.actions inclusion A.action M

/-- The full orbit normalization matches precisely the strata inside the containing stage's
closed support. Closed direct image preserves its middle perversity there and on the union. -/
def NormalizedClosedImage {c : ContinuousJets} {D : GrassmannianStages c}
    (L : StageOrbitLabels D) {ab : DominantPair} {M : ℕ} {hM : OrbitBound ab M}
    {A : SchubertJetAction c ab M hM} (H : SchubertStageSupport D A) : Prop :=
  let j := H.fullSupport.inclusion
  (∀ s : (D.stratification M).Index,
    Set.range ((D.stratification M).stratum s).inclusion ⊆ Set.range j ↔
      Below (L.label M s) ab) ∧
  ∀ (P : Stratification (SchubertSpace ab M hM))
    (F : DimensionFiltration (SchubertSpace ab M hM) (orbitDimension ab (difference ab / 2))),
    IsNormalizedOrbitIC ab M hM (𝟙 _) (difference ab / 2) P F →
    ∃ (e : P.Index ≃ OrbitIndex ab) (C : ClosedStrata j P (D.stratification M)),
      (∀ p, Set.range (P.stratum p).inclusion = orbitPoints ab M hM (e p) ∧
        L.label M (C.index p).val = orbitLabel ab (e p)) ∧
      IsMiddlePerverse (D.stratification M) ((derivedDirectImage j).obj (complex F)).obj ∧
      IsFiniteStagePerverse D.stages D.stratification
        ((derivedDirectImage H.inclusion).obj (complex F)).obj

namespace Expected

/-- One choice of symmetric stages works for every occupied Schubert support and
every actual Schubert jet action. -/
def SchubertSupportStages : Prop :=
  ∀ c : ContinuousJets, ∃ (D : GrassmannianStages c) (L : StageOrbitLabels D),
    ∀ (ab : DominantPair) (M : ℕ) (hM : OrbitBound ab M) (A : SchubertJetAction c ab M hM),
      ∃ H : SchubertStageSupport D A, NormalizedClosedImage L H

end Expected
end RepTheorySurvey.Geometric.SchubertSupportStagesSpecs
