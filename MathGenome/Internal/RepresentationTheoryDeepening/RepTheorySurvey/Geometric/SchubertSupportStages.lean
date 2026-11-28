import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SchubertSupportStages
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeConvolutionSquare
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.CentralTranslationBoundedJetSupport
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory Topology
open scoped MatrixGroups

namespace RepTheorySurvey.Geometric.SchubertSupportStages

open Analytic Analytic.IntersectionComplex
open LatticeModelSpecs BoundedLatticeSpecs RankTwoSchubertStrataSpecs
open SchubertIntersectionConstructibilitySpecs EquivariantIntersectionComplexesSpecs
open MinusculeConvolutionSquareSpecs (Gr GrassmannianStages)
open MinusculeSupportIntersectionsSpecs (SupportInStage)
open FiniteStageClosedExtensionSpecs (SupportIntersections ClosedStrata)
open SchubertSupportStagesSpecs
open RankTwoSchubertStrata (reduceGL_surjective smul_mem_closureLattices)
open EquivariantIntersectionComplexes
  (invariantRange restrictJetAction restrictJetAction_commutes intertwines_apply
    intertwines_openSquare)

open private latticeStages latticeStageActions latticeStageStratification
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeConvolutionSquare
open private boundedVal_closedEmbedding from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ShortWindowTopology
open private boundedSubspace_injective from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.RankTwoSchubertStrata
open private boundedLoop from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.CentralTranslationBoundedJetSupport
open private SupportActionOnLattices stageTransition_intertwines factorIntoStage sameOrbitLabel
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeSupportIntersections
open private orbitLabel_bounded below_iff_orbitLabel orbitLabel_injective normalizedOrbitIC_realizes
  normalizedOrbitIC_perverse from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SchubertIntersectionConstructibility

private abbrev IntersectionSpace (T : ClosedStages Gr) {Y : TopCat.{0}} (i : Y ⟶ Gr)
    (n : ℕ) := TopCat.of (intersectionSet T i n)

private theorem intersectionToSupport_apply {T : ClosedStages Gr} {Y : TopCat.{0}} {i : Y ⟶ Gr}
    (hi : IsClosedEmbedding i) (n : ℕ) (x : IntersectionSpace T i n) :
    i (intersectionToSupport T i hi n x) = x.val.val := by
  let e := hi.isEmbedding.toHomeomorph
  exact congrArg Subtype.val (e.apply_symm_apply ⟨x.val.val, x.property⟩)

private def intersectionTransition (T : ClosedStages Gr) {Y : TopCat.{0}} (i : Y ⟶ Gr)
    {n m : ℕ} (h : n ≤ m) : IntersectionSpace T i n ⟶ IntersectionSpace T i m :=
  TopCat.ofHom ⟨fun x => ⟨T.transition h x.val, x.property⟩,
    ((T.transition h).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

private theorem intersectionInvariant {c : ContinuousJets} (D : GrassmannianStages c)
    {Y : TopCat.{0}} {i : Y ⟶ Gr} {ab : DominantPair} (hr : Set.range i = closureLattices ab)
    (n k : ℕ) (hk : (D.actions.stageAction n).cutoff ≤ k) :
    invariantRange ((D.actions.stageAction n).action k hk)
      (closedInclusion (intersectionSet D.stages i n)) := by
  intro q x
  obtain ⟨g, rfl⟩ := reduceGL_surjective 2 (k + 1) (Nat.succ_pos k) q
  let z := ((D.actions.stageAction n).action k hk).act
    (reduceGL 2 (k + 1) (Nat.succ_pos k) g, x.val)
  refine ⟨⟨z, ?_⟩, rfl⟩
  have hx : x.val.val ∈ Set.range i := x.property
  change z.val ∈ Set.range i
  rw [hr] at hx ⊢
  exact (D.actionOnLattices n k hk g x.val) ▸
    (smul_mem_closureLattices ab ⟨positiveGLMap 2 g, ⟨g, rfl⟩⟩ hx)

private def supportIntersections {c : ContinuousJets} (D : GrassmannianStages c)
    {Y : TopCat.{0}} {i : Y ⟶ Gr} {S : JetAction (jetSystem c) Y} {ab : DominantPair}
    (hi : IsClosedEmbedding i) (hr : Set.range i = closureLattices ab)
    (hS : SupportActionOnLattices i S) : SupportIntersections D.actions i S := by
  let s (n : ℕ) := closedInclusion (intersectionSet D.stages i n)
  let v := intersectionToSupport D.stages i hi
  have hClosed (n : ℕ) : IsClosedEmbedding (s n) :=
    (hi.isClosed_range.preimage (D.stages.inclusion n).hom.continuous).isClosedEmbedding_subtypeVal
  let C n := restrictJetAction (D.actions.stageAction n) (hClosed n).isEmbedding
    (intersectionInvariant D hr n)
  have hStage (n : ℕ) : Intertwines (C n) (D.actions.stageAction n) (s n) :=
    restrictJetAction_commutes (D.actions.stageAction n) (hClosed n).isEmbedding
      (intersectionInvariant D hr n)
  have hTrans {n m : ℕ} (h : n ≤ m) :
      intersectionTransition D.stages i h ≫ s m = s n ≫ D.stages.transition h :=
    TopCat.ext fun _ => rfl
  refine {
    space := IntersectionSpace D.stages i
    intoStage := s
    intoSupport := v
    closed := hClosed
    square := fun n => TopCat.ext fun x => (intersectionToSupport_apply hi n x).symm
    range_eq := ?_
    transition := intersectionTransition D.stages i
    transition_stage := hTrans
    transition_support := ?_
    action := C
    cutoff_le := fun _ => le_rfl
    stageActionSquare := hStage
    supportActionSquare := ?_
    transitionActionSquare := ?_ }
  · intro n
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  · intro n m h
    apply TopCat.ext
    intro x
    apply hi.injective
    change i (v m (intersectionTransition D.stages i h x)) = i (v n x)
    rw [intersectionToSupport_apply hi m, intersectionToSupport_apply hi n]
    rfl
  · intro n k hk hs
    apply TopCat.ext
    rintro ⟨q, x⟩
    obtain ⟨g, rfl⟩ := reduceGL_surjective 2 (k + 1) (Nat.succ_pos k) q
    let q := reduceGL 2 (k + 1) (Nat.succ_pos k) g
    apply hi.injective
    change i ((S.action k hs).act (q, v n x)) =
      i (v n (((C n).action k hk).act (q, x)))
    rw [hS k hs g, intersectionToSupport_apply hi n, intersectionToSupport_apply hi n]
    exact (D.actionOnLattices n k hk g x.val).symm.trans
      (congrArg Subtype.val (intertwines_apply (hStage n) k hk hk q x))
  · intro n m h
    exact intertwines_openSquare (hTrans h).symm (hClosed m).injective rfl rfl
      (hStage n) (stageTransition_intertwines D.actions h) (hStage m)

private theorem supportGeometry {c : ContinuousJets} (D : GrassmannianStages c)
    {ab : DominantPair} {M : ℕ} {hM : OrbitBound ab M} (A : SchubertJetAction c ab M hM) :
    Nonempty (SchubertStageSupport D A) := by
  obtain ⟨hZ, v, _, _, hCoords, _, _, _, _⟩ :=
    CentralTranslationBoundedJetSupport.boundedJetSupport c ab M hM A
  let Z := schubertLatticeSet ab M
  let b : TopCat.of (BoundedLattice 2 M) ⟶ Gr :=
    TopCat.ofHom ⟨Subtype.val, (boundedVal_closedEmbedding M).continuous⟩
  let i := v.hom ≫ closedInclusion (X := TopCat.of (BoundedLattice 2 M)) Z ≫ b
  have hi : IsClosedEmbedding i := (boundedVal_closedEmbedding M).comp
    (hZ.isClosedEmbedding_subtypeVal.comp (TopCat.homeoOfIso v).isClosedEmbedding)
  have hr : Set.range i = closureLattices ab := by
    ext L
    constructor
    · rintro ⟨y, rfl⟩
      exact (v.hom y).property
    · intro hL
      obtain ⟨B, rfl⟩ := RankTwoSchubertStrata.closureLattices_bounded hM hL
      let z : TopCat.of Z := ⟨B, hL⟩
      exact ⟨v.inv z, congrArg (fun q : TopCat.of Z => q.val.val)
        (ConcreteCategory.congr_hom v.inv_hom_id z)⟩
  have hAct : SupportActionOnLattices i A.action := by
    intro k hk g y
    have h := A.actual.2.1 k hk g y (v.hom y).val (hCoords y)
    rw [hCoords] at h
    exact congrArg Subtype.val (boundedSubspace_injective M
      (show boundedSubspace _ = boundedSubspace (boundedLoop g (v.hom y).val) from h))
  have hStage : Set.range i ⊆ D.stages.stage M := by
    rintro _ ⟨y, rfl⟩
    rw [D.isBoundedSet]
    exact (v.hom y).val.property
  let I := supportIntersections D hi hr hAct
  exact ⟨{
    inclusion := i
    closed := hi
    range_eq := hr
    coordinates := hCoords
    intersections := I
    space_eq := fun _ => rfl
    intoStage_eq := fun _ => (Category.id_comp _).symm
    intoSupport_eq := fun _ => (Category.id_comp _).symm
    cutoff_eq := fun _ => rfl
    fullSupport := factorIntoStage D.actionOnLattices hi hAct M hStage }⟩

private theorem stageOrbitOccupied {c : ContinuousJets} (D : GrassmannianStages c)
    (n : ℕ) (ab : DominantPair) (hb : OrbitBound ab n) :
    ∃ x : D.stages.space n, x.val ∈ gl2Orbit ab := by
  let B := diagonalBounded ab n hb
  exact ⟨⟨B.val, (D.isBoundedSet n).symm ▸ B.property⟩, MulAction.mem_orbit_self _⟩

private theorem orbitDimension_label (ab : DominantPair) (r : OrbitIndex ab) :
    difference (orbitLabel ab r) = orbitDimension ab r.val := by
  simp only [difference, orbitLabel, orbitDimension]
  omega

private theorem normalizedClosedImage {c : ContinuousJets} {D : GrassmannianStages c}
    (L : StageOrbitLabels D) {ab : DominantPair} {M : ℕ} {hM : OrbitBound ab M}
    {A : SchubertJetAction c ab M hM} (H : SchubertStageSupport D A) :
    NormalizedClosedImage L H := by
  classical
  let j := H.fullSupport.inclusion
  let Q := D.stratification M
  have hVal (y : SchubertSpace ab M hM) : (j y).val = H.inclusion y :=
    ConcreteCategory.congr_hom H.fullSupport.factors y
  have hMemRange (x : D.stages.space M) :
      x ∈ Set.range j ↔ x.val ∈ closureLattices ab := by
    rw [← H.range_eq]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, (hVal y).symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, Subtype.ext ((hVal y).trans hy)⟩
  have hOccupied (s : Q.Index) : (Set.range (Q.stratum s).inclusion).Nonempty := by
    rw [L.range_eq]
    exact stageOrbitOccupied D M (L.label M s) (L.bounded M s)
  have hLabelInj : Function.Injective (L.label M) := by
    intro s t hst
    obtain ⟨x, hx⟩ := hOccupied s
    have ht : x ∈ Set.range (Q.stratum t).inclusion := by
      rwa [L.range_eq M t, ← hst, ← L.range_eq M s]
    obtain ⟨_, _, hu⟩ := Q.partition x
    exact (hu s hx).trans (hu t ht).symm
  have hBelow (s : Q.Index) :
      Set.range (Q.stratum s).inclusion ⊆ Set.range j ↔ Below (L.label M s) ab := by
    constructor
    · intro hs
      obtain ⟨x, hx⟩ := hOccupied s
      obtain ⟨cd, hcd, hOrbit⟩ := (hMemRange x).mp (hs hx)
      rw [L.range_eq] at hx
      rwa [sameOrbitLabel hx hOrbit]
    · intro hs x hx
      rw [L.range_eq] at hx
      exact (hMemRange x).mpr ⟨L.label M s, hs, hx⟩
  refine ⟨hBelow, ?_⟩
  intro P F hF
  obtain ⟨_, _, e₀, he₀⟩ := normalizedOrbitIC_realizes hF
  let e : P.Index ≃ OrbitIndex ab :=
    e₀.trans (Equiv.subtypeUnivEquiv fun r => Nat.le_of_lt_succ r.isLt)
  have hP (p : P.Index) :
      Set.range (P.stratum p).inclusion = orbitPoints ab M hM (e p) ∧
      (P.stratum p).complexDimension = difference (orbitLabel ab (e p)) := by
    refine ⟨(he₀ p).1, (he₀ p).2.trans ?_⟩
    exact (orbitDimension_label ab (e p)).symm
  have hOrbit (y : SchubertSpace ab M hM) (r : OrbitIndex ab) :
      y ∈ orbitPoints ab M hM r ↔ (j y).val ∈ gl2Orbit (orbitLabel ab r) := by
    let B : BoundedLattice 2 M := ⟨(j y).val, by
      change (j y).val ∈ MinusculeConvolutionSquareSpecs.boundedSet M
      rw [← D.isBoundedSet M]
      exact (j y).property⟩
    have hB : schubertPointSubspace y = boundedSubspace B :=
      (H.coordinates y).trans (congrArg (latticeSubspace (-(M : ℤ)) (2 * M)) (hVal y).symm)
    constructor
    · rintro ⟨B', hB', hy⟩
      have he : B' = B := boundedSubspace_injective M (hy.symm.trans hB)
      rw [he] at hB'
      exact hB'
    · intro hy
      exact ⟨B, hy, hB⟩
  have hImage (p : P.Index) :
      j '' Set.range (P.stratum p).inclusion =
        {x | x.val ∈ gl2Orbit (orbitLabel ab (e p))} := by
    rw [(hP p).1]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hOrbit y (e p)).mp hy
    · intro hx
      have hb := (below_iff_orbitLabel ab (orbitLabel ab (e p))).2 ⟨e p, rfl⟩
      obtain ⟨y, rfl⟩ := (hMemRange x).2 ⟨_, hb, hx⟩
      exact ⟨y, (hOrbit y (e p)).mpr hx, rfl⟩
  have hMatch (p : P.Index) : ∃ s : Q.Index, L.label M s = orbitLabel ab (e p) := by
    obtain ⟨x, hx⟩ := stageOrbitOccupied D M _ (orbitLabel_bounded hM (e p))
    obtain ⟨s, hs, _⟩ := Q.partition x
    rw [L.range_eq] at hs
    exact ⟨s, sameOrbitLabel hs hx⟩
  choose s hs using hMatch
  have hMatchRange (p : P.Index) :
      Set.range (Q.stratum (s p)).inclusion = j '' Set.range (P.stratum p).inclusion := by
    rw [L.range_eq, hs, hImage]
  let f (p : P.Index) : {s : Q.Index // Set.range (Q.stratum s).inclusion ⊆ Set.range j} :=
    ⟨s p, (hBelow (s p)).mpr ((below_iff_orbitLabel ab _).2 ⟨e p, hs p⟩)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p p' h
      apply e.injective
      apply orbitLabel_injective ab
      exact (hs p).symm.trans ((congrArg (fun q => L.label M q.val) h).trans (hs p'))
    · intro t
      obtain ⟨r, hr⟩ := (below_iff_orbitLabel ab _).1 ((hBelow t.val).mp t.property)
      exact ⟨e.symm r, Subtype.ext (hLabelInj ((hs (e.symm r)).trans
        ((congrArg (orbitLabel ab) (e.apply_symm_apply r)).trans hr.symm)))⟩
  let C : ClosedStrata j P Q :=
    { index := Equiv.ofBijective f hf
      range_eq := hMatchRange
      dimension_eq := fun p => (L.dimension_eq M (s p)).trans
        ((congrArg difference (hs p)).trans (hP p).2.symm)
      disjoint := by
        intro t ht
        refine Set.disjoint_left.mpr fun x hx hx' => ht ((hBelow t).mpr ?_)
        obtain ⟨cd, hcd, horbit⟩ := (hMemRange x).mp hx'
        rw [L.range_eq] at hx
        rwa [sameOrbitLabel hx horbit] }
  refine ⟨e, C, fun p => ⟨(hP p).1, hs p⟩, ?_⟩
  have hp := FiniteStageClosedExtensions.closedExtensionPerverse D.stages P D.stratification M j
    H.fullSupport.closed C (complex F) (normalizedOrbitIC_perverse hF)
  rwa [H.fullSupport.factors] at hp

theorem schubertSupportStages : Expected.SchubertSupportStages := by
  classical
  intro c
  obtain ⟨B, hcutoff, hact⟩ := latticeStageActions c
  choose P label hBound hRange hDim using latticeStageStratification
  let D : GrassmannianStages c := ⟨latticeStages, fun _ => rfl, B, hcutoff, hact, P,
    fun n s => ⟨label n s, hRange n s, hDim n s⟩⟩
  let L : StageOrbitLabels D := ⟨label, hBound, hRange, hDim⟩
  refine ⟨D, L, ?_⟩
  intro ab M hM A
  obtain ⟨H⟩ := supportGeometry D A
  exact ⟨H, normalizedClosedImage L H⟩

end RepTheorySurvey.Geometric.SchubertSupportStages
