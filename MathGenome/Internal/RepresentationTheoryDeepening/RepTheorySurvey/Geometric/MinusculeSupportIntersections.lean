import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.MinusculeSupportIntersections
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.ClosedSupportPerversity
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeAndTwoStep
import Batteries.Tactic.OpenPrivate

noncomputable section

set_option autoImplicit false

open CategoryTheory Topology
open scoped MatrixGroups

namespace RepTheorySurvey.Geometric.MinusculeSupportIntersections

open Analytic
open LatticeModelSpecs MinusculeAndTwoStepSpecs RankTwoSchubertStrataSpecs
open ConvolutionUnitConeSpecs
open ConvolutionEquivariantSplittingSpecs (SplittingData)
open ConvolutionSplittingSpecs (orbitStratification)
open EquivariantIntersectionComplexesSpecs (ContinuousJets jetSystem Intertwines)
open EquivariantIntersectionComplexes
  (invariantRange restrictJetAction restrictJetAction_commutes intertwines_apply
    intertwines_openSquare)
open FiniteStageClosedExtensionSpecs (SupportIntersections PointIntersectionMaps ClosedStrata)
open MinusculeSupportIntersectionsSpecs

private abbrev StageActionOnLattices {c : ContinuousJets} {A : ClosedStages Gr}
    (B : StageJetActions (jetSystem c) A) : Prop :=
  ∀ n k (hk : (B.stageAction n).cutoff ≤ k) (g : GL (Fin 2) O) (L : A.space n),
    (((B.stageAction n).action k hk).act
      (reduceGL 2 (k + 1) (Nat.succ_pos k) g, L)).val = positiveGLMap 2 g • L.val

private abbrev SupportActionOnLattices {c : ContinuousJets} {Y : TopCat.{0}}
    (i : Y ⟶ Gr) (S : JetAction (jetSystem c) Y) : Prop :=
  ∀ k (hk : S.cutoff ≤ k) (g : GL (Fin 2) O) (y : Y),
    i ((S.action k hk).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, y)) =
      positiveGLMap 2 g • i y

private abbrev Intersection (A : ClosedStages Gr) {Y : TopCat.{0}} (i : Y ⟶ Gr) (n : ℕ) :=
  TopCat.of (i ⁻¹' A.stage n)

private def intersectionToStage (A : ClosedStages Gr) {Y : TopCat.{0}} (i : Y ⟶ Gr)
    (n : ℕ) : Intersection A i n ⟶ A.space n :=
  TopCat.ofHom ⟨fun y ↦ ⟨i y.val, y.property⟩,
    (i.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

private theorem intersectionToStage_closed (A : ClosedStages Gr) {Y : TopCat.{0}}
    {i : Y ⟶ Gr} (hi : IsClosedEmbedding i) (n : ℕ) :
    IsClosedEmbedding (intersectionToStage A i n) :=
  IsClosedEmbedding.of_comp IsEmbedding.subtypeVal
    (hi.comp ((A.closed n).preimage i.hom.continuous).isClosedEmbedding_subtypeVal)

private def intersectionTransition (A : ClosedStages Gr) {Y : TopCat.{0}} (i : Y ⟶ Gr)
    {n m : ℕ} (h : n ≤ m) : Intersection A i n ⟶ Intersection A i m :=
  TopCat.ofHom ⟨fun y ↦ ⟨y.val, A.monotone h y.property⟩, continuous_subtype_val.subtype_mk _⟩

private theorem stageTransition_intertwines {J : JetSystem.{0}} {A : ClosedStages Gr}
    (B : StageJetActions J A) {n m : ℕ} (h : n ≤ m) :
    Intertwines (B.stageAction n) (B.stageAction m) (A.transition h) := by
  intro k hn hm
  have e : J.parameterMap (le_refl k) (A.transition h) =
      ClosedEquivarianceExtensionSpecs.parameterInclusion (J.group k) (A.transition h) := by
    apply TopCat.ext
    intro p
    change ((J.truncate _ _ (le_refl k)) p.1, A.transition h p.2) =
      (p.1, A.transition h p.2)
    rw [J.truncate_id]
    rfl
  rw [← e]
  exact B.compatible h hn hm

private theorem intersectionInvariant {c : ContinuousJets} {A : ClosedStages Gr}
    {B : StageJetActions (jetSystem c) A} (hB : StageActionOnLattices B)
    {Y : TopCat.{0}} {i : Y ⟶ Gr} {S : JetAction (jetSystem c) Y}
    (hS : SupportActionOnLattices i S) (n k : ℕ) (hk : (B.stageAction n).cutoff ≤ k) :
    invariantRange ((B.stageAction n).action k hk) (intersectionToStage A i n) := by
  intro p y
  obtain ⟨g, rfl⟩ := RankTwoSchubertStrata.reduceGL_surjective 2 (k + 1) (Nat.succ_pos k) p
  let z := (S.action S.cutoff (le_refl _)).act
    (reduceGL 2 (S.cutoff + 1) (Nat.succ_pos _) g, y.val)
  let L := ((B.stageAction n).action k hk).act
    (reduceGL 2 (k + 1) (Nat.succ_pos k) g, intersectionToStage A i n y)
  have e : i z = L.val :=
    (hS _ (le_refl _) g y.val).trans (hB n k hk g (intersectionToStage A i n y)).symm
  have hz : i z ∈ A.stage n := e ▸ L.property
  exact ⟨⟨z, hz⟩, Subtype.ext e⟩

private def supportIntersections {c : ContinuousJets} {A : ClosedStages Gr}
    {B : StageJetActions (jetSystem c) A} (hB : StageActionOnLattices B)
    {Y : TopCat.{0}} {i : Y ⟶ Gr} (hi : IsClosedEmbedding i)
    {S : JetAction (jetSystem c) Y} (hS : SupportActionOnLattices i S) :
    SupportIntersections B i S := by
  let stageMap := intersectionToStage A i
  let supportMap (n : ℕ) : Intersection A i n ⟶ Y := closedInclusion (i ⁻¹' A.stage n)
  let hClosed := intersectionToStage_closed A hi
  let C (n : ℕ) := restrictJetAction (B.stageAction n) (hClosed n).isEmbedding
    (intersectionInvariant hB hS n)
  have hStage (n : ℕ) : Intertwines (C n) (B.stageAction n) (stageMap n) :=
    restrictJetAction_commutes (B.stageAction n) (hClosed n).isEmbedding
      (intersectionInvariant hB hS n)
  refine
    { space := Intersection A i
      intoStage := stageMap
      intoSupport := supportMap
      closed := hClosed
      square := fun _ ↦ TopCat.ext fun _ ↦ rfl
      range_eq := ?_
      transition := intersectionTransition A i
      transition_stage := fun _ ↦ TopCat.ext fun _ ↦ rfl
      transition_support := fun _ ↦ TopCat.ext fun _ ↦ rfl
      action := C
      cutoff_le := fun _ ↦ le_rfl
      stageActionSquare := hStage
      supportActionSquare := ?_
      transitionActionSquare := ?_ }
  · intro n
    ext L
    change (∃ y : Intersection A i n, stageMap n y = L) ↔ ∃ y : Y, i y = L.val
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.val, rfl⟩
    · rintro ⟨y, hy⟩
      have hy' : i y ∈ A.stage n := by
        rw [hy]
        exact L.property
      exact ⟨⟨y, hy'⟩, Subtype.ext hy⟩
  · intro n k hk hs
    apply TopCat.ext
    rintro ⟨p, y⟩
    obtain ⟨g, rfl⟩ := RankTwoSchubertStrata.reduceGL_surjective 2 (k + 1) (Nat.succ_pos k) p
    apply hi.injective
    have e := congrArg Subtype.val
      (intertwines_apply (hStage n) k hk hk
        (reduceGL 2 (k + 1) (Nat.succ_pos k) g) y)
    change i ((S.action k hs).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, y.val)) =
      i (((C n).action k hk).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, y)).val
    change (((B.stageAction n).action k hk).act
      (reduceGL 2 (k + 1) (Nat.succ_pos k) g, stageMap n y)).val =
        i (((C n).action k hk).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, y)).val at e
    exact (hS _ hs g y.val).trans ((hB n k hk g (stageMap n y)).symm.trans e)
  · intro n m h
    exact intertwines_openSquare (j := stageMap n) (k := stageMap m)
      (e := A.transition h) (v := intersectionTransition A i h)
      (TopCat.ext fun _ ↦ rfl) (hClosed m).injective
      rfl rfl (hStage n) (stageTransition_intertwines B h) (hStage m)

private def factorIntoStage {c : ContinuousJets} {A : ClosedStages Gr}
    {B : StageJetActions (jetSystem c) A} (hB : StageActionOnLattices B)
    {Y : TopCat.{0}} {i : Y ⟶ Gr} (hi : IsClosedEmbedding i)
    {S : JetAction (jetSystem c) Y} (hS : SupportActionOnLattices i S)
    (n : ℕ) (h : Set.range i ⊆ A.stage n) : SupportInStage B i S n := by
  let f : Y ⟶ A.space n :=
    TopCat.ofHom ⟨fun y ↦ ⟨i y, h (Set.mem_range_self y)⟩, i.hom.continuous.subtype_mk _⟩
  refine ⟨f, IsClosedEmbedding.of_comp IsEmbedding.subtypeVal hi, TopCat.ext fun _ ↦ rfl, ?_⟩
  intro k hs hk
  apply TopCat.ext
  rintro ⟨p, y⟩
  obtain ⟨g, rfl⟩ := RankTwoSchubertStrata.reduceGL_surjective 2 (k + 1) (Nat.succ_pos k) p
  apply Subtype.ext
  change (((B.stageAction n).action k hk).act
    (reduceGL 2 (k + 1) (Nat.succ_pos k) g, f y)).val =
    i ((S.action k hs).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, y))
  rw [hB, hS]
  rfl

private theorem pointEmbedding_value (d : SplittingData) {j₂ : surface ⟶ Gr}
    (hScalar : j₂ d.point = scalarPoint) (p : Point d) :
    pointEmbedding d j₂ p = scalarPoint := by
  change j₂ p.val = scalarPoint
  rw [show p.val = d.point from p.property, hScalar]

private theorem pointActionOnLattices {c : ContinuousJets} (d : SplittingData)
    {j₂ : surface ⟶ Gr} (hScalar : j₂ d.point = scalarPoint)
    (S : JetAction (jetSystem c) (Point d)) :
    SupportActionOnLattices (pointEmbedding d j₂) S := by
  intro k hk g p
  rw [pointEmbedding_value d hScalar, pointEmbedding_value d hScalar]
  exact (positiveGL_preserves_scalar g 1).symm

private def pointIntersectionMaps {c : ContinuousJets} {A : ClosedStages Gr}
    {B : StageJetActions (jetSystem c) A} (hB : StageActionOnLattices B)
    (d : SplittingData) {j₂ : surface ⟶ Gr}
    (hi : IsClosedEmbedding j₂) (hp : IsClosedEmbedding (pointEmbedding d j₂))
    {S₂ : JetAction (jetSystem c) surface} {Sₚ : JetAction (jetSystem c) (Point d)}
    (hS₂ : SupportActionOnLattices j₂ S₂)
    (hSₚ : SupportActionOnLattices (pointEmbedding d j₂) Sₚ) :
    PointIntersectionMaps (supportIntersections hB hi hS₂) (supportIntersections hB hp hSₚ) := by
  let D := supportIntersections hB hi hS₂
  let T := supportIntersections hB hp hSₚ
  let q (n : ℕ) : T.space n ⟶ D.space n :=
    TopCat.ofHom ⟨fun p ↦ ⟨p.val.val, p.property⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  have hStage (n : ℕ) (p : T.space n) : D.intoStage n (q n p) = T.intoStage n p := rfl
  refine ⟨q, fun n ↦ TopCat.ext (hStage n), fun _ ↦ TopCat.ext fun _ ↦ rfl, ?_⟩
  intro n k hp' hd'
  apply TopCat.ext
  rintro ⟨g, p⟩
  apply (D.closed n).injective
  change D.intoStage n (((D.action n).action k hd').act (g, q n p)) =
    D.intoStage n (q n (((T.action n).action k hp').act (g, p)))
  have hs₁ : (B.stageAction n).cutoff ≤ k := (T.cutoff_le n).trans hp'
  have hs₂ : (B.stageAction n).cutoff ≤ k := (D.cutoff_le n).trans hd'
  rw [← intertwines_apply (D.stageActionSquare n) k hd' hs₂,
    hStage, hStage, ← intertwines_apply (T.stageActionSquare n) k hp' hs₁]

private theorem twoStepOrbitCases {L : Gr} (h : L ∈ colength 2) :
    L ∈ gl2Orbit twoStepPair ∨ L ∈ gl2Orbit scalarPair := by
  rw [MinusculeAndTwoStep.twoStepOrbits.2.1, MinusculeAndTwoStep.twoStepOrbits.2.2.1]
  by_cases hs : L ∈ ({scalarPoint} : Set Gr)
  · exact Or.inr hs
  · exact Or.inl ⟨h, hs⟩

private theorem noMinusculeAtZero {L : Gr} (h : L ∈ colength 1) (h₀ : L ∈ boundedSet 0) :
    False := by
  rw [MinusculeAndTwoStep.minusculeOrbit.1] at h
  have he := ((RankTwoSchubertStrata.orbit_endpoints h).1 0).mp h₀.1
  change (1 : ℤ) ≤ 0 at he
  omega

private theorem noTerminalAtZero {L : Gr} (h : L ∈ colength 2) (h₀ : L ∈ boundedSet 0) :
    False := by
  rcases twoStepOrbitCases h with h | h
  · have he := ((RankTwoSchubertStrata.orbit_endpoints h).1 0).mp h₀.1
    change (2 : ℤ) ≤ 0 at he
    omega
  · have he := ((RankTwoSchubertStrata.orbit_endpoints h).1 0).mp h₀.1
    change (1 : ℤ) ≤ 0 at he
    omega

private theorem terminalAtOne {L : Gr} (h : L ∈ colength 2) :
    L ∈ boundedSet 1 ↔ L = scalarPoint := by
  constructor
  · intro h₁
    rcases twoStepOrbitCases h with h | h
    · have he := ((RankTwoSchubertStrata.orbit_endpoints h).1 1).mp h₁.1
      change (2 : ℤ) ≤ 1 at he
      omega
    · rwa [MinusculeAndTwoStep.twoStepOrbits.2.1] at h
  · rintro rfl
    exact ⟨le_rfl, diagonalLattice_le (fun _ ↦ by decide)⟩

open private colength_bound from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MinusculeAndTwoStep

private theorem colength_inStageTwo {L : Gr} {m : ℕ} (hm : m ≤ 2) (h : L ∈ colength m) :
    L ∈ boundedSet 2 := by
  have hLower : (scalarLattice 2 2).val ≤ (scalarLattice 2 (m : ℤ)).val :=
    diagonalLattice_le (fun _ ↦ by exact_mod_cast hm)
  have hUpper : (scalarLattice 2 0).val ≤ (scalarLattice 2 (-2)).val :=
    diagonalLattice_le (fun _ ↦ by decide)
  exact ⟨hLower.trans (colength_bound h), h.1.trans hUpper⟩

private theorem intersectionAtZero {A : ClosedStages Gr}
    (hA : A.stage 0 = boundedSet 0) {Y : TopCat.{0}} {i : Y ⟶ Gr}
    (hEmpty : ∀ {L : Gr}, L ∈ Set.range i → L ∈ boundedSet 0 → False) :
    IsEmpty (Intersection A i 0) := by
  constructor
  intro y
  exact hEmpty (Set.mem_range_self y.val) (hA ▸ y.property)

private theorem intersectionLevels {c : ContinuousJets} {A : ClosedStages Gr}
    {B : StageJetActions (jetSystem c) A} (hB : StageActionOnLattices B)
    (hCutoff : ∀ n, (B.stageAction n).cutoff = 2 * n - 1)
    {Y : TopCat.{0}} {i : Y ⟶ Gr} (hi : IsClosedEmbedding i)
    {S : JetAction (jetSystem c) Y} (hS : SupportActionOnLattices i S) (hCut : S.cutoff ≤ 1)
    (hEmpty : IsEmpty (Intersection A i 0)) (n k : ℕ)
    (hk : ((supportIntersections hB hi hS).action n).cutoff ≤ k) :
    S.cutoff ≤ k ∨ IsEmpty ((supportIntersections hB hi hS).space n) := by
  cases n with
  | zero => exact Or.inr hEmpty
  | succ n =>
    left
    change (B.stageAction (n + 1)).cutoff ≤ k at hk
    rw [hCutoff] at hk
    exact hCut.trans (by omega)

private def supportGeometry {c : ContinuousJets} (A : ClosedStages Gr)
    (B : StageJetActions (jetSystem c) A)
    (hA : ∀ n, A.stage n = boundedSet n)
    (hCut : ∀ n, (B.stageAction n).cutoff = 2 * n - 1) (hB : StageActionOnLattices B)
    (d : SplittingData) {j₁ : minuscule ⟶ Gr} {j₂ : surface ⟶ Gr}
    (hj₁ : IsClosedEmbedding j₁) (hj₂ : IsClosedEmbedding j₂)
    (hr₁ : Set.range j₁ = colength 1) (hr₂ : Set.range j₂ = colength 2)
    (hScalar : j₂ d.point = scalarPoint)
    {S₁ : JetAction (jetSystem c) minuscule} {S₂ : JetAction (jetSystem c) surface}
    (Sₚ : JetAction (jetSystem c) (Point d))
    (hc₁ : S₁.cutoff ≤ 1) (hc₂ : S₂.cutoff ≤ 1) (hcₚ : Sₚ.cutoff ≤ 1)
    (ha₁ : SupportActionOnLattices j₁ S₁) (ha₂ : SupportActionOnLattices j₂ S₂) :
    SupportGeometry B d j₁ j₂ S₁ S₂ Sₚ := by
  let jₚ := pointEmbedding d j₂
  have hjₚ : IsClosedEmbedding jₚ := hj₂.comp d.closed.isClosedEmbedding_subtypeVal
  have haₚ : SupportActionOnLattices jₚ Sₚ := pointActionOnLattices d hScalar Sₚ
  have hPointRange : Set.range jₚ ⊆ Set.range j₂ := by
    rintro _ ⟨p, rfl⟩
    exact ⟨p.val, rfl⟩
  have hEmpty₁ : IsEmpty (Intersection A j₁ 0) :=
    intersectionAtZero (hA 0) (fun h ↦ noMinusculeAtZero (hr₁ ▸ h))
  have hEmpty₂ : IsEmpty (Intersection A j₂ 0) :=
    intersectionAtZero (hA 0) (fun h ↦ noTerminalAtZero (hr₂ ▸ h))
  have hEmptyₚ : IsEmpty (Intersection A jₚ 0) :=
    intersectionAtZero (hA 0) (fun h ↦ noTerminalAtZero (hr₂ ▸ hPointRange h))
  have hStage₁ : Set.range j₁ ⊆ A.stage 2 := by
    rw [hr₁, hA]
    exact fun _ h ↦ colength_inStageTwo (by decide) h
  have hStage₂ : Set.range j₂ ⊆ A.stage 2 := by
    rw [hr₂, hA]
    exact fun _ h ↦ colength_inStageTwo le_rfl h
  let D₁ := supportIntersections hB hj₁ ha₁
  let D₂ := supportIntersections hB hj₂ ha₂
  let Dₚ := supportIntersections hB hjₚ haₚ
  refine
    { first := D₁
      terminal := D₂
      scalar := Dₚ
      pointMaps := pointIntersectionMaps hB d hj₂ hjₚ ha₂ haₚ
      firstAtZero := hEmpty₁
      terminalAtZero := hEmpty₂
      scalarAtZero := hEmptyₚ
      terminalAtOne := ?_
      firstLevels := intersectionLevels hB hCut hj₁ ha₁ hc₁ hEmpty₁
      terminalLevels := intersectionLevels hB hCut hj₂ ha₂ hc₂ hEmpty₂
      scalarLevels := intersectionLevels hB hCut hjₚ haₚ hcₚ hEmptyₚ
      pointTerminalLevels := ?_
      firstInStage := fun n hn ↦ factorIntoStage hB hj₁ ha₁ n (hStage₁.trans (A.monotone hn))
      terminalInStage := fun n hn ↦ factorIntoStage hB hj₂ ha₂ n (hStage₂.trans (A.monotone hn))
      scalarInStage := fun n hn ↦ factorIntoStage hB hjₚ haₚ n
        (hPointRange.trans (hStage₂.trans (A.monotone hn))) }
  · ext y
    change (∃ p : Intersection A j₂ 1, p.val = y) ↔ y ∈ ({d.point} : Set surface)
    constructor
    · rintro ⟨p, rfl⟩
      have h := (terminalAtOne (hr₂ ▸ Set.mem_range_self (f := j₂) p.val)).mp
        (hA 1 ▸ p.property)
      exact hj₂.injective (h.trans hScalar.symm)
    · rintro rfl
      have h := (terminalAtOne (hr₂ ▸ Set.mem_range_self (f := j₂) d.point)).mpr hScalar
      exact ⟨⟨d.point, (hA 1).symm ▸ h⟩, rfl⟩
  · intro n k hk _
    cases n with
    | zero => exact Or.inr hEmptyₚ
    | succ n =>
      left
      change (B.stageAction (n + 1)).cutoff ≤ k at hk
      rw [hCut] at hk
      have h : 1 ≤ k := by omega
      exact ⟨hcₚ.trans h, hc₂.trans h⟩


private theorem stageOrbit_occupied {A : ClosedStages Gr} (hA : A.stage 2 = boundedSet 2)
    (ab : DominantPair) (hb : OrbitBound ab 2) :
    ∃ L : A.space 2, L.val ∈ gl2Orbit ab := by
  let L := diagonalBounded ab 2 hb
  exact ⟨⟨L.val, hA.symm ▸ L.property⟩, MulAction.mem_orbit_self _⟩

private theorem sameOrbitLabel {ab cd : DominantPair} {L : Gr}
    (ha : L ∈ gl2Orbit ab) (hc : L ∈ gl2Orbit cd) : ab = cd := by
  obtain ⟨_, _, h⟩ := RankTwoSchubertStrata.smithClassification.1 L
  exact (h _ ha).trans (h _ hc).symm

private theorem closedStrataFromOrbits {A : ClosedStages Gr} (hA : A.stage 2 = boundedSet 2)
    (Q : Stratification (A.space 2)) (label : Q.Index → DominantPair)
    (hBound : ∀ q, OrbitBound (label q) 2)
    (hRange : ∀ q, Set.range (Q.stratum q).inclusion = {L | L.val ∈ gl2Orbit (label q)})
    (hDim : ∀ q, (Q.stratum q).complexDimension = difference (label q))
    {Y : TopCat.{0}} (j : Y ⟶ A.space 2) (hj : Function.Injective j)
    (P : Stratification Y) (sourceLabel : P.Index → DominantPair)
    (hSourceBound : ∀ p, OrbitBound (sourceLabel p) 2)
    (hSourceRange : ∀ p,
      j '' Set.range (P.stratum p).inclusion = {L | L.val ∈ gl2Orbit (sourceLabel p)})
    (hSourceDim : ∀ p, (P.stratum p).complexDimension = difference (sourceLabel p)) :
    ∃ C : ClosedStrata j P Q, ∀ p, label (C.index p).val = sourceLabel p := by
  classical
  have hOccupied (q : Q.Index) : (Set.range (Q.stratum q).inclusion).Nonempty := by
    rw [hRange]
    exact stageOrbit_occupied hA (label q) (hBound q)
  have hMatch (p : P.Index) : ∃ q, label q = sourceLabel p := by
    obtain ⟨L, hL⟩ := stageOrbit_occupied hA _ (hSourceBound p)
    obtain ⟨q, hq, _⟩ := Q.partition L
    rw [hRange] at hq
    exact ⟨q, sameOrbitLabel hq hL⟩
  choose q hLabel using hMatch
  have hMatchRange (p : P.Index) :
      Set.range (Q.stratum (q p)).inclusion = j '' Set.range (P.stratum p).inclusion := by
    rw [hRange, hLabel, hSourceRange]
  have hUnique {L : A.space 2} {a b : Q.Index}
      (ha : L ∈ Set.range (Q.stratum a).inclusion) (hb : L ∈ Set.range (Q.stratum b).inclusion) :
      a = b := by
    obtain ⟨_, _, h⟩ := Q.partition L
    exact (h _ ha).trans (h _ hb).symm
  let f : P.Index → {q : Q.Index // Set.range (Q.stratum q).inclusion ⊆ Set.range j} :=
    fun p ↦ ⟨q p, by
      rw [hMatchRange]
      rintro _ ⟨y, _, rfl⟩
      exact Set.mem_range_self y⟩
  have hInj : Function.Injective f := by
    intro a b hab
    have he : q a = q b := congrArg Subtype.val hab
    obtain ⟨L, hL⟩ := hOccupied (q a)
    have hL' := he ▸ hL
    rw [hMatchRange a] at hL
    rw [hMatchRange b] at hL'
    obtain ⟨y, hy, hyL⟩ := hL
    obtain ⟨z, hz, hzL⟩ := hL'
    have e : y = z := hj (hyL.trans hzL.symm)
    obtain ⟨_, _, h⟩ := P.partition y
    exact (h _ hy).trans (h _ (e ▸ hz)).symm
  have hOfPoint {y : Y} {a : Q.Index} (hy : j y ∈ Set.range (Q.stratum a).inclusion) :
      ∃ p, q p = a := by
    obtain ⟨p, hp, _⟩ := P.partition y
    have h : j y ∈ Set.range (Q.stratum (q p)).inclusion := by
      rw [hMatchRange]
      exact ⟨y, hp, rfl⟩
    exact ⟨p, hUnique h hy⟩
  have hSurj : Function.Surjective f := by
    intro a
    obtain ⟨L, hL⟩ := hOccupied a.val
    obtain ⟨y, rfl⟩ := a.property hL
    obtain ⟨p, hp⟩ := hOfPoint hL
    exact ⟨p, Subtype.ext hp⟩
  refine ⟨⟨Equiv.ofBijective f ⟨hInj, hSurj⟩, hMatchRange, ?_, ?_⟩, hLabel⟩
  · intro p
    change (Q.stratum (q p)).complexDimension = (P.stratum p).complexDimension
    rw [hDim, hLabel, hSourceDim]
  · intro a ha
    apply Set.disjoint_left.mpr
    intro L hL hL'
    obtain ⟨y, rfl⟩ := hL'
    obtain ⟨p, hp⟩ := hOfPoint hL
    exact ha (hp ▸ (f p).property)

private theorem wholeStratum_range (X : TopCat.{0}) (d : ℕ) (s : (wholeStratum X d).Index) :
    Set.range ((wholeStratum X d).stratum s).inclusion = Set.univ :=
  Set.eq_univ_of_forall fun x ↦ ⟨⟨⟨x, Set.mem_univ x⟩, Set.mem_univ _⟩, rfl⟩

private theorem imageAlongFactor {A : ClosedStages Gr} {Y : TopCat.{0}}
    {j : Y ⟶ A.space 2} {i : Y ⟶ Gr} (hf : j ≫ A.inclusion 2 = i)
    {s : Set Y} {t : Set Gr} (h : i '' s = t) :
    j '' s = {L | L.val ∈ t} := by
  have he (y : Y) : (j y).val = i y := congrArg (fun f : Y ⟶ Gr ↦ f y) hf
  ext L
  change L ∈ j '' s ↔ L.val ∈ t
  rw [← h]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (he y).symm⟩
  · rintro ⟨y, hy, hL⟩
    exact ⟨y, hy, Subtype.ext ((he y).trans hL)⟩

private theorem scalar_range (d : SplittingData) {j₂ : surface ⟶ Gr}
    (hScalar : j₂ d.point = scalarPoint) : Set.range (pointEmbedding d j₂) = {scalarPoint} := by
  ext L
  constructor
  · rintro ⟨p, rfl⟩
    exact pointEmbedding_value d hScalar p
  · rintro rfl
    exact ⟨⟨d.point, rfl⟩, pointEmbedding_value d hScalar _⟩

private theorem scalarPair_bound : OrbitBound scalarPair 2 := by
  intro i
  fin_cases i <;> decide

private theorem minusculePair_bound : OrbitBound minusculePair 2 := by
  intro i
  fin_cases i <;> decide

private theorem twoStepPair_bound : OrbitBound twoStepPair 2 := by
  intro i
  fin_cases i <;> decide

private theorem stageTwoStrata {A : ClosedStages Gr} (hA : A.stage 2 = boundedSet 2)
    (Q : Stratification (A.space 2)) (label : Q.Index → DominantPair)
    (hBound : ∀ q, OrbitBound (label q) 2)
    (hRange : ∀ q, Set.range (Q.stratum q).inclusion = {L | L.val ∈ gl2Orbit (label q)})
    (hDim : ∀ q, (Q.stratum q).complexDimension = difference (label q))
    (d : SplittingData) {j₁ : minuscule ⟶ Gr} {j₂ : surface ⟶ Gr}
    (hj₂ : IsClosedEmbedding j₂)
    (hr₁ : Set.range j₁ = colength 1) (hr₂ : Set.range j₂ = colength 2)
    (hScalar : j₂ d.point = scalarPoint)
    {i₁ : minuscule ⟶ A.space 2} {i₂ : surface ⟶ A.space 2} {iₚ : Point d ⟶ A.space 2}
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂) (hiₚ : Function.Injective iₚ)
    (hf₁ : i₁ ≫ A.inclusion 2 = j₁) (hf₂ : i₂ ≫ A.inclusion 2 = j₂)
    (hfₚ : iₚ ≫ A.inclusion 2 = pointEmbedding d j₂) :
    Nonempty (StageTwoStrata d Q label i₁ i₂ iₚ) := by
  have hFirst (p : (wholeStratum minuscule 1).Index) :
      i₁ '' Set.range ((wholeStratum minuscule 1).stratum p).inclusion =
        {L | L.val ∈ gl2Orbit minusculePair} := by
    apply imageAlongFactor hf₁
    rw [wholeStratum_range, Set.image_univ, hr₁, MinusculeAndTwoStep.minusculeOrbit.1]
  have hPoint (p : (wholeStratum (Point d) 0).Index) :
      iₚ '' Set.range ((wholeStratum (Point d) 0).stratum p).inclusion =
        {L | L.val ∈ gl2Orbit scalarPair} := by
    apply imageAlongFactor hfₚ
    rw [wholeStratum_range, Set.image_univ, scalar_range d hScalar,
      MinusculeAndTwoStep.twoStepOrbits.2.1]
  let P := orbitStratification d.point d.closed
  let labels (b : Bool) := if b then twoStepPair else scalarPair
  have hTerminal (p : P.Index) :
      i₂ '' Set.range (P.stratum p).inclusion = {L | L.val ∈ gl2Orbit (labels p)} := by
    have hImage : j₂ '' ({d.point} : Set surface) = {scalarPoint} := by
      rw [Set.image_singleton, hScalar]
    apply imageAlongFactor hf₂
    change Bool at p
    cases p
    · change j₂ '' Set.range (ConvolutionSplittingSpecs.closedOrbitStratum d.point d.closed).inclusion =
        gl2Orbit scalarPair
      rw [ConvolutionSplittingSpecs.closedOrbitStratum_range, hImage,
        MinusculeAndTwoStep.twoStepOrbits.2.1]
    · change j₂ '' Set.range (ConvolutionSplittingSpecs.openOrbitStratum d.point d.closed).inclusion =
        gl2Orbit twoStepPair
      rw [ConvolutionSplittingSpecs.openOrbitStratum_range,
        Set.image_compl_eq_range_sdiff_image hj₂.injective, hr₂, hImage,
        MinusculeAndTwoStep.twoStepOrbits.2.2.1]
  have hTerminalBound (p : P.Index) : OrbitBound (labels p) 2 := by
    change Bool at p
    cases p
    · exact scalarPair_bound
    · exact twoStepPair_bound
  have hTerminalDim (p : P.Index) : (P.stratum p).complexDimension = difference (labels p) := by
    change Bool at p
    cases p <;> rfl
  obtain ⟨C₁, e₁⟩ := closedStrataFromOrbits hA Q label hBound hRange hDim i₁ hi₁
    (wholeStratum minuscule 1) (fun _ ↦ minusculePair) (fun _ ↦ minusculePair_bound)
    hFirst (fun _ ↦ rfl)
  obtain ⟨C₂, e₂⟩ := closedStrataFromOrbits hA Q label hBound hRange hDim i₂ hi₂
    P labels hTerminalBound hTerminal hTerminalDim
  obtain ⟨Cₚ, eₚ⟩ := closedStrataFromOrbits hA Q label hBound hRange hDim iₚ hiₚ
    (wholeStratum (Point d) 0) (fun _ ↦ scalarPair) (fun _ ↦ scalarPair_bound)
    hPoint (fun _ ↦ rfl)
  exact ⟨⟨C₁, C₂, Cₚ, e₁ (), e₂ true, e₂ false, eₚ ()⟩⟩

open private shiftedConstant_isMiddlePerverse
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.SchubertIntersectionConstructibility
open private locallyConstantFiniteRank_of_iso from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.MiddleExtension

private theorem middlePerverse_of_iso {X : TopCat.{0}} (P : Stratification X)
    {F G : BoundedBelow X} (e : F.obj ≅ G.obj) (h : IsMiddlePerverse P F.obj) :
    IsMiddlePerverse P G.obj := by
  let a := (Functor.FullyFaithful.ofFullyFaithful
    (DerivedCategory.Plus.ι (C := Sheaves X))).preimageIso e
  obtain ⟨⟨hf, hc⟩, _, hb⟩ := h
  refine ⟨⟨hf.subset ?_, ?_⟩, G.property, ?_⟩
  · intro n hn hz
    exact hn (hz.of_iso ((cohomology X n).mapIso e.symm))
  · intro s n
    exact locallyConstantFiniteRank_of_iso
      ((cohomology X n ⋙ inverseImage (P.stratum s).inclusion).mapIso e) (hc s n)
  · intro s
    refine ⟨fun n hn ↦ ?_, fun n hn ↦ ?_⟩
    · exact ((hb s).1 n hn).of_iso (((P.stratum s).star ⋙
        cohomology (P.stratum s).space n).mapIso e.symm)
    · exact ((hb s).2 n hn).of_iso (((P.stratum s).shriek ⋙
        DerivedCategory.Plus.homologyFunctor _ n).mapIso a.symm)

private theorem point_perverse (d : SplittingData) :
    IsMiddlePerverse (wholeStratum (Point d) 0) (IntersectionComplex.point d.point).obj := by
  let e : (IntersectionComplex.shiftedConstant (Point d) 0).obj ≅
      (IntersectionComplex.point d.point).obj :=
    (shiftFunctorZero (Derived (Point d)) ℤ).app _
  exact middlePerverse_of_iso _ e
    (shiftedConstant_isMiddlePerverse _ 0 (wholeStratum_range _ _) (fun _ ↦ rfl))

private theorem perverseImageAtTwo {J : JetSystem.{0}} {A : ClosedStages Gr}
    {B : StageJetActions J A} {Y : TopCat.{0}} {i : Y ⟶ Gr} {S : JetAction J Y}
    (P : Stratification Y) (Q : ∀ n, Stratification (A.space n))
    (T : SupportInStage B i S 2) (C : ClosedStrata T.inclusion P (Q 2))
    (F : BoundedBelow Y) (hF : IsMiddlePerverse P F.obj) :
    PerverseClosedImage Q T.inclusion i F := by
  obtain ⟨hStage, hUnion⟩ := ClosedSupportPerversity.closedExtensionPerverse
    A P Q 2 T.inclusion T.closed C.index C.range_eq C.dimension_eq C.disjoint F hF
  exact ⟨hStage, by simpa only [T.factors] using hUnion⟩

/-- The actual minuscule, terminal, and scalar supports inherit compatible stage
actions, and their normalized complexes extend perversely through stage two. -/
theorem minusculeSupportIntersections : Expected.MinusculeSupportIntersections := by
  intro c A B hA hCut hB Q label hBound hRange hDim d j₁ j₂ hj₁ hj₂ hr₁ hr₂ hScalar
    S₁ S₂ Sₚ hc₁ hc₂ hcₚ ha₁ ha₂ _
  let G := supportGeometry A B hA hCut hB d hj₁ hj₂ hr₁ hr₂ hScalar Sₚ hc₁ hc₂ hcₚ ha₁ ha₂
  let T₁ := G.firstInStage 2 le_rfl
  let T₂ := G.terminalInStage 2 le_rfl
  let Tₚ := G.scalarInStage 2 le_rfl
  have hm := stageTwoStrata (hA 2) (Q 2) label hBound hRange hDim d hj₂ hr₁ hr₂ hScalar
    T₁.closed.injective T₂.closed.injective Tₚ.closed.injective T₁.factors T₂.factors Tₚ.factors
  refine ⟨G, hm, ?_⟩
  intro e
  obtain ⟨C⟩ := hm
  exact ⟨perverseImageAtTwo _ Q T₁ C.first minusculeFactor
      (shiftedConstant_isMiddlePerverse _ 1 (wholeStratum_range _ _) (fun _ ↦ rfl)),
    perverseImageAtTwo _ Q T₂ C.terminal (IntersectionComplex.surface d.point d.closed)
      (middlePerverse_of_iso _ e d.constant_perverse),
    perverseImageAtTwo _ Q Tₚ C.scalar (IntersectionComplex.point d.point) (point_perverse d),
    perverseImageAtTwo _ Q T₂ C.terminal convolution d.convolution_perverse⟩

end RepTheorySurvey.Geometric.MinusculeSupportIntersections
