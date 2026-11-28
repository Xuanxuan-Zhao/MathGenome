import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.FiniteStageClosedExtensions
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionEquivariantSplitting

noncomputable section

set_option autoImplicit false

open CategoryTheory Topology
open scoped MatrixGroups

namespace RepTheorySurvey.Geometric.MinusculeSupportIntersectionsSpecs

open Analytic
open LatticeModelSpecs MinusculeAndTwoStepSpecs RankTwoSchubertStrataSpecs
open ConvolutionUnitConeSpecs
open ConvolutionEquivariantSplittingSpecs (SplittingData)
open ConvolutionSplittingSpecs (orbitStratification)
open EquivariantIntersectionComplexesSpecs (ContinuousJets jetSystem Intertwines)
open FiniteStageClosedExtensionSpecs (SupportIntersections PointIntersectionMaps ClosedStrata)

abbrev Gr : TopCat.{0} := TopCat.of GL2Lattice

/-- Lattices satisfying the symmetric bound `t^N L₀ ⊆ L ⊆ t^(-N) L₀`. -/
def boundedSet (N : ℕ) : Set Gr :=
  {L | (scalarLattice 2 (N : ℤ)).val ≤ L.val ∧
    L.val ≤ (scalarLattice 2 (-(N : ℤ))).val}

abbrev Point (d : SplittingData) : TopCat.{0} :=
  TopCat.of ({d.point} : Set surface)

def pointEmbedding (d : SplittingData) (j : surface ⟶ Gr) : Point d ⟶ Gr :=
  closedInclusion ({d.point} : Set surface) ≫ j

/-- The factorization of a whole support through a stage that contains it. -/
structure SupportInStage {J : JetSystem.{0}} {A : ClosedStages Gr}
    (B : StageJetActions J A) {Y : TopCat.{0}} (i : Y ⟶ Gr)
    (S : JetAction J Y) (n : ℕ) where
  inclusion : Y ⟶ A.space n
  closed : IsClosedEmbedding inclusion
  factors : inclusion ≫ A.inclusion n = i
  actionSquare : Intertwines S (B.stageAction n) inclusion

/-- All stage intersections of the three supports, with their common point inclusion. -/
structure SupportGeometry {J : JetSystem.{0}} {A : ClosedStages Gr}
    (B : StageJetActions J A) (d : SplittingData) (j₁ : minuscule ⟶ Gr) (j₂ : surface ⟶ Gr)
    (S₁ : JetAction J minuscule) (S₂ : JetAction J surface) (Sₚ : JetAction J (Point d)) where
  first : SupportIntersections B j₁ S₁
  terminal : SupportIntersections B j₂ S₂
  scalar : SupportIntersections B (pointEmbedding d j₂) Sₚ
  pointMaps : PointIntersectionMaps terminal scalar
  firstAtZero : IsEmpty (first.space 0)
  terminalAtZero : IsEmpty (terminal.space 0)
  scalarAtZero : IsEmpty (scalar.space 0)
  terminalAtOne : Set.range (terminal.intoSupport 1) = {d.point}
  firstLevels : ∀ n k, (first.action n).cutoff ≤ k →
    S₁.cutoff ≤ k ∨ IsEmpty (first.space n)
  terminalLevels : ∀ n k, (terminal.action n).cutoff ≤ k →
    S₂.cutoff ≤ k ∨ IsEmpty (terminal.space n)
  scalarLevels : ∀ n k, (scalar.action n).cutoff ≤ k →
    Sₚ.cutoff ≤ k ∨ IsEmpty (scalar.space n)
  pointTerminalLevels : ∀ n k, (scalar.action n).cutoff ≤ k → (terminal.action n).cutoff ≤ k →
    (Sₚ.cutoff ≤ k ∧ S₂.cutoff ≤ k) ∨ IsEmpty (scalar.space n)
  firstInStage : ∀ n, 2 ≤ n → SupportInStage B j₁ S₁ n
  terminalInStage : ∀ n, 2 ≤ n → SupportInStage B j₂ S₂ n
  scalarInStage : ∀ n, 2 ≤ n → SupportInStage B (pointEmbedding d j₂) Sₚ n

/-- The stratification with the whole space as one smooth stratum of dimension `d`. -/
def wholeStratum (X : TopCat.{0}) (d : ℕ) : Stratification X where
  Index := Unit
  stratum _ := ⟨⊤, Set.univ, isClosed_univ, d⟩
  partition x := by
    refine ⟨(), ?_, fun _ _ ↦ Subsingleton.elim _ _⟩
    exact ⟨⟨⟨x, Set.mem_univ x⟩, Set.mem_univ _⟩, rfl⟩

/-- The dimension-preserving matches into the occupied stage-two orbit strata. -/
structure StageTwoStrata {A : ClosedStages Gr} (d : SplittingData)
    (P : Stratification (A.space 2)) (label : P.Index → DominantPair)
    (j₁ : minuscule ⟶ A.space 2) (j₂ : surface ⟶ A.space 2)
    (jₚ : Point d ⟶ A.space 2) where
  first : ClosedStrata j₁ (wholeStratum minuscule 1) P
  terminal : ClosedStrata j₂ (orbitStratification d.point d.closed) P
  scalar : ClosedStrata jₚ (wholeStratum (Point d) 0) P
  firstLabel : label (first.index ()).val = minusculePair
  terminalOpenLabel : label (terminal.index true).val = twoStepPair
  terminalClosedLabel : label (terminal.index false).val = scalarPair
  scalarLabel : label (scalar.index ()).val = scalarPair

/-- Perversity of the direct image in the containing stage and its extension to the union. -/
def PerverseClosedImage {Y : TopCat.{0}} {A : ClosedStages Gr}
    (P : ∀ n, Stratification (A.space n)) (j : Y ⟶ A.space 2)
    (i : Y ⟶ Gr) (F : BoundedBelow Y) : Prop :=
  IsMiddlePerverse (P 2) ((derivedDirectImage j).obj F).obj ∧
    IsFiniteStagePerverse A P ((derivedDirectImage i).obj F).obj

namespace Expected

/-- The support intersections, action squares and perversity for the minuscule square. -/
def MinusculeSupportIntersections : Prop :=
  ∀ (c : ContinuousJets) (A : ClosedStages Gr) (B : StageJetActions (jetSystem c) A)
    (_hStages : ∀ n, A.stage n = boundedSet n)
    (_hCutoff : ∀ n, (B.stageAction n).cutoff = 2 * n - 1)
    (_hAction : ∀ n k (hk : (B.stageAction n).cutoff ≤ k)
      (g : GL (Fin 2) O) (L : A.space n),
        (((B.stageAction n).action k hk).act
          (reduceGL 2 (k + 1) (Nat.succ_pos k) g, L)).val = positiveGLMap 2 g • L.val)
    (P : ∀ n, Stratification (A.space n))
    (label : (P 2).Index → DominantPair)
    (_hBound : ∀ s, OrbitBound (label s) 2)
    (_hRange : ∀ s, Set.range ((P 2).stratum s).inclusion = {L | L.val ∈ gl2Orbit (label s)})
    (_hDimension : ∀ s, ((P 2).stratum s).complexDimension = difference (label s))
    (d : SplittingData) (j₁ : minuscule ⟶ Gr) (j₂ : surface ⟶ Gr)
    (_hClosed₁ : IsClosedEmbedding j₁) (_hClosed₂ : IsClosedEmbedding j₂)
    (_hRange₁ : Set.range j₁ = colength 1) (_hRange₂ : Set.range j₂ = colength 2)
    (_hScalar : j₂ d.point = scalarPoint)
    (S₁ : JetAction (jetSystem c) minuscule) (S₂ : JetAction (jetSystem c) surface)
    (Sₚ : JetAction (jetSystem c) (Point d))
    (_hCutoff₁ : S₁.cutoff ≤ 1) (_hCutoff₂ : S₂.cutoff ≤ 1) (_hCutoffₚ : Sₚ.cutoff ≤ 1)
    (_hAction₁ : ∀ k (hk : S₁.cutoff ≤ k) (g : GL (Fin 2) O) (p : minuscule),
      j₁ ((S₁.action k hk).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, p)) =
        positiveGLMap 2 g • j₁ p)
    (_hAction₂ : ∀ k (hk : S₂.cutoff ≤ k) (g : GL (Fin 2) O) (p : surface),
      j₂ ((S₂.action k hk).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, p)) =
        positiveGLMap 2 g • j₂ p)
    (_hActionₚ : ∀ k (hk : Sₚ.cutoff ≤ k),
      (Sₚ.action k hk).act = AnalyticAction.projection _ _),
    ∃ G : SupportGeometry B d j₁ j₂ S₁ S₂ Sₚ,
      let i₁ := (G.firstInStage 2 (le_refl 2)).inclusion
      let i₂ := (G.terminalInStage 2 (le_refl 2)).inclusion
      let iₚ := (G.scalarInStage 2 (le_refl 2)).inclusion
      Nonempty (StageTwoStrata d (P 2) label i₁ i₂ iₚ) ∧
        ∀ (_terminalIC : (IntersectionComplex.shiftedConstant surface 2).obj ≅
            (IntersectionComplex.surface d.point d.closed).obj),
          PerverseClosedImage P i₁ j₁ minusculeFactor ∧
          PerverseClosedImage P i₂ j₂ (IntersectionComplex.surface d.point d.closed) ∧
          PerverseClosedImage P iₚ (pointEmbedding d j₂) (IntersectionComplex.point d.point) ∧
          PerverseClosedImage P i₂ j₂ convolution

end Expected
end RepTheorySurvey.Geometric.MinusculeSupportIntersectionsSpecs
