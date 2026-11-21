import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Existence.ReflexiveWeakCompactness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05BidualIsometry
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C12WeakStarComparison
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14WeakSubsequence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14BallCharacterization

noncomputable section
open Set Filter
open scoped Topology
universe u
namespace VariationalNotes.Existence

/-- Canonical evaluation into the norm-continuous bidual. -/
def canonicalEvaluation : Specs.canonicalEvaluationType.{u} := Specs.canonicalEvaluation

/-- Reflexivity is surjectivity of the canonical evaluation map. -/
def IsReflexive : Specs.IsReflexiveType.{u} := Specs.IsReflexive

/-- σ(X,X′), using the original norm-continuous dual. -/
def weakTopology : Specs.weakTopologyType.{u} := Specs.weakTopology

/-- σ(X′,X), on the carrier of the original norm-continuous dual. -/
def weakStarTopology : Specs.weakStarTopologyType.{u} := Specs.weakStarTopology

theorem canonicalEvaluation_apply : Specs.canonicalEvaluation_apply.{u} := by
  intro X _ _ x f
  rfl

/-- Hahn–Banach gives the norm isometry without completeness assumptions. -/
theorem canonicalEvaluation_isometry : Specs.canonicalEvaluation_isometry.{u} := by
  intro X _ _
  exact (ExpandedFA.P1.C05BidualIsometry.canonicalEvaluation_linear_isometry ℝ X).2.2

/-- Under surjectivity, every bidual test is evaluation at a vector of X. -/
theorem dual_weakTopology_eq_weakStarTopology :
    Specs.dual_weakTopology_eq_weakStarTopology.{u} := by
  intro X _ _ hX
  exact ((ExpandedFA.P1.C12WeakStarComparison.weakStar_eq_weak_iff_surjective ℝ X).mpr
    hX).symm

/-- The library proof uses the separable closed span of the sequence and
sequential Alaoglu there, so no separability of X is required. -/
theorem reflexive_weak_subsequence : Specs.reflexive_weak_subsequence.{u} := by
  intro X _ _ _ hX a ha
  obtain ⟨k, hk, x, hx⟩ :=
    ExpandedFA.P1.C14WeakSubsequence.reflexive_weak_subsequence ℝ X hX a ha
  refine ⟨k, hk, x, ?_⟩
  have ht : ExpandedFA.P1.C12DualPairSpec.DualPairTopologyValue ℝ X
      (X →L[ℝ] ℝ) (topDualPairing ℝ X) = instTopologicalSpaceWeakSpace ℝ X :=
    @induced_id (WeakSpace ℝ X) _
  rw [ht] at hx
  exact hx

/-- Topological weak compactness, separately from sequential compactness.
The bounded weakly closed set characterization covers all centers and radii. -/
theorem reflexive_closedBall_isWeaklyCompact :
    Specs.reflexive_closedBall_isWeaklyCompact.{u} := by
  intro X _ _ _ hX c r
  have hu := (ExpandedFA.P1.C14BallCharacterization.reflexive_iff_weakCompact_unitBall
    ℝ X).mp hX
  have hc : @IsClosed X (ExpandedFA.P1.C12DualPairSpec.DualPairTopologyValue ℝ X
      (X →L[ℝ] ℝ) (topDualPairing ℝ X)) (Metric.closedBall c r) := by
    simpa only [Metric.closedBall, dist_eq_norm] using
      ExpandedFA.P1.C12NormLsc.weak_closed_balls ℝ X c r
  have hb := (ExpandedFA.P1.C14BallCharacterization.weakCompact_unitBall_iff_closed_bounded
    ℝ X).mp hu (Metric.closedBall c r) Metric.isBounded_closedBall hc
  have ht : ExpandedFA.P1.C12DualPairSpec.DualPairTopologyValue ℝ X
      (X →L[ℝ] ℝ) (topDualPairing ℝ X) = instTopologicalSpaceWeakSpace ℝ X :=
    @induced_id (WeakSpace ℝ X) _
  rw [ht] at hb
  change @IsCompact X (instTopologicalSpaceWeakSpace ℝ X)
    (id '' Metric.closedBall c r)
  rw [Set.image_id]
  exact hb

end VariationalNotes.Existence
