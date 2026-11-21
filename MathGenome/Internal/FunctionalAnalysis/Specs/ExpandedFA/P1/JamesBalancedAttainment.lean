import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.EberleinSmulian
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.JamesBlockLemma
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.JamesWitness

/-! The real balanced step of James's theorem, paper.tex:3718–3750.
No convexity or separability assumption is imposed on A. The continuous dual
is formed with the norm topology; closedness and compactness use the weak topology.
-/
universe u
namespace ExpandedFA.P1.JamesBalancedAttainment.Spec

noncomputable abbrev weakTopology (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  EberleinSmulian.Spec.weakTopology ℝ E

/-- A noncompact balanced set has a finite absolute supremum which is
strictly larger than the value at every point of the set. -/
def NoncompactHasNonattaining : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : Set E), A.Nonempty → Balanced ℝ A → A ⊆ Metric.closedBall (0 : E) 1 →
    @IsClosed E (weakTopology E) A → ¬ @IsCompact E (weakTopology E) A →
    ∃ z : E →L[ℝ] ℝ,
      BddAbove ((fun x => |z x|) '' A) ∧
      ∀ x ∈ A, |z x| < sSup ((fun y => |z y|) '' A)

/-- Attainment of every finite absolute supremum implies weak compactness. -/
def BalancedAttainmentCompact : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : Set E), A.Nonempty → Balanced ℝ A → A ⊆ Metric.closedBall (0 : E) 1 →
    @IsClosed E (weakTopology E) A →
    (∀ f : E →L[ℝ] ℝ, BddAbove ((fun x => |f x|) '' A) ∧
      ∃ x ∈ A, |f x| = sSup ((fun y => |f y|) '' A)) →
    @IsCompact E (weakTopology E) A

end ExpandedFA.P1.JamesBalancedAttainment.Spec
