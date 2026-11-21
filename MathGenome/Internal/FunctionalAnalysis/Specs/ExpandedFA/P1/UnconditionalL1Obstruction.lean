import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.DualBases
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C15SubsetProjections

/-! The ℓ¹/shrinking equivalence in `fa2:p1:unconditional-reflexivity`,
paper.tex 4336–4357. The copy of ℓ¹ may be any closed scalar-linear
subspace of the ambient space. It is not restricted to a prescribed block
sequence. Scalar index 0 denotes manuscript index 1. -/
noncomputable section
open Filter Topology
open scoped BigOperators
universe u v
namespace ExpandedFA.P1.UnconditionalL1Obstruction.Spec
open C01SequenceSpaces DualBasisBasicity.Spec

/-- A closed copy with the inherited norm and a bounded linear isomorphism. -/
def ContainsClosedL1 (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] : Prop :=
  ∃ M : Submodule 𝕜 E, IsClosed (M : Set E) ∧
    Nonempty (SequenceLp 𝕜 1 ≃L[𝕜] M)

/-- Native ordered bases, with unconditionality of their actual expansions. -/
def ShrinkingCriterion : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (b : SchauderBasis 𝕜 E),
    (∀ x, Summable (fun n => b.coord n x • b n)) →
    (IsShrinking b ↔ ¬ ContainsClosedL1 𝕜 E)

/-- The manuscript's raw unconditional basis acquires its unique continuous
coordinates through the accepted upstream basis interface. -/
def RawShrinkingCriterion : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {e : ℕ → E}, C15Unconditional.Spec.IsUnconditionalSchauderBasisValue 𝕜 E e →
    ∃ b : SchauderBasis 𝕜 E, b.basis = e ∧
      (IsShrinking b ↔ ¬ ContainsClosedL1 𝕜 E)

/-- Finite lists include the empty basis of the zero space. -/
def FiniteShrinkingCriterion : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {d : ℕ} (b : UnconditionalSchauderBasis (Fin d) 𝕜 E),
    DualBases.Spec.finiteShrinking b ↔ ¬ ContainsClosedL1 𝕜 E

/-- Raw finite lists, including length zero, use the same continuous coordinates. -/
def RawFiniteShrinkingCriterion : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {d : ℕ} {e : Fin d → E}, C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) e →
    ∃ b : UnconditionalSchauderBasis (Fin d) 𝕜 E, b.basis = e ∧
      (DualBases.Spec.finiteShrinking b ↔ ¬ ContainsClosedL1 𝕜 E)

/-- This implication holds for all Schauder bases, even conditional ones. -/
def ShrinkingExcludesL1 : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (b : SchauderBasis 𝕜 E), IsShrinking b → ¬ ContainsClosedL1 𝕜 E

end ExpandedFA.P1.UnconditionalL1Obstruction.Spec
