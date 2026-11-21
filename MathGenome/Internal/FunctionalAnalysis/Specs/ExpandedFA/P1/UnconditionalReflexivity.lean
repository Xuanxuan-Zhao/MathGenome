import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.UnconditionalL1Obstruction
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.UnconditionalC0Obstruction

/-! Independent statements for `fa2:p1:unconditional-reflexivity`,
paper.tex 4336–4379. The hypotheses are the raw unique expansion and
unconditional convergence properties, without assumed coordinate continuity.
The finite version includes the empty basis. Copies of the sequence spaces
are arbitrary closed scalar-linear subspaces with bounded linear isomorphisms.
All duals and the canonical bidual map use continuous scalar-linear maps. -/

noncomputable section
universe u v
namespace ExpandedFA.P1.UnconditionalReflexivity.Spec
open DualBasisBasicity.Spec
open UnconditionalL1Obstruction.Spec (ContainsClosedL1)
open UnconditionalC0Obstruction.Spec (ContainsC0)

/-- Both basis properties and the resulting intrinsic reflexivity criterion. -/
def BasisFacts {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (b : SchauderBasis 𝕜 E) : Prop :=
  (IsShrinking b ↔ ¬ ContainsClosedL1 𝕜 E) ∧
  (IsBoundedlyComplete (𝕜 := 𝕜) b.basis ↔ ¬ ContainsC0 𝕜 E) ∧
  (C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E ↔
    ¬ ContainsC0 𝕜 E ∧ ¬ ContainsClosedL1 𝕜 E)

def UnconditionalBasisCharacterization : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {e : ℕ → E}, C15Unconditional.Spec.IsUnconditionalSchauderBasisValue 𝕜 E e →
    ∃ b : SchauderBasis 𝕜 E, b.basis = e ∧ BasisFacts b

def ReflexivityCriterion : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {e : ℕ → E}, C15Unconditional.Spec.IsUnconditionalSchauderBasisValue 𝕜 E e →
    (C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E ↔
      ¬ ContainsC0 𝕜 E ∧ ¬ ContainsClosedL1 𝕜 E)

/-- Applied to the closed span of an unconditional basic sequence, this is
also the final alternative in the source proof. -/
def ReflexivityAlternative : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {e : ℕ → E}, C15Unconditional.Spec.IsUnconditionalSchauderBasisValue 𝕜 E e →
    C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E ∨
      ContainsC0 𝕜 E ∨ ContainsClosedL1 𝕜 E

def FiniteBasisFacts {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {d : ℕ}
    (b : UnconditionalSchauderBasis (Fin d) 𝕜 E) : Prop :=
  (DualBases.Spec.finiteShrinking b ↔ ¬ ContainsClosedL1 𝕜 E) ∧
  (DualBases.Spec.finiteBoundedlyComplete (𝕜 := 𝕜) b.basis ↔ ¬ ContainsC0 𝕜 E) ∧
  (C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E ↔
    ¬ ContainsC0 𝕜 E ∧ ¬ ContainsClosedL1 𝕜 E)

def FiniteBasisCharacterization : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {d : ℕ} {e : Fin d → E}, C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) e →
    ∃ b : UnconditionalSchauderBasis (Fin d) 𝕜 E, b.basis = e ∧ FiniteBasisFacts b

def FiniteReflexivityCriterion : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {d : ℕ} {e : Fin d → E}, C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) e →
    (C04CanonicalMap.Spec.IsReflexiveValue 𝕜 E ↔
      ¬ ContainsC0 𝕜 E ∧ ¬ ContainsClosedL1 𝕜 E)

end ExpandedFA.P1.UnconditionalReflexivity.Spec
