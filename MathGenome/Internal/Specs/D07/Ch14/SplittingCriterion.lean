import MathGenome.Internal.Specs.D07.Ch12.NormalDefinition
import MathGenome.Internal.Specs.D07.Ch12.SeparableDefinition
import MathGenome.Internal.Specs.D07.Ch12.DegreeDefinition

/-!
Independent specification for K07.14.splitting_criterion,
paper.tex:4157–4165 (chapters/M07.14.tex:75–83).

The chosen `Algebra K L` records the field embedding and scalar action.
Galois is written out as algebraic, normal, and separable, without an
automorphism-count condition. Finite degree uses the shared cardinal-degree
predicate. Splitting fields use the shared nonzero-polynomial predicate,
including both splitting and generation as a field by all roots.
No characteristic, closed-field, or finite-underlying-set assumption is made.
The last two statements have no finite-degree premise.
-/

universe u v

namespace Specs.D07.Ch14.SplittingCriterion

/-- The equivalence for an arbitrary finite extension. -/
def FiniteGaloisIffSeparableSplittingField : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    Ch12.DegreeDefinition.finiteExtensionValue K L →
      ((Algebra.IsAlgebraic K L ∧ Normal K L ∧
          Ch12.SeparableDefinition.extensionSeparableValue K L) ↔
        ∃ f : Polynomial K, f.Separable ∧
          Ch12.SplittingDefinition.splittingFieldValue K L f)

/-- Finiteness is a conclusion for every realization of a separable
polynomial's splitting field, including nonzero constants. -/
def SeparableSplittingFieldFinite : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : Polynomial K), f.Separable →
    Ch12.SplittingDefinition.splittingFieldValue K L f →
      Ch12.DegreeDefinition.finiteExtensionValue K L

/-- The converse does not require any prior finiteness assumption. -/
def SeparableSplittingFieldGalois : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : Polynomial K), f.Separable →
    Ch12.SplittingDefinition.splittingFieldValue K L f →
      Algebra.IsAlgebraic K L ∧ Normal K L ∧
        Ch12.SeparableDefinition.extensionSeparableValue K L

end Specs.D07.Ch14.SplittingCriterion
