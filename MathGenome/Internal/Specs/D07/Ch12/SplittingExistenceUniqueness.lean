import MathGenome.Internal.Specs.D07.Ch12.SplittingDefinition
import MathGenome.Internal.Specs.D07.Ch12.DegreeDefinition

/-!
Independent specification for K07.12.splitting_existence_uniqueness,
paper.tex:3702–3713. The splitting-field predicate includes the nonzero
condition, splitting, and generation as a field by all roots. Finiteness is
finite cardinal vector-space dimension, using the chosen structure map.
No separability, characteristic, or algebraic-closedness assumption is made.
-/

universe u v w z

namespace Specs.D07.Ch12.SplittingExistenceUniqueness

open Polynomial SplittingDefinition DegreeDefinition

/-- The constructed extension can be taken in the universe of its base.
Both its field structure and its chosen embedding are existential data. -/
def FiniteExistence : Prop :=
  ∀ (K : Type u) [Field K] (f : Polynomial K), f ≠ 0 →
    ∃ (L : Type u) (_ : Field L) (A : Algebra K L),
      @splittingFieldValue K L _ _ A f ∧
      @finiteExtensionValue K L _ _ A

/-- Every realization of a splitting field has finite degree. -/
def FiniteSplittingField : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : Polynomial K), splittingFieldValue K L f → finiteExtensionValue K L

/-- Uniqueness is existence of an isomorphism commuting with the specified
base embeddings; no uniqueness of the isomorphism is asserted. -/
def Uniqueness : Prop :=
  ∀ (K : Type u) (L : Type v) (E : Type w)
    [Field K] [Field L] [Field E] [Algebra K L] [Algebra K E]
    (f : Polynomial K),
    splittingFieldValue K L f → splittingFieldValue K E f →
      Nonempty (L ≃ₐ[K] E)

/-- The full coefficient-transport conclusion for possibly unequal bases
and arbitrary specified embeddings into their splitting fields. -/
def BaseIsomorphismExtension : Prop :=
  ∀ (K : Type u) (K' : Type v) (L : Type w) (L' : Type z)
    [Field K] [Field K'] [Field L] [Field L'] [Algebra K L] [Algebra K' L']
    (σ : K ≃+* K') (f : Polynomial K),
    splittingFieldValue K L f →
    splittingFieldValue K' L' (f.map σ.toRingHom) →
      ∃ e : L ≃+* L', ∀ a : K,
        e (algebraMap K L a) = algebraMap K' L' (σ a)

end Specs.D07.Ch12.SplittingExistenceUniqueness
