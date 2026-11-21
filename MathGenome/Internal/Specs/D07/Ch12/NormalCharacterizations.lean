import MathGenome.Internal.Specs.D07.Ch12.NormalDefinition
import MathGenome.Internal.Specs.D07.Ch12.SplittingExistenceUniqueness
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
Independent specification of K07.12.normal_characterizations
(paper.tex:3847–3860).

All structure maps are specified by the algebra instances, and the scalar
tower identifies their composite. Thus the image of L in Ω means the range
of the specified embedding, rather than an equality of unrelated field types.
There is no finite-degree or separability hypothesis in the embedding criterion
or in the change of intermediate base. The splitting-field predicate includes
both nonzeroness of the polynomial and generation by its roots.
-/

universe u v w

namespace Specs.D07.Ch12.NormalCharacterizations

/-- Every embedding has exactly the original embedded image, also for infinite
algebraic extensions. Ω is an arbitrary specified algebraic closure of K. -/
def NormalIffEmbeddingImage : Prop :=
  ∀ (K : Type u) (L : Type v) (Ω : Type w)
    [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    [Algebra.IsAlgebraic K L] [IsAlgClosure K Ω],
    Normal K L ↔
      ∀ σ : L →ₐ[K] Ω,
        Set.range (σ : L → Ω) = Set.range (algebraMap L Ω)

/-- Finite degree is cardinal vector-space dimension being a natural number,
using the shared degree definition. Nonzero constants are permitted. -/
def FiniteNormalIffSplittingField : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L],
    DegreeDefinition.finiteExtensionValue K L →
      (Normal K L ↔ ∃ f : Polynomial K, SplittingDefinition.splittingFieldValue K L f)

/-- A normal extension remains normal over every intermediate base, expressed
for arbitrary compatible embeddings K → M → L. -/
def NormalOverIntermediateBase : Prop :=
  ∀ (K : Type u) (M : Type v) (L : Type w)
    [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra K L] [Algebra M L] [IsScalarTower K M L],
    Normal K L → Normal M L

end Specs.D07.Ch12.NormalCharacterizations
