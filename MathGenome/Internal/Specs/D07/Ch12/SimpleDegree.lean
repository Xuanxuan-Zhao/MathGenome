import MathGenome.Internal.Specs.D07.Ch12.PowerBasis
import MathGenome.Internal.Specs.D07.Ch12.FiniteAlgebraic

/-!
Independent specification for K07.12.simple_degree, paper.tex:3615–3621.
The chosen algebra structure specifies the embedding of K into L. Degree is
cardinal vector-space dimension, including for an arbitrary ambient extension.
The minimal polynomial's natural degree is used only under algebraicity, when
the upstream specification guarantees that the polynomial is nonzero.
-/

universe u v

namespace Specs.D07.Ch12.SimpleDegree

/-- The degree of an algebraic simple extension equals the degree of the
minimal polynomial. No finiteness is assumed of the ambient extension L/K. -/
def DegreeEqualsMinpolyDegree : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (α : L),
    IsAlgebraic K α →
      Module.rank K (IntermediateField.adjoin K {α}) =
        ((minpoly K α).natDegree : Cardinal.{v})

/-- Finite means that the cardinal dimension is a natural number. This
equivalence applies to every α, without an algebraicity premise. -/
def AlgebraicIffFiniteSimpleExtension : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (α : L),
    IsAlgebraic K α ↔
      ∃ n : ℕ, Module.rank K (IntermediateField.adjoin K {α}) = (n : Cardinal.{v})

/-- Membership in K means membership in the image of the specified embedding.
No algebraicity or finite-dimensionality assumption restricts this assertion. -/
def SimpleDegreeOneIffMemBase : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] (α : L),
    Module.rank K (IntermediateField.adjoin K {α}) = 1 ↔
      α ∈ Set.range (algebraMap K L)

end Specs.D07.Ch12.SimpleDegree
