import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Etale.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Universal
import Mathlib.FieldTheory.Separable

/-! Independent specifications for ET-11 (paper.tex, lines 1777–1819).
The algebra is only assumed to be of finite type; neither finite dimension
nor reducedness is an input. The finite product may have no factors.
-/
namespace Specs.AdvCommAlg.Etale.FieldAlgebraClassification

universe u v

/-- A finite product of finite separable field extensions, as a K-algebra.
The index and factor universes agree with that of B, as for the canonical
Artinian decomposition into quotients of B. No nonempty-index condition occurs.
-/
def FiniteSeparableProduct (K : Type u) (B : Type v)
    [Field K] [CommRing B] [Algebra K B] : Prop :=
  ∃ (I : Type v) (_ : Finite I) (L : I → Type v) (_ : ∀ i, Field (L i))
    (_ : ∀ i, Algebra K (L i)) (_ : B ≃ₐ[K] ∀ i, L i),
    ∀ i, FiniteDimensional K (L i) ∧ Algebra.IsSeparable K (L i)

/-- Both properties needed for the Artinian field decomposition are conclusions. -/
def finiteReducedOfOmegaZero : Prop :=
  ∀ (K : Type u) (B : Type v) [Field K] [CommRing B] [Algebra K B]
    [Algebra.FiniteType K B],
    Subsingleton (Differentials.omegaValue K B) →
      FiniteDimensional K B ∧ IsReduced B

/-- The first two conditions of the source theorem. -/
def omegaZeroIffEtale : Prop :=
  ∀ (K : Type u) (B : Type v) [Field K] [CommRing B] [Algebra K B]
    [Algebra.FiniteType K B],
    Subsingleton (Differentials.omegaValue K B) ↔ etaleValue K B

/-- The second and third conditions of the source theorem. Together with
omegaZeroIffEtale, this gives equivalence of all three conditions. -/
def etaleIffFiniteSeparableProduct : Prop :=
  ∀ (K : Type u) (B : Type v) [Field K] [CommRing B] [Algebra K B]
    [Algebra.FiniteType K B],
    etaleValue K B ↔ FiniteSeparableProduct K B

/-- The zero ring is included, without requiring a nontrivial factor. -/
def emptyProduct : Prop :=
  ∀ (K : Type u) (B : Type v) [Field K] [CommRing B] [Algebra K B]
    [Subsingleton B], etaleValue K B ∧ FiniteSeparableProduct K B

end Specs.AdvCommAlg.Etale.FieldAlgebraClassification
