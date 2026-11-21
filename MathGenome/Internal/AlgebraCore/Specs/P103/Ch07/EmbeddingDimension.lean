import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.DimensionConventions
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-!
The generator-count part of Theorem 7.7, paper.tex:1281–1289.
`ResidueField R` is R/𝔪. `CotangentSpace R` is 𝔪/(𝔪 • 𝔪),
and `Ideal.mem_toCotangent_ker` identifies its kernel with 𝔪².
The local-ring hypothesis includes a proper maximal ideal and excludes the zero ring.
Generators are elements of the actual maximal ideal, and their span is taken over R.
Minimality below means that deleting any one member destroys generation; no
independence or basis property is included in this definition.
The graded, domain and regular-sequence parts are allocated to later goals.
-/

namespace P103.Specs.Ch07.EmbeddingDimension

universe u v
open IsLocalRing Module
open P103.Specs.Ch06.DimensionConventions

def EmbeddingDimensionType :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R], ℕ

noncomputable def embeddingDimensionValue : EmbeddingDimensionType.{u} :=
  fun R _ _ _ => Module.finrank (ResidueField R) (CotangentSpace R)

def RegularLocalType :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R], Prop

noncomputable def regularLocalValue : RegularLocalType.{u} :=
  fun R _ _ _ => (embeddingDimensionValue R : WithBot ℕ∞) = ringDimensionValue R

def GeneratesMaximalIdeal {R : Type u} [CommRing R] [IsLocalRing R]
    {ι : Type v} (x : ι → maximalIdeal R) : Prop :=
  Submodule.span R (Set.range x) = ⊤

def MinimalGeneratingFamily {R : Type u} [CommRing R] [IsLocalRing R]
    {ι : Type v} (x : ι → maximalIdeal R) : Prop :=
  GeneratesMaximalIdeal x ∧
    ∀ i, Submodule.span R (x '' (Set.univ \ {i})) ≠ ⊤

def finite_dimensionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    FiniteDimensional (ResidueField R) (CotangentSpace R) ∧
      Module.rank (ResidueField R) (CotangentSpace R) =
        (embeddingDimensionValue R : Cardinal)

/-- Relates subtype generators to the usual ideal generated in R. -/
def generators_iff_ideal_spanType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] (ι : Type v)
    (x : ι → maximalIdeal R),
    GeneratesMaximalIdeal x ↔ Ideal.span (Set.range (fun i => (x i : R))) = maximalIdeal R

def span_iffType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (ι : Type v) (x : ι → maximalIdeal R),
    Submodule.span (ResidueField R)
      (Set.range (fun i => (maximalIdeal R).toCotangent (x i))) = ⊤ ↔
        GeneratesMaximalIdeal x

/-- Attainment and the lower bound characterize the least natural generator count. -/
def least_generator_countType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    IsLeast {n : ℕ | ∃ x : Fin n → maximalIdeal R, GeneratesMaximalIdeal x}
      (embeddingDimensionValue R)

def generator_lower_boundType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (ι : Type v) [Fintype ι] (x : ι → maximalIdeal R),
    GeneratesMaximalIdeal x → embeddingDimensionValue R ≤ Fintype.card ι

def basis_liftsType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (ι : Type v) (b : Basis ι (ResidueField R) (CotangentSpace R))
    (x : ι → maximalIdeal R),
    (∀ i, (maximalIdeal R).toCotangent (x i) = b i) → GeneratesMaximalIdeal x

def minimal_generators_basisType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (ι : Type v) (x : ι → maximalIdeal R),
    MinimalGeneratingFamily x →
      ∃ b : Basis ι (ResidueField R) (CotangentSpace R),
        ∀ i, b i = (maximalIdeal R).toCotangent (x i)

/-- A family of least possible finite cardinality also maps to a basis. -/
def minimum_generators_basisType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (ι : Type v) [Fintype ι] (x : ι → maximalIdeal R),
    GeneratesMaximalIdeal x → Fintype.card ι = embeddingDimensionValue R →
      ∃ b : Basis ι (ResidueField R) (CotangentSpace R),
        ∀ i, b i = (maximalIdeal R).toCotangent (x i)

def dimension_le_embeddingDimensionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    ringDimensionValue R ≤ (embeddingDimensionValue R : WithBot ℕ∞)

def dimension_boundType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (d : ℕ), ringDimensionValue R = (d : WithBot ℕ∞) → d ≤ embeddingDimensionValue R

def regular_iffType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (d : ℕ), ringDimensionValue R = (d : WithBot ℕ∞) →
      (regularLocalValue R ↔ embeddingDimensionValue R = d)

def regular_dimension_zeroType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    regularLocalValue R → ringDimensionValue R = (0 : WithBot ℕ∞) →
      maximalIdeal R = ⊥ ∧ IsField R

end P103.Specs.Ch07.EmbeddingDimension
