import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.EmbeddingDimension
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Regular.RegularSequence

/-! The regular-sequence assertion of Theorem 7.7 (paper.tex:1286,1291).
The quotient by each ordered prefix is the actual ideal quotient. Regularity
of a quotient uses Mathlib's equivalent generator-count definition, rather
than an assumed domain or regular-sequence certificate. -/
namespace P103.Specs.Ch07.RegularSequence

open IsLocalRing P103.Specs.Ch07.EmbeddingDimension
open P103.Specs.Ch06.DimensionConventions
universe u

/-- Every prefix quotient is regular local of the stated dimension; each
next generator multiplies injectively; the final ideal is proper. -/
def RegularGeneratorConclusions {R : Type u} [CommRing R]
    (d : ℕ) (xs : List R) : Prop :=
  (∀ i : ℕ, i ≤ d →
    IsRegularLocalRing (R ⧸ Ideal.ofList (xs.take i)) ∧
      ringDimensionValue (R ⧸ Ideal.ofList (xs.take i)) = ((d - i : ℕ) : WithBot ℕ∞)) ∧
  (∀ (i : ℕ) (hi : i < xs.length), Function.Injective
    (fun z : R ⧸ Ideal.ofList (xs.take i) =>
      Ideal.Quotient.mk (Ideal.ofList (xs.take i)) xs[i] * z)) ∧
  Ideal.ofList xs ≠ ⊤

/-- A d-element generating list in dimension d includes all ordered minimal
lists. No regularity of the list is assumed. Empty lists are allowed. -/
def generatingListType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (d : ℕ) (xs : List R), regularLocalValue R →
    ringDimensionValue R = (d : WithBot ℕ∞) → xs.length = d →
    Ideal.ofList xs = maximalIdeal R → RegularGeneratorConclusions d xs

/-- The shared deletion-minimal convention, with arbitrary ordered generators
and with no cardinality hypothesis or regular-sequence assumption. -/
def minimalGeneratorsType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (d : ℕ) (x : Fin d → maximalIdeal R), regularLocalValue R →
    MinimalGeneratingFamily x →
    ringDimensionValue R = (d : WithBot ℕ∞) ∧
      RegularGeneratorConclusions d (List.ofFn (fun i => (x i : R)))

end P103.Specs.Ch07.RegularSequence
