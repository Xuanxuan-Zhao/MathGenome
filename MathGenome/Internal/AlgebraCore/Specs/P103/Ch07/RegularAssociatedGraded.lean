import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.EmbeddingDimension
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.ReesGradedConstruction
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
The graded-ring assertion of Theorem 7.7 (paper.tex:1281–1289).
The ring is the canonical Rees quotient, with the actual `ringPiece` grading.
Regularity is the generator-count definition from EmbeddingDimension; no
injectivity or absence of relations is included in the hypotheses.
The family is arbitrary and minimal in the deletion sense, including an empty
family. The isomorphism is the evaluation map on its degree-one initial forms.
-/
namespace P103.RegularAssociatedGraded

noncomputable section
open IsLocalRing P103.Rees

universe u v
variable {R : Type u} [CommRing R] [IsLocalRing R]

instance residueAlgebra : Algebra (ResidueField R) (AssociatedRing (maximalIdeal R)) :=
  associatedBase (maximalIdeal R)

instance residueAlgebraTower :
    IsScalarTower R (ResidueField R) (AssociatedRing (maximalIdeal R)) :=
  associatedBaseTower (maximalIdeal R)

/-- The degree-one class of an element of the maximal ideal. -/
def initialForm (a : maximalIdeal R) : AssociatedRing (maximalIdeal R) :=
  ringClass (maximalIdeal R) 1 ⟨a.1, by simpa only [pow_one] using a.2⟩

/-- The canonical map, defined without any regularity assumption. -/
def canonicalMap {ι : Type v} (x : ι → maximalIdeal R) :
    MvPolynomial ι (ResidueField R) →ₐ[ResidueField R]
      AssociatedRing (maximalIdeal R) :=
  MvPolynomial.aeval (initialForm ∘ x)

end
end P103.RegularAssociatedGraded

namespace Specs.P103.RegularAssociatedGraded

open IsLocalRing _root_.P103.Rees _root_.P103.RegularAssociatedGraded
open _root_.P103.Specs.Ch07.EmbeddingDimension
open _root_.P103.Specs.Ch06.DimensionConventions

universe u v

/-- Every generating family gives the canonical graded surjection. -/
def gradedSurjectionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (ι : Type v) [Fintype ι] (x : ι → maximalIdeal R),
    GeneratesMaximalIdeal x →
      Function.Surjective (canonicalMap x) ∧
      ∀ n : ℕ,
        canonicalMap x '' (MvPolynomial.homogeneousSubmodule ι (ResidueField R) n :
          Set (MvPolynomial ι (ResidueField R))) =
            (ringPiece (maximalIdeal R) n : Set (AssociatedRing (maximalIdeal R)))

/-- The complete regular-local assertion, for any minimal generating family.
Equality of the images of all pieces gives a graded isomorphism in both directions.
The cardinality conclusion identifies the number of variables with dim R. -/
def gradedIsomorphismType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (ι : Type v) [Fintype ι] (x : ι → maximalIdeal R),
    regularLocalValue R → MinimalGeneratingFamily x →
      (Fintype.card ι : WithBot ℕ∞) = ringDimensionValue R ∧
      ∃ e : MvPolynomial ι (ResidueField R) ≃ₐ[ResidueField R]
          AssociatedRing (maximalIdeal R),
        (e : MvPolynomial ι (ResidueField R) → AssociatedRing (maximalIdeal R)) =
          canonicalMap x ∧
        (∀ i, e (MvPolynomial.X i) = initialForm (x i)) ∧
        ∀ n : ℕ,
          e '' (MvPolynomial.homogeneousSubmodule ι (ResidueField R) n :
            Set (MvPolynomial ι (ResidueField R))) =
              (ringPiece (maximalIdeal R) n : Set (AssociatedRing (maximalIdeal R)))

/-- Explicit dimension-zero boundary: the structural residue-field map is
an isomorphism onto the entire associated graded ring. -/
def dimensionZeroType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    regularLocalValue R → ringDimensionValue R = 0 →
      ∃ e : ResidueField R ≃ₐ[ResidueField R] AssociatedRing (maximalIdeal R),
        (e : ResidueField R → AssociatedRing (maximalIdeal R)) =
          algebraMap (ResidueField R) (AssociatedRing (maximalIdeal R)) ∧
        (ringPiece (maximalIdeal R) 0 = ⊤) ∧
        ∀ n : ℕ, 0 < n → ringPiece (maximalIdeal R) n = ⊥

end Specs.P103.RegularAssociatedGraded
