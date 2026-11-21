import MathGenome.Internal.Specs.D07.Ch14.PolynomialRootAction
import MathGenome.Internal.Specs.D07.Ch02.TranspositionsParity
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Algebra.Group.Even

/-!
Independent specification of K07.14.discriminant, paper.tex:4280–4290.
The discriminant here is the square of the displayed root-difference product,
without a monicity hypothesis. All splitting-field realizations and all
numberings are allowed. The base embedding is the specified Algebra structure.
Empty products (degrees zero and one) are retained. The characteristic condition
is written as (2 : K) ≠ 0, equivalently char K ≠ 2 for a field.
-/

universe u v

namespace Specs.D07.Ch14.Discriminant

open Polynomial

/-- Exactly the source's product, with the difference in the order a_i - a_j. -/
def differenceProduct {L : Type v} [CommRing L] {n : ℕ} (a : Fin n → L) : L :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (a i - a j)

/-- The accepted root action conjugated by the specified numbering. -/
def numberedAction {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {f : K[X]} {n : ℕ} (b : Fin n ≃ f.rootSet L) :
    (L ≃ₐ[K] L) →* Equiv.Perm (Fin n) :=
  b.symm.permCongrHom.toMonoidHom.comp (PolynomialRootAction.rootPermutationValue K L f)

/-- The alternating sign law holds for arbitrary lists of field elements. -/
def PermutationSign : Prop :=
  ∀ (L : Type v) [Field L] (n : ℕ) (a : Fin n → L) (π : Equiv.Perm (Fin n)),
    differenceProduct (a ∘ π) = ((Equiv.Perm.sign π : ℤ) : L) * differenceProduct a

/-- Distinct roots ensure the product is nonzero, including the empty product. -/
def ProductNonzero : Prop :=
  ∀ (L : Type v) [Field L] (n : ℕ) (a : Fin n → L),
    Function.Injective a → differenceProduct a ≠ 0

/-- Each splitting-field automorphism acts on D by the sign of its root action. -/
def AutomorphismSign : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : K[X]) (n : ℕ) (b : Fin n ≃ f.rootSet L) (σ : L ≃ₐ[K] L),
    σ (differenceProduct (fun i => (b i).val)) =
      ((Equiv.Perm.sign (numberedAction b σ) : ℤ) : L) *
        differenceProduct (fun i => (b i).val)

/-- D² is a nonzero element of the embedded base field; finiteness and
Galoisness of the splitting field are conclusions available from separability. -/
def DiscriminantInBase : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : K[X]) (n : ℕ), f.Separable →
    Ch12.SplittingDefinition.splittingFieldValue K L f → f.natDegree = n →
    ∀ b : Fin n ≃ f.rootSet L,
      ∃ Δ : K, Δ ≠ 0 ∧
        algebraMap K L Δ = differenceProduct (fun i => (b i).val) ^ 2

/-- Containment of the actual numbered root group in A_n is equivalent to
squareness of the base element whose image is D². -/
def AlternatingIffSquare : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : K[X]) (n : ℕ), (2 : K) ≠ 0 → f.Separable →
    Ch12.SplittingDefinition.splittingFieldValue K L f → f.natDegree = n →
    ∀ (b : Fin n ≃ f.rootSet L) (Δ : K),
      algebraMap K L Δ = differenceProduct (fun i => (b i).val) ^ 2 →
      ((numberedAction b).range ≤ alternatingGroup (Fin n) ↔ IsSquare Δ)

/-- The usual nonmonic root normalization multiplies Δ by the even power
of the nonzero leading coefficient, preserving precisely its square test.
The universal coefficient/resultant formula is separately allocated in Ch19. -/
def LeadingCoefficientSquareTest : Prop :=
  ∀ (K : Type u) [Field K] (f : K[X]) (Δ : K), f ≠ 0 →
    (IsSquare (f.leadingCoeff ^ (2 * (f.natDegree - 1)) * Δ) ↔ IsSquare Δ)

/-- The complete source conclusion with the base discriminant constructed,
including the equivalent test for its usual leading-coefficient normalization. -/
def DiscriminantCriterion : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (f : K[X]) (n : ℕ), (2 : K) ≠ 0 → f.Separable →
    Ch12.SplittingDefinition.splittingFieldValue K L f → f.natDegree = n →
    ∀ b : Fin n ≃ f.rootSet L,
      ∃ Δ : K, Δ ≠ 0 ∧
        algebraMap K L Δ = differenceProduct (fun i => (b i).val) ^ 2 ∧
        ((numberedAction b).range ≤ alternatingGroup (Fin n) ↔ IsSquare Δ) ∧
        ((numberedAction b).range ≤ alternatingGroup (Fin n) ↔
          IsSquare (f.leadingCoeff ^ (2 * (n - 1)) * Δ))

end Specs.D07.Ch14.Discriminant
