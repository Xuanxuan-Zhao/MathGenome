import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.GradedComparison
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Basis.Basic

/-! Independent contracts for the forward direction of RK-11,
`paper.tex:2380–2391, 2401–2435`. No separation, finite generation,
Noetherian, nonzero, or properness hypothesis is imposed on the comparison.
Properness occurs only in the stated conormal corollary. -/

universe u v
namespace AdvCommAlg.RegularSequence.AssociatedGraded.Core
open GradedComparison.Core
noncomputable section
variable {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- Every coefficient of a homogeneous relation modulo the next filtration
step lies in IM. This is an intermediate claim, not an assumed certificate. -/
def HomogeneousCoefficients (x : List R) : Prop :=
  ∀ (n : ℕ) (s : Finset (Fin x.length →₀ ℕ))
    (_hd : ∀ d ∈ s, d.degree = n) (m : (Fin x.length →₀ ℕ) → M),
    (∑ d ∈ s, monomialValue x d • m d) ∈
      (sequenceIdeal x ^ (n + 1) • (⊤ : Submodule R M)) →
    ∀ d ∈ s, m d ∈ (sequenceIdeal x • (⊤ : Submodule R M))

/-- The specified generator class in the actual conormal module I/I². -/
def conormalClass (x : List R) (i : Fin x.length) : (sequenceIdeal x).Cotangent :=
  (sequenceIdeal x).toCotangent
    ⟨x[i], Ideal.subset_span (List.getElem_mem i.isLt)⟩
end
end AdvCommAlg.RegularSequence.AssociatedGraded.Core

namespace AdvCommAlg.RegularSequence.AssociatedGraded.Specs
open P103.Rees GradedComparison.Core Core
noncomputable section

def coefficients_of_weaklyRegularType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R), RingTheory.Sequence.IsWeaklyRegular M x → HomogeneousCoefficients M x

def comparison_bijectiveType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R), RingTheory.Sequence.IsWeaklyRegular M x →
    Function.Bijective (GradedComparison.Core.comparison M x)

def gradedModuleEquivType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R), RingTheory.Sequence.IsWeaklyRegular M x →
    ∃ e : PolynomialModule M x ≃ₗ[PolynomialRing x] AssociatedModule (sequenceIdeal x) M,
      (∀ p, e p = GradedComparison.Core.comparison M x p) ∧
      (∀ n p, PolynomialHomogeneous M x n p ↔ e p ∈ modulePiece (sequenceIdeal x) M n)

def ringComparison_bijectiveType : Prop :=
  ∀ {R : Type u} [CommRing R] (x : List R),
    RingTheory.Sequence.IsWeaklyRegular R x →
    Function.Bijective (GradedComparison.Core.ringComparison x)

def gradedAlgebraEquivType : Prop :=
  ∀ {R : Type u} [CommRing R] (x : List R),
    RingTheory.Sequence.IsWeaklyRegular R x →
    ∃ e : PolynomialRing x ≃ₐ[R ⧸ sequenceIdeal x] AssociatedRing (sequenceIdeal x),
      (∀ p, e p = GradedComparison.Core.ringComparison x p) ∧
      (∀ n p, p.IsHomogeneous n ↔ e p ∈ ringPiece (sequenceIdeal x) n)

def conormalBasisType : Prop :=
  ∀ {R : Type u} [CommRing R] (x : List R),
    RingTheory.Sequence.IsRegular R x →
    ∃ b : Module.Basis (Fin x.length) (R ⧸ sequenceIdeal x) (sequenceIdeal x).Cotangent,
      ∀ i, b i = conormalClass x i

end
end AdvCommAlg.RegularSequence.AssociatedGraded.Specs
