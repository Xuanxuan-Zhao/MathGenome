import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.AssociatedGraded
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Conormal
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.SplittingCriterion
import Mathlib.Algebra.Polynomial.Div

/-! The application and counterexample in paper.tex:2457–2466.
The basis statement is given for every ring, hence in particular for every
polynomial presenting ring. The counterexample uses the literal quotient
k[X]/(X²), and the conormal map of the specified quotient surjection. -/
namespace AdvCommAlg.RegularSequence.ConormalExample

universe u
noncomputable section
open TensorProduct
open Specs.AdvCommAlg.Differentials

namespace Core
variable (k : Type u) [Field k]

abbrev squareIdeal : Ideal (Polynomial k) := Ideal.span {(Polynomial.X : Polynomial k) ^ 2}
abbrev Dual := Polynomial k ⧸ squareIdeal k
abbrev xbar : Dual k := Ideal.Quotient.mk (squareIdeal k) Polynomial.X

theorem quotientSurjective : Function.Surjective (algebraMap (Polynomial k) (Dual k)) :=
  Ideal.Quotient.mk_surjective

abbrev extension := conormalExtension k (Polynomial k) (Dual k) (quotientSurjective k)
abbrev Conormal := (extension k).Cotangent

/-- The actual defining relation, in the kernel of the quotient map. -/
def relation : (extension k).ker :=
  ⟨Polynomial.X ^ 2, by
    change Ideal.Quotient.mk (squareIdeal k) (Polynomial.X ^ 2) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))⟩

abbrev relationClass : Conormal k := Algebra.Extension.Cotangent.mk (relation k)
abbrev dX : Dual k ⊗[Polynomial k] KaehlerDifferential k (Polynomial k) :=
  1 ⊗ₜ[Polynomial k] KaehlerDifferential.D k (Polynomial k) Polynomial.X
abbrev conormalArrow : Conormal k →ₗ[Dual k]
    Dual k ⊗[Polynomial k] KaehlerDifferential k (Polynomial k) :=
  conormalMapValue k (Polynomial k) (Dual k) (quotientSurjective k)
end Core

namespace Specs
open AssociatedGraded.Core GradedComparison.Core Core

/-- Any finite regular generating list, including one in a polynomial ring,
gives the displayed basis over the literal quotient by its ideal. -/
def regularRelationsBasis : Prop :=
  ∀ {P : Type u} [CommRing P] (f : List P),
    RingTheory.Sequence.IsRegular P f →
    ∃ b : Module.Basis (Fin f.length) (P ⧸ sequenceIdeal f) (sequenceIdeal f).Cotangent,
      ∀ i, b i = conormalClass f i

/-- Characteristic two is included. No hypothesis that 2 is invertible is used,
so this includes every field in which 2 is invertible as well. -/
def dualNumbersExample : Prop :=
  ∀ (k : Type u) [Field k],
    RingTheory.Sequence.IsRegular (Polynomial k) [(Polynomial.X : Polynomial k) ^ 2] ∧
    xbar k ≠ 0 ∧ relationClass k ≠ 0 ∧
    xbar k • relationClass k ≠ 0 ∧
    conormalArrow k (relationClass k) = (2 * xbar k) • dX k ∧
    conormalArrow k (xbar k • relationClass k) = 0 ∧
    ¬ Function.Injective (conormalArrow k) ∧
    ¬ Specs.AdvCommAlg.FormalLifting.SplittingCriterion.SplitConormal
      k (Polynomial k) (Dual k) (quotientSurjective k)

end Specs
end
end AdvCommAlg.RegularSequence.ConormalExample
