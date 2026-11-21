import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.Construction
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.GradedComparison

/-! RK-15, paper.tex:2560–2564 and 2584–2612.
The comparison is exactly the shared RK-11 evaluation map. In particular the
conclusion does not include the nonzero-quotient clause of quasi-regularity.
There are no finiteness, separation, properness, or Noetherian assumptions. -/
noncomputable section
universe u v
namespace Specs.AdvCommAlg.Koszul
open _root_.AdvCommAlg.Koszul
open _root_.AdvCommAlg.RegularSequence.GradedComparison.Core
open _root_.P103.Rees

def degreeOneComparisonBijective : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R), Subsingleton (homology M x 1) →
      Function.Bijective (comparison M x)

/-- Both the map and its inverse preserve homogeneous components. -/
def degreeOneComparisonGradedIso : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R), Subsingleton (homology M x 1) →
      ∃ e : PolynomialModule M x ≃ₗ[PolynomialRing x]
          AssociatedModule (sequenceIdeal x) M,
        (e : PolynomialModule M x → AssociatedModule (sequenceIdeal x) M) =
          comparison M x ∧
        ∀ (n : ℕ) (p : PolynomialModule M x),
          PolynomialHomogeneous M x n p ↔ e p ∈ modulePiece (sequenceIdeal x) M n

end Specs.AdvCommAlg.Koszul
