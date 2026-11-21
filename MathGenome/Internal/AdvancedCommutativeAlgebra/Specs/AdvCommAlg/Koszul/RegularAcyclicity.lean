import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.Construction
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.Definitions

/-! The acyclicity assertion of RK-07, paper.tex:2261–2278.
Weak regularity is successive injectivity, without a nonzero final quotient.
Vanishing of a module is expressed by `Subsingleton`, so the zero ring,
the zero module, and the empty list require no exclusions. -/

universe u v
namespace Specs.AdvCommAlg.Koszul
open _root_.AdvCommAlg.Koszul

def weaklyRegularAcyclicity : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (x : List R), RingTheory.Sequence.IsWeaklyRegular M x →
    ∀ q : ℕ, 0 < q → Subsingleton (homology M x q)

end Specs.AdvCommAlg.Koszul
