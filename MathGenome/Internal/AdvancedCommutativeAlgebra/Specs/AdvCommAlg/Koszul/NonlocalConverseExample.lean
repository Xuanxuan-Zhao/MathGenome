import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.OrderExample
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.Construction

/-! The nonlocal counterexample in RK-13, paper.tex:2510–2514.
The polynomial ring and coordinates are exactly those of the example after RK-02.
Positive homology vanishing refers to the canonical coefficient Koszul complex. -/
universe u
namespace Specs.AdvCommAlg.Koszul.NonlocalConverseExample
open _root_.AdvCommAlg.RegularSequence.OrderExample
open _root_.AdvCommAlg.Koszul

def properIdeal : Prop := ∀ (k : Type u) [Field k],
  Ideal.ofList ([Y * (1 - X), Z * (1 - X), X] : List (Poly k)) ≠ ⊤

def positiveHomologyVanishes : Prop := ∀ (k : Type u) [Field k]
  (q : ℕ), 0 < q →
    Subsingleton (homology (Poly k) ([Y * (1 - X), Z * (1 - X), X] : List (Poly k)) q)

def notWeaklyRegular : Prop := ∀ (k : Type u) [Field k],
  ¬ RingTheory.Sequence.IsWeaklyRegular (Poly k)
    ([Y * (1 - X), Z * (1 - X), X] : List (Poly k))

end Specs.AdvCommAlg.Koszul.NonlocalConverseExample
