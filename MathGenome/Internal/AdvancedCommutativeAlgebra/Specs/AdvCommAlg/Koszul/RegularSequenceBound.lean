import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.TopHomologyAndRegularElement
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.Definitions

/-! The iterated assertion of RK-14, paper.tex:2527–2557.
The ring and coefficient module are arbitrary. In particular neither
Noetherianity nor finite generation of the module is assumed. -/

open scoped Pointwise
noncomputable section
universe u v
namespace Specs.AdvCommAlg.Koszul.RegularSequenceBound
open _root_.AdvCommAlg.Koszul _root_.AdvCommAlg.Koszul.TopHomology

/-- A regular list in an ideal bounds the support of Koszul homology, and
its extremal group is the annihilator in the quotient by that whole list.
The extremal group is allowed to be zero; both lists may be empty. -/
def regularSequenceBound : Prop := ∀ {R : Type u} [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M]
  (I : Ideal R) (x y : List R),
  listIdeal x = I → Nontrivial (M ⧸ (I • ⊤ : Submodule R M)) →
  (∀ a ∈ y, a ∈ I) → RingTheory.Sequence.IsRegular M y →
  y.length ≤ x.length ∧
  (∀ q : ℕ, x.length - y.length < q → Subsingleton (homology M x q)) ∧
  Nonempty (homology M x (x.length - y.length) ≃ₗ[R]
    idealAnnihilator (M ⧸ (Ideal.ofList y • ⊤ : Submodule R M)) I)

end Specs.AdvCommAlg.Koszul.RegularSequenceBound
